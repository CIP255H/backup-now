#!/usr/bin/env python3
"""
LHBM - Local Hosted Backups Management (single-file version)
==============================================================
Aplikasi desktop independen (Linux/Mac) untuk memantau perubahan
file/folder secara otomatis (track) dan menyimpan backup secara
HEMAT RUANG memakai skema "manifest + delta": tiap kali ada
perubahan, hanya file yang benar-benar berubah/baru yang disalin
ke arsip kecil (`<ts>.delta.zip`); file yang tidak berubah cukup
dirujuk lewat manifest teks kecil (`<ts>.manifest.json`), tidak
disalin ulang. Zip lengkap untuk suatu titik waktu baru dirakit
saat kamu benar-benar melakukan Recall (on-demand), bukan disimpan
permanen tiap snapshot.

Alur pemakaian (sesuai README):

Cara Track:
    1. Tambahkan file/folder yang mau dipantau (source)
    2. Tentukan folder tujuan backup (destination)
    3. Atur interval cek (per detik/menit, sesuai pilihan) dan durasi
       tracking total (dalam jam, 0 = tanpa batas/sampai di-stop manual)
    4. Selesai - LHBM otomatis membuat .zip baru setiap kali ada
       file yang berubah/ditambah/dihapus

Cara Recall:
    1. Cari folder backup (destination) kamu
    2. Buka folder "zips" di dalamnya
    3. Pilih titik waktu (timestamp) mana yang mau direcall
    4. Ambil (copy) zip tersebut, atau langsung Extract lewat LHBM
    5. Unzip / selesai

Cara jalankan:
    python3 local_backup_manager.py

Tidak butuh library eksternal - hanya Python standard library + Tkinter.
Kalau tkinter belum ada:
    sudo apt install python3-tk      (Ubuntu/Debian)
    sudo dnf install python3-tkinter (Fedora)
    brew install python-tk           (macOS Homebrew)

Config tersimpan otomatis di ~/.config/local-backup-manager/config.json
"""

import concurrent.futures
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
import uuid
import zipfile
from collections import OrderedDict
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from tkinter import ttk, filedialog, messagebox
from typing import Iterator, List, Optional, Tuple

APP_VERSION = "3.3"


CONFIG_DIR = Path.home() / ".config" / "local-backup-manager"
CONFIG_FILE = CONFIG_DIR / "config.json"
ZIPS_DIRNAME = "zips"


@dataclass
class BackupJob:
    id: str
    name: str
    source: str             
    destination: str      
    interval_value: int = 30     
    interval_unit: str = "detik" 
    duration_hours: float = 0.0 
    retention: int = 10      
    mirror_delete: bool = False
    check_mode: str = "quick" 
    excludes: list = field(default_factory=list)
    enabled: bool = False

    def interval_seconds(self) -> int:
        multiplier = 60 if self.interval_unit == "menit" else 1
        return max(1, int(self.interval_value) * multiplier)

    def interval_display(self) -> str:
        return f"{self.interval_value} {self.interval_unit}"

    def duration_display(self) -> str:
        return "Tanpa batas" if not self.duration_hours or self.duration_hours <= 0 else f"{self.duration_hours:g} jam"

    def zips_dir(self) -> Path:
    
        safe_name = "".join(c if c.isalnum() or c in ("-", "_") else "_" for c in self.name) or self.id
        return Path(self.destination) / ZIPS_DIRNAME / f"{safe_name}_{self.id}"


def new_job_id() -> str:
    return str(uuid.uuid4())[:8]


def _migrate_job_dict(d: dict) -> dict:
    """Konversi config lama (field 'interval' dalam detik) ke skema baru
    interval_value + interval_unit, supaya job lama tidak hilang saat update."""
    d = dict(d)
    if "interval" in d and "interval_value" not in d:
        old_seconds = d.pop("interval")
        try:
            old_seconds = int(old_seconds)
        except (TypeError, ValueError):
            old_seconds = 30
        if old_seconds % 60 == 0 and old_seconds >= 60:
            d["interval_value"] = old_seconds // 60
            d["interval_unit"] = "menit"
        else:
            d["interval_value"] = old_seconds
            d["interval_unit"] = "detik"
    d.pop("interval", None)
    d.setdefault("duration_hours", 0.0)
    return d


def load_jobs() -> List[BackupJob]:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    if not CONFIG_FILE.exists():
        return []
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            raw = json.load(f)
        return [BackupJob(**_migrate_job_dict(d)) for d in raw]
    except (json.JSONDecodeError, TypeError, ValueError):
        backup_path = CONFIG_FILE.with_suffix(".json.bak")
        try:
            CONFIG_FILE.replace(backup_path)
        except OSError:
            pass
        return []


def save_jobs(jobs: List[BackupJob]) -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    data = [asdict(j) for j in jobs]
    tmp_file = CONFIG_FILE.with_suffix(".json.tmp")
    with open(tmp_file, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    tmp_file.replace(CONFIG_FILE)


CHECKSUM_CACHE_FILE = CONFIG_DIR / "checksum_cache.json"


class ChecksumCache:
    """
    Cache checksum (SHA-256) yang disimpan di disk, terpisah dari manifest
    job. Sebelumnya, "cache" hash cuma hidup di dalam manifest terakhir
    tiap job (state di memori JobRunner._state) - begitu manifest lama
    dihapus lewat retention/pruning, atau begitu aplikasi direstart tanpa
    manifest yang cocok, file yang sebenarnya tidak berubah bisa saja
    di-hash ulang dari nol. ChecksumCache mengatasi ini dengan menyimpan
    setiap hasil hash secara independen, seumur hidup file itu sendiri:

      Key   : "<path_absolut>|<size>|<mtime>"
      Value : sha256 hex digest

    Selama mtime+size sebuah path belum berubah, hash-nya tidak perlu
    dihitung ulang - baik oleh job yang sama, job lain yang memantau path
    tumpang tindih, maupun setelah aplikasi direstart.

    - Thread-safe: dipakai bersamaan oleh beberapa JobRunner.
    - Kapasitas dibatasi (MAX_ENTRIES) dengan eviction FIFO/LRU sederhana
      lewat OrderedDict, supaya cache tidak tumbuh tanpa batas di mesin
      yang memantau jutaan file kecil selama bertahun-tahun.
    - Penulisan ke disk di-debounce (minimal MIN_SAVE_INTERVAL detik
      antar simpan) supaya tidak menulis ulang file JSON di setiap siklus
      scan kalau interval cek job diset sangat pendek (mis. tiap detik).
    """

    MAX_ENTRIES = 50_000
    MIN_SAVE_INTERVAL = 5.0  
    def __init__(self, path: Path = CHECKSUM_CACHE_FILE):
        self._path = path
        self._lock = threading.Lock()
        self._data: "OrderedDict[str, str]" = OrderedDict()
        self._dirty = False
        self._last_save = 0.0
        self._load()

    @staticmethod
    def make_key(path: str, size: int, mtime: float) -> str:
        return f"{path}|{size}|{mtime}"

    def _load(self):
        if not self._path.exists():
            return
        try:
            with open(self._path, "r", encoding="utf-8") as f:
                raw = json.load(f)
            if isinstance(raw, dict):
                self._data = OrderedDict(raw)
        except (json.JSONDecodeError, OSError):
            pass

    def get(self, key: str) -> Optional[str]:
        with self._lock:
            val = self._data.get(key)
            if val is not None:
                self._data.move_to_end(key) 
            return val

    def put(self, key: str, digest: str):
        with self._lock:
            self._data[key] = digest
            self._data.move_to_end(key)
            excess = len(self._data) - self.MAX_ENTRIES
            for _ in range(max(0, excess)):
                self._data.popitem(last=False)  
            self._dirty = True

    def save(self, force: bool = False):
        """Simpan ke disk kalau ada perubahan. Di-debounce kecuali force=True
        (dipakai saat job/app benar-benar berhenti, supaya hash terakhir
        tidak hilang)."""
        with self._lock:
            if not self._dirty:
                return
            now = time.monotonic()
            if not force and (now - self._last_save) < self.MIN_SAVE_INTERVAL:
                return
            try:
                CONFIG_DIR.mkdir(parents=True, exist_ok=True)
                tmp = self._path.with_suffix(".json.tmp")
                with open(tmp, "w", encoding="utf-8") as f:
                    json.dump(self._data, f)
                tmp.replace(self._path)
                self._dirty = False
                self._last_save = now
            except OSError:
                pass



_checksum_cache = ChecksumCache()



class JobRunner(threading.Thread):
    """
    Memantau `job.source` setiap `job.interval_seconds()` detik.

    Skema penyimpanan "manifest + delta" (hemat ruang):
      - `<ts>.delta.zip`  : HANYA berisi file yang baru/berubah sejak
        snapshot terakhir (bukan seluruh source).
      - `<ts>.manifest.json` : file teks kecil (JSON) yang mendaftar semua
        file pada titik waktu `ts`, masing-masing menunjuk ke delta.zip
        mana isinya tersimpan (bisa delta.zip saat ini, atau delta.zip
        yang lebih lama kalau file itu tidak berubah).

    Full zip HANYA dirakit sesaat, on-demand, ketika user melakukan Recall
    (lihat RecallDialog._reconstruct_manifest), bukan disimpan permanen.

    --- Optimisasi kinerja (v3.2) ---
    1. Scan directory pakai `os.scandir` rekursif, bukan `os.walk` +
       `os.stat` terpisah - `DirEntry.stat()` memakai hasil yang sudah
       didapat scandir (di Linux tidak perlu syscall stat() kedua),
       jadi jumlah syscall per file kira-kira setengahnya dibanding versi
       sebelumnya. Ini paling terasa di folder besar / drive eksternal /
       folder sync cloud yang I/O-nya relatif lambat.
    2. Mode "hash": sebelumnya SEMUA file di-hash ulang setiap siklus,
       walau isinya tidak berubah. Sekarang ada quick pre-filter
       (mtime+size) dulu - hash SHA-256 cuma dihitung untuk file yang
       mtime/size-nya berubah dibanding cek terakhir. Untuk folder yang
       sebagian besar isinya statis, ini memangkas kerja hashing sangat
       signifikan tiap siklus (bukan cuma di awal).
    3. Hashing file yang lolos pre-filter dijalankan paralel lewat
       ThreadPoolExecutor (I/O-bound: waktu tunggu disk/network jadi bisa
       tumpang-tindih antar file, bukan menunggu satu-satu).
    4. Ukuran buffer baca untuk hashing dinaikkan dari 64 KB ke 1 MB,
       mengurangi jumlah pemanggilan read() untuk file besar.
    5. Exclude pattern (`fnmatch`) di-precompile jadi regex sekali di awal
       thread, bukan di-parse ulang untuk setiap file di setiap siklus.

    --- Optimisasi kinerja (v3.3) ---
    6. Checksum cache persisten (`ChecksumCache`, lihat di atas): hash yang
       lolos pre-filter mtime+size dicek dulu ke cache disk sebelum file
       benar-benar dibaca ulang. Cache ini independen dari manifest job,
       jadi tetap kena hit walau manifest lama sudah dihapus retention,
       job baru saja direstart, atau job lain memantau path yang sama.
    7. Hashing pakai `hashlib.file_digest()` (Python 3.11+) kalau tersedia
       - implementasi C yang membaca & meng-update hash langsung tanpa
       loop Python per-chunk, lebih cepat dari loop manual untuk file
       besar. Otomatis fallback ke loop manual di Python < 3.11.
    8. Jumlah worker hashing paralel kini menyesuaikan jumlah core CPU
       (dulu tetap 8), dengan batas atas wajar - karena kerjanya I/O-bound
       (menunggu disk), memakai lebih banyak worker daripada core CPU
       tetap menguntungkan sampai batas tersebut.
    9. Recall (Get Zip Away / Extract Now) sekarang mengalirkan isi file
       satu-per-satu dari delta.zip ke tujuan (bukan mengumpulkan seluruh
       isi backup ke memori dulu sebagai list besar), sehingga pemakaian
       memori saat me-recall backup besar jauh lebih rendah dan hampir
       konstan terlepas dari jumlah/ukuran file di dalamnya.
    """

    HASH_CHUNK_SIZE = 1024 * 1024  
    MAX_HASH_WORKERS = min(32, max(4, (os.cpu_count() or 4) * 4))
    _HAS_FILE_DIGEST = hasattr(hashlib, "file_digest")

    def __init__(self, job: BackupJob, log_callback, status_callback):
        super().__init__(daemon=True)
        self.job = job
        self.log = log_callback
        self.status_callback = status_callback
        self._stop_event = threading.Event()
        self._state = {} 
        self._first_scan = True

        self._exclude_res = [re.compile(fnmatch.translate(p)) for p in job.excludes]

    def stop(self):
        self._stop_event.set()

    def run(self):
        interval_s = self.job.interval_seconds()
        self._load_state_from_disk()
        self.log(f"[{self.job.name}] Tracking dimulai (setiap {self.job.interval_display()}, "
                  f"durasi {self.job.duration_display()})")
        self.status_callback(self.job.id, "running")
        start_time = time.monotonic()
        duration_limit = self.job.duration_hours * 3600 if self.job.duration_hours and self.job.duration_hours > 0 else None
        try:
            while not self._stop_event.is_set():
                if duration_limit is not None and (time.monotonic() - start_time) >= duration_limit:
                    self.log(f"[{self.job.name}] Durasi tracking {self.job.duration_display()} tercapai, berhenti otomatis")
                    break
                try:
                    self._scan_and_backup()
                except FileNotFoundError:
                    self.log(f"[{self.job.name}] Source tidak ditemukan, dicoba lagi nanti")
                except Exception as e:
                    self.log(f"[{self.job.name}] ERROR: {e}")
                self._stop_event.wait(interval_s)
        finally:
            _checksum_cache.save(force=True)
            self.status_callback(self.job.id, "stopped")
            self.log(f"[{self.job.name}] Tracking dihentikan")

    def _is_excluded(self, relpath: str) -> bool:
        return any(p.match(relpath) for p in self._exclude_res)

    def _hash_file(self, path: Path, size: int, mtime: float) -> str:
        """Hitung SHA-256 dari `path`, tapi cek checksum cache persisten
        dulu (key: path+size+mtime). Kalau cache hit, file tidak perlu
        dibaca sama sekali - cukup kembalikan hash yang sudah pernah
        dihitung sebelumnya (bisa dari siklus scan sebelumnya, job lain,
        atau sesi aplikasi yang lalu)."""
        key = _checksum_cache.make_key(str(path), size, mtime)
        cached = _checksum_cache.get(key)
        if cached is not None:
            return cached

        if self._HAS_FILE_DIGEST:
            with open(path, "rb") as f:
                digest = hashlib.file_digest(f, "sha256").hexdigest()
        else:
            h = hashlib.sha256()
            with open(path, "rb") as f:
                for chunk in iter(lambda: f.read(self.HASH_CHUNK_SIZE), b""):
                    h.update(chunk)
            digest = h.hexdigest()

        _checksum_cache.put(key, digest)
        return digest

    def _iter_source_entries(self, src: Path):
        """Walk direktori pakai os.scandir (bukan os.walk + os.stat manual).
        DirEntry.stat() memakai info yang sudah didapat scandir, jadi tidak
        perlu syscall stat() kedua per file seperti pendekatan lama."""
        if src.is_file():
            try:
                st = src.stat()
            except OSError:
                return
            yield src, src.name, st
            return

        stack = [(str(src), "")]
        while stack:
            current_dir, rel_prefix = stack.pop()
            try:
                entries = os.scandir(current_dir)
            except OSError:
                continue
            with entries:
                for entry in entries:
                    rel = f"{rel_prefix}/{entry.name}" if rel_prefix else entry.name
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            stack.append((entry.path, rel))
                        elif entry.is_file(follow_symlinks=False):
                            if self._is_excluded(rel):
                                continue
                            st = entry.stat(follow_symlinks=False)
                            yield Path(entry.path), rel, st
                    except OSError:
                        continue

    def _load_state_from_disk(self):
        """Lanjutkan dari manifest terakhir (kalau ada) supaya restart job
        tidak memaksa membuat delta penuh lagi dari nol."""
        zips_dir = self.job.zips_dir()
        if not zips_dir.exists():
            return
        manifests = sorted(zips_dir.glob("*.manifest.json"), key=lambda p: p.stat().st_mtime)
        if not manifests:
            return
        latest = manifests[-1]
        try:
            with open(latest, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._state = self._migrate_state(data.get("files", {}))
            self._first_scan = False
        except (json.JSONDecodeError, OSError):
            pass

    @staticmethod
    def _migrate_state(raw_state: dict) -> dict:
        """Konversi manifest lama (field 'sig' tunggal, dari sebelum v3.2)
        ke skema baru 'quick'/'hash' terpisah, supaya job lama tetap bisa
        lanjut tracking tanpa membuat delta ulang penuh dari nol. delta_id
        tetap dipertahankan apa adanya sehingga Recall snapshot lama tidak
        terpengaruh sama sekali (Recall selalu baca file manifest langsung
        dari disk, bukan lewat state di memori ini)."""
        migrated = {}
        for rel, info in raw_state.items():
            if "sig" in info and "quick" not in info and "hash" not in info:
                sig = info["sig"]
                new_info = {"delta_id": info.get("delta_id")}
                if isinstance(sig, list):
                    new_info["quick"] = sig
                else:
                    new_info["hash"] = sig
                migrated[rel] = new_info
            else:
                migrated[rel] = info
        return migrated

    def _scan_and_backup(self):
        try:
            self._scan_and_backup_impl()
        finally:
            # Simpan hash baru yang mungkin dihitung siklus ini (di-debounce
            # di dalam ChecksumCache.save, jadi aman dipanggil tiap siklus).
            _checksum_cache.save()

    def _scan_and_backup_impl(self):
        src = Path(self.job.source)
        if not src.exists():
            raise FileNotFoundError(str(src))

        current_rels = set()
        new_state = {}
        # Kandidat yang mtime/size-nya berubah (atau file baru) - untuk mode
        # "hash" ini baru dipastikan berubah beneran setelah dihash; untuk
        # mode "quick" ini langsung dianggap berubah.
        candidates = []  # (full_path, rel, quick_sig)

        for full_path, rel, st in self._iter_source_entries(src):
            current_rels.add(rel)
            quick_sig = [st.st_mtime, st.st_size]
            prev = self._state.get(rel)
            if prev is not None and prev.get("quick") == quick_sig:
                new_state[rel] = prev  # mtime & size sama persis -> anggap tidak berubah, skip
                continue
            candidates.append((full_path, rel, quick_sig))

        changed_files = []  # (full_path, rel) yang benar-benar perlu masuk delta.zip

        if self.job.check_mode == "hash" and candidates:
            # Hash paralel: hanya untuk kandidat yang lolos quick pre-filter,
            # bukan seluruh source setiap siklus seperti versi sebelumnya.
            with concurrent.futures.ThreadPoolExecutor(max_workers=self.MAX_HASH_WORKERS) as pool:
                future_map = {
                    pool.submit(self._hash_file, fp, qsig[1], qsig[0]): (fp, rel, qsig)
                    for fp, rel, qsig in candidates
                }
                for fut in concurrent.futures.as_completed(future_map):
                    full_path, rel, quick_sig = future_map[fut]
                    try:
                        digest = fut.result()
                    except (FileNotFoundError, PermissionError, OSError):
                        continue
                    prev = self._state.get(rel)
                    if prev is not None and prev.get("hash") == digest:
                        # Isi sebenarnya sama (mis. mtime berubah tanpa isi berubah)
                        # -> tidak perlu disalin ulang ke delta, cukup update quick sig.
                        new_state[rel] = {"quick": quick_sig, "hash": digest, "delta_id": prev.get("delta_id")}
                    else:
                        changed_files.append((full_path, rel))
                        new_state[rel] = {"quick": quick_sig, "hash": digest, "delta_id": None}
        else:
            for full_path, rel, quick_sig in candidates:
                changed_files.append((full_path, rel))
                new_state[rel] = {"quick": quick_sig, "delta_id": None}

        deleted_rels = sorted(set(self._state.keys()) - current_rels)
        any_change = bool(changed_files) or bool(deleted_rels)

        if not any_change:
            return

        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        zips_dir = self.job.zips_dir()
        zips_dir.mkdir(parents=True, exist_ok=True)

        if changed_files:
            delta_path = zips_dir / f"{ts}.delta.zip"
            try:
                with zipfile.ZipFile(delta_path, "w", zipfile.ZIP_DEFLATED) as zf:
                    for full_path, rel in changed_files:
                        try:
                            zf.write(full_path, arcname=rel)
                        except (FileNotFoundError, PermissionError) as e:
                            self.log(f"[{self.job.name}] Lewati {rel}: {e}")
            except OSError as e:
                self.log(f"[{self.job.name}] Gagal membuat delta: {e}")
                return
            for _full_path, rel in changed_files:
                new_state[rel]["delta_id"] = ts

        manifest_path = zips_dir / f"{ts}.manifest.json"
        manifest_data = {"timestamp": ts, "files": new_state}
        tmp_path = manifest_path.with_suffix(".json.tmp")
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(manifest_data, f, ensure_ascii=False)
        tmp_path.replace(manifest_path)

        self._state = new_state
        self._first_scan = False

        note = f"Snapshot baru: {len(changed_files)} file diperbarui"
        if deleted_rels:
            note += f", {len(deleted_rels)} file dihapus"
        note += f" ({ts})"
        self.log(f"[{self.job.name}] {note}")

        self._prune_manifests(zips_dir)

    def _prune_manifests(self, zips_dir: Path):
        """Retention dihitung per titik-waktu (manifest), bukan per delta.zip.
        Delta.zip yang masih dirujuk oleh manifest yang dipertahankan TIDAK
        dihapus, walau usianya lebih tua dari retention (mark & sweep)."""
        if self.job.retention <= 0:
            return
        manifests = sorted(zips_dir.glob("*.manifest.json"), key=lambda p: p.stat().st_mtime)
        excess = len(manifests) - self.job.retention
        if excess <= 0:
            return
        to_delete = manifests[:excess]
        to_keep = manifests[excess:]

        referenced_delta_ids = set()
        for m in to_keep:
            try:
                with open(m, "r", encoding="utf-8") as f:
                    data = json.load(f)
                for finfo in data.get("files", {}).values():
                    if finfo.get("delta_id"):
                        referenced_delta_ids.add(finfo["delta_id"])
            except (json.JSONDecodeError, OSError):
                continue

        for m in to_delete:
            try:
                m.unlink()
            except OSError:
                pass

        for delta in zips_dir.glob("*.delta.zip"):
            delta_id = delta.name[: -len(".delta.zip")]
            if delta_id not in referenced_delta_ids:
                try:
                    delta.unlink()
                except OSError:
                    pass


THEME = {
    "bg": "#F5F4EF",          
    "bg_card": "#FFFFFF",     
    "bg_sidebar": "#ECE8DD",   
    "border": "#E3DFD3",      
    "text": "#3D3929",         
    "text_muted": "#8A8578",  
    "accent": "#D97757",       
    "accent_hover": "#C7663F", 
    "accent_press": "#B85A3A", 
    "accent_soft": "#F3DDD0",  
    "success": "#5C8A5C",     
    "success_soft": "#E4EEE1",
    "danger": "#B3492D",       
    "danger_soft": "#F7E3DC",
    "danger_hover": "#F1D0C4",
    "log_bg": "#FFFFFF",
    "log_fg": "#3D3929",
}

FONT_FAMILY = "Helvetica"


def apply_theme(root: tk.Tk) -> ttk.Style:
    """Terapkan palet warna & style ttk supaya UI terasa bersih, hangat,
    dan konsisten - terinspirasi tampilan Claude (krem + terracotta)."""
    root.configure(bg=THEME["bg"])

    style = ttk.Style()
    try:
        style.theme_use("clam")
    except Exception:
        pass

    style.configure(".", background=THEME["bg"], foreground=THEME["text"],
                     font=(FONT_FAMILY, 10))

    style.configure("TFrame", background=THEME["bg"])
    style.configure("Card.TFrame", background=THEME["bg_card"])
    style.configure("TLabel", background=THEME["bg"], foreground=THEME["text"])
    style.configure("Card.TLabel", background=THEME["bg_card"], foreground=THEME["text"])
    style.configure("Muted.TLabel", background=THEME["bg"], foreground=THEME["text_muted"],
                     font=(FONT_FAMILY, 9))
    style.configure("Card.Muted.TLabel", background=THEME["bg_card"], foreground=THEME["text_muted"],
                     font=(FONT_FAMILY, 9))
    style.configure("Title.TLabel", background=THEME["bg"], foreground=THEME["text"],
                     font=(FONT_FAMILY, 16, "bold"))
    style.configure("Subtitle.TLabel", background=THEME["bg"], foreground=THEME["text_muted"],
                     font=(FONT_FAMILY, 9))
    style.configure("SectionTitle.TLabel", background=THEME["bg"], foreground=THEME["text"],
                     font=(FONT_FAMILY, 10, "bold"))

    style.configure("Card.TLabelframe", background=THEME["bg_card"],
                     bordercolor=THEME["border"], relief="solid", borderwidth=1)
    style.configure("Card.TLabelframe.Label", background=THEME["bg_card"],
                     foreground=THEME["text_muted"], font=(FONT_FAMILY, 9, "bold"))

  
    style.configure("TButton", font=(FONT_FAMILY, 10), padding=(10, 6),
                     borderwidth=0, relief="flat",
                     background=THEME["bg_sidebar"], foreground=THEME["text"])
    style.map("TButton",
              background=[("active", THEME["border"]), ("disabled", THEME["bg_sidebar"])],
              foreground=[("disabled", THEME["text_muted"])])

    style.configure("Primary.TButton", font=(FONT_FAMILY, 10, "bold"), padding=(14, 7),
                     borderwidth=0, relief="flat",
                     background=THEME["accent"], foreground="#FFFFFF")
    style.map("Primary.TButton",
              background=[("active", THEME["accent_hover"]), ("pressed", THEME["accent_press"])])

    style.configure("Secondary.TButton", font=(FONT_FAMILY, 10), padding=(12, 6),
                     borderwidth=1, relief="flat",
                     background=THEME["bg_card"], foreground=THEME["text"])
    style.map("Secondary.TButton",
              background=[("active", THEME["bg_sidebar"])])

    style.configure("Danger.TButton", font=(FONT_FAMILY, 10), padding=(12, 6),
                     borderwidth=0, relief="flat",
                     background=THEME["danger_soft"], foreground=THEME["danger"])
    style.map("Danger.TButton",
              background=[("active", THEME["danger_hover"])])


    style.configure("TEntry", fieldbackground="#FFFFFF", foreground=THEME["text"],
                     bordercolor=THEME["border"], lightcolor=THEME["border"],
                     darkcolor=THEME["border"], padding=6)
    style.configure("TCombobox", fieldbackground="#FFFFFF", foreground=THEME["text"],
                     bordercolor=THEME["border"], padding=5)
    style.map("TCombobox", fieldbackground=[("readonly", "#FFFFFF")])


    style.configure("TCheckbutton", background=THEME["bg"], foreground=THEME["text"])
    style.configure("Card.TCheckbutton", background=THEME["bg_card"], foreground=THEME["text"])


    style.configure("Treeview", background="#FFFFFF", fieldbackground="#FFFFFF",
                     foreground=THEME["text"], rowheight=26, borderwidth=0,
                     font=(FONT_FAMILY, 10))
    style.configure("Treeview.Heading", background=THEME["bg_sidebar"], foreground=THEME["text"],
                     font=(FONT_FAMILY, 9, "bold"), relief="flat", padding=(6, 6))
    style.map("Treeview.Heading", background=[("active", THEME["border"])])
    style.map("Treeview",
              background=[("selected", THEME["accent_soft"])],
              foreground=[("selected", THEME["text"])])


    style.configure("TSeparator", background=THEME["border"])

    return style


def _pill_group(parent, title=None):
    """Bikin 'kartu' kelompok tombol (LabelFrame bergaya kartu putih)."""
    frame = ttk.LabelFrame(parent, text=title or "", style="Card.TLabelframe")
    return frame



class App:
    def __init__(self, root):
        self.root = root
        root.title(f"LHBM - Local Hosted Backups Management v{APP_VERSION}")
        root.geometry("1080x640")
        root.minsize(820, 480)

        self.style = apply_theme(root)

        self.jobs = load_jobs()
        self.runners = {}

        self._build_ui()
        self._refresh_tree()


    def _build_ui(self):
        outer = ttk.Frame(self.root, padding=(16, 14, 16, 12))
        outer.pack(fill="both", expand=True)


        header = ttk.Frame(outer)
        header.pack(fill="x", pady=(0, 12))
        ttk.Label(header, text="LHBM", style="Title.TLabel").pack(side="left")
        ttk.Label(header, text=f"  ·  Local Hosted Backups Management  ·  v{APP_VERSION}",
                  style="Subtitle.TLabel").pack(side="left", padx=(2, 0), anchor="s", pady=(0, 3))


        toolbar = ttk.Frame(outer)
        toolbar.pack(fill="x", pady=(0, 12))

        grp_job = _pill_group(toolbar, "KELOLA JOB")
        grp_job.pack(side="left", padx=(0, 8), ipady=2)
        ttk.Button(grp_job, text="+  Tambah Job", style="Primary.TButton",
                   command=self.add_job).pack(side="left", padx=6, pady=8)
        ttk.Button(grp_job, text="Edit", style="Secondary.TButton",
                   command=self.edit_job).pack(side="left", padx=4, pady=8)
        ttk.Button(grp_job, text="Hapus", style="Danger.TButton",
                   command=self.remove_job).pack(side="left", padx=(4, 8), pady=8)

        grp_run = _pill_group(toolbar, "KONTROL TRACKING")
        grp_run.pack(side="left", padx=8, ipady=2)
        ttk.Button(grp_run, text="▶  Start", style="Secondary.TButton",
                   command=self.start_selected).pack(side="left", padx=6, pady=8)
        ttk.Button(grp_run, text="■  Stop", style="Secondary.TButton",
                   command=self.stop_selected).pack(side="left", padx=4, pady=8)
        ttk.Separator(grp_run, orient="vertical").pack(side="left", fill="y", padx=6, pady=8)
        ttk.Button(grp_run, text="Start Semua", style="Secondary.TButton",
                   command=self.start_all).pack(side="left", padx=4, pady=8)
        ttk.Button(grp_run, text="Stop Semua", style="Secondary.TButton",
                   command=self.stop_all).pack(side="left", padx=(4, 8), pady=8)

        grp_recall = _pill_group(toolbar, "BACKUP")
        grp_recall.pack(side="left", padx=(8, 0), ipady=2)
        ttk.Button(grp_recall, text="⟲  Recall Backup...", style="Secondary.TButton",
                   command=self.open_recall).pack(side="left", padx=8, pady=8)


        ttk.Label(outer, text="DAFTAR JOB", style="SectionTitle.TLabel").pack(anchor="w", pady=(4, 4))

        tree_card = ttk.Frame(outer, style="Card.TFrame")
        tree_card.pack(fill="x", pady=(0, 12))

        columns = ("name", "source", "destination", "interval", "duration", "status", "last")
        headers = {
            "name": "Nama", "source": "Source", "destination": "Destination",
            "interval": "Interval Cek", "duration": "Durasi Tracking",
            "status": "Status", "last": "Update Terakhir",
        }
        self.tree = ttk.Treeview(tree_card, columns=columns, show="headings", height=8)
        for c in columns:
            self.tree.heading(c, text=headers[c])
            width = 220 if c in ("source", "destination") else 110
            self.tree.column(c, width=width, anchor="w")
        self.tree.tag_configure("running", foreground=THEME["success"])
        self.tree.tag_configure("stopped", foreground=THEME["text_muted"])
        self.tree.tag_configure("odd", background="#FBFAF7")
        self.tree.tag_configure("even", background="#FFFFFF")
        self.tree.pack(fill="x", padx=1, pady=1)

 
        ttk.Label(outer, text="LOG AKTIVITAS", style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 4))
        log_card = ttk.Frame(outer, style="Card.TFrame")
        log_card.pack(fill="both", expand=True)
        log_inner = ttk.Frame(log_card, style="Card.TFrame", padding=1)
        log_inner.pack(fill="both", expand=True)

        log_frame = tk.Frame(log_inner, bg=THEME["border"])
        log_frame.pack(fill="both", expand=True)
        inner = tk.Frame(log_frame, bg=THEME["log_bg"])
        inner.pack(fill="both", expand=True, padx=1, pady=1)

        self.log_text = tk.Text(inner, height=12, state="disabled", wrap="word",
                                 bg=THEME["log_bg"], fg=THEME["log_fg"],
                                 insertbackground=THEME["log_fg"],
                                 relief="flat", borderwidth=0, padx=10, pady=8,
                                 font=("Consolas", 9))
        scrollbar = ttk.Scrollbar(inner, command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=scrollbar.set)
        self.log_text.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

  
    def log(self, msg: str):
        ts = time.strftime("%H:%M:%S")

        def append():
            self.log_text.configure(state="normal")
            self.log_text.insert("end", f"[{ts}] {msg}\n")
            self.log_text.see("end")
            self.log_text.configure(state="disabled")

        self.root.after(0, append)

    def status_callback(self, job_id, status):
        self.root.after(0, self._refresh_tree)

    def _refresh_tree(self):
        self.tree.delete(*self.tree.get_children())
        for idx, job in enumerate(self.jobs):
            running = job.id in self.runners and self.runners[job.id].is_alive()
            status = "● Running" if running else "○ Stopped"
            last = time.strftime("%H:%M:%S") if running else "-"
            row_tag = "odd" if idx % 2 else "even"
            status_tag = "running" if running else "stopped"
            self.tree.insert("", "end", iid=job.id,
                              values=(job.name, job.source, job.destination,
                                       job.interval_display(), job.duration_display(), status, last),
                              tags=(row_tag, status_tag))

    def _selected_job(self):
        sel = self.tree.selection()
        if not sel:
            return None
        job_id = sel[0]
        return next((j for j in self.jobs if j.id == job_id), None)

    def add_job(self):
        dlg = JobDialog(self.root)
        self.root.wait_window(dlg.top)
        if dlg.result:
            self.jobs.append(dlg.result)
            save_jobs(self.jobs)
            self._refresh_tree()

    def edit_job(self):
        job = self._selected_job()
        if not job:
            messagebox.showinfo("Info", "Pilih job dulu di tabel")
            return
        if job.id in self.runners and self.runners[job.id].is_alive():
            messagebox.showwarning("Peringatan", "Stop job ini dulu sebelum diedit")
            return
        dlg = JobDialog(self.root, job)
        self.root.wait_window(dlg.top)
        if dlg.result:
            idx = self.jobs.index(job)
            self.jobs[idx] = dlg.result
            save_jobs(self.jobs)
            self._refresh_tree()

    def remove_job(self):
        job = self._selected_job()
        if not job:
            messagebox.showinfo("Info", "Pilih job dulu di tabel")
            return
        if job.id in self.runners and self.runners[job.id].is_alive():
            messagebox.showwarning("Peringatan", "Stop job ini dulu sebelum dihapus")
            return
        if messagebox.askyesno("Konfirmasi", f"Hapus job '{job.name}'? (zip backup yang sudah ada tidak dihapus)"):
            self.jobs.remove(job)
            save_jobs(self.jobs)
            self._refresh_tree()

    def start_selected(self):
        job = self._selected_job()
        if not job:
            messagebox.showinfo("Info", "Pilih job dulu di tabel")
            return
        self._start_job(job)

    def stop_selected(self):
        job = self._selected_job()
        if job:
            self._stop_job(job)

    def start_all(self):
        for job in self.jobs:
            self._start_job(job)

    def stop_all(self):
        for job in self.jobs:
            self._stop_job(job)

    def _start_job(self, job: BackupJob):
        if job.id in self.runners and self.runners[job.id].is_alive():
            return
        runner = JobRunner(job, self.log, self.status_callback)
        self.runners[job.id] = runner
        runner.start()
        self._refresh_tree()

    def _stop_job(self, job: BackupJob):
        runner = self.runners.get(job.id)
        if runner:
            runner.stop()
        self._refresh_tree()

    def open_recall(self):
        job = self._selected_job()
        RecallDialog(self.root, self.jobs, job, self.log)

    def on_close(self):
        for runner in self.runners.values():
            runner.stop()
        save_jobs(self.jobs)
        _checksum_cache.save(force=True)
        self.root.after(250, self.root.destroy)


class JobDialog:
    def __init__(self, parent, job: BackupJob = None):
        self.result = None
        self.top = tk.Toplevel(parent)
        self.top.title("Tambah Job Backup" if job is None else f"Edit: {job.name}")
        self.top.configure(bg=THEME["bg"])
        self.top.grab_set()
        self.top.resizable(False, False)

        outer = ttk.Frame(self.top, padding=16)
        outer.pack(fill="both", expand=True)

        pad = {"padx": 8, "pady": 5}

        sec_loc = ttk.LabelFrame(outer, text="LOKASI", style="Card.TLabelframe", padding=10)
        sec_loc.pack(fill="x", pady=(0, 10))

        ttk.Label(sec_loc, text="Nama Job:", style="Card.TLabel").grid(row=0, column=0, sticky="w", **pad)
        self.name_var = tk.StringVar(value=job.name if job else "")
        ttk.Entry(sec_loc, textvariable=self.name_var, width=48).grid(row=0, column=1, columnspan=2, **pad)

        ttk.Label(sec_loc, text="Source (file/folder yang ditrack):", style="Card.TLabel").grid(
            row=1, column=0, sticky="w", **pad)
        self.source_var = tk.StringVar(value=job.source if job else "")
        ttk.Entry(sec_loc, textvariable=self.source_var, width=48).grid(row=1, column=1, **pad)
        ttk.Button(sec_loc, text="Pilih Folder", style="Secondary.TButton",
                   command=lambda: self._browse(self.source_var, True)).grid(row=1, column=2, **pad)
        ttk.Button(sec_loc, text="...atau Pilih File", style="Secondary.TButton",
                   command=lambda: self._browse(self.source_var, False)).grid(row=2, column=1, sticky="w", **pad)

        ttk.Label(sec_loc, text="Destination (folder tujuan backup):", style="Card.TLabel").grid(
            row=3, column=0, sticky="w", **pad)
        self.dest_var = tk.StringVar(value=job.destination if job else "")
        ttk.Entry(sec_loc, textvariable=self.dest_var, width=48).grid(row=3, column=1, **pad)
        ttk.Button(sec_loc, text="Pilih Folder", style="Secondary.TButton",
                   command=lambda: self._browse(self.dest_var, True)).grid(row=3, column=2, **pad)

        sec_sched = ttk.LabelFrame(outer, text="JADWAL", style="Card.TLabelframe", padding=10)
        sec_sched.pack(fill="x", pady=(0, 10))

        ttk.Label(sec_sched, text="Interval cek:", style="Card.TLabel").grid(row=0, column=0, sticky="w", **pad)
        interval_row = ttk.Frame(sec_sched, style="Card.TFrame")
        interval_row.grid(row=0, column=1, sticky="w", **pad)
        self.interval_value_var = tk.StringVar(value=str(job.interval_value) if job else "30")
        ttk.Entry(interval_row, textvariable=self.interval_value_var, width=8).pack(side="left")
        self.interval_unit_var = tk.StringVar(value=job.interval_unit if job else "detik")
        ttk.Combobox(interval_row, textvariable=self.interval_unit_var, values=["detik", "menit"],
                     state="readonly", width=8).pack(side="left", padx=(6, 0))

        ttk.Label(sec_sched, text="Durasi tracking (jam, 0 = tanpa batas):", style="Card.TLabel").grid(
            row=1, column=0, sticky="w", **pad)
        self.duration_var = tk.StringVar(value=(f"{job.duration_hours:g}" if job else "0"))
        ttk.Entry(sec_sched, textvariable=self.duration_var, width=10).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_sched, text="job berhenti sendiri setelah durasi ini tercapai",
                  style="Card.Muted.TLabel").grid(row=1, column=2, sticky="w", **pad)

        sec_adv = ttk.LabelFrame(outer, text="RETENSI & DETEKSI PERUBAHAN", style="Card.TLabelframe", padding=10)
        sec_adv.pack(fill="x", pady=(0, 10))

        ttk.Label(sec_adv, text="Jumlah zip lama disimpan per job:", style="Card.TLabel").grid(
            row=0, column=0, sticky="w", **pad)
        self.retention_var = tk.StringVar(value=str(job.retention) if job else "10")
        ttk.Entry(sec_adv, textvariable=self.retention_var, width=10).grid(row=0, column=1, sticky="w", **pad)

        ttk.Label(sec_adv, text="Mode deteksi perubahan:", style="Card.TLabel").grid(row=1, column=0, sticky="w", **pad)
        self.mode_var = tk.StringVar(value=job.check_mode if job else "quick")
        ttk.Combobox(sec_adv, textvariable=self.mode_var, values=["quick", "hash"],
                     state="readonly", width=10).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_adv, text="quick = cepat (mtime+size)  ·  hash = akurat, lebih berat",
                  style="Card.Muted.TLabel").grid(row=1, column=2, sticky="w", **pad)

        ttk.Label(sec_adv,
                  text="Catatan: file yang dihapus di source selalu otomatis tercatat di snapshot\n"
                       "berikutnya - opsi mirror sekarang ada di dialog Recall.",
                  style="Card.Muted.TLabel", justify="left").grid(row=2, column=0, columnspan=3, sticky="w", **pad)

 
        sec_filter = ttk.LabelFrame(outer, text="FILTER LANJUTAN", style="Card.TLabelframe", padding=10)
        sec_filter.pack(fill="x", pady=(0, 12))

        ttk.Label(sec_filter, text="Exclude pattern (pisah koma, contoh: *.tmp,*.log,.git/*):",
                  style="Card.TLabel").grid(row=0, column=0, sticky="w", **pad)
        self.exclude_var = tk.StringVar(value=",".join(job.excludes) if job else "")
        ttk.Entry(sec_filter, textvariable=self.exclude_var, width=48).grid(row=1, column=0, sticky="we", **pad)

    
        btn_frame = ttk.Frame(outer)
        btn_frame.pack(fill="x")
        ttk.Button(btn_frame, text="Simpan", style="Primary.TButton",
                   command=lambda: self._save(job)).pack(side="right", padx=(6, 0))
        ttk.Button(btn_frame, text="Batal", style="Secondary.TButton",
                   command=self.top.destroy).pack(side="right")

    def _browse(self, var: tk.StringVar, folder: bool):
        path = filedialog.askdirectory() if folder else filedialog.askopenfilename()
        if path:
            var.set(path)

    def _save(self, existing_job):
        name = self.name_var.get().strip()
        source = self.source_var.get().strip()
        dest = self.dest_var.get().strip()
        if not name or not source or not dest:
            messagebox.showerror("Error", "Nama, Source, dan Destination wajib diisi")
            return
        try:
            interval_value = int(self.interval_value_var.get())
            retention = int(self.retention_var.get())
            if interval_value <= 0 or retention < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Error", "Interval cek harus angka > 0 dan Retention harus angka >= 0")
            return

        interval_unit = self.interval_unit_var.get()
        if interval_unit not in ("detik", "menit"):
            interval_unit = "detik"

        try:
            duration_hours = float(self.duration_var.get().replace(",", "."))
            if duration_hours < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Error", "Durasi tracking (jam) harus angka >= 0 (0 = tanpa batas)")
            return

        excludes = [p.strip() for p in self.exclude_var.get().split(",") if p.strip()]
        job_id = existing_job.id if existing_job else new_job_id()
        self.result = BackupJob(
            id=job_id, name=name, source=source, destination=dest,
            interval_value=interval_value, interval_unit=interval_unit,
            duration_hours=duration_hours, retention=retention,
            check_mode=self.mode_var.get(), excludes=excludes,
            enabled=False,
        )
        self.top.destroy()



class RecallDialog:
    """
    Implementasi alur "Cara Recall" dari README:
      1. Locate folder backup (destination)
      2. Buka folder "zips"
      3. Pilih titik waktu yang mau direcall
      4. Ambil zip-nya (copy keluar), atau langsung Extract
      5. Unzip / selesai

    Mendukung dua format:
      - "manifest" (skema baru, hemat ruang): dirakit on-demand dari
        <ts>.manifest.json + rantai <ts>.delta.zip yang dirujuknya.
      - "legacy" (skema lama sebelum update ini): file <ts>.zip utuh,
        dipakai langsung seperti sebelumnya supaya backup lama tetap
        bisa direcall setelah update.
    """

    def __init__(self, parent, jobs: List[BackupJob], selected_job: Optional[BackupJob], log_callback):
        self.jobs = jobs
        self.log = log_callback
        self.top = tk.Toplevel(parent)
        self.top.title("Recall Backup")
        self.top.configure(bg=THEME["bg"])
        self.top.grab_set()
        self.top.geometry("700x500")
        self.top.minsize(640, 440)

        outer = ttk.Frame(self.top, padding=16)
        outer.pack(fill="both", expand=True)

        # ---- Step 1 ----
        step1 = ttk.LabelFrame(outer, text="1) FOLDER BACKUP (DESTINATION)", style="Card.TLabelframe", padding=10)
        step1.pack(fill="x", pady=(0, 10))
        path_row = ttk.Frame(step1, style="Card.TFrame")
        path_row.pack(fill="x")
        self.dest_var = tk.StringVar(value=selected_job.destination if selected_job else "")
        ttk.Entry(path_row, textvariable=self.dest_var, width=50).pack(side="left", fill="x", expand=True)
        ttk.Button(path_row, text="Locate Folder...", style="Secondary.TButton",
                   command=self._browse_dest).pack(side="left", padx=4)
        ttk.Button(path_row, text="Buka \"zips\"", style="Secondary.TButton",
                   command=self._scan).pack(side="left")

        ttk.Label(outer, text="2) PILIH TITIK WAKTU (TIMESTAMP) YANG MAU DIRECALL",
                  style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 6))

        list_frame = ttk.Frame(outer, style="Card.TFrame")
        list_frame.pack(fill="both", expand=True, pady=(0, 10))
        columns = ("job", "timestamp", "files", "type")
        self.result_tree = ttk.Treeview(list_frame, columns=columns, show="headings", height=10)
        self.result_tree.heading("job", text="Job")
        self.result_tree.heading("timestamp", text="Waktu Backup")
        self.result_tree.heading("files", text="Jml File")
        self.result_tree.heading("type", text="Format")
        self.result_tree.column("job", width=170, anchor="w")
        self.result_tree.column("timestamp", width=180, anchor="w")
        self.result_tree.column("files", width=80, anchor="e")
        self.result_tree.column("type", width=90, anchor="w")
        self.result_tree.tag_configure("odd", background="#FBFAF7")
        self.result_tree.tag_configure("even", background="#FFFFFF")
        scrollbar = ttk.Scrollbar(list_frame, command=self.result_tree.yview)
        self.result_tree.configure(yscrollcommand=scrollbar.set)
        self.result_tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        # ---- Opsi ----
        opt_frame = ttk.Frame(outer)
        opt_frame.pack(fill="x", pady=(0, 10))
        self.mirror_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            opt_frame,
            text="Extract sebagai mirror (hapus file di folder tujuan yang tidak ada di titik waktu ini)",
            variable=self.mirror_var,
        ).pack(anchor="w")
        
        btn_frame = ttk.Frame(outer)
        btn_frame.pack(fill="x")
        ttk.Label(btn_frame, text="3) & 4) Ambil hasil recall-nya:", style="Muted.TLabel").pack(side="left")
        ttk.Button(btn_frame, text="Extract Now...", style="Primary.TButton",
                   command=self._extract_zip).pack(side="right", padx=(6, 0))
        ttk.Button(btn_frame, text="Get Zip Away... (copy)", style="Secondary.TButton",
                   command=self._copy_zip).pack(side="right")

        self._entry_index = {}  
        if self.dest_var.get():
            self._scan()

    def _browse_dest(self):
        path = filedialog.askdirectory()
        if path:
            self.dest_var.set(path)
            self._scan()

    def _scan(self):
        self.result_tree.delete(*self.result_tree.get_children())
        self._entry_index.clear()
        dest = self.dest_var.get().strip()
        if not dest:
            messagebox.showinfo("Info", "Locate folder backup (destination) dulu")
            return
        zips_root = Path(dest) / ZIPS_DIRNAME
        if not zips_root.exists():
            messagebox.showwarning("Tidak ditemukan", f"Folder \"{ZIPS_DIRNAME}\" tidak ada di:\n{dest}")
            return

        entries = [] 
        for job_dir in sorted(zips_root.iterdir()):
            if not job_dir.is_dir():
                continue
          
            for manifest_path in job_dir.glob("*.manifest.json"):
                try:
                    with open(manifest_path, "r", encoding="utf-8") as f:
                        data = json.load(f)
                except (json.JSONDecodeError, OSError):
                    continue
                n_files = len(data.get("files", {}))
                entries.append((job_dir.name, manifest_path.stat().st_mtime,
                                 {"kind": "manifest", "manifest": manifest_path,
                                  "job_dir": job_dir, "n_files": n_files,
                                  "ts": data.get("timestamp", manifest_path.stem)}))
          
            for zip_file in job_dir.glob("*.zip"):
                if zip_file.name.endswith(".delta.zip"):
                    continue 
                try:
                    n_files = len(zipfile.ZipFile(zip_file).namelist())
                except (OSError, zipfile.BadZipFile):
                    n_files = "?"
                entries.append((job_dir.name, zip_file.stat().st_mtime,
                                 {"kind": "legacy", "path": zip_file, "n_files": n_files,
                                  "ts": zip_file.stem}))

        entries.sort(key=lambda t: t[1], reverse=True)

        for idx, (job_name, _mtime, entry) in enumerate(entries):
            try:
                dt = datetime.strptime(entry["ts"], "%Y%m%d_%H%M%S")
                ts_display = dt.strftime("%Y-%m-%d %H:%M:%S")
            except ValueError:
                ts_display = entry["ts"]
            type_display = "Hemat (baru)" if entry["kind"] == "manifest" else "Full (lama)"
            iid = str(entry.get("manifest") or entry.get("path"))
            row_tag = "odd" if idx % 2 else "even"
            self.result_tree.insert("", "end", iid=iid,
                                     values=(job_name, ts_display, entry["n_files"], type_display),
                                     tags=(row_tag,))
            self._entry_index[iid] = entry

        if not entries:
            messagebox.showinfo("Info", "Belum ada backup di folder ini")

    def _selected_entry(self):
        sel = self.result_tree.selection()
        if not sel:
            messagebox.showinfo("Info", "Pilih dulu titik waktu backup di daftar")
            return None
        return self._entry_index.get(sel[0])

    def _resolve_files_iter(self, entry) -> "Iterator[Tuple[str, bytes]]":
        """Generator (relpath, bytes) untuk entry manifest ATAU legacy zip.

        --- Optimisasi kinerja (v3.3) ---
        Sebelumnya fungsi ini mengumpulkan SELURUH isi backup (semua file,
        seluruh isinya) ke satu list besar di memori sebelum baris
        pertama sempat ditulis ke tujuan (copy) atau ke disk (extract).
        Untuk backup dengan banyak/besar file, itu berarti penggunaan RAM
        bisa membengkak sebesar total ukuran backup, dan tidak ada apa pun
        yang tertulis sampai SEMUA file selesai dibaca ke memori.

        Sekarang isi setiap file di-yield satu per satu begitu dibaca dari
        delta.zip/legacy zip, jadi pemanggil bisa langsung menuliskannya
        dan melepas memori untuk file itu sebelum lanjut ke file
        berikutnya - pemakaian memori kira-kira konstan (seukuran satu
        file terbesar + overhead zip), bukan proporsional dengan total
        ukuran backup."""
        if entry["kind"] == "legacy":
            with zipfile.ZipFile(entry["path"], "r") as zf:
                for name in zf.namelist():
                    yield name, zf.read(name)
            return


        with open(entry["manifest"], "r", encoding="utf-8") as f:
            data = json.load(f)
     
        open_zips = {}
        try:
            for rel, finfo in data.get("files", {}).items():
                delta_id = finfo.get("delta_id")
                if not delta_id:
                    continue
                if delta_id not in open_zips:
                    delta_path = entry["job_dir"] / f"{delta_id}.delta.zip"
                    if not delta_path.exists():
                        self.log(f"[Recall] PERINGATAN: delta {delta_id} hilang, file '{rel}' dilewati")
                        continue
                    open_zips[delta_id] = zipfile.ZipFile(delta_path, "r")
                zf = open_zips.get(delta_id)
                if zf is None:
                    continue
                yield rel, zf.read(rel)
        finally:
            for zf in open_zips.values():
                zf.close()

    def _copy_zip(self):
        entry = self._selected_entry()
        if not entry:
            return
        default_name = f"{entry['ts']}.zip"
        target = filedialog.asksaveasfilename(
            title="Get Zip Away - simpan ke mana?",
            initialfile=default_name,
            defaultextension=".zip",
            filetypes=[("Zip archive", "*.zip")],
        )
        if not target:
            return

        if entry["kind"] == "legacy":
            try:
                shutil.copy2(entry["path"], target)
            except OSError as e:
                messagebox.showerror("Error", f"Gagal menyalin zip: {e}")
                return
        else:
            try:
                with zipfile.ZipFile(target, "w", zipfile.ZIP_DEFLATED) as zf:
                    for rel, content in self._resolve_files_iter(entry):
                        zf.writestr(rel, content)
            except (OSError, zipfile.BadZipFile) as e:
                messagebox.showerror("Error", f"Gagal merakit zip: {e}")
                return

        self.log(f"[Recall] Zip diambil ({entry['ts']}) -> {target}")
        messagebox.showinfo("Selesai", f"Zip berhasil diambil ke:\n{target}\n\nTinggal unzip file itu kapan saja.")

    def _extract_zip(self):
        entry = self._selected_entry()
        if not entry:
            return
        target_dir = filedialog.askdirectory(title="Extract Now - unzip ke folder mana?")
        if not target_dir:
            return

        target_path = Path(target_dir)
        restored_rels = set()
        try:
            for rel, content in self._resolve_files_iter(entry):
                out_path = target_path / rel
                out_path.parent.mkdir(parents=True, exist_ok=True)
                with open(out_path, "wb") as f:
                    f.write(content)
                restored_rels.add(rel)
        except (OSError, zipfile.BadZipFile) as e:
            messagebox.showerror("Error", f"Gagal extract: {e}")
            return

        removed_count = 0
        if self.mirror_var.get():
            for root, _dirs, filenames in os.walk(target_path):
                for fn in filenames:
                    full = Path(root) / fn
                    rel = str(full.relative_to(target_path))
                    if rel not in restored_rels:
                        try:
                            full.unlink()
                            removed_count += 1
                        except OSError:
                            pass

        note = f"[Recall] Extract ({entry['ts']}) -> {target_dir}: {len(restored_rels)} file dipulihkan"
        if removed_count:
            note += f", {removed_count} file lama dihapus (mirror)"
        self.log(note)

        msg = f"{len(restored_rels)} file berhasil dipulihkan ke:\n{target_dir}"
        if removed_count:
            msg += f"\n({removed_count} file lama di folder itu dihapus karena mode mirror aktif)"
        if messagebox.askyesno("Selesai", msg + "\n\nBuka folder sekarang?"):
            self._open_folder(target_dir)

    @staticmethod
    def _open_folder(path: str):
        try:
            if sys.platform.startswith("darwin"):
                subprocess.Popen(["open", path])
            elif sys.platform.startswith("win"):
                os.startfile(path)  
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception:
            pass


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
