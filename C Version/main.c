#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/stat.h>

static void get_time_string(char *buf, size_t buf_size) {
    time_t now = time(NULL);
    struct tm *tm_info = localtime(&now);
    strftime(buf, buf_size, "%Y-%m-%d %H:%M:%S", tm_info);
}

int main(int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "Penggunaan: %s <nama_file> <durasi_detik> <interval_detik>\n", argv[0]);
        fprintf(stderr, "Contoh   : %s data.txt 60 2\n", argv[0]);
        return 1;
    }

    const char *filename   = argv[1];
    int duration_seconds    = atoi(argv[2]);
    int interval_seconds    = atoi(argv[3]);

    if (duration_seconds <= 0 || interval_seconds <= 0) {
        fprintf(stderr, "Error: durasi dan interval harus berupa angka positif.\n");
        return 1;
    }

    struct stat st_awal, st_sekarang;
    char waktu_buf[32];

    if (stat(filename, &st_awal) != 0) {
        fprintf(stderr, "Error: tidak dapat mengakses file '%s'. Pastikan file ada.\n", filename);
        return 1;
    }

    get_time_string(waktu_buf, sizeof(waktu_buf));
    printf("[%s] Mulai memantau file: %s\n", waktu_buf, filename);
    printf("Durasi pemantauan : %d detik\n", duration_seconds);
    printf("Interval cek      : %d detik\n", interval_seconds);
    printf("Ukuran awal       : %ld byte\n", (long)st_awal.st_size);
    printf("Waktu ubah awal   : %s", ctime(&st_awal.st_mtime));
    printf("----------------------------------------\n");

    time_t waktu_mulai = time(NULL);
    int terdeteksi_perubahan = 0;

    while (difftime(time(NULL), waktu_mulai) < duration_seconds) {
        sleep(interval_seconds);

        if (stat(filename, &st_sekarang) != 0) {
            get_time_string(waktu_buf, sizeof(waktu_buf));
            printf("[%s] PERINGATAN: file '%s' tidak ditemukan (mungkin dihapus/dipindah).\n",
                   waktu_buf, filename);
            continue;
        }

        if (st_sekarang.st_mtime != st_awal.st_mtime ||
            st_sekarang.st_size  != st_awal.st_size) {

            get_time_string(waktu_buf, sizeof(waktu_buf));
            printf("[%s] PERUBAHAN TERDETEKSI pada file '%s'\n", waktu_buf, filename);
            printf("    Ukuran lama -> baru : %ld -> %ld byte\n",
                   (long)st_awal.st_size, (long)st_sekarang.st_size);
            printf("    Mtime baru          : %s", ctime(&st_sekarang.st_mtime));

            
            st_awal = st_sekarang;
            terdeteksi_perubahan++;
        }
    }

    printf("----------------------------------------\n");
    get_time_string(waktu_buf, sizeof(waktu_buf));
    printf("[%s] Pemantauan selesai.\n", waktu_buf);
    printf("Total perubahan terdeteksi: %d\n", terdeteksi_perubahan);

    return 0;
}