#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int64_t nexa_print_bool(int64_t x) { puts(x ? "true" : "false"); return x; }
int64_t nexa_print_i64(int64_t x) {
    if (((uint64_t)x & UINT64_C(0x8000000000000000)) != 0) {
        puts((const char *)(uintptr_t)(x & INT64_MAX));
        return 0;
    }
    printf("%ld\n", (long)x);
    return x;
}
int64_t nexa_print_str(int64_t p, int64_t n) { fwrite((const void*)p, 1, (size_t)n, stdout); fputc('\n', stdout); return 0; }

int64_t nexa_array_new(int64_t length) {
    return (int64_t)(uintptr_t)calloc((size_t)length, sizeof(int64_t));
}

int64_t nexa_array_get(int64_t array, int64_t index) {
    return ((int64_t *)(uintptr_t)array)[index];
}

int64_t nexa_array_set(int64_t array, int64_t index, int64_t value) {
    ((int64_t *)(uintptr_t)array)[index] = value;
    return value;
}

int64_t nexa_concat_str(int64_t a, int64_t b) {
    const char *left = (const char *)(uintptr_t)(a & INT64_MAX);
    const char *right = (const char *)(uintptr_t)(b & INT64_MAX);
    size_t left_len = 0;
    size_t right_len = 0;
    while (left[left_len] != '\0') left_len++;
    while (right[right_len] != '\0') right_len++;
    char *out = malloc(left_len + right_len + 1);
    if (!out) return 0;
    for (size_t i = 0; i < left_len; i++) out[i] = left[i];
    for (size_t i = 0; i < right_len; i++) out[left_len + i] = right[i];
    out[left_len + right_len] = '\0';
    return (int64_t)(uintptr_t)out | INT64_MIN;
}
