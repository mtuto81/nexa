#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>

typedef int64_t (*NexaClosureCode)(int64_t env);
typedef struct { int64_t code_ptr; int64_t env_ptr; } NxClosure;

int64_t nexa_env_new(int64_t slots) { return (int64_t)(uintptr_t)calloc((size_t)slots, sizeof(int64_t)); }
int64_t nexa_env_get(int64_t env, int64_t slot) { return ((int64_t *)(uintptr_t)env)[slot]; }
int64_t nexa_env_set(int64_t env, int64_t slot, int64_t value) { ((int64_t *)(uintptr_t)env)[slot] = value; return value; }
int64_t nexa_cell_new(int64_t value) { int64_t *cell = malloc(sizeof(*cell)); if (!cell) return 0; *cell = value; return (int64_t)(uintptr_t)cell; }
int64_t nexa_cell_get(int64_t cell) { return *(int64_t *)(uintptr_t)cell; }
int64_t nexa_cell_set(int64_t cell, int64_t value) { *(int64_t *)(uintptr_t)cell = value; return value; }
int64_t nexa_closure_new(int64_t code_ptr, int64_t env_ptr) { NxClosure *closure = malloc(sizeof(*closure)); if (!closure) return 0; closure->code_ptr = code_ptr; closure->env_ptr = env_ptr; return (int64_t)(uintptr_t)closure; }
int64_t nexa_closure_call(int64_t closure_ptr) { NxClosure *closure = (NxClosure *)(uintptr_t)closure_ptr; return ((NexaClosureCode)(uintptr_t)closure->code_ptr)(closure->env_ptr); }

int64_t nexa_class_new(int64_t size) { return (int64_t)(uintptr_t)calloc(1, (size_t)size); }

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

int64_t nexa_stdin_line(void) {
    char buf[1024];
    if (!fgets(buf, sizeof buf, stdin)) { buf[0] = '\0'; }
    size_t n = strlen(buf);
    if (n > 0 && buf[n - 1] == '\n') { buf[n - 1] = '\0'; n--; }
    char *out = malloc(n + 1);
    if (!out) { return (int64_t)(uintptr_t)"" | INT64_MIN; }
    memcpy(out, buf, n + 1);
    return (int64_t)(uintptr_t)out | INT64_MIN;
}

int64_t nexa_std_parse_number(int64_t tagged) {
    const char *s = (const char *)(uintptr_t)(tagged & INT64_MAX);
    char *end = NULL;
    double d = strtod(s, &end);
    if (end == s || end == NULL) {
        fprintf(stderr, "nexa runtime error: std.parseNumber failed to parse \"%s\" as a number\n", s);
        exit(1);
    }
    return (int64_t)d;
}

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
