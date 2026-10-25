#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <time.h>

typedef int64_t (*NexaClosureCode)(int64_t env);
typedef struct { int64_t code_ptr; int64_t env_ptr; } NxClosure;
typedef struct NxRcHeader {
    uint64_t references;
    uint64_t kind;
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
    struct NxRcHeader *debug_next;
#endif
} NxRcHeader;
enum { NEXA_RC_ENV = 1, NEXA_RC_CELL = 2 };
typedef struct { 
    int64_t slot_count; 
    int64_t cell_mask; 
    int64_t slots[]; 
} NxEnv;

static int64_t nexa_live_env_count = 0;
static int64_t nexa_live_cell_count = 0;
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
_Static_assert(sizeof(NxRcHeader) % 8 == 0, "RC header must preserve 8-byte payload alignment");
static NxRcHeader *nexa_rc_live_headers = NULL;
#endif

#ifdef NEXA_TESTING
static int64_t nexa_test_alloc_fail_countdown = -1;
void nexa_test_fail_alloc_after(int64_t successful_allocations) {
    nexa_test_alloc_fail_countdown = successful_allocations;
}
static int nexa_test_should_fail_alloc(void) {
    if (nexa_test_alloc_fail_countdown < 0) return 0;
    if (nexa_test_alloc_fail_countdown == 0) {
        nexa_test_alloc_fail_countdown = -1;
        return 1;
    }
    nexa_test_alloc_fail_countdown--;
    return 0;
}
#else
static int nexa_test_should_fail_alloc(void) { return 0; }
#endif

static void nexa_out_of_memory(const char *allocation) {
    fprintf(stderr, "nexa: out of memory allocating %s\n", allocation);
    fflush(stderr);
    _Exit(70);
}

static NxRcHeader *nexa_rc_header(int64_t ptr) {
    if (ptr == 0) return NULL;
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
    NxRcHeader *header = nexa_rc_live_headers;
    while (header && (int64_t)(uintptr_t)(header + 1) != ptr) header = header->debug_next;
    assert(header != NULL && "invalid or already-released Nexa RC pointer");
    return header;
#else
    return ((NxRcHeader *)(uintptr_t)ptr) - 1;
#endif
}
static int64_t nexa_rc_alloc(size_t size, uint64_t kind) {
    if (nexa_test_should_fail_alloc()) return 0;
    NxRcHeader *header = calloc(1, sizeof(*header) + size);
    if (!header) return 0;
    header->references = 1;
    header->kind = kind;
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
    assert(kind == NEXA_RC_ENV || kind == NEXA_RC_CELL);
    header->debug_next = nexa_rc_live_headers;
    nexa_rc_live_headers = header;
#endif
    return (int64_t)(uintptr_t)(header + 1);
}
void nexa_free(int64_t ptr) { free((void *)(uintptr_t)ptr); }
void nexa_rc_inc(int64_t ptr) {
    NxRcHeader *header = nexa_rc_header(ptr);
    if (!header) return;
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
    assert(header->kind == NEXA_RC_ENV || header->kind == NEXA_RC_CELL);
    assert(header->references > 0 && "incrementing a dead Nexa RC allocation");
    assert(header->references < UINT64_MAX && "Nexa RC count overflow");
#endif
    header->references++;
}
void nexa_rc_dec(int64_t ptr) {
    NxRcHeader *header = nexa_rc_header(ptr);
    if (!header) return;
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
    assert(header->kind == NEXA_RC_ENV || header->kind == NEXA_RC_CELL);
    assert(header->references > 0 && "decrementing a dead Nexa RC allocation");
#endif
    if (--header->references != 0) return;
    if (header->kind == NEXA_RC_ENV) {
        NxEnv *env = (NxEnv *)(uintptr_t)ptr;
        nexa_live_env_count--;
        for (int64_t i = 0; i < env->slot_count; i++) {
            if ((env->cell_mask & (INT64_C(1) << i)) != 0) nexa_rc_dec(env->slots[i]);
        }
    } else if (header->kind == NEXA_RC_CELL) {
        nexa_live_cell_count--;
    }
#if defined(NEXA_RC_DEBUG) && !defined(NDEBUG)
    NxRcHeader **link = &nexa_rc_live_headers;
    while (*link && *link != header) link = &(*link)->debug_next;
    assert(*link == header && "Nexa RC allocation missing from debug registry");
    *link = header->debug_next;
#endif
    nexa_free((int64_t)(uintptr_t)header);
}
int64_t nexa_live_closure_envs(void) { return nexa_live_env_count; }
int64_t nexa_live_capture_cells(void) { return nexa_live_cell_count; }


// Monotonic wall-clock time for Nexa's std/time module.
int64_t nexa_time_now_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return -1;
    return (int64_t)ts.tv_sec * 1000 + (int64_t)(ts.tv_nsec / 1000000);
}

// Synchronous file helpers used by bundled std/fs. The read buffer is copied
// into a Nexa string by the wrapper before the raw buffer is freed.
int64_t nexa_fs_read_file(int64_t path_ptr) {
    const char *path = (const char *)(uintptr_t)(path_ptr & INT64_MAX);
    FILE *f = fopen(path, "rb");
    if (!f || fseek(f, 0, SEEK_END) != 0) { if (f) fclose(f); return 0; }
    long size = ftell(f);
    if (size < 0 || fseek(f, 0, SEEK_SET) != 0) { fclose(f); return 0; }
    char *buf = (char *)malloc((size_t)size + 1);
    if (!buf) { fclose(f); return 0; }
    size_t got = fread(buf, 1, (size_t)size, f);
    fclose(f);
    buf[got] = '\0';
    return (int64_t)(uintptr_t)buf;
}

int64_t nexa_fs_read_file_len(int64_t path_ptr) {
    const char *path = (const char *)(uintptr_t)(path_ptr & INT64_MAX);
    FILE *f = fopen(path, "rb");
    if (!f || fseek(f, 0, SEEK_END) != 0) { if (f) fclose(f); return -1; }
    long size = ftell(f);
    fclose(f);
    return size < 0 ? -1 : (int64_t)size;
}

int64_t nexa_fs_write_file(int64_t path_ptr, int64_t data_ptr, int64_t len, int64_t append) {
    const char *path = (const char *)(uintptr_t)(path_ptr & INT64_MAX);
    const char *data = (const char *)(uintptr_t)(data_ptr & INT64_MAX);
    FILE *f = fopen(path, append ? "ab" : "wb");
    if (!f) return -1;
    size_t wrote = fwrite(data, 1, (size_t)len, f);
    int failed = ferror(f);
    fclose(f);
    return failed || wrote != (size_t)len ? -1 : (int64_t)wrote;
}

int64_t nexa_fs_exists(int64_t path_ptr) {
    const char *path = (const char *)(uintptr_t)(path_ptr & INT64_MAX);
    return access(path, F_OK) == 0 ? 1 : 0;
}

/* Nexa strings carry an 8-byte length header immediately preceding the
   character buffer, mirroring the array layout: the tagged pointer points at
   char[0], and ((int64_t *)str)[-1] holds the byte length. The char buffer
   remains NUL-terminated at str[len] for C interop (puts, toCString etc.). */
#define NEXA_STR_LEN(p) (((int64_t *)(p))[-1])

int64_t nexa_env_new(int64_t slot_count,int64_t cell_mask) {
    if (slot_count < 0 || slot_count > 63) {
        fprintf(stderr, "nexa: invalid closure environment layout (%lld capture slots)\n", (long long)slot_count);
        fflush(stderr);
        _Exit(70);
    }
    NxEnv *env = (NxEnv *)(uintptr_t)nexa_rc_alloc(sizeof(NxEnv) + (size_t)slot_count * sizeof(int64_t), NEXA_RC_ENV);
    if (!env) nexa_out_of_memory("closure environment");
    env->slot_count = slot_count;
    env->cell_mask = cell_mask;
    nexa_live_env_count++;
    return (int64_t)(uintptr_t)env;
}



int64_t nexa_env_get(int64_t env, int64_t slot) { 
    NxEnv *capture_env = (NxEnv *)(uintptr_t)env;
    return (capture_env)->slots[slot]; }
int64_t nexa_env_set(int64_t env, int64_t slot, int64_t value) { 
    NxEnv *capture_env = (NxEnv *)(uintptr_t)env;
    (capture_env)->slots[slot] = value; return value; }

int64_t nexa_cell_new(int64_t value) { int64_t *cell = (int64_t *)(uintptr_t)nexa_rc_alloc(sizeof(*cell), NEXA_RC_CELL); if (!cell) nexa_out_of_memory("mutable capture cell"); *cell = value; nexa_live_cell_count++; return (int64_t)(uintptr_t)cell; }
int64_t nexa_cell_get(int64_t cell) { return *(int64_t *)(uintptr_t)cell; }
int64_t nexa_cell_set(int64_t cell, int64_t value) { *(int64_t *)(uintptr_t)cell = value; return value; }
int64_t nexa_closure_new(int64_t code_ptr, int64_t env_ptr) { NxClosure *closure = nexa_test_should_fail_alloc() ? NULL : malloc(sizeof(*closure)); if (!closure) { nexa_rc_dec(env_ptr); nexa_out_of_memory("closure object"); } closure->code_ptr = code_ptr; closure->env_ptr = env_ptr; return (int64_t)(uintptr_t)closure; }
int64_t nexa_closure_call(int64_t closure_ptr) { NxClosure *closure = (NxClosure *)(uintptr_t)closure_ptr; return ((NexaClosureCode)(uintptr_t)closure->code_ptr)(closure->env_ptr); }

int64_t nexa_class_new(int64_t size) { return (int64_t)(uintptr_t)calloc(1, (size_t)size); }

int64_t nexa_print_bool(int64_t x) { puts(x ? "true" : "false"); return x; }
int64_t nexa_print_i64(int64_t x) {
    printf("%lld\n", (long long)x);
    return x;
}
// Statically string-typed values alone reach this helper. The string tag is
// removed and the stored length preserves embedded NUL bytes.
int64_t nexa_print_cstr(int64_t tagged) {
    const char *s = (const char *)(uintptr_t)(tagged & INT64_MAX);
    size_t len = (size_t)NEXA_STR_LEN(s);
    fwrite(s, 1, len, stdout);
    fputc('\n', stdout);
    return 0;
}
int64_t nexa_print_f64(double x) { printf("%g\n", x); return 0; }
int64_t nexa_print_f32(float x) { printf("%g\n", x); return 0; }

int64_t nexa_stdin_line(void) {
    char buf[1024];
    if (!fgets(buf, sizeof buf, stdin)) { buf[0] = '\0'; }
    size_t n = strlen(buf);
    if (n > 0 && buf[n - 1] == '\n') { buf[n - 1] = '\0'; n--; }
    int64_t *outb = (int64_t *)malloc((size_t)sizeof(int64_t) + n + 1);
    if (!outb) return 0;
    outb[0] = (int64_t)n; /* stored length header at outb[0] */
    char *out = (char *)(outb + 1);
    if (n > 0) memcpy(out, buf, n);
    out[n] = '\0';
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
#define NEXA_ARRAY_HDR ((size_t)sizeof(int64_t))
    int64_t *buf = (int64_t *)calloc((size_t)length + 1, sizeof(int64_t));
    buf[0] = length; /* header: element count lives just before element data */
    return (int64_t)(uintptr_t)(buf + 1); /* array pointer = &elem0, unchanged in shape */
} /* length header is at ((int64_t*)array)[-1] */

int64_t nexa_array_get(int64_t array, int64_t index) {
    return ((int64_t *)(uintptr_t)array)[index];
}

int64_t nexa_array_set(int64_t array, int64_t index, int64_t value) {
    ((int64_t *)(uintptr_t)array)[index] = value;
    return value;
}

int64_t nexa_array_get_f32(int64_t array, int64_t index) {
    return (int64_t)(int32_t)((int32_t *)(uintptr_t)array)[index];
}

int64_t nexa_array_set_f32(int64_t array, int64_t index, int64_t value) {
    ((int32_t *)(uintptr_t)array)[index] = (int32_t)value;
    return value;
}

int64_t nexa_concat_str(int64_t a, int64_t b) {
    char *left = (char *)(uintptr_t)(a & INT64_MAX);
    char *right = (char *)(uintptr_t)(b & INT64_MAX);
    size_t left_len = (size_t)NEXA_STR_LEN(left);
    size_t right_len = (size_t)NEXA_STR_LEN(right);
    int64_t *buf = (int64_t *)malloc((size_t)sizeof(int64_t) + left_len + right_len + 1);
    if (!buf) return 0;
    buf[0] = (int64_t)(left_len + right_len); /* stored length header at buf[0] */
    char *out = (char *)(buf + 1); /* char data begins right after the header */
    if (left_len) memcpy(out, left, left_len);
    if (right_len) memcpy(out + left_len, right, right_len);
    out[left_len + right_len] = '\0';
    return (int64_t)(uintptr_t)out | INT64_MIN;
}

// Copy `n` raw bytes from the source pointer into a brand-new Nexa string
// buffer. Always allocates and memcpy's -- never aliases the input. Returns
// the UNTAGGED pointer (the codegen ORs in INT64_MIN so the result behaves as
// a normal tagged Nexa string). The explicit `n` is required because the
// source may be a socket-read buffer with embedded NUL bytes and no
// terminator; we must not scan for '\0'. The byte length is stored directly
// as the header (rather than recomputed) since the source carries no length.
int64_t nexa_from_cstring(int64_t src_ptr, int64_t n) {
    const char *s = (const char *)(uintptr_t)(src_ptr & INT64_MAX);
    size_t len = (size_t)n;
    int64_t *buf = (int64_t *)malloc((size_t)sizeof(int64_t) + len + 1);
    if (!buf) return 0;
    buf[0] = (int64_t)len; /* stored length header at buf[0] */
    char *out = (char *)(buf + 1);
    if (len > 0) memcpy(out, s, len);
    out[len] = '\0';
    return (int64_t)(uintptr_t)out;
}

// Content equality for two Nexa strings. Masks the INT64_MIN tag bit off both
// operands (the same masking toCString/fromCString use), compares lengths
// (read from the stored headers) first as a fast-path short-circuit, then
// compares bytes only when lengths match. Returns 1 if equal content, 0
// otherwise. This is value (==) / value (!=) semantics for strings -- two
// independently-built strings with identical content are equal even though
// they live at different addresses.
int64_t nexa_str_eq(int64_t a, int64_t b) {
    const char *left = (const char *)(uintptr_t)(a & INT64_MAX);
    const char *right = (const char *)(uintptr_t)(b & INT64_MAX);
    size_t llen = (size_t)NEXA_STR_LEN(left);
    size_t rlen = (size_t)NEXA_STR_LEN(right);
    if (llen != rlen) return 0;
    if (llen && memcmp(left, right, llen) != 0) return 0;
    return 1;
}

// Length of a Nexa string, in bytes. Nexa strings carry an explicit 8-byte
// length header immediately before the character buffer (the same layout the
// runtime uses for arrays: header at pointer[-1]). strlen reads this header
// directly rather than NUL-scanning, so a string may legitimately contain
// embedded NUL bytes (raw/socket-read data) without being truncated.
int64_t nexa_strlen(int64_t tagged) {
    const char *s = (const char *)(uintptr_t)(tagged & INT64_MAX);
    return (int64_t)NEXA_STR_LEN(s);
}

// Extract the single byte at index `i` of a Nexa string as a NEW one-byte
// Nexa string (a 2-byte char buffer: the byte followed by a NUL terminator,
// with a length header of 1), tagged like any other Nexa string. There is no
// separate char type in Nexa. The byte is taken as-is (no codec conversion);
// raw byte semantics.
int64_t nexa_char_at(int64_t tagged, int64_t index) {
    const char *s = (const char *)(uintptr_t)(tagged & INT64_MAX);
    int64_t *buf = (int64_t *)malloc((size_t)sizeof(int64_t) + 2);
    if (!buf) return 0;
    buf[0] = 1; /* stored length header: this is a 1-byte string */
    char *out = (char *)(buf + 1);
    out[0] = s[(size_t)index];
    out[1] = '\0';
    return (int64_t)(uintptr_t)out | INT64_MIN;
}

// Free the buffer backing a Nexa string. The tagged/char pointer points 8
// bytes past the malloc base (the header precedes char[0]), so free exactly
// the base. This is the correct way to release a string's storage once it is
// no longer needed; passing the raw toCString pointer to libc free() directly
// is invalid because that pointer is offset past the allocation header.
void nexa_str_free(int64_t tagged) {
    char *buf = (char *)(uintptr_t)(tagged & INT64_MAX);
    free(buf - (int64_t)sizeof(int64_t));
}

// ---- std.net.* helpers ----------------------------------------------------
// IPv4-only, purpose-built FFI glue for the socket syscalls. Everything is
// exposed as int64_t at the ABI boundary (the Nexa `number`/`Pointer` types).

// Build a real struct sockaddr_in on the heap and return a pointer to it.
// `port` and `addr` are plain host-order integers; htons/htonl produce the
// correct network-order bytes, replacing the hand-spelled "\xNN" byte-string
// approach used by earlier examples. IPv4 only.
int64_t nexa_net_sockaddr_in(int64_t port, int64_t addr) {
    struct sockaddr_in *sa = (struct sockaddr_in *)malloc(sizeof(struct sockaddr_in));
    if (!sa) return 0;
    memset(sa, 0, sizeof(struct sockaddr_in));
    sa->sin_family = AF_INET;
    sa->sin_port = htons((uint16_t)port);
    sa->sin_addr.s_addr = htonl((uint32_t)addr);
    return (int64_t)(uintptr_t)sa;
}

int64_t nexa_net_socket(int64_t domain, int64_t type, int64_t protocol) {
    return (int64_t)socket((int)domain, (int)type, (int)protocol);
}

int64_t nexa_net_setsockopt(int64_t fd, int64_t level, int64_t option, int64_t value, int64_t length) {
    return (int64_t)setsockopt((int)fd, (int)level, (int)option,
                               (const void *)(uintptr_t)value, (socklen_t)length);
}

int64_t nexa_net_bind(int64_t fd, int64_t addr, int64_t len) {
    return (int64_t)bind((int)fd, (const struct sockaddr *)(uintptr_t)addr, (socklen_t)len);
}

int64_t nexa_net_listen(int64_t fd, int64_t backlog) {
    return (int64_t)listen((int)fd, (int)backlog);
}

// Accept hides the peer-address details by passing NULL/0 for addr/addrlen,
// matching how the earlier HTTP server experiment used it.
int64_t nexa_net_accept(int64_t fd) {
    return (int64_t)accept((int)fd, NULL, NULL);
}

int64_t nexa_net_recv(int64_t fd, int64_t buf, int64_t n, int64_t flags) {
    return (int64_t)recv((int)fd, (void *)(uintptr_t)buf, (size_t)n, (int)flags);
}

int64_t nexa_net_send(int64_t fd, int64_t buf, int64_t n, int64_t flags) {
    return (int64_t)send((int)fd, (const void *)(uintptr_t)buf, (size_t)n, (int)flags);
}

int64_t nexa_net_close(int64_t fd) {
    return (int64_t)close((int)fd);
}

// ---- std.process.* helpers -------------------------------------------------
// Thin wrappers around the libc process/syscall primitives, following the same
// pattern as the net helpers: everything is int64_t at the ABI boundary.
//
// exec1/exec2 use execvp so PATH is searched to resolve the program name
// (matching how a shell/user typically invokes a command), not just an exact
// path. execve with an absolute path would be the alternative; execvp is
// friendlier for calls like exec2("ls", "-l"). The argv arrays are built here
// in C ({path, NULL} and {path, arg1, NULL}); the environment is inherited.

int64_t nexa_process_fork(void) {
    return (int64_t)fork();
}

int64_t nexa_process_exec1(int64_t path) {
    const char *p = (const char *)(uintptr_t)path;
    char *argv[] = { (char *)p, NULL };
    execvp(p, argv);
    return (int64_t)-1; /* only reached if execvp fails */
}

int64_t nexa_process_exec2(int64_t path, int64_t arg1) {
    const char *p = (const char *)(uintptr_t)path;
    const char *a = (const char *)(uintptr_t)arg1;
    char *argv[] = { (char *)p, (char *)a, NULL };
    execvp(p, argv);
    return (int64_t)-1; /* only reached if execvp fails */
}

// pipe() into a freshly malloc'd 2-int buffer. Returns a pointer to the buffer
// (read fd at index 0, write fd at index 1), or 0 (NULL) on malloc/pipe error.
int64_t nexa_process_pipe(void) {
    int *fds = (int *)malloc(sizeof(int) * 2);
    if (!fds) return 0;
    if (pipe(fds) != 0) {
        free(fds);
        return 0;
    }
    return (int64_t)(uintptr_t)fds;
}

int64_t nexa_process_pipe_read(int64_t p) {
    return (int64_t)((int *)(uintptr_t)p)[0];
}

int64_t nexa_process_pipe_write(int64_t p) {
    return (int64_t)((int *)(uintptr_t)p)[1];
}

// Blocking waitpid for the specific child; returns the exit status. waitpid
// (rather than wait()) is used because fork returns a concrete child PID that
// we want to wait on specifically with no children-unrelated surprises.
int64_t nexa_process_wait(int64_t pid) {
    int status = 0;
    waitpid((pid_t)pid, &status, 0);
    return (int64_t)WEXITSTATUS(status);
}

// _exit (not exit/return/abort with full buffer flushes) so that after fork the
// child does not flush stdio buffers that were copied from the parent. Both
// processes share the same underlying file-descriptor offsets for stdout, so
// buffer-flushing the parent's pending output in the child before exec/exit
// could interleave or duplicate parent output.
//
// However we DO fflush(NULL) first so the child's OWN buffered stdout (e.g. a
// std.log it issued after fork, which under a fully-buffered pipe stdout would
// otherwise be discarded) is emitted before _exit. In the common program that
// has issued no output prior to fork, the copied parent buffer is empty, so
// this cannot duplicate the parent's output; the caveat (duplication if the
// parent had buffered unsent output at fork time) is documented in the task
// notes as a real-world fork/stdio caveat.
void nexa_process_exit(int64_t code) {
    fflush(NULL);
    _exit((int)code);
}
