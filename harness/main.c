/* The harness for the compiled checker (lane `abi`; ConAgua/Compiler/Abi.lean).

   usage: main [--jobs=N] [--driver] FILE [PINS]

   Reads FILE (the input) and PINS (the pin data, byte array 1; empty if not given) into memory
   (each read whole, until end of file; a regular file that changes while it is read is an error,
   status 3; see `slurp`),
   maps a zero region of ca_region_size bytes (MAP_NORESERVE: the pages the checker never touches
   never become real; needs overcommit) and calls, once,

     ca_start(in, in_len, pins, pins_len, region, region_len)

   The entry stub lays out everything else inside the region. Prints one line:
     accept            rdx = 0 and rax = ACCEPT (0x414343455054), the only accept
     ok R              rdx = 0, any other rax (R in decimal; 1: the frontend rejected a line)
     exhausted         rdx = 1 (fuel, stack, or a region smaller than ca_region_size)
     missing CODE      rdx = 2 and the DIAG array's word 0 is CODE != 0 (`e2e-l asm` programs)
     error             rdx = 2 otherwise (an abort or an out-of-bounds access)

   With --jobs=N for N > 1, the parallel mode (lane `parmode`, docs/design/parmode.md): `run_jobs`
   below. With --driver (and no --jobs above 1), the sequential driver `ca_start_drv` (entry 1,
   then entry 2 over every pending group, on the same region); it replaces `ca_start` once its
   theorem is proved (docs/design/parmode.md). */
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_start(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                       void *base, uint64_t base_len);
extern ca_res ca_start_a(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                         void *base, uint64_t base_len);
extern ca_res ca_check_b(const uint64_t *buf, uint64_t buf_len, uint64_t lo, uint64_t hi,
                         void *region, uint64_t region_len);
extern ca_res ca_start_drv(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                           void *base, uint64_t base_len);
extern const uint64_t ca_region_size, ca_slot, ca_w0, ca_diag, ca_nw, ca_out_off, ca_worker_size;

#define ACCEPT 0x414343455054ull

/* Read the whole of `path` into a fresh malloc'd buffer: read(2) until end of file into a buffer
   that grows by doubling, so the buffer holds exactly the bytes the file delivered (never a
   prefix fixed by an earlier ftell). For a regular file the size must stay put: fstat before and
   after the read must agree with each other and with the number of bytes read, and the
   modification time must not change; otherwise the file changed while we read it and we stop
   with status 3 instead of checking a prefix or a mixture. This also rejects /proc-like files,
   whose st_size (0) is not what they deliver. Pipes, sockets and character devices
   (`/dev/stdin` on a pipe) have no size to compare and are read until EOF, which is all they say
   about their contents. Any read error, and an input of 2^63 bytes or more (`AbiCall`'s `b.size < 2^63`),
   stops with status 3. This is the "buffer to stream" step of the trusted base: the bytes `b` the
   theorems talk about are exactly the buffer this returns. */
static uint8_t *slurp(const char *path, uint64_t *n) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) { perror(path); exit(3); }
  struct stat st0, st1;
  if (fstat(fd, &st0) != 0) { perror(path); exit(3); }
  size_t cap = S_ISREG(st0.st_mode) && st0.st_size > 0 ? (size_t)st0.st_size + 1 : 1 << 16, len = 0;
  uint8_t *buf = malloc(cap);
  if (!buf) { perror(path); exit(3); }
  for (;;) {
    if (len == cap) {
      if (cap > SIZE_MAX / 2) { fprintf(stderr, "%s: too large\n", path); exit(3); }
      cap *= 2;
      uint8_t *nb = realloc(buf, cap);
      if (!nb) { perror(path); exit(3); }
      buf = nb;
    }
    ssize_t k = read(fd, buf + len, cap - len);
    if (k < 0) { if (errno == EINTR) continue; perror(path); exit(3); }
    if (k == 0) break;
    len += (size_t)k;
  }
  if (fstat(fd, &st1) != 0) { perror(path); exit(3); }
  close(fd);
  if (S_ISREG(st0.st_mode) &&
      (st1.st_size != st0.st_size || (uint64_t)st0.st_size != len ||
       st1.st_mtim.tv_sec != st0.st_mtim.tv_sec || st1.st_mtim.tv_nsec != st0.st_mtim.tv_nsec)) {
    fprintf(stderr, "%s: changed while being read\n", path);
    exit(3);
  }
  if ((uint64_t)len >= (1ull << 63)) { fprintf(stderr, "%s: too large\n", path); exit(3); }
  *n = len;
  return buf;
}

/* `--jobs=N`. Entry 1 (`ca_start_a`) runs the stages and phase A in the region and, on success
   (rdx = 0, rax = 2^63 + k, k pending checks), leaves the frozen buffer (`OUT`: word 1 is its
   length in words) in the region. The buffer is copied into a fresh mapping, the region is
   unmapped, and the copy is made read-only (a write to it faults: the process dies, which is never
   an accept). N threads then each map a zero region of ca_worker_size bytes and claim the pending
   groups 0 .. k-1 in chunks from an atomic counter, calling `ca_check_b(buf, len, lo, hi, region,
   size)` on each chunk (entry 2 checks groups lo .. hi-1 in order), one after the other on the
   region as the previous call left it. The chunk is k / (16 N) groups, at least 1 and at most 64:
   small enough to balance, large enough that the stub (~2 K instructions) is rare. Accept iff every call returned
   rdx = 0, rax = ACCEPT; a failing call stops the claims. */
static const uint64_t *g_buf;
static uint64_t g_len, g_k, g_next, g_chunk;
static int g_fail; /* 0 ok, 1 exhausted, 2 error (the worst wins) */
static int g_hp = 1;

static void *worker(void *arg) {
  (void)arg;
  uint8_t *reg = mmap(0, ca_worker_size, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (reg == MAP_FAILED) { __atomic_store_n(&g_fail, 2, __ATOMIC_RELAXED); return 0; }
  /* transparent huge pages as in sequential mode: not the first and last 2 MB of each slot */
  for (uint64_t a = 2; g_hp && a < ca_worker_size / ca_slot; a++) {
    uintptr_t h = 2u << 20, s = (uintptr_t)reg + a * ca_slot;
    uintptr_t lo = (s + 2 * h - 1) & ~(h - 1), hi = (s + ca_slot - h) & ~(h - 1);
    if (hi > lo) madvise((void *)lo, hi - lo, MADV_HUGEPAGE);
  }
  for (;;) {
    if (__atomic_load_n(&g_fail, __ATOMIC_RELAXED)) break;
    uint64_t j = __atomic_fetch_add(&g_next, g_chunk, __ATOMIC_RELAXED);
    if (j >= g_k) break;
    uint64_t hi = j + g_chunk < g_k ? j + g_chunk : g_k;
    ca_res q = ca_check_b(g_buf, g_len, j, hi, reg, ca_worker_size);
    if (!(q.rdx == 0 && q.rax == ACCEPT)) {
      int f = q.rdx == 1 ? 1 : 2, old = __atomic_load_n(&g_fail, __ATOMIC_RELAXED);
      while (old < f && !__atomic_compare_exchange_n(&g_fail, &old, f, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {}
      break;
    }
  }
  munmap(reg, ca_worker_size);
  return 0;
}

static int run_jobs(int jobs, uint8_t *in, uint64_t n, uint8_t *pins, uint64_t np, uint8_t *base) {
  ca_res r = ca_start_a(in, n, pins, np, base, ca_region_size);
  if (!(r.rdx == 0 && r.rax >= (1ull << 63))) {
    if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
    else if (r.rdx == 1) printf("exhausted\n");
    else printf("error\n");
    return 0;
  }
  g_k = r.rax - (1ull << 63);
  const uint64_t *out = (const uint64_t *)(base + ca_out_off);
  g_len = out[1];
  if (g_len > ca_slot / 8) { printf("error\n"); return 0; }
  /* The buffer stays where entry 1 wrote it: the rest of the region is unmapped around it (no
     second copy at the peak; `OUT` starts at a slot, so the cut is page-aligned). */
  size_t bytes = (g_len * 8 + 4095) & ~(size_t)4095;
  uint64_t *buf = (uint64_t *)out;
  munmap(base, ca_out_off);
  munmap((uint8_t *)buf + bytes, ca_region_size - ca_out_off - bytes);
  if (mprotect(buf, bytes, PROT_READ) != 0) { perror("mprotect"); return 3; }
  /* phase B reads neither input buffer (entry 2 gives the byte arrays no memory) */
  free(in);
  free(pins);
  if (getenv("CA_PAR_ONLYA")) { printf("phase-a %llu\n", (unsigned long long)g_k); return 0; }
  g_buf = buf;
  g_chunk = g_k / (16 * (uint64_t)jobs);
  if (g_chunk < 1) g_chunk = 1;
  if (g_chunk > 64) g_chunk = 64;
  if (getenv("CA_PAR_INFO")) fprintf(stderr, "pending %llu, buffer %llu words\n",
                                     (unsigned long long)g_k, (unsigned long long)g_len);
  if (getenv("CA_PAR_INFO") && getenv("CA_PAR_INFO")[0] == '2')
    for (uint64_t i = 8; i + 1 < buf[8 + 1] && i < 4096; i += 2)
      fprintf(stderr, "entry %llu: off %llu len %llu\n", (unsigned long long)(i - 8) / 2,
              (unsigned long long)buf[i], (unsigned long long)buf[i + 1]);
  pthread_t *th = calloc(jobs, sizeof *th);
  int started = 0;
  for (int w = 0; w < jobs; w++) {
    pthread_attr_t at;
    pthread_attr_init(&at);
    pthread_attr_setstacksize(&at, 1 << 20);
    if (pthread_create(&th[w], &at, worker, 0) == 0) started++; else th[w] = 0;
    pthread_attr_destroy(&at);
  }
  if (!started) worker(0);
  for (int w = 0; w < jobs; w++) if (th[w]) pthread_join(th[w], 0);
  if (g_fail == 2) printf("error\n");
  else if (g_fail == 1) printf("exhausted\n");
  else printf("accept\n");
  return 0;
}

int main(int argc, char **argv) {
  int jobs = 0, drv = 0;
  for (;;) {
    if (argc > 1 && strncmp(argv[1], "--jobs=", 7) == 0) {
      jobs = atoi(argv[1] + 7);
      if (jobs < 1) { fprintf(stderr, "bad --jobs\n"); return 3; }
    } else if (argc > 1 && strcmp(argv[1], "--driver") == 0) drv = 1;
    else break;
    argv++; argc--;
  }
  if (getenv("CA_NOHP")) g_hp = 0;
  if (argc < 2) { fprintf(stderr, "usage: %s [--jobs=N] [--driver] FILE [PINS]\n", argv[0]); return 3; }
  uint64_t n, np = 0;
  uint8_t *in = slurp(argv[1], &n), *pins = argc > 2 ? slurp(argv[2], &np) : 0;
  uint64_t size = ca_region_size;
  uint8_t *base = mmap(0, size, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (base == MAP_FAILED) { perror("mmap"); return 3; }
  /* Transparent huge pages for the word arrays (lane compopt2: dTLB misses were 13.5 M on c03d
     against con-ron's 54 K; big fixtures -10..14% wall, Init -5%). Not the first and last 2 MB
     of each array's slot: a small run touches only those (the start of every array, and the
     slot tables' size word at the end), and must not zero 2 MB per array. */
  for (uint64_t a = 0; a < ca_nw; a++) {
    uintptr_t h = 2u << 20, s = (uintptr_t)base + ca_w0 + a * ca_slot;
    uintptr_t lo = (s + 2 * h - 1) & ~(h - 1), hi = (s + ca_slot - h) & ~(h - 1);
    if (hi > lo) madvise((void *)lo, hi - lo, MADV_HUGEPAGE);
  }
  if (jobs > 1) return run_jobs(jobs, in, n, pins, np, base);
  ca_res r = drv ? ca_start_drv(in, n, pins, np, base, size) : ca_start(in, n, pins, np, base, size);
  if (r.rdx == 0 && r.rax == ACCEPT) printf("accept\n");
  else if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
  else if (r.rdx == 1) printf("exhausted\n");
  else if (ca_diag < ca_nw && *(uint64_t *)(base + ca_w0 + ca_diag * ca_slot) != 0)
    printf("missing %llu\n", (unsigned long long)*(uint64_t *)(base + ca_w0 + ca_diag * ca_slot));
  else printf("error\n");
  return 0;
}
