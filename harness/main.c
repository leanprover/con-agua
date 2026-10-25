/* The harness for the compiled checker: the trusted C side of the end-to-end theorem.

   build:  cc -O2 -o checker harness/main.c asm/checker.s
   usage:  checker [--jobs=N] [--driver] FILE [PINS]

   The default path is the one the final theorem covers (`checkerFile_accepts_remaining`,
   ConAgua/Final/Remaining.lean; the call is as `AbiCall` in ConAgua/Final/Abi.lean states it).
   It reads FILE (the input) and PINS (the pin data, empty if not given) whole into two buffers
   (`slurp`), maps one zero region of ca_region_size bytes, and calls, once,

     ca_start(in, in_len, pins, pins_len, region, region_len)

   The entry stub lays out everything else inside the region. The verdict is one line on stdout,
   and the exit status is 0:
     accept      rdx = 0 and rax = ACCEPT (0x414343455054): the only accept
     ok R        rdx = 0 and any other rax (R in decimal; 1: the frontend rejected a line)
     exhausted   rdx = 1 (fuel, stack, or a region smaller than ca_region_size)
     error       otherwise (an abort or an out-of-bounds access)
   A failure of the harness itself (usage, a file that cannot be read, no memory) prints a message on stderr and exits with status 3 and no verdict line. A crash
   (e.g. a page of the region the kernel cannot supply) prints nothing. Neither is an accept.

   Not covered by the theorem yet (lane parmode, docs/design/parmode.md): with --jobs=N for N > 1,
   the parallel mode, `run_jobs` below; with --driver (and no --jobs above 1), the sequential
   driver `ca_start_drv` (entry 1, then entry 2 over every pending group, on the same region),
   which replaces `ca_start` once its theorem is proved. */
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

/* The entry points' result: a struct of two 64-bit integers, which System V returns in rax
   (first member) and rdx. */
typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_start(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                       void *base, uint64_t base_len);
extern ca_res ca_start_a(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                         void *base, uint64_t base_len);
extern ca_res ca_check_b(const uint64_t *buf, uint64_t buf_len, uint64_t j, void *region,
                         uint64_t region_len);
extern ca_res ca_start_drv(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                           void *base, uint64_t base_len);
/* Constants of asm/checker.s: the region size `ca_start` needs; the slot size, the offset of
   word array 0 and the number of word arrays (for `advise_huge`); and parmode's two. */
extern const uint64_t ca_region_size, ca_slot, ca_w0, ca_nw, ca_out_off, ca_worker_size;

/* `ConAgua.Final.ACCEPT`, the verdict word for accept */
#define ACCEPT 0x414343455054ull

static void print_verdict(ca_res r) {
  if (r.rdx == 0 && r.rax == ACCEPT) printf("accept\n");
  else if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
  else if (r.rdx == 1) printf("exhausted\n");
  else printf("error\n");
}

/* Transparent huge pages for the `nslots` slots of ca_slot bytes from `start`, for the word
   arrays (performance only; lane compopt2: dTLB misses were 13.5 M on c03d against con-ron's
   54 K; big fixtures -10..14% wall, Init -5%). Not the first and last 2 MB of a slot: a small
   run touches only those (the start of every array, and the slot tables' size word at the end),
   and must not zero 2 MB per array. */
static void advise_huge(uint8_t *start, uint64_t nslots) {
  const uintptr_t huge = 2u << 20;
  for (uint64_t a = 0; a < nslots; a++) {
    uintptr_t s = (uintptr_t)start + a * ca_slot;
    uintptr_t lo = (s + huge + huge - 1) & ~(huge - 1);   /* s + 2 MB, rounded up */
    uintptr_t hi = (s + ca_slot - huge) & ~(huge - 1);    /* the slot's end - 2 MB, rounded down */
    if (hi > lo) madvise((void *)lo, hi - lo, MADV_HUGEPAGE);
  }
}

/* A failure of the harness itself: a message on stderr, status 3, no verdict line. */
static _Noreturn void fail(const char *what, const char *why) {
  fprintf(stderr, "%s: %s\n", what, why);
  exit(3);
}

/* Read `path` whole: read(2) until end of file into a malloc'd buffer that grows by doubling.
   The bytes `b` the theorem talks about are whatever this buffer holds. Fails on a read error and
   on 2^63 bytes or more (`AbiCall`'s `b.size < 2^63`). */
static uint8_t *slurp(const char *path, uint64_t *n) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) fail(path, strerror(errno));
  /* start with room for a regular file's size plus one, so that the read which sees end of file
     needs no growth (and a big input is never copied by realloc) */
  struct stat st;
  size_t cap = fstat(fd, &st) == 0 && st.st_size > 0 ? (size_t)st.st_size + 1 : 1 << 16;
  size_t len = 0;
  uint8_t *buf = malloc(cap);
  if (!buf) fail(path, strerror(errno));
  for (;;) {
    if (len == cap) {
      if (cap > SIZE_MAX / 2) fail(path, "too large");
      cap *= 2;
      buf = realloc(buf, cap);
      if (!buf) fail(path, strerror(errno));
    }
    ssize_t k = read(fd, buf + len, cap - len);
    if (k < 0 && errno == EINTR) continue;
    if (k < 0) fail(path, strerror(errno));
    if (k == 0) break;
    len += (size_t)k;
  }
  close(fd);
  if ((uint64_t)len >= 1ull << 63) fail(path, "too large");
  *n = len;
  return buf;
}

/* `--jobs=N` (N > 1), the parallel mode (docs/design/parmode.md). Entry 1 (`ca_start_a`) runs the
   stages and phase A in the region and, on success (rdx = 0, rax = 2^63 + k, k pending groups),
   leaves the frozen buffer in the array `OUT` (word 1: its length in words). The rest of the region
   is unmapped around the buffer, the buffer is made read-only (a write to it faults and kills the
   process, which is never an accept: route A), and the input buffers are freed (phase B reads no
   byte array). N threads then each map a zero region of ca_worker_size bytes and claim groups one
   at a time from one atomic counter, calling `ca_check_b(buf, len, j, region, size)` for each, one
   after the other on the region as the previous call left it.

   Concurrency: the threads share only the read-only buffer and the claim counter (each value
   0, 1, 2, ... is handed out once by fetch_add); each has its own region and its own result slot,
   which main combines after joining them all. A plain flag (a hint, read and written without
   ordering) lets the others stop claiming after a failure; it only shortens the run. Accept iff
   every thread's slot says that every call it made returned rdx = 0, rax = ACCEPT and the claims
   covered 0 .. k-1 (a thread stops only on a failure or when the counter passed k). */
static const uint64_t *g_buf;
static uint64_t g_len, g_k, g_next;
static volatile int g_stop;

/* a thread's result: 0 every call accepted, 1 exhausted, 2 error or no region */
static void *worker(void *res) {
  int *r = res;
  *r = 0;
  uint8_t *reg = mmap(0, ca_worker_size, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (reg == MAP_FAILED) { *r = 2; g_stop = 1; return 0; }
  /* transparent huge pages as in sequential mode: not the first and last 2 MB of each slot */
  for (uint64_t a = 2; a < ca_worker_size / ca_slot; a++) {
    uintptr_t h = 2u << 20, s = (uintptr_t)reg + a * ca_slot;
    uintptr_t lo = (s + 2 * h - 1) & ~(h - 1), hi = (s + ca_slot - h) & ~(h - 1);
    if (hi > lo) madvise((void *)lo, hi - lo, MADV_HUGEPAGE);
  }
  while (!g_stop) {
    uint64_t j = __atomic_fetch_add(&g_next, 1, __ATOMIC_RELAXED);
    if (j >= g_k) break;
    ca_res q = ca_check_b(g_buf, g_len, j, reg, ca_worker_size);
    if (!(q.rdx == 0 && q.rax == ACCEPT)) { *r = q.rdx == 1 ? 1 : 2; g_stop = 1; break; }
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
  size_t bytes = (g_len * 8 + 4095) & ~(size_t)4095;
  munmap(base, ca_out_off);
  munmap((uint8_t *)out + bytes, ca_region_size - ca_out_off - bytes);
  if (mprotect((void *)out, bytes, PROT_READ) != 0) { perror("mprotect"); return 3; }
  free(in);
  free(pins);
  g_buf = out;
  pthread_t *th = calloc(jobs, sizeof *th);
  int *res = calloc(jobs, sizeof *res);
  int *ok = calloc(jobs, sizeof *ok);
  if (!th || !res || !ok) { perror("calloc"); return 3; }
  for (int w = 0; w < jobs; w++) {
    pthread_attr_t at;
    pthread_attr_init(&at);
    pthread_attr_setstacksize(&at, 1 << 20);
    ok[w] = pthread_create(&th[w], &at, worker, &res[w]) == 0;
    pthread_attr_destroy(&at);
  }
  int started = 0;
  for (int w = 0; w < jobs; w++) started += ok[w];
  if (!started) { ok[0] = 1; worker(&res[0]); } /* no thread: run on this one */
  else for (int w = 0; w < jobs; w++) if (ok[w]) pthread_join(th[w], 0);
  int worst = 0;
  for (int w = 0; w < jobs; w++) if (ok[w] && res[w] > worst) worst = res[w];
  if (worst == 2) printf("error\n");
  else if (worst == 1) printf("exhausted\n");
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
  if (argc < 2) { fprintf(stderr, "usage: %s [--jobs=N] [--driver] FILE [PINS]\n", argv[0]); return 3; }
  uint64_t in_len, pins_len = 0;
  uint8_t *in = slurp(argv[1], &in_len);
  uint8_t *pins = argc > 2 ? slurp(argv[2], &pins_len) : NULL;
  uint8_t *region = mmap(0, ca_region_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(region + ca_w0, ca_nw);
  if (jobs > 1) return run_jobs(jobs, in, in_len, pins, pins_len, region);
  print_verdict(drv ? ca_start_drv(in, in_len, pins, pins_len, region, ca_region_size)
                    : ca_start(in, in_len, pins, pins_len, region, ca_region_size));
  return 0;
}
