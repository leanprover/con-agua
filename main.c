/* The harness for the compiled checker: the trusted C side of the end-to-end theorem.

   build:  make   (cc -std=gnu23 -O2 -pthread -o checker main.c checker.s; Makefile)
   usage:  checker [--jobs=N] FILE

   The default path is the one the final theorem covers (`checkerFile_accepts`,
   ConAgua/Final/EndToEnd.lean; the call is as `AbiCall` in ConAgua/Final/Abi.lean states it).
   It maps FILE (the input) read-only, or reads it whole into a buffer if it is not a regular
   file (`read_input`); the theorem is about the bytes the buffer holds, so a file that another
   process changes during the run is outside it. It maps one zero region of ca_region_size
   bytes and calls, once,

     ca_start(in, in_len, pins, pins_len, region, region_len)

   with the pin data `pins` built into the binary (below). `ca_start` is the sequential driver:
   entry 1 (the stages and phase A), then entry 2 over every pending group, on the same region;
   the entry stubs lay out everything else inside the region. The verdict is one line on stdout,
   and the exit status follows the Lean kernel arena's convention (0 accepted, 1 rejected,
   2 declined, 3 error), claiming no more than the checker knows:
     accept      0  rdx = 0 and rax = ACCEPT (0x414343455054): the only accept
     error       2  rdx = 2: the checker aborted, which is a reject or a decline (it does not
                    tell them apart, so it claims neither: not accepted, nothing claimed)
     exhausted   2  rdx = 1: fuel, stack or region ran out (a resource limit; con-leche declines
                    when its fuel runs out)
     ok R        3  rdx = 0 and any other rax R, in decimal (1: the frontend rejected a malformed
                    line, which con-leche reports as an error too)
   A failure of the harness itself (usage, a file that cannot be read, no memory) prints a
   message on stderr and exits with status 3 and no verdict line. A crash (e.g. a page of the
   region the kernel cannot supply) prints nothing and ends with a signal. None is an accept.

   With --jobs=N for N > 1, the threaded mode, `run_jobs` below: its accept is covered by
   `checkerFile_threads_accept` (ConAgua/Final/EndToEnd.lean), under the hypotheses
   `ThreadsRun` (ConAgua/Final/ThreadsFinal.lean) states about this harness's threads. */
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
/* Constants of checker.s: the region size `ca_start` needs; the slot size, the offset of
   word array 0 and the number of word arrays (for `advise_huge`); and parmode's two. */
extern const uint64_t ca_region_size, ca_slot, ca_w0, ca_nw, ca_out_off, ca_worker_size;

/* The pin data (the checker's startup data and con-leche's `Nat`-operation pin variants, the set
   con-ron embeds): `pins.bin`, written by `romgen pins.bin 3` and kept up to date by
   scripts/asm_file.py. Not trusted: the theorem holds for every pin buffer, and the checker decodes
   and checks it at run time. C23 `#embed` (GCC >= 15, Clang >= 19). */
static const uint8_t pins[] = {
#embed "pins.bin"
};

/* `ConAgua.Final.ACCEPT`, the verdict word for accept */
#define ACCEPT 0x414343455054ull

/* Prints the verdict line and returns the exit status (the table above). */
static int print_verdict(ca_res r) {
  if (r.rdx == 0 && r.rax == ACCEPT) { printf("accept\n"); return 0; }
  if (r.rdx == 0) { printf("ok %llu\n", (unsigned long long)r.rax); return 3; }
  if (r.rdx == 1) { printf("exhausted\n"); return 2; }
  printf("error\n");
  return 2;
}

/* Transparent huge pages for the `nslots` slots of ca_slot bytes from `start`, for the word
   arrays (performance only: far fewer TLB misses; 10-14% less wall time on big inputs, 5% on
   Lean's `Init`). Not the first and last 2 MB of a slot: a small
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

/* Read the open file `fd` whole: read(2) until end of file into a malloc'd buffer that grows by
   doubling. Fails on a read error and on 2^63 bytes or more (`AbiCall`'s `b.size < 2^63`). */
static uint8_t *slurp(int fd, const char *path, uint64_t *n) {
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

static int in_mapped;  /* the input buffer is a mapping of the file, not a malloc'd buffer */

/* The input: a nonempty regular file is mapped read-only (its size, an off_t, is below 2^63);
   anything else (a pipe, stdin, an empty file) or a file mmap refuses is read with `slurp`.
   The bytes `b` the theorem talks about are whatever the buffer holds: a mapped file that
   another process changes during the run changes them (and one cut short faults, a crash). */
static uint8_t *read_input(const char *path, uint64_t *n) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) fail(path, strerror(errno));
  struct stat st;
  if (fstat(fd, &st) == 0 && S_ISREG(st.st_mode) && st.st_size > 0) {
    uint8_t *buf = mmap(0, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (buf != MAP_FAILED) {
      close(fd);
      in_mapped = 1;
      *n = st.st_size;
      return buf;
    }
  }
  return slurp(fd, path, n);
}

/* `--jobs=N` (N > 1), the threaded mode.

   Entry 1 (`ca_start_a`) runs the stages and phase A in the region. On success (rdx = 0,
   rax = 2^63 + k, k pending groups) it has written the frozen buffer into the array `OUT`, whose
   word 1 is the buffer's length in words. The buffer stays where it is: the rest of the region is
   unmapped around it and the buffer is made read-only, so a write to it faults and kills the
   process, which is never an accept (route A). N threads then each map their own zero region of
   ca_worker_size bytes and claim group indices from one atomic counter, calling
   `ca_check_b(buf, len, j, region, region_len)` for each claimed j, one call after the other on
   the region as the previous call left it.

   Concurrency: the threads share only the read-only buffer, the claim counter (fetch_add hands
   out each of 0, 1, 2, ... once) and a stop flag that only shortens a failing run. Each thread
   has its own region and its own result slot; main combines the slots after joining every
   thread. Accept iff every slot is 0: every call that thread made accepted, and the threads drain
   the counter past k unless one fails. */
static const uint64_t *g_buf;   /* the frozen buffer */
static uint64_t g_len, g_k;     /* its length in words; the number of pending groups */
static uint64_t g_next;         /* the claim counter */
static int g_stop;              /* set after a failure: the other threads stop claiming */

/* One thread: its result slot ends as 0 (every call accepted), 1 (exhausted) or 2 (error). */
static void *worker(void *slot) {
  int *res = slot;
  uint8_t *region = mmap(0, ca_worker_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(region + 2 * ca_slot, ca_worker_size / ca_slot - 2);  /* the owned arrays' slots */
  while (!__atomic_load_n(&g_stop, __ATOMIC_RELAXED)) {
    uint64_t j = __atomic_fetch_add(&g_next, 1, __ATOMIC_RELAXED);
    if (j >= g_k) break;
    ca_res r = ca_check_b(g_buf, g_len, j, region, ca_worker_size);
    if (!(r.rdx == 0 && r.rax == ACCEPT)) {
      *res = r.rdx == 1 ? 1 : 2;
      __atomic_store_n(&g_stop, 1, __ATOMIC_RELAXED);
      break;
    }
  }
  return NULL;
}

static int run_jobs(int jobs, uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                    uint8_t *base) {
  ca_res r = ca_start_a(in, in_len, pins, pins_len, base, ca_region_size);
  if (!(r.rdx == 0 && r.rax >= 1ull << 63)) return print_verdict(r);
  g_k = r.rax - (1ull << 63);
  uint64_t *out = (uint64_t *)(base + ca_out_off);
  g_len = out[1];
  /* `OUT` holds at most ca_slot / 8 words; entry 1 never reports more (its proved postcondition),
     but the unmapping below must stay inside the region whatever it says */
  if (g_len > ca_slot / 8) return print_verdict((ca_res){0, 2});
  size_t bytes = (g_len * 8 + 4095) & ~(size_t)4095;   /* whole 4096-byte pages: munmap, mprotect */
  munmap(base, ca_out_off);
  munmap((uint8_t *)out + bytes, ca_region_size - ca_out_off - bytes);
  if (mprotect(out, bytes, PROT_READ) != 0) fail("mprotect", strerror(errno));
  if (in_mapped) munmap(in, in_len); else free(in);  /* phase B reads no input byte */
  g_buf = out;
  pthread_t *th = calloc(jobs, sizeof *th);
  int *res = calloc(jobs, sizeof *res);
  if (!th || !res) fail("calloc", strerror(errno));
  int n = 0;  /* threads started; those that start drain the counter, so any n >= 1 is sound */
  for (int t = 0; t < jobs; t++)
    if (pthread_create(&th[n], NULL, worker, &res[n]) == 0) n++;
  if (n == 0) fail("pthread_create", "no thread could be started");
  int worst = 0;
  for (int t = 0; t < n; t++) {
    pthread_join(th[t], NULL);
    if (res[t] > worst) worst = res[t];
  }
  return print_verdict(worst == 0 ? (ca_res){ACCEPT, 0} : (ca_res){0, (uint64_t)worst});
}

int main(int argc, char **argv) {
  int jobs = 0;
  if (argc > 1 && strncmp(argv[1], "--jobs=", 7) == 0) {
    jobs = atoi(argv[1] + 7);
    if (jobs < 1) { fprintf(stderr, "bad --jobs\n"); return 3; }
    argv++; argc--;
  }
  if (argc != 2) { fprintf(stderr, "usage: %s [--jobs=N] FILE\n", argv[0]); return 3; }
  uint64_t in_len;
  uint8_t *in = read_input(argv[1], &in_len);
  uint8_t *region = mmap(0, ca_region_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(region + ca_w0, ca_nw);
  if (jobs > 1) return run_jobs(jobs, in, in_len, pins, sizeof pins, region);
  return print_verdict(ca_start(in, in_len, pins, sizeof pins, region, ca_region_size));
}
