/* The harness for the compiled checker: the trusted C side of the end-to-end theorem.

   build:  make   (cc -std=gnu23 -O2 -pthread -o checker main.c checker.s; Makefile)
   usage:  checker [--jobs=N] FILE
           checker [--jobs=N] --compare [--] CHALLENGE SOLUTION

   The default path is the one the final theorem covers (`checkerFile_accepts`,
   ConAgua/Final/EndToEnd.lean; the call is as `AbiCall` in ConAgua/Final/Abi.lean states it).
   It maps FILE (the input) read-only, or reads it whole into a buffer if it is not a regular
   file (`read_input`); the theorem is about the bytes the buffer holds, so a file that another
   process changes during the run is outside it. It maps one zero region of ca_region_size
   bytes and calls, once,

     ca_start(in, in_len, pins, pins_len, region, region_len)

   with the pin data `pins` built into the binary (below). `ca_start` is the sequential driver:
   entry 1 (the stages and the stream index), then entry 2 over every record's job, in place;
   the entry stubs lay out everything else inside the region. The verdict is one line on stdout,
   and the exit status follows the Lean kernel arena's convention (0 accepted, 1 rejected,
   2 declined, 3 error):
     accept         0  rdx = 0 and rax = ACCEPT (0x414343455054): the only accept
     rejected: M    1  rdx = 2, class 1: the checker aborted where the twin fails as invalid
     declined: M    2  rdx = 2, class 2: the checker aborted where the twin fails as not
                       implemented
     error: M       3  rdx = 2, class 0: any other abort (a capacity of the checker, a check the
                       twin does not make, an out-of-bounds access); claims nothing
     exhausted      3  rdx = 1: fuel, stack or region ran out
     ok R           3  rdx = 0 and any other rax R, in decimal (1: the frontend rejected a malformed
                       line, which con-leche reports as an error too)
   On an abort, rax is its code: the class in bits 0-1, the reason in bits 2 and up, whose
   message M is reasons[reason] (reasons.h, generated from the twin's own messages; reason 0
   prints no message). The classes are proved (`checkerFile_accepts`): rdx = 2 with class 1 or 2
   means the twin's pipeline fails on the input with `invalid` resp. `notImplemented`; the
   messages are not part of the theorem.
   A failure of the harness itself (usage, a file that cannot be read, no memory) prints a
   message on stderr and exits with status 3 and no verdict line. A crash (e.g. a page of the
   region the kernel cannot supply) prints nothing and ends with a signal. None is an accept.

   With --jobs=N for N > 1, the threaded mode, `run_jobs` below: its accept is covered by
   `checkerFile_threads_accept` (ConAgua/Final/EndToEnd.lean), under the hypotheses
   `ThreadsRun` (ConAgua/Final/ThreadsFinal.lean) states about this harness's threads. A failing
   threaded run prints the verdict of the failing job with the smallest index, which is what the
   sequential run prints; a reject or decline is covered by `checkerFile_threads_verdict`, under
   `ThreadsFail` (ConAgua/Final/ThreadsVerdict.lean): the failing call and the jobs below it. */
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
   con-ron embeds): `pins.bin`, written by `romgen pins.bin 4` and kept up to date by
   scripts/asm_file.py. Not trusted: the theorem holds for every pin buffer, and the checker decodes
   and checks it at run time. C23 `#embed` (GCC >= 15, Clang >= 19). */
static const uint8_t pins[] = {
#embed "pins.bin"
};

#include "reasons.h"

/* `ConAgua.Final.ACCEPT`, the verdict word for accept */
#define ACCEPT 0x414343455054ull

static int accepted(ca_res r) { return r.rdx == 0 && r.rax == ACCEPT; }

/* Prints the verdict line and returns the exit status (the table above). */
static int print_verdict(ca_res r) {
  if (accepted(r)) { printf("accept\n"); return 0; }
  if (r.rdx == 0) { printf("ok %llu\n", (unsigned long long)r.rax); return 3; }
  if (r.rdx == 1) { printf("exhausted\n"); return 3; }
  uint64_t cls = r.rax & 3, why = r.rax >> 2;
  const char *msg = why < sizeof reasons / sizeof *reasons ? reasons[why] : "unknown reason";
  const char *sep = why ? ": " : "";
  if (cls == 1) { printf("rejected%s%s\n", sep, msg); return 1; }
  if (cls == 2) { printf("declined%s%s\n", sep, msg); return 2; }
  printf("error%s%s\n", sep, msg);
  return 3;
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
   doubling. Fails on a read error. */
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
  *n = len;
  return buf;
}

static int in_mapped;  /* the input buffer is a mapping of the file, not a malloc'd buffer */

/* The input: a nonempty regular file is mapped read-only;
   anything else (a pipe, a terminal, an empty file) or a file mmap refuses is read with `slurp`.
   The bytes `b` the theorem talks about are whatever the buffer holds: a mapped file that
   another process changes during the run changes them (and one truncated faults: a crash). */
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

   Entry 1 (`ca_start_a`) runs the stages and the stream index in the region. On success
   (rdx = 0, rax = 2^63 + k for k records, one job each) it has written the frozen buffer into
   `OUT`, whose word 1 is the buffer's length in words. The buffer stays where it is: the rest of
   the region is unmapped around it and the buffer is made read-only, so a write to it faults and
   kills the process, which is never an accept (route A). N threads then each map their own zero
   region of ca_worker_size bytes and claim job indices from one atomic counter, calling
   `ca_check_b(buf, len, j, region, region_len)` for each claimed j, one call after the other on
   the region as the previous call left it.

   Concurrency: the threads share only the read-only buffer, the claim counter (fetch_add hands
   out each of 0, 1, 2, ... once, in order, so each thread's claims increase: `ThreadsRun`'s
   `incr`) and a stop flag that only shortens a failing run. Each thread has its own region and
   its own result slot; main combines the slots after joining every thread. Accept iff no slot
   holds a failure: every call that thread made accepted, and the threads drain the counter past
   k unless one fails. Otherwise the verdict is that of the failing job with the smallest index:
   the indices are claimed in order and a thread finishes the job it holds, so every lower job
   has been run, and accepted, when the threads are joined (`ThreadFail`'s `below`). */
static const uint64_t *g_buf;   /* the frozen buffer */
static uint64_t g_len, g_k;     /* its length in words; the number of jobs (records) */
static uint64_t g_next;         /* the claim counter */
static int g_stop;              /* set after a failure: the other threads stop claiming */

/* A thread's result: the first job it saw fail (j = UINT64_MAX: none) and that call's result. */
typedef struct { uint64_t j; ca_res r; } slot_t;

/* One thread: claims jobs until the counter passes k or a call fails. */
static void *worker(void *arg) {
  slot_t *res = arg;
  uint8_t *region = mmap(0, ca_worker_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(region + 2 * ca_slot, ca_worker_size / ca_slot - 2);  /* the owned arrays' slots */
  while (!__atomic_load_n(&g_stop, __ATOMIC_RELAXED)) {
    uint64_t j = __atomic_fetch_add(&g_next, 1, __ATOMIC_RELAXED);
    if (j >= g_k) break;
    ca_res r = ca_check_b(g_buf, g_len, j, region, ca_worker_size);
    if (!accepted(r)) {
      *res = (slot_t){j, r};
      __atomic_store_n(&g_stop, 1, __ATOMIC_RELAXED);
      break;
    }
  }
  munmap(region, ca_worker_size);  /* the compared run's second phase maps fresh regions */
  return NULL;
}

/* The pool: `jobs` threads run the `k` jobs of the frozen buffer `buf` (`len` words) as described
   above, and the result is the failing job's with the smallest index, or accept. Shared by the
   flat threaded run and both check phases of the threaded compared run. */
static ca_res run_pool(const uint64_t *buf, uint64_t len, uint64_t k, int jobs) {
  g_buf = buf; g_len = len; g_k = k; g_next = 0; g_stop = 0;
  pthread_t *th = calloc(jobs, sizeof *th);
  slot_t *res = calloc(jobs, sizeof *res);
  if (!th || !res) fail("calloc", strerror(errno));
  for (int t = 0; t < jobs; t++) res[t].j = UINT64_MAX;
  int n = 0;  /* threads started; those that start drain the counter, so any n >= 1 is sound */
  for (int t = 0; t < jobs; t++)
    if (pthread_create(&th[n], NULL, worker, &res[n]) == 0) n++;
  if (n == 0) fail("pthread_create", "no thread could be started");
  slot_t first = {UINT64_MAX, {ACCEPT, 0}};
  for (int t = 0; t < n; t++) {
    pthread_join(th[t], NULL);
    if (res[t].j < first.j) first = res[t];
  }
  free(th); free(res);
  return first.r;
}

/* The frozen buffer an entry left in `OUT` of the region at `base`: its length in words (word 1),
   0 if it says more than `OUT` holds (entry 1 never does: its proved postcondition; but the
   unmapping and mprotect below must stay inside the region whatever it says). */
static uint64_t out_len(uint8_t *base) {
  uint64_t len = ((uint64_t *)(base + ca_out_off))[1];
  return len > ca_slot / 8 ? 0 : len;
}

/* `OUT`'s pages that hold `len` words: whole 4096-byte pages (munmap, mprotect). */
static size_t out_bytes(uint64_t len) { return (len * 8 + 4095) & ~(size_t)4095; }

static int run_jobs(int jobs, uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                    uint8_t *base) {
  ca_res r = ca_start_a(in, in_len, pins, pins_len, base, ca_region_size);
  if (!(r.rdx == 0 && r.rax >= 1ull << 63)) return print_verdict(r);
  uint64_t len = out_len(base);
  if (len == 0) return print_verdict((ca_res){0, 2});
  uint64_t *out = (uint64_t *)(base + ca_out_off);
  size_t bytes = out_bytes(len);
  munmap(base, ca_out_off);
  munmap((uint8_t *)out + bytes, ca_region_size - ca_out_off - bytes);
  if (mprotect(out, bytes, PROT_READ) != 0) fail("mprotect", strerror(errno));
  if (in_mapped) munmap(in, in_len); else free(in);  /* the jobs read no input byte */
  return print_verdict(run_pool(out, len, r.rax - (1ull << 63), jobs));
}

static int run_compare(const char *prog, int jobs, int argc, char **argv);

/* `--jobs=N`: the worker count (N >= 1), or -1 if the argument is not that flag, 0 if malformed. */
static int jobs_flag(const char *a) {
  if (strncmp(a, "--jobs=", 7) != 0) return -1;
  int n = atoi(a + 7);
  return n < 1 ? 0 : n;
}

static int run_main(int argc, char **argv) {
  const char *prog = argv[0];
  int jobs = 1, cmp = 0;
  argv++; argc--;
  /* the flags, before the files: --jobs=N and --compare, in either order (as con-ron) */
  while (argc > 0) {
    int n = jobs_flag(argv[0]);
    if (n == 0) { fprintf(stderr, "bad --jobs\n"); return 3; }
    if (n > 0) jobs = n;
    else if (strcmp(argv[0], "--compare") == 0 && !cmp) cmp = 1;
    else break;
    argv++; argc--;
  }
  if (cmp) return run_compare(prog, jobs, argc, argv);
  if (argc != 1) { fprintf(stderr, "usage: %s [--jobs=N] FILE\n       %s [--jobs=N] --compare [--] CHALLENGE SOLUTION\n", prog, prog); return 3; }
  uint64_t in_len;
  uint8_t *in = read_input(argv[0], &in_len);
  uint8_t *region = mmap(0, ca_region_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(region + ca_w0, ca_nw);
  if (jobs > 1) return run_jobs(jobs, in, in_len, pins, sizeof pins, region);
  return print_verdict(ca_start(in, in_len, pins, sizeof pins, region, ca_region_size));
}

/* `[--jobs=N] --compare [--] CHALLENGE SOLUTION` (the flags in either order): CHALLENGE checked
   with its axioms other than the built-in ones, and its declarations whose value uses `sorryAx`,
   justified by SOLUTION, which is checked as a FILE is. The two files are read as FILE is
   (`read_input`); the verdict line and the exit status are `print_verdict`'s.

   Sequential (N = 1, the default): the region is ca_cmp_region_size bytes, and `ca_compare` is
   called once, the challenge's bytes in the first two arguments (as `ca_start`'s input), the
   solution's in the last two (on the stack). Its accept is covered by
   `checkerFile_compare_accepts` (ConAgua/Final/Compare.lean; the call is as `CmpCall` states).

   Threaded (N > 1), `run_compare_jobs`: the harness drives the mode entries itself, all on one
   region of ca_region_size bytes, each call on the region as the previous call left it:
     ca_start_a4(c, ...)  the stages up to the challenge's parse; on with rdx = 0, rax >= 2^63
     ca_start_a5(s, ...)  the solution's parse, preparation, pins, index, its frozen buffer in
                          `OUT`; rax = 2^63 + kS
     the solution's kS jobs on N threads (`run_pool`, as the flat threaded mode; `OUT` read-only
                          meanwhile, the rest of the region kept mapped and untouched)
     ca_start_a7(s, ...)  `OUT` writable again: the challenge's preparation, index (the
                          solution's moved aside), its frozen buffer in `OUT`; rax = 2^63 + kC
     the challenge's kC jobs on N threads (`run_pool`)
   The pin data and both files stay in place until the end (each entry's setup reads the
   descriptors of the input and the pins). A failure in a phase ends the run with its verdict
   (the failing job with the smallest index, as the flat threaded mode). Its accept is covered by
   `checkerFile_compare_threads_accept` (ConAgua/Final/CmpThreads.lean), under the hypotheses
   `CmpThreadsRun` states about this harness. */
extern ca_res ca_compare(const uint8_t *c, uint64_t c_len, const uint8_t *pins, uint64_t pins_len,
                         void *base, uint64_t base_len, const uint8_t *s, uint64_t s_len);
extern ca_res ca_start_a4(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                          void *base, uint64_t base_len);
extern ca_res ca_start_a5(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                          void *base, uint64_t base_len);
extern ca_res ca_start_a7(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                          void *base, uint64_t base_len);
extern const uint64_t ca_cmp_region_size;

static int high(ca_res r) { return r.rdx == 0 && r.rax >= 1ull << 63; }

/* One check phase of the threaded compared run: the buffer the entry left in `OUT`, read-only
   while the pool runs `k` jobs on it, writable again after. */
static ca_res cmp_phase(uint8_t *base, uint64_t k, int jobs) {
  uint64_t len = out_len(base);
  if (len == 0) return (ca_res){0, 2};
  uint64_t *out = (uint64_t *)(base + ca_out_off);
  size_t bytes = out_bytes(len);
  if (mprotect(out, bytes, PROT_READ) != 0) fail("mprotect", strerror(errno));
  ca_res r = run_pool(out, len, k, jobs);
  if (mprotect(out, bytes, PROT_READ | PROT_WRITE) != 0) fail("mprotect", strerror(errno));
  return r;
}

static int run_compare_jobs(int jobs, uint8_t *c, uint64_t c_len, uint8_t *s, uint64_t s_len) {
  uint8_t *base = mmap(0, ca_region_size, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (base == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(base + ca_w0, ca_nw);
  ca_res r = ca_start_a4(c, c_len, pins, sizeof pins, base, ca_region_size);
  if (!high(r)) return print_verdict(r);
  r = ca_start_a5(s, s_len, pins, sizeof pins, base, ca_region_size);
  if (!high(r)) return print_verdict(r);
  r = cmp_phase(base, r.rax - (1ull << 63), jobs);
  if (!accepted(r)) return print_verdict(r);
  r = ca_start_a7(s, s_len, pins, sizeof pins, base, ca_region_size);
  if (!high(r)) return print_verdict(r);
  return print_verdict(cmp_phase(base, r.rax - (1ull << 63), jobs));
}

static int compare_usage(const char *prog, const char *why) {
  fprintf(stderr, "%s: --compare takes %s, a challenge and its solution\n", prog, why);
  return 3;
}

static int run_compare(const char *prog, int jobs, int argc, char **argv) {
  if (argc > 0 && strcmp(argv[0], "--") == 0) { argv++; argc--; }
  if (argc != 2) return compare_usage(prog, "two files");
  if (strcmp(argv[0], argv[1]) == 0) return compare_usage(prog, "two different files");
  uint64_t c_len, s_len;
  uint8_t *c = read_input(argv[0], &c_len);
  uint8_t *s = read_input(argv[1], &s_len);
  if (jobs > 1) return run_compare_jobs(jobs, c, c_len, s, s_len);
  uint8_t *region = mmap(0, ca_cmp_region_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) fail("mmap", strerror(errno));
  advise_huge(region + ca_w0, ca_nw);
  return print_verdict(ca_compare(c, c_len, pins, sizeof pins, region, ca_cmp_region_size, s, s_len));
}

/* Every path flushes the verdict line before exiting: a flush that fails is status 3 (the
   verdict was not written), whatever the run's status was. */
int main(int argc, char **argv) {
  int st = run_main(argc, argv);
  if (fflush(stdout) != 0 || ferror(stdout)) {
    fprintf(stderr, "error: cannot write the verdict\n");
    return 3;
  }
  return st;
}
