/* The harness for the compiled checker (lane `abi`; ConAgua/Compiler/Abi.lean).

   usage: main FILE [PINS]

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
     error             rdx = 2 otherwise (an abort or an out-of-bounds access) */
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_start(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                       void *base, uint64_t base_len);
extern const uint64_t ca_region_size, ca_slot, ca_w0, ca_diag, ca_nw;

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

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s FILE [PINS]\n", argv[0]); return 3; }
  uint64_t n, np = 0;
  uint8_t *in = slurp(argv[1], &n), *pins = argc > 2 ? slurp(argv[2], &np) : 0;
  uint8_t *base = mmap(0, ca_region_size, PROT_READ | PROT_WRITE,
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
  ca_res r = ca_start(in, n, pins, np, base, ca_region_size);
  if (r.rdx == 0 && r.rax == ACCEPT) printf("accept\n");
  else if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
  else if (r.rdx == 1) printf("exhausted\n");
  else if (ca_diag < ca_nw && *(uint64_t *)(base + ca_w0 + ca_diag * ca_slot) != 0)
    printf("missing %llu\n", (unsigned long long)*(uint64_t *)(base + ca_w0 + ca_diag * ca_slot));
  else printf("error\n");
  return 0;
}
