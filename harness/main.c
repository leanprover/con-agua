/* The harness for the compiled checker (lane `abi`; ConAgua/Compiler/Abi.lean).

   usage: main FILE [PINS]

   Reads FILE (the input) and PINS (the pin data, byte array 1; empty if not given) into memory,
   maps a zero region of ca_region_size bytes (MAP_NORESERVE: the pages the checker never touches
   never become real; needs overcommit) and calls, once,

     ca_start(in, in_len, pins, pins_len, region, region_len)

   The entry stub lays out everything else inside the region. Prints one line:
     accept            rdx = 0 and rax = ACCEPT (0x414343455054), the only accept
     ok R              rdx = 0, any other rax (R in decimal; 1: the frontend rejected a line)
     exhausted         rdx = 1 (fuel, stack, or a region smaller than ca_region_size)
     missing CODE      rdx = 2 and the DIAG array's word 0 is CODE != 0 (`e2e-l asm` programs)
     error             rdx = 2 otherwise (an abort or an out-of-bounds access) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>

typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_start(const uint8_t *in, uint64_t in_len, const uint8_t *pins, uint64_t pins_len,
                       void *base, uint64_t base_len);
extern const uint64_t ca_region_size, ca_slot, ca_w0, ca_diag, ca_nw;

#define ACCEPT 0x414343455054ull

static uint8_t *slurp(const char *path, uint64_t *n) {
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); exit(3); }
  fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
  uint8_t *buf = malloc(len ? len : 1);
  if (!buf || fread(buf, 1, len, f) != (size_t)len) { perror(path); exit(3); }
  fclose(f);
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
