/* Driver for the compiled instantiate1 benchmark (ConAgua/Arena/Inst1Emit.lean): sets up the
   descriptor table (L.Compiler.Tab with nb = 0, nw = NW = 48, the full layout through the
   derived-range arrays and both memos), all arrays zero, and calls ca_enter(T, fuel) on
   inst1_bench(n, k, val, d). `harness/lift.c`'s shape exactly, one array wider.

   usage: inst1 N K VAL D      k < 2^63: build the N-deep term over bvar K and return
                                inst_entry(x, bvar VAL, D) of it;
                                k >= 2^63: build only (the harness-and-build baseline)
   env:   CA_FUEL (default 2^62), CA_STACK (bytes, default 1 GiB)
   prints "ok R", "exhausted" (rdx = 1) or "error" (rdx = 2) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_enter(uint64_t *T, uint64_t fuel);
extern const uint8_t ca_rom[];
extern const uint64_t ca_rom_len;

#define NW 48
static uint64_t T[8192];

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: inst1 N K VAL D\n"); return 2; }
  uint64_t n = strtoull(argv[1], 0, 0), k = strtoull(argv[2], 0, 0);
  uint64_t val = strtoull(argv[3], 0, 0), d = strtoull(argv[4], 0, 0);
  const char *e;
  uint64_t fuel = (e = getenv("CA_FUEL")) ? strtoull(e, 0, 0) : (1ull << 62);
  size_t stack = (e = getenv("CA_STACK")) ? strtoull(e, 0, 0) : (1ull << 30);
  uint8_t *st = mmap(0, stack, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (st == MAP_FAILED) { perror("mmap"); return 2; }
  uint64_t len[NW] = {0};
  len[1] = 64;                                /* CTL */
  for (int a = 2; a < NW; a++) len[a] = 8 * (n + 16); /* every content array, generously */
  T[0] = (uint64_t)(st + stack); T[1] = (uint64_t)st;
  for (int a = 0; a < NW; a++) {
    uint64_t *p = len[a] ? mmap(0, 8 * len[a], PROT_READ | PROT_WRITE,
                                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0) : 0;
    if (p == MAP_FAILED) { perror("mmap"); return 2; }
    T[2 + 2 * a] = (uint64_t)p; T[3 + 2 * a] = len[a];
  }
  uint64_t argw = 2 + 2 * NW + (ca_rom_len + 7) / 8;
  memcpy(&T[2 + 2 * NW], ca_rom, ca_rom_len);
  T[argw] = n; T[argw + 1] = k; T[argw + 2] = val; T[argw + 3] = d;
  ca_res r = ca_enter(T, fuel);
  if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
  else if (r.rdx == 1) printf("exhausted\n");
  else printf("error\n");
  return 0;
}
