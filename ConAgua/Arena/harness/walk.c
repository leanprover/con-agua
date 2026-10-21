/* Driver for the compiled walk (ConAgua/Arena/WalkEmit.lean): sets up the descriptor table
   (L.Compiler.Tab with nb = 0, nw = 25) over the arena layout of ConAgua/Arena/ArenaRel.lean,
   all arrays zero, and calls ca_enter(T, fuel) on bb_bench(n, k).

   usage: walk N K      k < 2^63: build the N-deep term over bvar K and return bb_memo of it;
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

static uint64_t T[4096];

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: walk N K\n"); return 2; }
  uint64_t n = strtoull(argv[1], 0, 0), k = strtoull(argv[2], 0, 0);
  const char *e;
  uint64_t fuel = (e = getenv("CA_FUEL")) ? strtoull(e, 0, 0) : (1ull << 62);
  size_t stack = (e = getenv("CA_STACK")) ? strtoull(e, 0, 0) : (1ull << 30);
  uint8_t *st = mmap(0, stack, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (st == MAP_FAILED) { perror("mmap"); return 2; }
  uint64_t len[25] = {0};
  len[1] = 26;                                   /* CTL */
  len[4] = 4 * (n + 16); len[5] = 4 * (n + 16);  /* AREC, ASLOT */
  for (int a = 6; a < 22; a++) len[a] = 64;      /* the other tables, unused */
  len[22] = 64; len[23] = 64;                    /* BREC, BSLOT */
  len[24] = 8 * (n + 16);                        /* BMEMO: 2 (n + 16) slots */
  T[0] = (uint64_t)(st + stack); T[1] = (uint64_t)st;
  for (int a = 0; a < 25; a++) {
    uint64_t *p = len[a] ? mmap(0, 8 * len[a], PROT_READ | PROT_WRITE,
                                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0) : 0;
    if (p == MAP_FAILED) { perror("mmap"); return 2; }
    T[2 + 2 * a] = (uint64_t)p; T[3 + 2 * a] = len[a];
  }
  uint64_t argw = 52 + (ca_rom_len + 7) / 8;
  memcpy(&T[52], ca_rom, ca_rom_len);
  T[argw] = n; T[argw + 1] = k;
  ca_res r = ca_enter(T, fuel);
  if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
  else if (r.rdx == 1) printf("exhausted\n");
  else printf("error\n");
  return 0;
}
