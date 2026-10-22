/* Driver for the e2e lane's assembled checker (ConAgua/E2E/Main.lean `e2e-l asm`, scripts/e2e.py).

   Loads FILE into byte array 0, gives every word array CA_WORDS words (default 2^22; zeroed,
   mapped lazily), sets up the descriptor table (L.Compiler.Tab: stack top, stack limit, the
   base/length pairs of the ca_nb byte arrays and the ca_nw word arrays, the constant data ca_rom,
   the result area, the global variables, no entry arguments) and calls ca_enter(T, fuel) once.

   Prints one line:
     accept            rdx = 0 and rax = ACCEPT (0x414343455054), the only accept
     ok R              rdx = 0, any other rax (R in decimal; 1: the frontend rejected a line)
     exhausted         rdx = 1 (fuel or stack)
     missing CODE      rdx = 2 and the DIAG array's word 0 is CODE != 0: a stub was reached
                       (`ca_diag` = -1: no DIAG array, as in `ConAgua/Checker/AsmEmit.lean`)
     error             rdx = 2 otherwise (an abort or an out-of-bounds access)

   Byte array 1, if the program has it, is the pin-data buffer (DESIGN.md, lane `romload`): the
   file CA_PINS (empty if unset).

   env: CA_FUEL (default 2^62), CA_STACK (bytes, default 1 GiB), CA_WORDS (words per array),
        CA_PINS (the pin-data file) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_enter(uint64_t *T, uint64_t fuel);
extern const uint8_t ca_rom[];
extern const uint64_t ca_rom_len, ca_nw, ca_nb, ca_diag, ca_ng;

#define ACCEPT 0x414343455054ull

static void *map(size_t bytes) {
  void *p = mmap(0, bytes ? bytes : 8, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED) { perror("mmap"); exit(3); }
  return p;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: e2e FILE\n"); return 3; }
  const char *e;
  uint64_t fuel = (e = getenv("CA_FUEL")) ? strtoull(e, 0, 0) : (1ull << 62);
  size_t stack = (e = getenv("CA_STACK")) ? strtoull(e, 0, 0) : (1ull << 30);
  uint64_t words = (e = getenv("CA_WORDS")) ? strtoull(e, 0, 0) : (1ull << 22);
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 3; }
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  uint8_t *buf = map(n + 1);
  if (fread(buf, 1, n, f) != (size_t)n) { perror("read"); return 3; }
  fclose(f);
  uint8_t *st = map(stack);
  uint64_t na = ca_nb + ca_nw;
  /* table: 2 + 2 na words, the rom, a generous result area, the ca_ng global variables (zero, as
     mmap gives them), no arguments */
  size_t tw = 2 + 2 * na + (ca_rom_len + 7) / 8 + 64 + ca_ng;
  uint64_t *T = map(8 * tw);
  T[0] = (uint64_t)(st + stack); T[1] = (uint64_t)st;
  uint64_t *arr[4096];
  if (ca_nw > 4096) { fprintf(stderr, "too many arrays\n"); return 3; }
  uint8_t *pins = 0; long np = 0;
  if (ca_nb > 1 && (e = getenv("CA_PINS"))) {
    FILE *g = fopen(e, "rb");
    if (!g) { perror(e); return 3; }
    fseek(g, 0, SEEK_END); np = ftell(g); fseek(g, 0, SEEK_SET);
    pins = map(np + 1);
    if (fread(pins, 1, np, g) != (size_t)np) { perror("read"); return 3; }
    fclose(g);
  }
  for (uint64_t a = 0; a < ca_nb; a++) {
    /* byte arrays from 2 on (the prelude's bytes, lane integrate): CA_WORDS bytes each */
    T[2 + 2 * a] = a == 0 ? (uint64_t)buf : a == 1 ? (pins ? (uint64_t)pins : (uint64_t)map(8)) : (uint64_t)map(words);
    T[3 + 2 * a] = a == 0 ? (uint64_t)n : a == 1 ? (uint64_t)np : words;
  }
  for (uint64_t a = 0; a < ca_nw; a++) {
    arr[a] = map(8 * words);
    T[2 + 2 * (ca_nb + a)] = (uint64_t)arr[a];
    T[3 + 2 * (ca_nb + a)] = words;
  }
  memcpy(&T[2 + 2 * na], ca_rom, ca_rom_len);
  ca_res r = ca_enter(T, fuel);
  if (r.rdx == 0 && r.rax == ACCEPT) printf("accept\n");
  else if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
  else if (r.rdx == 1) printf("exhausted\n");
  else if (ca_diag < ca_nw && arr[ca_diag][0] != 0) printf("missing %llu\n", (unsigned long long)arr[ca_diag][0]);
  else printf("error\n");
  fflush(stdout);
  return 0;
}
