/* Driver for code compiled from L (ConAgua/Compiler): loads a file into byte array 0, sets up
   the descriptor table (L.Compiler.Tab with nb = 1, nw = 0, and the program's constant data
   ca_rom) and an L stack, and calls ca_enter(T, fuel).

   usage: run FILE ARG...        one call with the given word arguments; prints the outcome
          run --lines FILE       one call skip_braced(start + 1, 0) per line that starts with '{';
                                 checks that each returns the position after the line's object
   env:   CA_FUEL (default 2^62), CA_STACK (bytes, default 1 GiB) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

typedef struct { uint64_t rax, rdx; } ca_res;
extern ca_res ca_enter(uint64_t *T, uint64_t fuel);
extern const uint8_t ca_rom[];
extern const uint64_t ca_rom_len, ca_ng;

static uint64_t T[4096];
static uint64_t argw; /* the word index of the entry arguments in T */

static uint8_t *load(const char *path, size_t *len) {
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); exit(2); }
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  uint8_t *buf = malloc(n + 1);
  if (fread(buf, 1, n, f) != (size_t)n) { perror("read"); exit(2); }
  fclose(f);
  *len = n;
  return buf;
}

static ca_res call(uint64_t fuel, int nargs, const uint64_t *args) {
  for (int i = 0; i < nargs; i++) T[argw + i] = args[i];
  return ca_enter(T, fuel);
}

int main(int argc, char **argv) {
  int lines = argc > 1 && strcmp(argv[1], "--lines") == 0;
  if (argc < 2 + lines) { fprintf(stderr, "usage: run [--lines] FILE ARG...\n"); return 2; }
  const char *e;
  uint64_t fuel = (e = getenv("CA_FUEL")) ? strtoull(e, 0, 0) : (1ull << 62);
  size_t stack = (e = getenv("CA_STACK")) ? strtoull(e, 0, 0) : (1ull << 30);
  uint8_t *st = mmap(0, stack, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (st == MAP_FAILED) { perror("mmap"); return 2; }
  size_t len;
  uint8_t *buf = load(argv[1 + lines], &len);
  T[0] = (uint64_t)(st + stack); T[1] = (uint64_t)st;
  T[2] = (uint64_t)buf; T[3] = len;
  argw = 4 + (ca_rom_len + 7) / 8 + ca_ng; /* the global variables (zero) sit before the arguments */
  if (argw + 8 > sizeof T / sizeof T[0]) { fprintf(stderr, "constant data too large\n"); return 2; }
  memcpy(&T[4], ca_rom, ca_rom_len);
  if (!lines) {
    uint64_t args[8];
    int n = argc - 2;
    for (int i = 0; i < n && i < 8; i++) args[i] = strtoull(argv[2 + i], 0, 0);
    ca_res r = call(fuel, n, args);
    if (r.rdx == 0) printf("ok %llu\n", (unsigned long long)r.rax);
    else if (r.rdx == 1) printf("exhausted\n");
    else printf("error\n");
    return 0;
  }
  uint64_t nlines = 0, sum = 0, bad = 0;
  for (size_t i = 0; i < len;) {
    size_t eol = i;
    while (eol < len && buf[eol] != '\n') eol++;
    if (buf[i] == '{') {
      uint64_t args[2] = {i + 1, 0};
      ca_res r = call(fuel, 2, args);
      if (r.rdx != 0) { printf("line at %zu: outcome %llu\n", i, (unsigned long long)r.rdx); return 1; }
      /* the object ends the line (lean4export ndjson) */
      if (r.rax != eol) bad++;
      sum += r.rax; nlines++;
    }
    i = eol + 1;
  }
  printf("lines %llu checksum %llu mismatches %llu\n", (unsigned long long)nlines,
         (unsigned long long)sum, (unsigned long long)bad);
  return bad != 0;
}
