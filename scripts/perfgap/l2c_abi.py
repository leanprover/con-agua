#!/usr/bin/env python3
"""L program file -> C: the "good compiler" oracle (lane compopt2's l2c.py, ported by lane perfgap to
the current language and ABI: tiered arrays `l64t`/`n64t`/`s64t`, block ops `cp64`/`cp8w`/`scan`/`l8x8`,
globals in the table, tiercost A's descriptor layout).

The C file defines `ca_enter(T, fuel)` only; the real entry stub of `asm/checker.s` lays out the region
and jumps to it, so the binary runs with `harness/main.c` exactly as the compiled checker does:

  e2e-l: checker.prog (scripts/e2e.py write_checker, in a worktree)
  python3 scripts/perfgap/l2c_abi.py checker.prog oracle.c [--no-bounds] [--no-fuel] [--volatile=nonleaf|all] [--inline-leaves=N]
  (sed -n 1,<line before ca_enter:>p asm/checker.s; sed -n '<first .section .rodata>,$p' asm/checker.s) > stub.s
  cc -O2 -w [-fno-inline] -o oracle.bin harness/main.c oracle.c stub.s
  ./oracle.bin FILE PINS

Same semantics as L (bounds checks abort, fuel at every call and loop back-edge, zeroed locals);
fuel is a global here (a memory decrement), so `--no-fuel` overstates the asm's fuel cost.
"""
import re, sys

def tok(s):
    return re.findall(r'\(|\)|[^\s()]+', s)

def parse(ts, i=0):
    if ts[i] == '(':
        out = []; i += 1
        while ts[i] != ')':
            x, i = parse(ts, i); out.append(x)
        return out, i + 1
    return ts[i], i + 1

args = [a for a in sys.argv[1:] if not a.startswith('--')]
BOUNDS = '--no-bounds' not in sys.argv
FUEL = '--no-fuel' not in sys.argv
# --inline-leaves=N: mark leaf functions (no calls) of at most N syntax nodes always_inline (with
# `cc -fno-inline`: the effect of inlining small leaves alone)
# --volatile=nonleaf|all: the locals of non-leaf (or all) functions are `volatile` (kept in memory,
# as a compiler without register allocation there would)
VOL = next((a.split('=')[1] for a in sys.argv if a.startswith('--volatile=')), None)
INL = next((int(a.split('=')[1]) for a in sys.argv if a.startswith('--inline-leaves=')), None)
src, dst = args
data, fns, stubs = [], [], []
for ln in open(src):
    ws = ln.split(' ')
    if ws[0] == 'data':
        data.append(bytes.fromhex(ws[2].strip()))
    elif ws[0] == 'fn':
        name, np_, nl = ws[1], int(ws[2]), int(ws[3])
        rest = ln[len('fn ') + len(ws[1]) + len(ws[2]) + len(ws[3]) + 3:]
        body, _ = parse(tok(rest))
        fns.append((name, np_, nl, body))
    elif ws[0] == 'stub':
        stubs.append((ws[1], int(ws[2]), int(ws[3])))

nb, nw, ng = 0, 0, 0
def scan(x):
    global nb, nw, ng
    if isinstance(x, list) and x:
        h = x[0]
        if h in ('l8', 'n8', 's8'): nb = max(nb, int(x[1]) + 1)
        if h in ('l64', 'n64', 's64'): nw = max(nw, int(x[1]) + 1)
        if h in ('g', 'gset'): ng = max(ng, int(x[1]) + 1)
        if h in ('l64t', 'n64t', 's64t'): nw = max(nw, int(x[1]) + 257)
        for y in x[1:]:
            scan(y)
for f in fns:
    scan(f[3])
nb = max(nb, 1)
diag = nw
NW = nw

def nret(s):
    if not isinstance(s, list): return 0
    h = s[0]
    if h == 'seq': return max(nret(s[1]), nret(s[2]))
    if h == 'if': return max(nret(s[2]), nret(s[3]))
    if h == 'while': return nret(s[2])
    if h == 'ret': return len(s) - 1
    return 0

cname = {}
for i, f in enumerate(fns + [(n, np_, np_, None) for n, np_, _ in stubs]):
    cname[f[0]] = 'f%d_%s' % (i, re.sub(r'[^A-Za-z0-9_]', '_', f[0]))
nr = {f[0]: max(1, nret(f[3])) for f in fns}
for n, np_, _ in stubs:
    nr[n] = 1

BIN = {'add': '+', 'sub': '-', 'mul': '*', 'and': '&', 'or': '|', 'xor': '^'}
CMP = {'eq': '==', 'ne': '!=', 'ult': '<', 'ule': '<='}

def E(e):
    h = e[0]
    if h == 'c': return '%sULL' % e[1]
    if h == 'v': return 'v%s' % e[1]
    if h == 'g': return 'G[%s]' % e[1]
    if h == 'n8': return 'L8[%s]' % e[1]
    if h == 'n64': return 'L64[%s]' % e[1]
    if h == 'l8': return 'LD8(%s, %s)' % (e[1], E(e[2]))
    if h == 'l64': return 'LD64(%s, %s)' % (e[1], E(e[2]))
    if h == 'l64t': return 'LD64(%s + 256 * (%s & 1), %s)' % (e[1], E(e[2]), E(e[3]))
    if h == 'n64t': return 'L64[%s + 256 * (%s & 1)]' % (e[1], E(e[2]))
    if h == 'l8x8': return 'LD8X8(%s, %s, %s)' % (BP(e[1]), BL(e[1]), E(e[2]))
    if h == 'ldc': return 'LDC(D%s, %d, %s)' % (e[1], len(data[int(e[1])]), E(e[2]))
    if h == 'b':
        op, a, b = e[1], E(e[2]), E(e[3])
        if op in BIN: return '(%s %s %s)' % (a, BIN[op], b)
        if op == 'shl': return '(%s << (%s & 63))' % (a, b)
        if op == 'shr': return '(%s >> (%s & 63))' % (a, b)
        if op == 'mulhi': return '(u64)(((unsigned __int128)%s * %s) >> 64)' % (a, b)
    if h == 'w': return '(u64)(%s)' % C(['cmp'] + e[1:])
    raise Exception('expr %r' % (e,))

def WA(w):
    return w[1] if w[0] == 'wp' else '(%s + 256 * (%s & 1))' % (w[1], E(w[2]))
def BP(b):
    return 'B8[%s]' % b[1] if b[0] == 'ba' else 'D%s' % b[1]
def BL(b):
    return 'L8[%s]' % b[1] if b[0] == 'ba' else '%dULL' % len(data[int(b[1])])

def C(c):
    h = c[0]
    if h == 'cmp':
        op, a, b = c[1], E(c[2]), E(c[3])
        if op in CMP: return '(%s %s %s)' % (a, CMP[op], b)
        return '((int64_t)%s %s (int64_t)%s)' % (a, '<' if op == 'slt' else '<=', b)
    if h == 'and': return '(%s && %s)' % (C(c[1]), C(c[2]))
    if h == 'or': return '(%s || %s)' % (C(c[1]), C(c[2]))
    if h == 'not': return '(!%s)' % C(c[1])
    raise Exception('cond %r' % (c,))

def S(s, fn, ind, inloop):
    p = '  ' * ind
    if not isinstance(s, list):
        if s == 'skip': return ''
        if s == 'abort': return p + 'ERR();\n'
        if s == 'brk': return p + ('break;\n' if inloop else 'goto fall;\n')
        raise Exception(s)
    h = s[0]
    if h == 'set': return p + 'v%s = %s;\n' % (s[1], E(s[2]))
    if h == 'gset': return p + 'G[%s] = %s;\n' % (s[1], E(s[2]))
    if h == 'cp64':
        return p + '{ u64 _d = %s; u64 _i = %s; u64 _s = %s; u64 _j = %s; u64 _n = %s; CHK(_i + _n <= L64[_d] && _j + _n <= L64[_s] && _i + _n >= _i && _j + _n >= _j); for (u64 _k = 0; _k < _n; _k++) B64[_d][_i + _k] = B64[_s][_j + _k]; }\n' % (WA(s[1]), E(s[2]), WA(s[3]), E(s[4]), E(s[5]))
    if h == 'cp8w':
        return p + '{ u64 _d = %s; u64 _i = %s; const uint8_t *_b = %s; u64 _bl = %s; u64 _j = %s; u64 _n = %s; CHK(_i + _n <= L64[_d] && _j + _n <= _bl && _i + _n >= _i && _j + _n >= _j); for (u64 _k = 0; _k < _n; _k++) B64[_d][_i + _k] = _b[_j + _k]; }\n' % (WA(s[1]), E(s[2]), BP(s[3]), BL(s[3]), E(s[4]), E(s[5]))
    if h == 'scan':
        return p + '{ const uint8_t *_b = %s; u64 _bl = %s; u64 _i = %s; u64 _e = %s; CHK(_i <= _e && _e <= _bl); while (_i < _e && !D%s[_b[_i]]) _i++; v%s = _i; }\n' % (BP(s[2]), BL(s[2]), E(s[3]), E(s[4]), s[5], s[1])
    if h == 's64t':
        return p + '{ u64 _t = %s; u64 _i = %s; u64 _e = %s; ST64(%s + 256 * (_t & 1), _i, _e); }\n' % (E(s[2]), E(s[3]), E(s[4]), s[1])
    if h in ('s8', 's64'):
        return p + '{ u64 _i = %s; u64 _e = %s; ST%s(%s, _i, _e); }\n' % (E(s[2]), E(s[3]), h[1:], s[1])
    if h == 'seq': return S(s[1], fn, ind, inloop) + S(s[2], fn, ind, inloop)
    if h == 'if':
        return p + 'if (%s) {\n%s%s} else {\n%s%s}\n' % (C(s[1]), S(s[2], fn, ind + 1, inloop), p,
                                                       S(s[3], fn, ind + 1, inloop), p)
    if h == 'while':
        return p + 'while (%s) {\n%s%s  FUEL();\n%s}\n' % (C(s[1]), S(s[2], fn, ind + 1, True), p, p)
    if h == 'ret':
        es = s[1:]
        n = nr[fn]
        vals = [E(e) for e in es] + ['0'] * (n - len(es))
        return p + '{ R_%s _r = {{%s}}; return _r; }\n' % (cname[fn], ', '.join(vals))
    if h == 'call':
        xs, f, as_ = s[1], s[2], s[3]
        out = p + '{ '
        for i, a in enumerate(as_):
            out += 'u64 _a%d = %s; ' % (i, E(a))
        out += 'FUEL(); R_%s _r = %s(%s);' % (cname[f], cname[f], ', '.join('_a%d' % i for i in range(len(as_))))
        for i, x in enumerate(xs):
            out += ' v%s = %s;' % (x, '_r.v[%d]' % i if i < nr[f] else '0')
        return out + ' }\n'
    raise Exception('stmt %r' % (s,))

o = []
o.append('''#include <stdint.h>
#include <setjmp.h>
#include <pthread.h>
#include <sys/mman.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;   /* the arrays' words */
typedef unsigned long uw;         /* lengths and fuel: the same width, another type (TBAA: array stores do not alias them) */
#define NB %d
#define NW %d
static u64 *B64[NW]; static uw L64[NW]; static uint8_t *B8[NB]; static uw L8[NB];
static u64 *G; /* %d globals, in the table */
static uw fuel; static jmp_buf jb;
#define ERR() longjmp(jb, 2)
''' % (nb, NW, max(ng, 1)))
if FUEL:
    o.append('#define FUEL() do { if (__builtin_expect(fuel == 0, 0)) longjmp(jb, 1); fuel--; } while (0)\n')
else:
    o.append('#define FUEL() do {} while (0)\n')
if BOUNDS:
    o.append('''#define CHK(c) do { if (__builtin_expect(!(c), 0)) ERR(); } while (0)
''')
else:
    o.append('#define CHK(c) do {} while (0)\n')
o.append('''static inline __attribute__((always_inline)) u64 LD64(u64 a, u64 i) { CHK(i < L64[a]); return B64[a][i]; }
static inline __attribute__((always_inline)) u64 LD8(int a, u64 i) { CHK(i < L8[a]); return B8[a][i]; }
static inline __attribute__((always_inline)) void ST64(u64 a, u64 i, u64 e) { CHK(i < L64[a]); B64[a][i] = e; }
static inline __attribute__((always_inline)) void ST8(int a, u64 i, u64 e) { CHK(i < L8[a]); B8[a][i] = (uint8_t)e; }
static inline __attribute__((always_inline)) u64 LD8X8(const uint8_t *b, u64 n, u64 i) { CHK(i + 8 <= n && i + 8 > i); u64 r; __builtin_memcpy(&r, b + i, 8); return r; }
static inline __attribute__((always_inline)) u64 LDC(const uint8_t *d, u64 n, u64 i) { CHK(i < n); return d[i]; }
''')
for i, d in enumerate(data):
    o.append('static const uint8_t D%d[%d] = {%s};\n' % (i, max(1, len(d)), ','.join(str(b) for b in d) or '0'))
allf = [(n, np_, nl, b) for n, np_, nl, b in fns] + [(n, np_, np_, ('stub', code)) for n, np_, code in stubs]
for n, np_, nl, b in allf:
    o.append('typedef struct { u64 v[%d]; } R_%s;\n' % (nr[n], cname[n]))
def size(x):
    return 1 + sum(size(y) for y in x) if isinstance(x, list) else 1
def calls(x):
    return isinstance(x, list) and (x[:1] == ['call'] or any(calls(y) for y in x))
inl = 0
def attr(n, b):
    global inl
    if INL is not None and not isinstance(b, tuple) and not calls(b) and size(b) <= INL:
        inl += 1
        return 'static inline __attribute__((always_inline)) '
    return 'static '
for n, np_, nl, b in allf:
    o.append('static R_%s %s(%s);\n' % (cname[n], cname[n], ', '.join('u64' for _ in range(np_)) or 'void'))
for n, np_, nl, b in allf:
    vol = VOL == 'all' or (VOL == 'nonleaf' and not isinstance(b, tuple) and calls(b))
    ps = ', '.join(('u64 p%d' if vol else 'u64 v%d') % i for i in range(np_)) or 'void'
    o.append('%sR_%s %s(%s) {\n' % (attr(n, b), cname[n], cname[n], ps))
    if isinstance(b, tuple):
        o.append('  ERR();\n}\n')
        continue
    if vol and np_:
        o.append('  volatile u64 %s;\n' % ', '.join('v%d = p%d' % (i, i) for i in range(np_)))
    if nl > np_:
        o.append('  %su64 %s;\n' % ('volatile ' if vol else '', ', '.join('v%d = 0' % i for i in range(np_, nl))))
    body = S(b, n, 1, False)
    o.append(body)
    o.append('  goto fall;\nfall:;\n  { R_%s _r = {{0}}; return _r; }\n}\n' % cname[n])
o.append('''
typedef struct { u64 rax, rdx; } ca_res;
/* nw %d nb %d diag %d ng %d: from the stub's asm */
extern const u64 ca_nw, ca_nb, ca_ng, ca_rom_len;
static u64 pi_(u64 a, u64 nw) { long K = (long)nw - 256; if (K < 0) K = 0; if (K > 256) K = 256;
  if (a < (u64)K) return 2 * a; if (a < 256) return a + K; if (a < 256 + (u64)K) return 2 * (a - 256) + 1; return a; }
static u64 res0, status;
static void *runner(void *x) {
  int k = setjmp(jb);
  if (k == 0) { FUEL(); R_%s r = %s(); res0 = r.v[0]; status = 0; }
  else status = k;
  return 0;
}
ca_res ca_enter(u64 *T, u64 f) {
  fuel = f;
  u64 nb = ca_nb, nw = ca_nw, W = 16 + 16 * nb;
  if (nb < NB || nw < NW) { abort(); }
  for (int a = 0; a < NB; a++) { B8[a] = (uint8_t *)T[2 + 2 * a]; L8[a] = T[3 + 2 * a]; }
  for (int a = 0; a < NW; a++) { B64[a] = (u64 *)T[(W + 8 * pi_(a, nw)) / 8]; L64[a] = T[(W + 8 * nw + 8 * pi_(a, nw)) / 8]; }
  { u64 arr_end = W + 16 * nw; u64 rom_end = arr_end + 8 * ((ca_rom_len + 7) / 8); G = &T[(rom_end + 8 * 3) / 8]; }
  { const char *am = getenv("CA_ARRMAP"); FILE *fm = am ? fopen(am, "w") : 0;  /* array map for ibs tools */
    if (fm) { for (int a = 0; a < NW; a++) fprintf(fm, "w %%d %%llx %%llu\\n", a, (unsigned long long)B64[a], (unsigned long long)L64[a]);
              for (int a = 0; a < NB; a++) fprintf(fm, "b %%d %%llx %%llu\\n", a, (unsigned long long)B8[a], (unsigned long long)L8[a]);
              fclose(fm); } }
  size_t sz = 64ull << 30;
  void *st = mmap(0, sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstack(&at, st, sz);
  pthread_t th; pthread_create(&th, &at, runner, 0); pthread_join(th, 0);
  ca_res r = { res0, status };
  return r;
}
''' % (NW, nb, diag, ng, cname['check'], cname['check']))
open(dst, 'w').write(''.join(o))
print(f'{inl} leaves inlined, {len(allf)} functions, nb {nb} nw {NW} ng {ng}')
