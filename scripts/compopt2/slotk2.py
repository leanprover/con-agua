#!/usr/bin/env python3
"""Prototypes K and K+S for the intern slot tables (lane compopt2; program-file edit of
app/lam/forall `*_find` and `*_push`). This file is meant as the spec of the layout and the
find/push/grow code, for a generic cons-table library.

Layout of slot array `S` (len words):
  word len-1      n - 8          (n = slot count, a power of two >= 8; all zero = n 8)
  word len-2      b              (the current table's first word; 0 initially)
  K   (tiers interleaved): slot i, tier t: value at b + 4i + 2t, key at b + 4i + 2t + 1
  K+S (tiers apart, --sep): tier t's table lives in its half h_t = t * (len/2):
                   slot i, tier t: value at h_t + b + 2i, key at h_t + b + 2i + 1
  value: 0 = free; for tier 1, `epoch base + index + 1` (CTL[62] * t is the epoch base): a value
         <= the base is stale = free (unchanged from master).
  key:   f | a << 32 (both handles < 2^32; `mk_*` abort otherwise).
Find(t, f, a, h): home = mulhi(mix(h), n); linear probing; a free slot is a miss (returns its
  index for the push); a slot whose key equals f | a << 32 is a hit (index = value - base - 1).
  The record is never read.
Push(t, f, a, i): append the record (unchanged), write value and key into slot i; if the tier's
  count reaches n/2: grow.
Grow: n' = 2n; the new table goes into a FRESH region right above the old one (b' = b + W n,
  W = 4 or 2 words a slot), which is still all zero, so nothing is zeroed and nothing is copied
  aside. Walk the old slots in order, both tiers; every live one (value > base) is re-inserted at
  mulhi(mix(FNV(f, a)), n') with linear probing. Because the home is monotone in the hash, the old
  slot order is (up to wrap-around runs) the new home order: the walk streams. Regions only move up
  (the old regions stay dirty and are never reused), so the array needs ~2x the final table
  (W n' + b' <= len - 2, resp. <= len/2 - 2 per half; else abort as a capacity error).

  slotk2.py IN.prog OUT.prog [--sep]"""
import re, sys

FNV0, FNVP, G = '14695981039346656037', '1099511628211', '11400714819323198485'
TABLES = [('app', 5), ('lam', 28), ('forall', 30)]
SEP = '--sep' in sys.argv
PT = '--pertier' in sys.argv   # (with --sep) each tier's table has its own size and base (words at the end of its half)
PP = '--pingpong' in sys.argv   # alternate between two fixed regions (zeroing the target) instead of moving up
W = 2 if SEP else 4

def c(k): return f'(c {k})'
def v(i): return f'(v {i})'
def b(op, x, y): return f'(b {op} {x} {y})'
def w(op, x, y): return f'(w {op} {x} {y})'
def l64(a, i): return f'(l64 {a} {i})'
def s64(a, i, e): return f'(s64 {a} {i} {e})'
def cmp(op, x, y): return f'(cmp {op} {x} {y})'
def st(x, e): return f'(set {x} {e})'
def ite(cd, s, t='skip'): return f'(if {cd} {s} {t})'
def wh(cd, s): return f'(while {cd} {s})'
def ret(*es): return '(ret ' + ' '.join(es) + ')'
def seq(*ss):
    ss = [s for s in ss if s != 'skip']
    r = ss[-1]
    for s in reversed(ss[:-1]):
        r = f'(seq {s} {r})'
    return r
def nxt(x, n): return b('mul', b('add', x, c(1)), w('ult', b('add', x, c(1)), n))
def home(h, n): return b('mulhi', b('xor', b('mul', h, c(G)), b('shr', b('mul', h, c(G)), c(32))), n)
def fnv(f, a): return b('mul', b('xor', b('mul', b('xor', c(FNV0), f), c(FNVP)), a), c(FNVP))
def lenm(S, k): return b('sub', f'(n64 {S})', c(k))
def half(S): return b('shr', f'(n64 {S})', c(1))
def nword(S, t, k):
    """The word holding n - 8 (k = 1) or the base (k = 2): of the shared table, or (--pertier) of
    tier t's table, at the end of tier t's half."""
    if PT:
        return b('sub', b('mul', b('add', t, c(1)), half(S)), c(k))
    return lenm(S, k)

def slot(S, base, i, t, k):
    """Word of slot i, tier t (k = 0 value, 1 key) of the table at `base`."""
    if SEP:
        return b('add', b('add', b('add', b('mul', t, half(S)), base), b('mul', i, c(2))), c(k))
    return b('add', b('add', base, b('add', b('mul', i, c(4)), b('mul', t, c(2)))), c(k))

def tbase(S, base, t):
    """First word of tier t's slot 0 in the table at `base` (slot i then at + W i)."""
    if SEP:
        return b('add', b('mul', t, half(S)), base)
    return b('add', base, b('mul', t, c(2)))

def find(S):
    # params 0 t, 1 f, 2 a, 3 h; locals 4 n, 5 home, 6 probes, 7 value, 8 epoch base, 9 key,
    # 10 tier base, 11 word of the probed slot
    return seq(st(4, b('add', l64(S, nword(S, v(0), 1)), c(8))), st(10, tbase(S, l64(S, nword(S, v(0), 2)), v(0))),
               st(8, b('mul', l64(1, c(62)), v(0))),
               st(9, b('or', v(1), b('shl', v(2), c(32)))), st(5, home(v(3), v(4))),
               wh(cmp('ult', v(6), v(4)), seq(
                   st(11, b('add', v(10), b('mul', v(5), c(W)))),
                   st(7, l64(S, v(11))),
                   ite(cmp('ule', v(7), v(8)), ret(c(0), c(0), v(5), v(6))),
                   ite(cmp('eq', l64(S, b('add', v(11), c(1))), v(9)), ret(c(1), b('sub', b('sub', v(7), v(8)), c(1)), v(5), v(6))),
                   st(5, nxt(v(5), v(4))), st(6, b('add', v(6), c(1))))),
               'abort')

def grow(S):
    # locals: 6 n', 7 n, 8 tier, 9 old word, 10 b then old end, 11 b', 12 value, 13 key, 14 home,
    # 5 epoch base of the tier, 3 new tier base (the push's slot argument is dead here)
    lim = b('sub', half(S), c(2)) if SEP else lenm(S, 2)
    def tier(t):
        return seq(
            st(5, b('mul', l64(1, c(62)), c(t))),
            st(3, tbase(S, v(11), c(t))),
            st(9, tbase(S, v(10), c(t))), st(2, b('add', v(9), b('mul', v(7), c(W)))),
            wh(cmp('ult', v(9), v(2)), seq(
                st(12, l64(S, v(9))),
                ite(cmp('ult', v(5), v(12)), seq(
                    st(13, l64(S, b('add', v(9), c(1)))),
                    st(14, home(fnv(b('and', v(13), c(4294967295)), b('shr', v(13), c(32))), v(6))),
                    wh(cmp('ne', l64(S, b('add', v(3), b('mul', v(14), c(W)))), c(0)), st(14, nxt(v(14), v(6)))),
                    s64(S, b('add', v(3), b('mul', v(14), c(W))), v(12)),
                    s64(S, b('add', b('add', v(3), b('mul', v(14), c(W))), c(1)), v(13)))),
                st(9, b('add', v(9), c(W))))))
    if PT:
        # only the pushing tier (param 0) grows; its region is [t half, (t+1) half - 2)
        t = v(0)
        if PP:
            # two regions per tier: [0, Q) and [Q, 2Q) of the tier's half; the target is zeroed first
            q = b('shl', b('shr', b('sub', half(S), c(2)), c(4)), c(3))
            place = seq(
                st(10, l64(S, nword(S, t, 2))), st(11, q), ite(cmp('ne', v(10), c(0)), st(11, c(0))),
                ite(cmp('ult', q, b('mul', v(6), c(W))), 'abort'),
                st(9, tbase(S, v(11), t)), st(2, b('add', v(9), b('mul', v(6), c(W)))),
                wh(cmp('ult', v(9), v(2)), seq(*[s64(S, b('add', v(9), c(k)), c(0)) for k in range(8)],
                                                st(9, b('add', v(9), c(8))))))
        else:
            place = seq(
                st(10, l64(S, nword(S, t, 2))), st(11, b('add', v(10), b('mul', v(7), c(W)))),
                ite(cmp('ult', b('sub', half(S), c(2)), b('add', v(11), b('mul', v(6), c(W)))), 'abort'))
        return seq(
            st(7, b('add', l64(S, nword(S, t, 1)), c(8))), st(6, b('mul', v(7), c(2))),
            place,
            s64(S, nword(S, t, 1), b('sub', v(6), c(8))), s64(S, nword(S, t, 2), v(11)),
            st(5, b('mul', l64(1, c(62)), t)),
            st(3, tbase(S, v(11), t)),
            st(9, tbase(S, v(10), t)), st(2, b('add', v(9), b('mul', v(7), c(W)))),
            wh(cmp('ult', v(9), v(2)), seq(
                st(12, l64(S, v(9))),
                ite(cmp('ult', v(5), v(12)), seq(
                    st(13, l64(S, b('add', v(9), c(1)))),
                    st(14, home(fnv(b('and', v(13), c(4294967295)), b('shr', v(13), c(32))), v(6))),
                    wh(cmp('ne', l64(S, b('add', v(3), b('mul', v(14), c(W)))), c(0)), st(14, nxt(v(14), v(6)))),
                    s64(S, b('add', v(3), b('mul', v(14), c(W))), v(12)),
                    s64(S, b('add', b('add', v(3), b('mul', v(14), c(W))), c(1)), v(13)))),
                st(9, b('add', v(9), c(W))))))
    if PP:
        q = b('shl', b('shr', lim, c(4)), c(3))      # the second region's start: half the room, 8-aligned
        def zero(t):
            return seq(st(9, tbase(S, v(11), c(t)) if SEP else v(11)),
                       st(2, b('add', v(9), b('mul', v(6), c(W)))),
                       wh(cmp('ult', v(9), v(2)), seq(*[s64(S, b('add', v(9), c(k)), c(0)) for k in range(8)],
                                                       st(9, b('add', v(9), c(8))))))
        return seq(
            st(7, b('add', l64(S, lenm(S, 1)), c(8))), st(6, b('mul', v(7), c(2))),
            st(10, l64(S, lenm(S, 2))), st(11, q), ite(cmp('ne', v(10), c(0)), st(11, c(0))),
            ite(cmp('ult', q, b('mul', v(6), c(W))), 'abort'),
            zero(0), *([zero(1)] if SEP else []),
            s64(S, lenm(S, 1), b('sub', v(6), c(8))), s64(S, lenm(S, 2), v(11)),
            tier(0), tier(1))
    return seq(
        st(7, b('add', l64(S, lenm(S, 1)), c(8))), st(6, b('mul', v(7), c(2))),
        st(10, l64(S, lenm(S, 2))), st(11, b('add', v(10), b('mul', v(7), c(W)))),
        ite(cmp('ult', lim, b('add', v(11), b('mul', v(6), c(W)))), 'abort'),
        s64(S, lenm(S, 1), b('sub', v(6), c(8))), s64(S, lenm(S, 2), v(11)),
        tier(0), tier(1))

def tok(s): return re.findall(r'\(|\)|[^\s()]+', s)
def parse(ts, i=0):
    if ts[i] == '(':
        out = []; i += 1
        while ts[i] != ')':
            x, i = parse(ts, i); out.append(x)
        return out, i + 1
    return ts[i], i + 1
def show(x): return '(' + ' '.join(show(y) for y in x) + ')' if isinstance(x, list) else x
def flat(x):
    out = []
    while isinstance(x, list) and x and x[0] == 'seq': out.append(x[1]); x = x[2]
    out.append(x); return out

src, dst = [x for x in sys.argv[1:] if not x.startswith('--')][:2]
lines = open(src).read().split('\n')
for k, ln in enumerate(lines):
    for name, S in TABLES:
        if ln.startswith(f'fn {name}_find '):
            lines[k] = f'fn {name}_find 4 12 ' + find(S)
        if ln.startswith(f'fn {name}_push '):
            ws = ln.split(' ')
            body, _ = parse(tok(ln[len(f'fn {name}_push ') + len(ws[2]) + len(ws[3]) + 2:]))
            xs = flat(body)
            gi = next(i for i, x in enumerate(xs) if isinstance(x, list) and x[0] == 'if' and
                      show(x[1]).startswith('(cmp ult (b add (v 7) (c 8))'))
            head, done = [], False
            for x in xs[:gi]:
                s = show(x)
                old = f'(s64 {S} (b add (b mul (v 3) (c 2)) (v 0)) '
                if s.startswith(old):   # the slot write: value and key at slot v3 of the current table
                    s = seq(st(10, l64(S, nword(S, v(0), 2))), s64(S, slot(S, v(10), v(3), v(0), 0), s[len(old):-1]),
                            s64(S, slot(S, v(10), v(3), v(0), 1), b('or', v(1), b('shl', v(2), c(32)))))
                    done = True
                if PT:
                    s = s.replace(f'(l64 {S} (b sub (n64 {S}) (c 1)))', l64(S, nword(S, v(0), 1)))
                head.append(s)
            assert done, name
            lines[k] = f'fn {name}_push 4 15 ' + seq(*head, ite(show(xs[gi][1]), grow(S)), ret(v(4)))
open(dst, 'w').write('\n'.join(lines))
print('ok', 'K+S' if SEP else 'K', 'per tier' if PT else '', 'ping-pong' if PP else 'moving up')
