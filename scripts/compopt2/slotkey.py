#!/usr/bin/env python3
"""Prototype K (lane compopt2, a program-file edit): the app/lam/forall intern slot tables keep the
key in the slot, and grow by a sequential rehash from the old slots.

Slot `i`, tier `t`: word `4i + 2t` = value (as before: epoch base + index + 1), word `4i + 2t + 1` =
the key `f | a << 32` (both handles are < 2^32: `mk_*` abort otherwise). A find compares the key in
the slot and never reads the record; growth copies the live (tier, value, key) triples out in slot
order to a scratch area past the new table, zeroes the old table, and re-inserts them (home =
mulhi(mix(h), n) is monotone in h, so slot order is home order: the writes stream), then zeroes
the scratch. The table may use at most 1/8 of the array's words as slots (`n <= len / 8`).

  slotkey.py IN.prog OUT.prog"""
import re, sys

FNV0, FNVP, G = '14695981039346656037', '1099511628211', '11400714819323198485'
TABLES = [('app', 5, 4, 4), ('lam', 28, 27, 28), ('forall', 30, 29, 30)]  # name, slots, records, CTL count base

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

def slw(S, i, t, k):
    """The word of slot i, tier t: value (k = 0) or key (k = 1)."""
    if SEP:   # tiers apart: tier t's table at word t * (len / 2), 2 words a slot
        return b('add', b('add', b('mul', t, b('shr', f'(n64 {S})', c(1))), b('mul', i, c(2))), c(k))
    return b('add', b('add', b('mul', i, c(4)), b('mul', t, c(2))), c(k))

def find(S):
    last = l64(S, b('sub', f'(n64 {S})', c(1)))
    sl = lambda i, k: slw(S, i, v(0), k)
    # params t f a h; locals 4 n, 5 home, 6 probes, 7 value, 8 epoch base, 9 key
    return seq(st(4, b('add', last, c(8))), st(8, b('mul', l64(1, c(62)), v(0))),
               st(9, b('or', v(1), b('shl', v(2), c(32)))), st(5, home(v(3), v(4))),
               wh(cmp('ult', v(6), v(4)), seq(
                   st(7, l64(S, sl(v(5), 0))),
                   ite(cmp('ule', v(7), v(8)), ret(c(0), c(0), v(5), v(6))),
                   ite(cmp('eq', l64(S, sl(v(5), 1)), v(9)), ret(c(1), b('sub', b('sub', v(7), v(8)), c(1)), v(5), v(6))),
                   st(5, nxt(v(5), v(4))), st(6, b('add', v(6), c(1))))),
               'abort')

def push(S, R, K, old_head):
    """old_head: the original push's statements before the growth test, with the slot write moved."""
    lenm1 = b('sub', f'(n64 {S})', c(1))
    # growth; locals: 6 new n, 7 old n, 8 tier, 9 count, 10 scratch base, 11 i, 12 value, 13 key, 14 home
    sl = lambda i, t, k: slw(S, i, t, k)
    scr = lambda k: b('add', v(10), b('add', b('mul', v(11), c(3)), c(k)))
    zero8 = seq(*[s64(S, b('add', v(11), c(k)), c(0)) for k in range(8)], st(11, b('add', v(11), c(8))))
    grow = seq(
        st(7, b('add', l64(S, lenm1), c(8))), st(6, b('mul', v(7), c(2))),
        st(10, b('shl', b('shr', lenm1, c(7 if SEP else 6)), c(3))), ite(cmp('ult', v(10), v(6)), st(6, v(10))),
        ite(cmp('ule', v(6), v(7)), 'abort'),
        s64(S, lenm1, b('sub', v(6), c(8))),
        st(10, b('mul', v(6), c(2 if SEP else 4))), st(9, c(0)), st(11, c(0)),
        # pass 1: live slots, in slot order, to the scratch area
        wh(cmp('ult', v(11), v(7)), seq(
            st(8, c(0)),
            wh(cmp('ult', v(8), c(2)), seq(
                st(12, l64(S, sl(v(11), v(8), 0))),
                ite(cmp('ult', b('mul', l64(1, c(62)), v(8)), v(12)), seq(
                    s64(S, b('add', v(10), b('mul', v(9), c(3))), v(8)),
                    s64(S, b('add', v(10), b('add', b('mul', v(9), c(3)), c(1))), v(12)),
                    s64(S, b('add', v(10), b('add', b('mul', v(9), c(3)), c(2))), l64(S, sl(v(11), v(8), 1))),
                    st(9, b('add', v(9), c(1))))),
                st(8, b('add', v(8), c(1))))),
            st(11, b('add', v(11), c(1))))),
        # pass 2: zero the old table
        st(11, c(0)), wh(cmp('ult', v(11), b('mul', v(7), c(2 if SEP else 4))), zero8),
        *([st(11, b('shr', f'(n64 {S})', c(1))),
           wh(cmp('ult', v(11), b('add', b('shr', f'(n64 {S})', c(1)), b('mul', v(7), c(2)))), zero8)] if SEP else []),
        # pass 3: re-insert in slot order, zero the scratch
        st(11, c(0)),
        wh(cmp('ult', v(11), v(9)), seq(
            st(8, l64(S, scr(0))), st(12, l64(S, scr(1))), st(13, l64(S, scr(2))),
            st(14, home(fnv(b('and', v(13), c(4294967295)), b('shr', v(13), c(32))), v(6))),
            wh(cmp('ne', l64(S, sl(v(14), v(8), 0)), c(0)), st(14, nxt(v(14), v(6)))),
            s64(S, sl(v(14), v(8), 0), v(12)), s64(S, sl(v(14), v(8), 1), v(13)),
            s64(S, scr(0), c(0)), s64(S, scr(1), c(0)), s64(S, scr(2), c(0)),
            st(11, b('add', v(11), c(1))))))
    return seq(*old_head,
               ite(cmp('ult', b('add', v(7), c(8)), b('mul', b('add', v(4), c(1)), c(2))), grow),
               ret(v(4)))

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

SEP = '--sep' in sys.argv
src, dst = [x for x in sys.argv[1:] if not x.startswith('--')][:2]
lines = open(src).read().split('\n')
for k, ln in enumerate(lines):
    for name, S, R, K in TABLES:
        if ln.startswith(f'fn {name}_find '):
            lines[k] = f'fn {name}_find 4 10 ' + find(S)
        if ln.startswith(f'fn {name}_push '):
            ws = ln.split(' ')
            body, _ = parse(tok(ln[len(f'fn {name}_push ') + len(ws[2]) + len(ws[3]) + 2:]))
            xs = flat(body)
            gi = next(i for i, x in enumerate(xs) if isinstance(x, list) and x[0] == 'if' and show(x[1]).startswith('(cmp ult (b add (v 7) (c 8))'))
            head = []
            for x in xs[:gi]:
                s = show(x)
                old = f'(s64 {S} (b add (b mul (v 3) (c 2)) (v 0)) '
                if s.startswith(old):
                    s = seq(s64(S, slw(S, v(3), v(0), 0), s[len(old):-1]),
                            s64(S, slw(S, v(3), v(0), 1), b('or', v(1), b('shl', v(2), c(32)))))
                head.append(s)
            assert any(f'(s64 {S} ' in h for h in head), name
            lines[k] = f'fn {name}_push 4 15 ' + push(S, R, K, head)
open(dst, 'w').write('\n'.join(lines))
