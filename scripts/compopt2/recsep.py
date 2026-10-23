#!/usr/bin/env python3
"""Prototype R (lane compopt2, a program-file edit): the app/lam/forall RECORD arrays keep the two
tiers apart: record x of tier t, field k (0, 1) at word t * (len/2) + 2x + k instead of 4x + 2t + k.
Every access `R[x*4 + t*2 (+1)]` is rewritten; the pushes compute the record base the same way.

  recsep.py IN.prog OUT.prog"""
import re, sys
RECS = {'4': 'app', '27': 'lam', '29': 'forall'}

def tok(s): return re.findall(r'\(|\)|[^\s()]+', s)
def parse(ts, i=0):
    if ts[i] == '(':
        out = []; i += 1
        while ts[i] != ')':
            x, i = parse(ts, i); out.append(x)
        return out, i + 1
    return ts[i], i + 1
def show(x): return '(' + ' '.join(show(y) for y in x) + ')' if isinstance(x, list) else x

def idx(R, e):
    """x*4 + t*2 -> t*(len/2) + x*2, and the same + 1; None if `e` is not of that form."""
    if isinstance(e, list) and e[:2] == ['b', 'add'] and e[3] == ['c', '1']:
        r = idx(R, e[2])
        return None if r is None else ['b', 'add', r, ['c', '1']]
    if (isinstance(e, list) and e[:2] == ['b', 'add'] and isinstance(e[2], list) and e[2][:2] == ['b', 'mul']
            and e[2][3] == ['c', '4'] and isinstance(e[3], list) and e[3][:2] == ['b', 'mul'] and e[3][3] == ['c', '2']):
        x, t = e[2][2], e[3][2]
        return ['b', 'add', ['b', 'mul', t, ['b', 'shr', ['n64', R], ['c', '1']]], ['b', 'mul', x, ['c', '2']]]
    return None

n = 0
def walk(x, R=None):
    global n
    if not isinstance(x, list):
        return x
    if x and x[0] in ('l64', 's64') and x[1] in RECS:
        r = idx(x[1], x[2])
        if r is not None:
            n += 1
            return [x[0], x[1], walk(r)] + [walk(y) for y in x[3:]]
    if x and x[0] == 'seq' and isinstance(x[1], list) and x[1][0] == 'set' and idx('0', x[1][2]) is not None:
        # `x := i*4 + t*2; ... R[x] ...` (e_view, the pushes): the base of a record of R
        var = ['v', x[1][1]]
        rs = set()
        def uses(y):
            if isinstance(y, list):
                if y and y[0] in ('l64', 's64') and y[1] in RECS and (y[2] == var or y[2] == ['b', 'add', var, ['c', '1']]):
                    rs.add(y[1])
                for z in y: uses(z)
        uses(x[2])
        if len(rs) == 1:
            n += 1
            return ['seq', ['set', x[1][1], idx(rs.pop(), x[1][2])], walk(x[2], R)]
    if x and x[0] == 'set' and R is not None:   # the push's record base
        r = idx(R, x[2])
        if r is not None:
            n += 1
            return ['set', x[1], r]
    return [walk(y, R) for y in x]

src, dst = sys.argv[1:3]
out = []
for ln in open(src).read().split('\n'):
    if ln.startswith('fn '):
        ws = ln.split(' ')
        pre = ' '.join(ws[:4])
        body, _ = parse(tok(ln[len(pre) + 1:]))
        R = next((r for r, nm in RECS.items() if ws[1] == f'{nm}_push'), None)
        ln = pre + ' ' + show(walk(body, R))
    out.append(ln)
open(dst, 'w').write('\n'.join(out))
print(n, 'accesses rewritten')
