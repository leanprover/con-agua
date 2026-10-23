#!/usr/bin/env python3
"""Lane compopt: L-source prototypes applied to a program file (`checker.prog`, s-expressions), so
they can be measured without rebuilding the L modules and their proofs.

  derorder  `der_b`'s tag tests in order of frequency on Init (4 0 3 5 1 6 2 9 7)
  mklazy    `mk_app`/`mk_lam`/`mk_forall` call `der_b` only after `intern_*` made a new node
            (as the twin's `internNodeE` computes derived data only on a miss)
  inlineaslot  `ASLOT` slots of 4 words (value, f, a) so `app_find` compares the key in the slot
            instead of reading the `AREC` record (give array 5 four times the words)
  flush     the 43 memo puts flush the table (stamp + 1, count 0) at half load instead of
            aborting at 3/4 (a memo is a cache: a miss is always allowed)

usage: progedit.py IN OUT [derorder] [mklazy] [inlineaslot] [flush]"""
import sys, re

def tok(s):
    return re.findall(r'\(|\)|[^\s()]+', s)

def parse(ts, i=0):
    if ts[i] == '(':
        out = []; i += 1
        while ts[i] != ')':
            x, i = parse(ts, i); out.append(x)
        return out, i + 1
    return ts[i], i + 1

def show(x):
    return '(' + ' '.join(show(y) for y in x) + ')' if isinstance(x, list) else x

def flat(x):
    out = []
    while isinstance(x, list) and x and x[0] == 'seq':
        out.append(x[1]); x = x[2]
    out.append(x)
    return out

def nest(xs):
    r = xs[-1]
    for x in reversed(xs[:-1]):
        r = ['seq', x, r]
    return r

ORDER = ['4', '0', '3', '5', '1', '6', '2', '9', '7']

def derorder(body):
    xs = flat(body)
    def tag(x):
        if isinstance(x, list) and x[0] == 'if' and x[1][:3] == ['cmp', 'eq', ['v', '1']] and x[1][3][0] == 'c':
            return x[1][3][1]
    arms = [x for x in xs if tag(x) is not None]
    first = xs.index(arms[0])
    rest = [x for x in xs[first:] if tag(x) is None]
    arms.sort(key=lambda x: ORDER.index(tag(x)))
    return nest(xs[:first] + arms + rest)

def mklazy(body):
    xs = flat(body)
    ders = [x for x in xs if isinstance(x, list) and x[0] == 'call' and x[2] == 'der_b']
    i_int = next(i for i, x in enumerate(xs) if isinstance(x, list) and x[0] == 'call' and x[2].startswith('intern_'))
    i_if = i_int + 1
    assert xs[i_if][0] == 'if' and xs[i_if][3] == 'skip'
    # statements between the der_b calls and the count snapshot that only touch der_b's results
    mid = [x for x in xs[:i_int] if x not in ders and isinstance(x, list) and x[0] == 'set' and x[1] == '3']
    pre = [x for x in xs[:i_int] if x not in ders and x not in mid]
    then = nest(ders + mid + [xs[i_if][2]])
    return nest(pre + [xs[i_int], ['if', xs[i_if][1], then, 'skip']] + xs[i_if + 1:])

FLUSH = re.compile(r'\(set 6 \(b add \(l64 1 \(c (\d+)\)\) \(c 1\)\)\) \(seq \(if \(cmp ult \(b mul \(b shr \(b shr \(n64 (\d+)\) \(c 2\)\) \(c 2\)\) \(c 3\)\) \(b add \(v 5\) \(c 1\)\)\) abort skip\)')

def flush(text):
    def rep(m):
        cs, a = m.group(1), m.group(2)
        return (f'(set 6 (b add (l64 1 (c {cs})) (c 1))) (seq (if (cmp ult (b mul (b shr (b shr (n64 {a}) (c 2)) (c 2)) (c 2)) (b add (v 5) (c 1))) '
                f'(seq (s64 1 (c {cs}) (v 6)) (seq (set 6 (b add (v 6) (c 1))) (set 5 (c 0)))) skip)')
    return FLUSH.sub(rep, text)

INLINE = [
    ('app_find', '(set 4 (b shr (n64 5) (c 1)))', '(set 4 (b shr (n64 5) (c 3)))'),
    ('app_find', '(set 7 (l64 5 (b add (b mul (v 5) (c 2)) (v 0))))',
     '(set 7 (l64 5 (b mul (b add (b mul (v 5) (c 2)) (v 0)) (c 4))))'),
    ('app_find', '(if (and (cmp eq (l64 4 (b add (b mul (b sub (v 7) (c 1)) (c 4)) (b mul (v 0) (c 2)))) (v 1)) '
     '(cmp eq (l64 4 (b add (b add (b mul (b sub (v 7) (c 1)) (c 4)) (b mul (v 0) (c 2))) (c 1))) (v 2)))',
     '(if (and (cmp eq (l64 5 (b add (b mul (b add (b mul (v 5) (c 2)) (v 0)) (c 4)) (c 1))) (v 1)) '
     '(cmp eq (l64 5 (b add (b mul (b add (b mul (v 5) (c 2)) (v 0)) (c 4)) (c 2))) (v 2)))'),
    ('app_push', '(b mul (b shr (b shr (n64 5) (c 1)) (c 2)) (c 3))', '(b mul (b shr (b shr (n64 5) (c 3)) (c 2)) (c 3))'),
    ('app_push', '(s64 5 (b add (b mul (v 3) (c 2)) (v 0)) (b add (b add (b mul (l64 1 (c 62)) (v 0)) (v 4)) (c 1)))',
     '(seq (s64 5 (b mul (b add (b mul (v 3) (c 2)) (v 0)) (c 4)) (b add (b add (b mul (l64 1 (c 62)) (v 0)) (v 4)) (c 1))) '
     '(seq (s64 5 (b add (b mul (b add (b mul (v 3) (c 2)) (v 0)) (c 4)) (c 1)) (v 1)) '
     '(s64 5 (b add (b mul (b add (b mul (v 3) (c 2)) (v 0)) (c 4)) (c 2)) (v 2))))'),
]

def inlineaslot(line):
    for fn, old, new in INLINE:
        if line.startswith(f'fn {fn} '):
            assert old in line, (fn, old)
            line = line.replace(old, new)
    return line

def main():
    src, dst, *opts = sys.argv[1:]
    out = []
    for line in open(src):
        w = line.split(' ', 4)
        if w[0] == 'fn':
            name = w[1]
            body = None
            if 'derorder' in opts and name == 'der_b':
                body = derorder(parse(tok(w[4]))[0])
            if 'mklazy' in opts and name in ('mk_app', 'mk_lam', 'mk_forall'):
                body = mklazy(parse(tok(w[4]))[0])
            if body is not None:
                line = ' '.join(w[:4]) + ' ' + show(body) + '\n'
        if 'inlineaslot' in opts:
            line = inlineaslot(line)
        out.append(line)
    text = ''.join(out)
    if 'flush' in opts:
        text = flush(text)
    open(dst, 'w').write(text)

main()
