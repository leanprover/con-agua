#!/usr/bin/env python3
"""Prototype L1 (lane compopt2, an L-source edit on a program file): `der_lbr` = `der_b` reduced to
its first result (the loose bvar range); the tag arms whose every path returns 0 are dropped. Every
call that binds only `der_b`'s first result calls `der_lbr` instead (`il_go`, `ilg_go`, `il_bvar`,
`inst_go`, ...: 64% of `der_b`'s calls on Init).

  derlbr.py IN.prog OUT.prog"""
import re, sys

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
def nest(xs):
    r = xs[-1]
    for x in reversed(xs[:-1]): r = ['seq', x, r]
    return r
def onlyzero(s):
    if not isinstance(s, list): return s == 'skip'
    if s[0] == 'seq': return onlyzero(s[1]) and onlyzero(s[2])
    if s[0] == 'if': return onlyzero(s[2]) and onlyzero(s[3])
    if s[0] == 'ret': return s[1:] == [['c', '0']]
    return False
def first(x):
    if isinstance(x, list):
        return ['ret', x[1]] if x and x[0] == 'ret' else [first(y) for y in x]
    return x

src, dst = sys.argv[1:3]
out, n = [], 0
for ln in open(src).read().split('\n'):
    if ln.startswith('fn der_b '):
        ws = ln.split(' ')
        body, _ = parse(tok(ln[len('fn der_b ') + len(ws[2]) + len(ws[3]) + 2:]))
        xs = [x for x in flat(first(body)) if not (isinstance(x, list) and x[0] == 'if' and
              x[1][:3] == ['cmp', 'eq', ['v', '1']] and x[3] == 'skip' and onlyzero(x[2]))]
        out += [ln, f'fn der_lbr {ws[2]} {ws[3]} ' + show(nest(xs))]
        continue
    if ln.startswith('fn '):
        new = re.sub(r'\(call \((\d+)\) der_b ', r'(call (\1) der_lbr ', ln)
        n += new != ln; ln = new
    out.append(ln)
open(dst, 'w').write('\n'.join(out))
print(n, 'functions call der_lbr')
