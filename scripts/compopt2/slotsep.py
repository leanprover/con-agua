#!/usr/bin/env python3
"""Prototype S alone (lane compopt2, a program-file edit): the app/lam/forall slot tables keep the
two tiers apart (tier t's slot i at word t * (len/2) + i) instead of interleaved (2i + t); records
and everything else unchanged. The zero loop of the growth also zeroes tier 1's half; the size cap
becomes len/4 slots.   slotsep.py IN.prog OUT.prog"""
import re, sys
src, dst = sys.argv[1:3]
out = []
for ln in open(src).read().split('\n'):
    for S in (5, 28, 30):
        names = {5: 'app', 28: 'lam', 30: 'forall'}[S]
        if ln.startswith(f'fn {names}_find ') or ln.startswith(f'fn {names}_push '):
            ln = re.sub(rf'\((l64|s64) {S} \(b add \(b mul \(v (\d+)\) \(c 2\)\) \(v (\d+)\)\)',
                        rf'(\1 {S} (b add (b mul (v \3) (b shr (n64 {S}) (c 1))) (v \2))', ln)
            ln = re.sub(rf'\(s64 {S} \(b add \(v 7\) \(c (\d)\)\) \(c 0\)\)',
                        rf'(seq (s64 {S} (b add (v 7) (c \1)) (c 0)) (s64 {S} (b add (b add (b shr (n64 {S}) (c 1)) (v 7)) (c \1)) (c 0)))', ln)
            ln = ln.replace(f'(set 10 (b shl (b shr (b sub (n64 {S}) (c 1)) (c 4)) (c 3)))',
                            f'(set 10 (b shl (b shr (b sub (n64 {S}) (c 1)) (c 5)) (c 3)))')
    out.append(ln)
open(dst, 'w').write('\n'.join(out))
