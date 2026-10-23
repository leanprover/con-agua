#!/usr/bin/env python3
"""Which instructions miss L1d (lane compopt2): IBS load samples by data source, per asmprof
category of the instruction (frame load, array element load, ...) and per function.

  ibsmiss.py PERF.data BIN BIN.s   (PERF.data: perf record -e ibs_op/cnt_ctl=1/ -d -- BIN ...)
"""
import collections, re, subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import asmprof  # noqa: E402

data, binp, srcp = sys.argv[1:4]
src = collections.defaultdict(list); cur = None
for ln in open(srcp):
    t = ln.strip()
    if not t: continue
    if t.endswith(':'):
        if not t.startswith('.L'): cur = t[:-1]
        continue
    if t.startswith('.'): continue
    if cur: src[cur].append(t)
dis = subprocess.run(['objdump', '-d', '--no-show-raw-insn', binp], capture_output=True, text=True).stdout
ins, fn, k = {}, None, 0
for ln in dis.splitlines():
    m = re.match(r'^([0-9a-f]+) <(.*)>:$', ln)
    if m: fn = m.group(2); k = 0; continue
    m = re.match(r'^\s+([0-9a-f]+):\s+(.*)$', ln)
    if m and fn:
        ins[int(m.group(1), 16)] = (fn, src[fn][k] if k < len(src[fn]) else m.group(2)); k += 1
syms = {}
for off, (f, t) in ins.items():
    syms.setdefault(f, off)
out = subprocess.run(['perf', 'script', '-i', data, '-F', 'ip,sym,symoff,data_src'], capture_output=True, text=True).stdout
meta = {"ca_nb": 2, "ca_nw": 215, "ca_ng": 0, "ca_rom_len": 0, "args": 10 ** 9}
cat = collections.Counter(); fns = collections.Counter(); tot = collections.Counter()
for ln in out.splitlines():
    if '|OP LOAD|' not in ln: continue
    m = re.search(r'\|LVL ([^|]*)\|.*?\s([0-9a-f]+)\s+(\S+)\+0x([0-9a-f]+)\s*$', ln)
    if not m: continue
    lvl = m.group(1)
    lv = 'L1' if lvl.startswith('L1') else 'L2' if lvl.startswith('L2') else 'RAM' if 'RAM' in lvl else 'L3+'
    f, so = m.group(3), int(m.group(4), 16)
    if f not in syms: continue
    t = ins.get(syms[f] + so, (f, '?'))[1]
    c = asmprof.category(t, meta)
    tot[lv] += 1
    if lv != 'L1':
        cat[(c, lv)] += 1; fns[(f, lv)] += 1
print('loads by source:', dict(tot))
print('\nL1 misses by category:')
for (c, lv), n in cat.most_common(20): print(f'{n:7d} {lv:4s} {c}')
print('\nL1 misses by function:')
for (f, lv), n in fns.most_common(20): print(f'{n:7d} {lv:4s} {f}')
