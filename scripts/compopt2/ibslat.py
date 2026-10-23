#!/usr/bin/env python3
"""Per-instruction IBS op latencies (lane compopt2): from a raw IBS recording
(`perf record -R -e ibs_op/cnt_ctl=1/ -c P -- BIN …`), the IbsOpData counters of every sampled user
op: TagToRet (dispatch to retire) and CompToRet (completion to retire); TagToRet - CompToRet is the
time the op waited for its operands and executed. Summed per function and per instruction category
(asmprof's categories), this shows where the window stalls, not just where instructions are.

  ibslat.py PERF.data BIN [--s BIN.s] [--top N] [--fn F]
(--s: the assembler source, for asmprof's categories: the k-th instruction of a function in the
binary is the k-th instruction line of that function in the source.)
"""
import collections, re, subprocess, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
import asmprof  # noqa: E402

data, binp = sys.argv[1], sys.argv[2]
top = int(sys.argv[sys.argv.index('--top') + 1]) if '--top' in sys.argv else 30
srcp = sys.argv[sys.argv.index('--s') + 1] if '--s' in sys.argv else None
src = collections.defaultdict(list)
if srcp:
    cur = None
    for ln in open(srcp):
        t = ln.strip()
        if not t:
            continue
        if t.endswith(':'):
            if not t.startswith('.L'):
                cur = t[:-1]
            continue
        if t.startswith('.'):
            continue
        if cur:
            src[cur].append(t)
fnsel = sys.argv[sys.argv.index('--fn') + 1] if '--fn' in sys.argv else None
# instructions of the binary: offset -> (function, text)
dis = subprocess.run(['objdump', '-d', '--no-show-raw-insn', '-M', 'att', binp], capture_output=True, text=True).stdout
ins, fn, k = {}, None, 0
for ln in dis.splitlines():
    m = re.match(r'^([0-9a-f]+) <(.*)>:$', ln)
    if m:
        fn = m.group(2); k = 0; continue
    m = re.match(r'^\s+([0-9a-f]+):\s+(.*)$', ln)
    if m and fn:
        t = re.sub(r'\s+', ' ', m.group(2).split('#')[0].strip())
        if fn in src and k < len(src[fn]):
            t = src[fn][k]
        ins[int(m.group(1), 16)] = (fn, t)
        k += 1
out = subprocess.run(['perf', 'report', '-D', '-i', data], capture_output=True, text=True).stdout
base = None
lines = out.splitlines()
samples = []
i = 0
while i < len(lines):
    ln = lines[i]
    if base is None and 'PERF_RECORD_MMAP2' in ln and binp.split('/')[-1] in ln and 'r-xp' in ln:
        m = re.search(r'\[0x([0-9a-f]+)\(0x[0-9a-f]+\) @ 0x([0-9a-f]+)', ln)
        base = int(m.group(1), 16) - int(m.group(2), 16)
    if '. ... raw event' in ln:
        hexs = []
        j = i + 1
        while j < len(lines) and re.match(r'^\.\s+[0-9a-f]{4}:', lines[j]):
            hexs += lines[j].split(':', 1)[1].strip().split('  ')[0].split()
            j += 1
        b = bytes(int(h, 16) for h in hexs)
        samples.append(b)
        i = j; continue
    i += 1
agg_fn = collections.Counter(); agg_cat = collections.Counter(); agg_ins = collections.Counter()
cnt_fn = collections.Counter(); n_user = 0; tot = 0
meta = {"ca_nb": 2, "ca_nw": 215, "ca_ng": 0, "ca_rom_len": 0, "args": 10 ** 9}
for b in samples:
    if len(b) < 0x70:
        continue
    raw = b[0x28:]   # u32 size, u32 caps, then IbsOpCtl, IbsOpRip, IbsOpData, ...
    q = [int.from_bytes(raw[8 + 8 * k: 16 + 8 * k], 'little') for k in range(8)]
    rip, d = q[1], q[2]
    if rip >= 1 << 47 or base is None:
        continue
    off = rip - base
    if off not in ins:
        continue
    f, t = ins[off]
    comp2ret, tag2ret = d & 0xffff, (d >> 16) & 0xffff
    w = max(tag2ret - comp2ret, 0)
    n_user += 1; tot += w
    agg_fn[f] += w; cnt_fn[f] += 1
    agg_ins[(f, off, t)] += w
    agg_cat[asmprof.category(t.replace('q ', 'q ').replace('movabs', 'movabsq'), meta)] += w
print(f"{n_user} user ops sampled; summed dispatch-to-complete latency {tot:,} cycles")
print("\n## by category (share of summed latency)")
for c, w in agg_cat.most_common(25):
    print(f"{100 * w / tot:6.2f}%  {c}")
print("\n## by function")
for f, w in agg_fn.most_common(top):
    print(f"{100 * w / tot:6.2f}%  ops {100 * cnt_fn[f] / n_user:5.2f}%  {f}")
print("\n## by instruction")
for (f, off, t), w in agg_ins.most_common(top):
    if fnsel is None or f == fnsel:
        print(f"{100 * w / tot:6.2f}%  {f:28s} {off:8x}  {t}")
