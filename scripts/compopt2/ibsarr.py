#!/usr/bin/env python3
"""Data-cache misses by L array (lane compopt2): IBS load samples with their data address, mapped to
the word/byte array they fall in (array map from an `l2c.py` binary run with CA_ARRMAP), summed per
array and per (array, function): sampled L1 misses by source and their summed latency.

  ibsarr.py [--period P] [--cpus C] [--top N] BIN FIXTURE   (an l2c.py binary; CA_PINS/CA_WORDS from env)
Array names: `abbrev NAME : ArrId := k` declarations under ConAgua/ (several names can share an id)."""
import argparse, bisect, collections, os, re, subprocess, tempfile

ap = argparse.ArgumentParser()
ap.add_argument('bin'); ap.add_argument('fixture')
ap.add_argument('--period', type=int, default=10000); ap.add_argument('--cpus'); ap.add_argument('--top', type=int, default=25)
a = ap.parse_args()
root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
names = collections.defaultdict(list)
for dp, _, fs in os.walk(os.path.join(root, 'ConAgua')):
    for f in fs:
        if f.endswith('.lean'):
            for m in re.finditer(r'^(?:abbrev|def) ([A-Z][A-Z0-9_]*) : ArrId := (\d+)', open(os.path.join(dp, f)).read(), re.M):
                if m.group(1) not in names[int(m.group(2))]:
                    names[int(m.group(2))].append(m.group(1))
tmp = tempfile.mkdtemp(dir=os.environ.get('TMPDIR', '/tmp'))
data, amap = os.path.join(tmp, 'ibs.data'), os.path.join(tmp, 'arrmap')
env = dict(os.environ, CA_ARRMAP=amap)
pre = ['taskset', '-c', a.cpus] if a.cpus else []
subprocess.run(pre + ['perf', 'record', '-q', '-e', 'ibs_op/cnt_ctl=1/', '-d', '-W', '-c', str(a.period), '-o', data, '--',
                      os.path.abspath(a.bin), a.fixture], env=env, check=True, stdout=subprocess.DEVNULL)
regs = []
for ln in open(amap):
    k, i, b, n = ln.split()
    regs.append((int(b, 16), int(b, 16) + int(n) * (8 if k == 'w' else 1), (k, int(i))))
regs.sort(); starts = [r[0] for r in regs]
def arr(addr):
    j = bisect.bisect_right(starts, addr) - 1
    if j >= 0 and addr < regs[j][1]:
        k, i = regs[j][2]
        return f"{'/'.join(names.get(i, ['?'])[:2]) if k == 'w' else 'bytes'}[{i}]"
    return 'stack/other'
out = subprocess.run(['perf', 'script', '-i', data, '-F', 'addr,ip,sym,data_src,weight'], capture_output=True, text=True).stdout
by_arr = collections.defaultdict(collections.Counter); by_af = collections.Counter(); lat_af = collections.Counter()
lat_arr = collections.Counter(); loads = collections.Counter()
for ln in out.splitlines():
    if '|OP LOAD|' not in ln:
        continue
    m = re.match(r'\s*([0-9a-f]+)\s.*\|LVL ([^|]*)\|.*BLK\s+\S+\s+(\d+)\s+([0-9a-f]+)\s+(\S+)', ln)
    if not m:
        continue
    addr, lvl, w, ip, sym = int(m.group(1), 16), m.group(2), int(m.group(3)), m.group(4), m.group(5)
    if ip.startswith('ffff'):
        continue
    ar = arr(addr)
    lv = 'L1' if lvl.startswith('L1') else 'L2' if lvl.startswith('L2') else 'RAM' if 'RAM' in lvl else 'L3+'
    loads[ar] += 1
    by_arr[ar][lv] += 1
    lat_arr[ar] += w
    if lv != 'L1':
        f = re.sub(r'^f\d+_', '', sym.split('+')[0])
        by_af[(ar, f)] += 1; lat_af[(ar, f)] += w
tl = sum(lat_arr.values()) or 1
P = a.period
print(f"summed miss latency x period: {tl * P / 1e9:.2f} G cycles (IBS samples ~1/4 of ops: shares only)")
print(f"\n{'lat%':>6} {'loads':>8} {'L2':>6} {'L3+':>6} {'RAM':>6}  array")
for ar, l in lat_arr.most_common(a.top):
    c = by_arr[ar]
    print(f"{100 * l / tl:6.1f} {loads[ar]:8d} {c['L2']:6d} {c['L3+']:6d} {c['RAM']:6d}  {ar}")
print(f"\n{'lat%':>6} {'miss':>6}  array / function")
for k, l in lat_af.most_common(a.top):
    print(f"{100 * l / tl:6.1f} {by_af[k]:6d}  {k[0]:24s} {k[1]}")
