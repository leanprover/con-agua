#!/usr/bin/env python3
"""Load-latency profile of a compiled L checker with AMD IBS (lane compopt2).

`perf record -e ibs_op/cnt_ctl=1/` tags every P-th dispatched op precisely (no skid) and reports, for
loads, where the data came from and the miss latency. Summed latency x P estimates the cycles spent
waiting on data-cache misses (an upper bound: misses can overlap), per function and per instruction.

  scripts/compopt2/ibsprof.py [--period P] [--cpus C] [--top N] BIN FIXTURE   (CA_PINS, CA_WORDS from env)
"""
import argparse, collections, os, re, subprocess, sys, tempfile

ap = argparse.ArgumentParser()
ap.add_argument("bin"); ap.add_argument("fixture")
ap.add_argument("--period", type=int, default=20000)
ap.add_argument("--cpus"); ap.add_argument("--top", type=int, default=25)
ap.add_argument("--data", help="reuse this perf.data")
a = ap.parse_args()
data = a.data or os.path.join(tempfile.mkdtemp(dir=os.environ.get("TMPDIR", "/tmp")), "ibs.data")
if not a.data:
    pre = ["taskset", "-c", a.cpus] if a.cpus else []
    subprocess.run(pre + ["perf", "record", "-q", "-e", "ibs_op/cnt_ctl=1/", "-d", "-W", "-c", str(a.period),
                          "-o", data, "--", os.path.abspath(a.bin), a.fixture], check=True,
                   stdout=subprocess.DEVNULL)
out = subprocess.run(["perf", "script", "-i", data, "-F", "ip,sym,weight,data_src", "--no-demangle"],
                     capture_output=True, text=True).stdout
ops = collections.Counter(); lat = collections.Counter(); lvl = collections.Counter()
fn_lvl = collections.defaultdict(collections.Counter); ip_lat = collections.Counter(); ip_sym = {}
user = kern = 0
for ln in out.splitlines():
    m = re.match(r"\s*[0-9a-f]+\s+\|OP ([^|]*)\|LVL ([^|]*)\|.*BLK\s+\S+\s+(\d+)\s+([0-9a-f]+)\s+(\S+)\s*$", ln)
    if not m:
        continue
    op, level, w, ip, sym = m.group(1).strip(), m.group(2).strip(), int(m.group(3)), m.group(4), m.group(5)
    if ip.startswith("ffff"):
        kern += 1
        continue
    user += 1
    sym = sym.split("+")[0]
    ops[sym] += 1
    if op == "LOAD":
        lv = "L1" if level.startswith("L1") else "L2" if level.startswith("L2") else \
            "RAM" if "RAM" in level else "L3/other cache" if level and level != "N/A" else "?"
        lvl[lv] += 1; fn_lvl[sym][lv] += 1
        lat[sym] += w; ip_lat[ip] += w; ip_sym[ip] = sym
P = a.period
tl = sum(lat.values())
print(f"user ops sampled {user} (~{user*P/1e9:.2f} G ops), kernel {kern}; loads by source: " +
      ", ".join(f"{k} {v*P/1e6:.1f} M" for k, v in lvl.most_common()))
print(f"summed miss latency x period: {tl*P/1e9:.2f} G cycles")
print(f"\n{'ops%':>6} {'misslat G':>9} {'lat%':>5} {'RAM M':>7} {'L2 M':>6}  function")
for s, l in sorted(lat.items(), key=lambda x: -x[1])[:a.top]:
    print(f"{100*ops[s]/user:6.2f} {l*P/1e9:9.3f} {100*l/max(tl,1):5.1f} {fn_lvl[s]['RAM']*P/1e6:7.2f} {fn_lvl[s]['L2']*P/1e6:6.2f}  {s}")
print("\ntop instructions by miss latency:")
for ip, l in ip_lat.most_common(a.top):
    print(f"  {ip} {ip_sym[ip]:30s} {l*P/1e9:.3f} G")
