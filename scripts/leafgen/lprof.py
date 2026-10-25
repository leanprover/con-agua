#!/usr/bin/env python3
"""lprof.py cats BIN CNT [--leaf]  : categories (leaf only with --leaf)
   lprof.py cmp BIN1 CNT1 BIN2 CNT2 [N] : per-function instruction counts side by side, leaf/nonleaf totals"""
import sys, json, array, collections, importlib.util
spec = importlib.util.spec_from_file_location("asmprof", "/home/joachim/con-agua/scripts/asmprof.py")
ap = importlib.util.module_from_spec(spec); spec.loader.exec_module(ap)

def load(binp, cnt):
    mp = json.load(open(binp + ".map")); blocks, meta = mp["blocks"], mp["meta"]
    a = array.array("Q"); a.frombytes(open(cnt, "rb").read())
    leaf = {b["fn"] for b in blocks} - {b["fn"] for b in blocks if any(i.startswith("call") for i in b["ins"])}
    byfn = collections.Counter(); calls = {}; cat = collections.Counter(); leafcat = collections.Counter()
    pat = collections.Counter()
    for b, n in zip(blocks, a):
        if b["fn"] not in calls: calls[b["fn"]] = n
        if not n: continue
        byfn[b["fn"]] += n * len(b["ins"])
        for i in b["ins"]:
            c = ap.category(i, meta); cat[c] += n
            if b["fn"] in leaf: leafcat[c] += n
    return byfn, calls, leaf, cat, leafcat

if sys.argv[1] == "cats":
    byfn, calls, leaf, cat, leafcat = load(sys.argv[2], sys.argv[3])
    c = leafcat if "--leaf" in sys.argv else cat
    t = sum(c.values()); print(f"total {t:,}")
    for k, n in c.most_common(): print(f"{100*n/t:6.2f}% {n:>16,} {k}")
elif sys.argv[1] == "cmp":
    f1, c1, l1, _, _ = load(sys.argv[2], sys.argv[3]); f2, c2, l2, _, _ = load(sys.argv[4], sys.argv[5])
    N = int(sys.argv[6]) if len(sys.argv) > 6 else 40
    t1, t2 = sum(f1.values()), sum(f2.values())
    lf1 = sum(n for f, n in f1.items() if f in l1); lf2 = sum(n for f, n in f2.items() if f in l1)
    print(f"total {t1/1e9:.2f} G -> {t2/1e9:.2f} G ({t2/t1:.4f}); leaves {lf1/1e9:.2f} -> {lf2/1e9:.2f} G; non-leaves {(t1-lf1)/1e9:.2f} -> {(t2-lf2)/1e9:.2f} G")
    for f, n in f1.most_common(N):
        m = f2.get(f, 0); k = max(c1.get(f, 1), 1)
        print(f"{f:28s} {'L' if f in l1 else ' '} {n/1e9:8.2f} G {m/1e9:8.2f} G  {n/k:7.1f} -> {m/max(c2.get(f,1),1):7.1f}")

if sys.argv[1] == "oracle":
    # lprof.py oracle BIN CNT : leaf/non-leaf totals vs clang -fno-inline (perfgap join_all.txt)
    import re
    cl = {}
    for ln in open("/home/joachim/con-agua/_tmp/perfgap/join_all.txt"):
        m = re.match(r"(\S+)\s+gap.*L\s+([\d.]+)/call clang\s+([\d.]+)/call\s+calls\s+([\d.]+)([MGK]?)", ln)
        if m:
            mult = {"M": 1e6, "G": 1e9, "K": 1e3, "": 1}[m.group(5)]
            cl[m.group(1)] = float(m.group(3)) * float(m.group(4)) * mult
    byfn, calls, leaf, _, _ = load(sys.argv[2], sys.argv[3])
    covered = [f for f in byfn if f in cl]
    for nm, S in (("leaf", [f for f in covered if f in leaf]), ("non-leaf", [f for f in covered if f not in leaf])):
        a = sum(byfn[f] for f in S); c = sum(cl[f] for f in S)
        print(f"{nm}: L {a/1e9:.1f} G, clang {c/1e9:.1f} G, gap {(a-c)/1e9:.1f} G")
    print(f"covered {sum(byfn[f] for f in covered)/1e9:.1f} of {sum(byfn.values())/1e9:.1f} G")
