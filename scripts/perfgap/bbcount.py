#!/usr/bin/env python3
"""Exact per-function instruction counts for a clang-generated .s (block counters, flags preserved).
  bbcount.py build IN.s OUT.s      (writes OUT.s and OUT.s.map)
  bbcount.py report MAP CNT [--top N]

Lane perfgap: `clang -O2 -fno-inline -mno-red-zone -S oracle.c`, then `build` (each block gets
`pushfq; incq ca_bb+8i(%rip); popfq`, so live flags survive; no red zone, so the push is safe), link
with main.c, the stub and asmprof.py's DUMP_C destructor, run with CA_BBOUT=CNT.
`join.py ASMPROF_REPORT BBCOUNT_REPORT N` lines up the two per-function tables (calls, instructions
per call, the gap).
"""
import sys, re, json, array, collections
JUMP = re.compile(r"^(j[a-z]+|call|ret)\b")
def build(src, dst):
    out, blocks = [], []
    fn = None; start = True; text = True
    for ln in open(src):
        ln = ln.rstrip("\n"); t = ln.split("#")[0].strip() if not ln.strip().startswith(".") else ln.strip()
        if t.startswith(".section"):
            text = ".text" in t
        if t in (".text",) or t.startswith(".text"):
            text = True
        if t.startswith(".data") or t.startswith(".bss"):
            text = False
        if not t or t.startswith("#"):
            out.append(ln); continue
        if t.endswith(":") and not t.startswith("."):
            fn = t[:-1]; out.append(ln); start = True; continue
        if t.endswith(":"):
            out.append(ln); start = True; continue
        if t.startswith("."):
            out.append(ln); continue
        if not text:
            out.append(ln); continue
        if start:
            i = len(blocks); blocks.append({"fn": fn, "n": 0})
            out.append(f"\tpushfq\n\tincq ca_bb+{8*i}(%rip)\n\tpopfq")
            start = False
        blocks[-1]["n"] += 1
        out.append(ln)
        if JUMP.match(t):
            start = True
    out.append(f"\t.section .bss\n\t.globl ca_bb\n\t.p2align 3\nca_bb: .zero {8*len(blocks)}\n"
               f"\t.section .rodata\n\t.globl ca_bb_n\nca_bb_n: .quad {len(blocks)}\n")
    open(dst, "w").write("\n".join(out) + "\n")
    json.dump(blocks, open(dst + ".map", "w"))
    print(len(blocks), "blocks")
def report(mp, cnt, top):
    blocks = json.load(open(mp)); a = array.array("Q"); a.frombytes(open(cnt, "rb").read())
    by = collections.Counter(); calls = collections.Counter(); seen = set()
    for b, n in zip(blocks, a):
        by[b["fn"]] += n * b["n"]
        if b["fn"] not in seen:
            seen.add(b["fn"]); calls[b["fn"]] = n
    tot = sum(by.values())
    print(f"total {tot:,}")
    for f, n in by.most_common(top):
        print(f"{100*n/tot:6.2f}% {n:>16,} {calls[f]:>14,} {n/max(calls[f],1):8.1f} {re.sub(r'^f[0-9]+_', '', str(f))}")
if sys.argv[1] == "build": build(sys.argv[2], sys.argv[3])
else: report(sys.argv[2], sys.argv[3], int(sys.argv[5]) if len(sys.argv) > 5 else 80)
