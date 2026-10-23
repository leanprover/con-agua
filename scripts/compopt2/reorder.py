#!/usr/bin/env python3
"""Reorder the functions of a compiled checker `.s` by profile (lane compopt2 prototype F: code layout).

  reorder.py IN.s OUT.s PROF.bin CNT...   (PROF.bin(.map) = asmprof build of a compile with the same
                                          function names; CNT = its counter dumps)
Functions are sorted by executed instructions (summed over the dumps, each normalised to 1), hot first;
never-executed ones keep their order at the end. The trampoline stays first.
"""
import array, collections, json, re, sys

ins, outs, prof, cnts = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
mp = json.load(open(prof + ".map"))
heat = collections.Counter()
for c in cnts:
    a = array.array("Q"); a.frombytes(open(c, "rb").read())
    per = collections.Counter()
    for b, n in zip(mp["blocks"], a):
        per[b["fn"]] += n * len(b["ins"])
    tot = sum(per.values())
    for f, n in per.items():
        heat[f] += n / tot
lines = open(ins).read().split("\n")
head, chunks, tail, cur = [], [], [], None
for ln in lines:
    if ln.startswith(".section") and cur is not None:
        chunks.append(cur); cur = None
        tail.append(ln); continue
    if tail:
        tail.append(ln); continue
    m = re.match(r"ca_f_(.*):$", ln)
    if m:
        if cur is not None:
            chunks.append(cur)
        cur = (m.group(1), [ln])
    elif cur is None:
        head.append(ln)
    else:
        cur[1].append(ln)
if cur is not None:
    chunks.append(cur)
order = sorted(range(len(chunks)), key=lambda i: (-heat.get(chunks[i][0], 0), i))
with open(outs, "w") as fh:
    fh.write("\n".join(head + [l for i in order for l in chunks[i][1]] + tail))
hot = sum(1 for c in chunks if heat.get(c[0], 0) > 0)
print(f"{len(chunks)} functions, {hot} executed in the profile")
