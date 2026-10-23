#!/usr/bin/env python3
"""Regenerate `leafFns` in ConAgua/Arena/LeafFns.lean: the functions of `loopFns` whose call closure in
`checkerProg` leaves the pins and the core memos alone (`LeafClosed`; `ConAgua/Checker/LeafAll.lean` fails when it is stale).
Needs ConAgua.Checker.Prog built. Usage: scripts/leaf_fns.py [--check]"""
import os, re, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
out = subprocess.run([os.path.join(ROOT, "scripts", "lake"), "env", "lean", "scripts/leaf_fns.lean"],
                     cwd=ROOT, capture_output=True, text=True)
fns = [l[3:].strip() for l in out.stdout.splitlines() if l.startswith("FN ")]
if not fns:
    sys.exit("no output:\n" + out.stdout + out.stderr)
lines, cur = [], "  ["
for f in fns:
    t = '"%s", ' % f
    if len(cur) + len(t) > 100:
        lines.append(cur.rstrip()); cur = "   "
    cur += t
lines.append(cur.rstrip().rstrip(",") + "]")
p = os.path.join(ROOT, "ConAgua", "Arena", "LeafFns.lean")
s = open(p).read()
new = re.sub(r"(def leafFns : List FnName :=\n).*?\]\n", lambda m: m.group(1) + "\n".join(lines) + "\n", s, count=1, flags=re.S)
new = re.sub(r"(call graph \()\d+( names;)", lambda m: m.group(1) + str(len(fns)) + m.group(2), new)
if "--check" in sys.argv:
    sys.exit(0 if new == s else "leafFns is stale: run scripts/leaf_fns.py")
open(p, "w").write(new)
print(len(fns), "functions")
