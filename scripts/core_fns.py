#!/usr/bin/env python3
"""Regenerate `coreFns` in ConAgua/Arena/CoreErec.lean: the call closure of `coreRoots` in
`checkerProg` (DESIGN.md, lane whnf3, "The record pool from the program text"). Needs
ConAgua.Checker.Prog built. Usage: scripts/core_fns.py [--check]"""
import os, re, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
out = subprocess.run([os.path.join(ROOT, "scripts", "lake"), "env", "lean", "scripts/core_fns.lean"],
                     cwd=ROOT, capture_output=True, text=True)
fns = [l[3:].strip() for l in out.stdout.splitlines() if l.startswith("FN ")]
if not fns:
    sys.exit("no output:\n" + out.stdout + out.stderr)
lines, cur = [], "  "
for f in fns:
    t = '"%s", ' % f
    if len(cur) + len(t) > 100:
        lines.append(cur.rstrip()); cur = "  "
    cur += t
lines.append(cur.rstrip().rstrip(","))
p = os.path.join(ROOT, "ConAgua", "Arena", "CoreErec.lean")
s = open(p).read()
new = re.sub(r"(def coreFns : List FnName := \[\n).*?(\n\])", lambda m: m.group(1) + "\n".join(lines) + m.group(2), s, flags=re.S)
new = re.sub(r"(closure of `coreRoots` in `checkerProg`, a literal list, )\d+( functions)", lambda m: m.group(1) + str(len(fns)) + m.group(2), new)
if "--check" in sys.argv:
    sys.exit(0 if new == s else "coreFns is stale: run scripts/core_fns.py")
open(p, "w").write(new)
print(len(fns), "functions")
