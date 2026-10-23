#!/usr/bin/env python3
"""Regenerate `preLoopFns`, `preLoopA` and `preLoopC` in ConAgua/Checker/PreLoopWS.lean: the call
closure of the stages `check` runs before the declaration loop in `checkerProg`, and the word
arrays and `CTL` words their bodies store into. Fails if a `CTL` index is not a literal or
`k + (e &&& 1)`, or a function stores bytes. Needs ConAgua.Checker.Prog built.
Usage: scripts/preloop_ws.py [--check]"""
import os, re, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STAGES = ["cap_check", "pb_check", "intern_reserved_pins", "builtin_prelude", "front_run",
          "prepare_prelude", "intern_all_pins"]
LEAN = r'''import ConAgua.Checker.Prog
open L
partial def L.Stmt.callsW : Stmt → List FnName
  | .seq s t => s.callsW ++ t.callsW
  | .ite _ s t => s.callsW ++ t.callsW
  | .while _ s => s.callsW
  | .call _ f _ => [f]
  | _ => []
partial def L.Stmt.storesW : Stmt → List (Bool × ArrId × Expr)
  | .seq s t => s.storesW ++ t.storesW
  | .ite _ s t => s.storesW ++ t.storesW
  | .while _ s => s.storesW
  | .st64 a i _ => [(true, a, i)]
  | .st8 a i _ => [(false, a, i)]
  | _ => []
partial def cloW (p : Prog) (todo seen : List FnName) : List FnName :=
  match todo with
  | [] => seen
  | f :: r => if f ∈ seen then cloW p r seen else
    match p.lookup f with
    | some fd => cloW p (fd.body.callsW ++ r) (f :: seen)
    | none => cloW p r (f :: seen)
#eval do
  let p := L.Checker.checkerProg
  for f in (cloW p STAGES []).mergeSort do
    IO.println s!"FN {f}"
    if let some fd := p.lookup f then
      for (w, a, i) in fd.body.storesW do
        if !w then IO.println s!"ST8 {f} {a}"
        else if a = 1 then
          match ctlIdx i with
          | some ws => IO.println s!"CTL {f} {ws.map UInt64.toNat}"
          | none => IO.println s!"CTLDYN {f}"
        else IO.println s!"ST {f} {a}"
'''.replace("STAGES", "[" + ", ".join('"%s"' % s for s in STAGES) + "]")
tmpdir = os.path.join(ROOT, "_tmp")
os.makedirs(tmpdir, exist_ok=True)
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=tmpdir, delete=False) as fh:
    fh.write(LEAN)
try:
    out = subprocess.run([os.path.join(ROOT, "scripts", "lake"), "env", "lean", fh.name],
                         cwd=ROOT, capture_output=True, text=True, timeout=900)
finally:
    os.unlink(fh.name)
ls = out.stdout.splitlines()
fns = [l[3:].strip() for l in ls if l.startswith("FN ")]
if not fns:
    sys.exit("no output:\n" + out.stdout + out.stderr)
bad = [l for l in ls if l.startswith("CTLDYN ") or l.startswith("ST8 ")]
if bad:
    sys.exit("stores the check cannot bound:\n" + "\n".join(bad))
A = sorted({int(l.split()[2]) for l in ls if l.startswith("ST ")})
C = sorted({int(x) for l in ls if l.startswith("CTL ") for x in re.findall(r"\d+", l.split(" ", 2)[2])})

def wrap(items):
    lines, cur = [], "  "
    for t in items:
        t += ", "
        if len(cur) + len(t) > 100:
            lines.append(cur.rstrip()); cur = "  "
        cur += t
    lines.append(cur.rstrip().rstrip(","))
    return "\n".join(lines)

p = os.path.join(ROOT, "ConAgua", "Checker", "PreLoopWS.lean")
s = open(p).read()
new = s
for name, ty, items in [("preLoopFns", "List FnName", ['"%s"' % f for f in fns]),
                        ("preLoopA", "List ArrId", [str(a) for a in A]),
                        ("preLoopC", "List Word", [str(c) for c in C])]:
    new = re.sub(r"(def %s : %s := \[\n).*?(\])" % (name, ty),
                 lambda m: m.group(1) + wrap(items) + m.group(2), new, flags=re.S)
new = re.sub(r"in `checkerProg` \(\d+ functions", "in `checkerProg` (%d functions" % len(fns), new)
if "--check" in sys.argv:
    sys.exit(0 if new == s else "PreLoopWS lists are stale: run scripts/preloop_ws.py")
open(p, "w").write(new)
print(len(fns), "functions,", len(A), "arrays,", len(C), "CTL words")
