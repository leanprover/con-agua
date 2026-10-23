#!/usr/bin/env python3
"""Regenerate `preLoopFns`, `preLoopA` and `preLoopC` in ConAgua/Checker/PreLoopWS.lean: the call
closure of the stages `check` runs before the declaration loop in `checkerProg`, and the word
arrays and `CTL` words their bodies store into. Also generate ConAgua/Checker/PreLoopWSStages.lean,
the same per stage (`stageFns_f`, `stageA_f`, `stageC_f`, `stageFrame_f`). Fails if a `CTL` index is not a literal or
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
  for g in STAGES do
    for f in (cloW p [g] []).mergeSort do
      IO.println s!"IN {g} {f}"
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

# Per stage: the closure, its arrays and CTL words.
stores = {}
for l in ls:
    if l.startswith("ST "):
        _, f, a = l.split()
        stores.setdefault(f, (set(), set()))[0].add(int(a))
    elif l.startswith("CTL "):
        f, ws = l.split(" ", 2)[1:]
        stores.setdefault(f, (set(), set()))[1].update(int(x) for x in re.findall(r"\d+", ws))
def lit(items):
    return "[\n" + wrap(items) + "]" if items else "[]"

WATCH = [131, 132, 148, 149, 150, 151, 240]
NOPINS = ["builtin_prelude", "front_run", "prepare_prelude"]
parts = []
for g in STAGES:
    gf = [l.split()[2] for l in ls if l.startswith("IN %s " % g)]
    gA = sorted(set().union(*[stores.get(f, (set(), set()))[0] for f in gf]))
    gC = sorted(set().union(*[stores.get(f, (set(), set()))[1] for f in gf]))
    on = [w for w in WATCH if w in gC]
    off = [w for w in WATCH if w not in gC]
    q = '"%s"' % g
    parts.append(f"""/-! ## `{g}` -/

/-- The call closure of `{g}` in `checkerProg` ({len(gf)} functions). -/
def stageFns_{g} : List FnName := [
{wrap(['"%s"' % f for f in gf])}]

/-- The word arrays (other than `CTL`) the functions of `stageFns_{g}` store
into. -/
def stageA_{g} : List ArrId := {lit([str(a) for a in gA])}

/-- The `CTL` words the functions of `stageFns_{g}` store into. -/
def stageC_{g} : List Word := {lit([str(c) for c in gC])}

names_tree stageTree_{g} : stageFns_{g}

prog_all checkerProg_stageChk_{g} : checkerProg
  (wsChk CTL (fun a => stageA_{g}.contains a)
    (fun w => stageC_{g}.contains w) stageTree_{g})

theorem checkerProg_stageClosed_{g} :
    closedA checkerProg stageA_{g} stageC_{g}
      stageFns_{g} = true :=
  closedW_of_all stageTree_{g}.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_{g}

/-- **A run of `{g}` is a frame of its own write set.** -/
theorem stageFrame_{g} (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) {q} []
    ⦃fun _ s' =>
      MemFrame stageA_{g} stageC_{g} s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_{g} n
    (mem_of_tree stageTree_{g}.eq {q} (by decide +kernel)) s₀
""")
    if g in NOPINS:
        parts.append(f"""theorem stageA_{g}_pins : PINS ∉ stageA_{g} := by decide +kernel
""")
    if off:
        parts.append(f"""/-- Of the `CTL` words {", ".join(map(str, WATCH))}, `{g}` writes
{"none" if not on else ", ".join(map(str, on))}. -/
theorem stageC_{g}_off :
    ∀ w : Word, w.toNat ∈ ({off} : List Nat) →
      w ∉ stageC_{g} :=
  not_mem_of_toNat (by decide +kernel)
""")
    else:
        parts.append(f"""-- Of the `CTL` words {", ".join(map(str, WATCH))}, `{g}` writes all.
""")
stagesSrc = """import ConAgua.Checker.Prog
import ConAgua.Arena.Frame
import ConAgua.Compiler.WriteSetSplit

/-!
# The write set of each pre-loop stage (lane `pipeline`; generated by `scripts/preloop_ws.py`)

For each stage `f` that `check` runs before the declaration loop: its call closure `stageFns_f`
in `checkerProg`, the word arrays `stageA_f` and `CTL` words `stageC_f` its functions store into,
the write-set check per chunk (`checkerProg_stageChk_f`, as `PreLoopWS.lean` for the union), and
`stageFrame_f`: every run of `f` is a `MemFrame stageA_f stageC_f`. So a fact about memory that
a stage does not write survives it (the pins `PINS` across `builtin_prelude`, `front_run` and
`prepare_prelude`: `stageA_f_pins`; the watched `CTL` words: `stageC_f_off`). Do not edit by
hand: rerun the script.
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-- Membership in a function list by its name tree. -/
theorem mem_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t) (f : FnName)
    (h : (t.find (nameCode f)).isSome = true) : f ∈ fs := by
  have := namesTree_spec ht f
  rw [h] at this; exact of_decide_eq_true this.symm

/-- `invoke_memFrame` without the byte arrays, at no arguments. -/
theorem memFrame_of_closed {A : List ArrId} {C : List Word} {fs : List FnName}
    (hp : closedA checkerProg A C fs = true) (n : Nat) {f : FnName} (hf : f ∈ fs) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) f []
    ⦃fun _ s' => MemFrame A C s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  exact (M.of_run (P := fun s => s = s₀) hs hrun (invoke_memFrame hp n hf [] s₀)).1

/-- Non-membership of words in a list of words, by numbers (deciding it on `List Word`
membership is slow). -/
theorem not_mem_of_toNat {C : List Word} {Z : List Nat}
    (h : (C.map UInt64.toNat).all (fun x => !Z.contains x) = true) :
    ∀ w : Word, w.toNat ∈ Z → w ∉ C := by
  intro w hw hc
  have := List.all_eq_true.mp h w.toNat (List.mem_map.mpr ⟨w, hc, rfl⟩)
  simp [hw] at this

""" + "\n".join(parts) + "\nend L.Checker\n"
ps = os.path.join(ROOT, "ConAgua", "Checker", "PreLoopWSStages.lean")
olds = open(ps).read() if os.path.exists(ps) else ""
if "--check" in sys.argv:
    sys.exit(0 if new == s and stagesSrc == olds else "PreLoopWS lists are stale: run scripts/preloop_ws.py")
open(p, "w").write(new)
open(ps, "w").write(stagesSrc)
print(len(fns), "functions,", len(A), "arrays,", len(C), "CTL words")
