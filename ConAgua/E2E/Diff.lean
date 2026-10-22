import ConRon.Arena.Main
import ConAgua.E2E.Ser
import ConAgua.Final.Statement

/-!
# Per-function differential tests against the twin (lane `e2e`)

`e2e-diff PROG FILE [N] [WORDS] [IDWORDS]`: from the same input, build the twin's state and L's memory the way the
pipeline does, compare the stores, then run single functions on both sides and compare results.

* **States.** Twin: `internReservedPins`, `parseBytes FILE`, `internAllPins P` from
  `AState.init EStore.empty` (the first stages of `e2e-ref --no-prelude`). L: `L.run` of
  `e2e_front()` (`ConAgua/E2E/Check.lean`: the same three stages) on `loadMem FILE …` (the stubs
  of `PROG` call `__missing_<name>`, so a missing callee is named).
* **Stores.** For each of the 19 cons tables and both tiers, L's node count `CTL[ca + t]` against
  the twin's `nodes.size` (the counts `ArenaR` relates; equal counts mean the two interned the
  same number of nodes in the same tables).
* **Functions.** For up to `N` persistent expression handles `h` (every tag, evenly spread):
  `whnf(0, 0, 0, h)`, `whnf_core(0, 0, 0, 0, h)`, `infer(0, 0, 0, h)` against the twin's knot
  (`pureFnsA .verified (mkIFEnv IEnv.empty) checkFuel`) slots `whnf 0 h`, `whnfCore false 0 h`,
  `infer 0 h`, each from the states above (verified mode, the empty environment, view word `0`,
  depth `0`). Agreement: both succeed with the same handle word (low 32 bits: `decE`) and the
  same store counts after, or both fail (the twin throws, L aborts). Prints one line per
  function: `fn NAME agree A disagree D missing M lerr E twinerr T` and the first disagreements.
-/

namespace L.E2E.Diff

open L
open ConRon.Arena

/-- The cons tables: name, `CTL` count word of tier 0, and the twin's counts per tier. -/
def tables : List (String × Nat × (AState → Nat × Nat)) := [
  ("lit", 2, fun a => (a.store.pers.lits.size, a.store.scr.lits.size)),
  ("app", 4, fun a => (a.store.pers.apps.size, a.store.scr.apps.size)),
  ("succ", 6, fun a => (a.store.lss.ls.pers.succs.size, a.store.lss.ls.scr.succs.size)),
  ("zero", 8, fun a => (a.store.lss.ls.pers.zeros.size, a.store.lss.ls.scr.zeros.size)),
  ("max", 10, fun a => (a.store.lss.ls.pers.maxs.size, a.store.lss.ls.scr.maxs.size)),
  ("imax", 12, fun a => (a.store.lss.ls.pers.imaxs.size, a.store.lss.ls.scr.imaxs.size)),
  ("param", 14, fun a => (a.store.lss.ls.pers.params.size, a.store.lss.ls.scr.params.size)),
  ("sort", 16, fun a => (a.store.pers.sorts.size, a.store.scr.sorts.size)),
  ("const", 18, fun a => (a.store.pers.consts.size, a.store.scr.consts.size)),
  ("letE", 20, fun a => (a.store.pers.lets.size, a.store.scr.lets.size)),
  ("bvar", 22, fun a => (a.store.pers.bvars.size, a.store.scr.bvars.size)),
  ("fvar", 26, fun a => (a.store.pers.fvars.size, a.store.scr.fvars.size)),
  ("lam", 28, fun a => (a.store.pers.lams.size, a.store.scr.lams.size)),
  ("forallE", 30, fun a => (a.store.pers.foralls.size, a.store.scr.foralls.size)),
  ("proj", 32, fun a => (a.store.pers.projs.size, a.store.scr.projs.size)),
  ("nanon", 34, fun a => (a.store.lss.ls.ns.pers.anons.size, a.store.lss.ls.ns.scr.anons.size)),
  ("nstr", 36, fun a => (a.store.lss.ls.ns.pers.strs.size, a.store.lss.ls.ns.scr.strs.size)),
  ("nnum", 38, fun a => (a.store.lss.ls.ns.pers.nums.size, a.store.lss.ls.ns.scr.nums.size)),
  ("ls", 40, fun a => (a.store.lss.pers.lists.size, a.store.lss.scr.lists.size))]

def ctl (m : Mem) (i : Nat) : Nat := ((m.arr64 1).getD i 0).toNat

/-- The tables whose counts differ: `name: L (t0, t1) vs twin (t0, t1)`. -/
def storeDiff (m : Mem) (a : AState) : List String :=
  tables.filterMap fun (n, ca, tw) =>
    let l := (ctl m ca, ctl m (ca + 1))
    if l == tw a then none else some s!"{n}: L {l} twin {tw a}"

/-- Expression tables: tag and the twin's persistent count. -/
def exprTags (a : AState) : List (Nat × Nat) :=
  [(0, a.store.pers.bvars.size), (1, a.store.pers.fvars.size), (2, a.store.pers.sorts.size),
   (3, a.store.pers.consts.size), (4, a.store.pers.apps.size), (5, a.store.pers.lams.size),
   (6, a.store.pers.foralls.size), (7, a.store.pers.lets.size), (8, a.store.pers.lits.size),
   (9, a.store.pers.projs.size)]

/-- Up to `n` persistent handles, spread over every tag. -/
def handles (a : AState) (n : Nat) : List Nat := Id.run do
  let all := exprTags a
  let total := all.foldl (· + ·.2) 0
  let mut out := #[]
  for (t, c) in all do
    let k := if total ≤ n then c else max 1 (c * n / max total 1)
    let step := max 1 (c / max k 1)
    for j in List.range (min k c) do
      out := out.push (t * 268435456 + j * step)
  return out.toList

structure Tally where
  agree : Nat := 0
  disagree : Nat := 0
  missing : Std.HashMap String Nat := {}
  lerr : Nat := 0
  twinerr : Nat := 0
  bothErr : Nat := 0
  examples : Array String := #[]

def Tally.add (t : Tally) (s : String) : Tally :=
  if t.examples.size < 8 then { t with examples := t.examples.push s } else t

def runFn (p : Prog) (m₁ : Mem) (a₁ : AState) (name : String) (args : Nat → List Word)
    (twin : CoreFnsA → Nat → AM EIdx) (hs : List Nat) (fuel : Nat) : Tally := Id.run do
  let fe := mkIFEnv IEnv.empty
  let r := pureFnsA .verified fe checkFuel
  let mut t : Tally := {}
  for h in hs do
    let tw := (twin r h).run a₁
    let lr := L.run p fuel name (args h) m₁
    match tw, lr with
    | .ok (e, a'), .ok (rs, m') =>
      let lw := (rs.headD 0).toNat % 2 ^ 32
      if lw == e.word.toNat && storeDiff m' a' == [] then t := { t with agree := t.agree + 1 }
      else
        t := { t with disagree := t.disagree + 1 }
        t := t.add s!"{name}({h}): L {lw} twin {e.word}{if storeDiff m' a' == [] then "" else s!", stores after: {storeDiff m' a'}"}"
    | .ok (e, _), .error err =>
      match err with
      | .noFun f =>
        let f := if f.startsWith "__missing_" then (f.drop 10).toString else f
        t := { t with missing := t.missing.insert f (t.missing.getD f 0 + 1) }
      | _ =>
        t := { t with lerr := t.lerr + 1 }
        t := t.add s!"{name}({h}): L {repr err} twin ok {e.word}"
    | .error e, .ok (rs, _) =>
      t := { t with twinerr := t.twinerr + 1 }
      t := t.add s!"{name}({h}): L ok {rs.headD 0} twin error {e.message}"
    | .error _, .error (.noFun f) =>
      let f := if f.startsWith "__missing_" then (f.drop 10).toString else f
      t := { t with missing := t.missing.insert f (t.missing.getD f 0 + 1) }
    | .error _, .error _ => t := { t with bothErr := t.bothErr + 1 }
  return t

def twinFront (b : ByteArray) (pins : List ConLeche.NatOpPinSet) :
    AM (Except ConRon.Arena.CheckError Unit) := do
  internReservedPins
  match ← Frontend.parseBytes b with
  | .error (e, n) => return .error (Frontend.atLine e n)
  | .ok _ =>
    let _ ← internAllPins pins
    return .ok ()

def main (args : List String) : IO UInt32 := do
  let [prog, file] := args.take 2 | IO.eprintln "usage: e2e-diff PROG FILE [N] [WORDS] [IDWORDS]"; return 2
  let n := (args[2]?.bind String.toNat?).getD 200
  let words := (args[3]?.bind String.toNat?).getD 65536
  -- the export's id tables' dense parts (`NID`, `LID`, `EID`: word arrays 64-66) sized for the file's ids
  -- (`scripts/e2e.py` caps it; larger ids go to the sparse overflow, arrays 72-74)
  let idWords := max words ((args[4]?.bind String.toNat?).getD 0)
  let pf ← match parseProgFile (← IO.FS.readFile prog) with
    | .ok pf => pure pf
    | .error e => throw (IO.userError e)
  let p0 : Prog := pf.fns.toList
  let nw := (L.Compiler.Prog.arrs p0).2
  let p : Prog := p0 ++ pf.stubs.toList.map fun (f, np, _) =>
    (f, { nparams := np, nlocals := np, body := .call [] ("__missing_" ++ f) [] })
  let b ← IO.FS.readBinFile file
  let fuel := 2 ^ 40
  -- the pin-data buffer (`$CA_PINS`, DESIGN.md lane `romload`) and the twin's list: its first variant
  let (pb, pins) ← match ← IO.getEnv "CA_PINS" with
    | some f => pure (← IO.FS.readBinFile f, ConLeche.natOpPinSets.take 1)
    | none => pure (ByteArray.empty, [])
  let m₀ := ConAgua.Final.loadMem b pb []
    ((List.range (nw + 1)).map fun a => if 64 ≤ a && a ≤ 66 then idWords else words)
  let (m₁, front) := match L.run p fuel "e2e_front" [] m₀ with
    | .ok (rs, m) => (m, s!"ok {rs.headD 0}")
    | .error e => (m₀, s!"error {repr e}")
  let (a₁, tfront) := match (twinFront b pins).run (AState.init EStore.empty) with
    | .ok (.ok (), a) => (a, "ok")
    | .ok (.error e, a) => (a, s!"reject {e.message}")
    | .error e => (AState.init EStore.empty, s!"error {e.message}")
  IO.println s!"front L {front} twin {tfront}"
  unless front == "ok 0" && tfront == "ok" do return 0
  let sd := storeDiff m₁ a₁
  IO.println s!"store {if sd.isEmpty then "agree" else "DIFFER " ++ ", ".intercalate sd}"
  unless sd.isEmpty do return 0
  let hs := handles a₁ n
  let fns : List (String × (Nat → List Word) × (CoreFnsA → Nat → AM EIdx)) := [
    ("whnf", fun h => [0, 0, 0, h.toUInt64], fun r h => r.whnf 0 ⟨h.toUInt32⟩),
    ("whnf_core", fun h => [0, 0, 0, 0, h.toUInt64], fun r h => r.whnfCore false 0 ⟨h.toUInt32⟩),
    ("infer", fun h => [0, 0, 0, h.toUInt64], fun r h => r.infer 0 ⟨h.toUInt32⟩)]
  for (name, la, tw) in fns do
    let t := runFn p m₁ a₁ name la tw hs fuel
    let miss := ", ".intercalate (t.missing.toList.map fun (f, k) => s!"{f}:{k}")
    IO.println s!"fn {name} n {hs.length} agree {t.agree} disagree {t.disagree} lerr {t.lerr} twinerr {t.twinerr} botherr {t.bothErr} missing [{miss}]"
    for e in t.examples do IO.println s!"  {e}"
  return 0

end L.E2E.Diff

def main (args : List String) : IO UInt32 := L.E2E.Diff.main args
