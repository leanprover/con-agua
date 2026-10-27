import ConAgua.Arena.IndCallM
import ConAgua.Arena.IndStubs
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import ConAgua.L.Examples

/-!
# LvlEqFueledSpecC

`lveW`, `lveC`, `lvlEqFueled_specC`, `agreeBodyAM`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `lvl_eq_fueled` -/

/-- The model of `lvl_eq_fueled(u, v)`: the stub `lvl_eq`, `none` (word `0`) aborts. -/
def lveW (m : Mem) (u v : Word) : Option (List Word × Mem) :=
  match stubM "lvl_eq_c" m [u, v] with
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then none else some ([if r.headD 0 = 2 then 1 else 0], m1)

/-- The model of `lvl_eq_fueled(u, v)` at L fuel `k`, its call of `lvl_eq_c` read through `cR`
(`lveW` is the stubs' reading, `lveC_stub`). -/
def lveC (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, u, v =>
    match cR k "lvl_eq_c" [u, v] m with
    | none => none
    | some (r, m1) => if r.headD 0 = 0 then none else some ([if r.headD 0 = 2 then 1 else 0], m1)

theorem lvlEqFueled_specC (p : Prog) (hp : p.lookup "lvl_eq_fueled" = some lvlEqFueled) (cR : CallM)
    (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "lvl_eq_fueled" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ lveC cR n s₀.mem u v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvlEqFueled]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, hcR n "lvl_eq_c"] <;>
      finish (gen := 20) [lveC]

/-- The per-member body of `checkBlockAgree` after member 0's telescope `fvs0` is opened. -/
def agreeBodyAM (fe : IFEnv) (nP : Nat) (fvs0 : List EIdx) (cvTa : IConstantVal) (s s₀ : LIdx) :
    AM Unit := do
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.invalid "parameters of all inductive datatypes must match")
  unless tq.1.length == fvs0.length do
    fail (.invalid "parameters of all inductive datatypes must match")
  let doms ← fvarTypeDs fvs0
  ConRon.Arena.checkBlockDomsAt V fe 0 tq.1 doms nP
  unless ← liftFueled "level comparison" (← lvlEq? s s₀) do
    fail (.invalid "mutually inductive types must live in the same universe")

end L.Ind

end
