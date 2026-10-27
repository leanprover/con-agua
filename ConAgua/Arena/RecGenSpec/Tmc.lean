import ConAgua.Arena.RecCheck
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Tmc

`tmfK6`, `tmcK2`, `tmcK1`, `tmcW`, `tmcK1_some`, `tmcK2_some` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

def tmfK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tmcK2 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) (r4 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 ≠ 0 then
      tmfK6 (callW p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y, r.tail.headD 0] m)
    else tmfK6 (callW p n "target_major_of_outside" [vis, pp, pfo, pfl, x, y, ao, al, r4.headD 0, r4.tail.headD 0] m)
def tmcK1 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y r
      (callW p n "sl_find" [r.headD 0, r.tail.headD 0, x] m)

/-- **The model of `target_major_of_const`** at exec fuel `n + 1`. -/
def tmcW (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) :
    Option (List Word × Mem) :=
  tmcK1 p n vis pp cao cal pfo pfl fvo fvl ao al x y (callW p n "block_shape_member_names" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) (r r4 : List Word)
theorem tmcK1_some : tmcK1 p n vis pp cao cal pfo pfl fvo fvl ao al x y (some (r, m)) =
    tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y r (callW p n "sl_find" [r.headD 0, r.tail.headD 0, x] m) := rfl
theorem tmcK2_some : tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y r4 (some (r, m)) =
    if r.headD 0 ≠ 0 then
      tmfK6 (callW p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y, r.tail.headD 0] m)
    else tmfK6 (callW p n "target_major_of_outside" [vis, pp, pfo, pfl, x, y, ao, al, r4.headD 0, r4.tail.headD 0] m) :=
  rfl
theorem tmfK6_some : tmfK6 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tmcK1_some tmcK2_some tmfK6_some

set_option maxHeartbeats 1600000 in
theorem tmc_spec (p : Prog) (hp : p.lookup "target_major_of_const" = some targetMajorOfConst) (n : Nat)
    (s₀ : St) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ tmcW p n s₀.mem vis pp cao cal pfo pfl fvo fvl ao al x y = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOfConst]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "block_shape_member_names", callW_spec p n "sl_find",
      callW_spec p n "target_major_of_member", callW_spec p n "target_major_of_outside"] <;>
    finish (gen := 40) (instances := 20000) [tmcW, rdW_eq]

def tmfK3 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmfK6 (callW p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, r1.headD 0,
      r1.tail.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m)
def tmfK2 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 >>> 28 ≠ 3 then none
      else tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1 (callW p n "e_view" [r.headD 0] m)
def tmfK1 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl mty : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmfK2 p n vis pp cao cal pfo pfl fvo fvl r (callW p n "get_app_fn_f" [CWF, mty] m)

/-- **The model of `target_major_of`** at exec fuel `n + 1`. -/
def tmfW (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl mty : Word) : Option (List Word × Mem) :=
  tmfK1 p n vis pp cao cal pfo pfl fvo fvl mty (callW p n "get_app_args_f" [CWF, mty] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl mty : Word) (r r1 : List Word)
theorem tmfK1_some : tmfK1 p n vis pp cao cal pfo pfl fvo fvl mty (some (r, m)) =
    tmfK2 p n vis pp cao cal pfo pfl fvo fvl r (callW p n "get_app_fn_f" [CWF, mty] m) := rfl
theorem tmfK2_some : tmfK2 p n vis pp cao cal pfo pfl fvo fvl r1 (some (r, m)) =
    if r.headD 0 >>> 28 ≠ 3 then none
      else tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1 (callW p n "e_view" [r.headD 0] m) := rfl
theorem tmfK3_some : tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1 (some (r, m)) =
    tmfK6 (callW p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, r1.headD 0,
      r1.tail.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m) := rfl
end arms
attribute [ind_grind] tmfK1_some tmfK2_some tmfK3_some

set_option maxHeartbeats 1600000 in
theorem tmf_spec (p : Prog) (hp : p.lookup "target_major_of" = some targetMajorOf) (n : Nat)
    (s₀ : St) (vis pp cao cal pfo pfl fvo fvl mty : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, mty]
    ⦃fun r s' => LocEq s' s₀ ∧ tmfW p n s₀.mem vis pp cao cal pfo pfl fvo fvl mty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOf]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_args_f", callW_spec p n "get_app_fn_f", callW_spec p n "e_view",
      callW_spec p n "target_major_of_const"] <;>
    finish (gen := 40) (instances := 20000) [tmfW, rdW_eq]

end L.Ind
