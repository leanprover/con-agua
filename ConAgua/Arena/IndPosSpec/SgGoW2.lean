import ConAgua.Arena.IndPosSpec.RpGoStep
import ConAgua.Arena.IndPosSpec.RxMapW
import ConAgua.Arena.IndGrindAttr

/-!
# SgGoW2

`posRpW`, `sgGoW`, `sgK1`, `sgK2`, `sgGoW_done`, `sgGoW_step` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `replace_apps` at any exec fuel. -/
def posRpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, us, b, nn, e => rpConstW k m no nl us b nn e

mutual
def sgGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, ctx, f, dO, dL, q, j =>
    if dL ≤ j then some m
    else sgK1 k ctx f dO dL q j (posRpW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (rdW (m.arr64 IW) (ctx + 10)) 0 (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 IW) (dO + j)))
def sgK1 (k : Nat) (ctx f dO dL q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (y, m1) => if 4294967296 ≤ y then none else sgK2 k ctx f dO dL q j (rxW k m1 f y)
def sgK2 (k : Nat) (ctx f dO dL q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (z, m2) => sgGoW k (m2.set64 IW (q + j) z) ctx f dO dL q (j + 1)
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (ctx f dO dL q j y z : Word)
theorem sgGoW_done (h : dL ≤ j) : sgGoW (k + 1) m ctx f dO dL q j = some m := by simp [sgGoW, h]
theorem sgGoW_step (h : ¬ dL ≤ j) : sgGoW (k + 1) m ctx f dO dL q j =
    sgK1 k ctx f dO dL q j (posRpW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (rdW (m.arr64 IW) (ctx + 10)) 0 (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 IW) (dO + j))) := by
  simp [sgGoW, h]
theorem sgK1_ok (h : ¬ 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) =
    sgK2 k ctx f dO dL q j (rxW k m1 f y) := by rw [sgK1, ite_eq_right h]
theorem sgK2_some : sgK2 k ctx f dO dL q j (some (z, m2)) =
    sgGoW k (m2.set64 IW (q + j) z) ctx f dO dL q (j + 1) := by rw [sgK2]
end arms
attribute [ind_grind] sgGoW_done sgGoW_step sgK1_ok sgK2_some

def sgC (nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m4) => some ([key, nPc], m4)
def sgB (k : Nat) (ctx f ind us dO dL nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => match sgGoW k m2 ctx f dO dL q 0 with
    | none => none
    | some m3 => sgC nPc (posRecW m3 [ind, us, q, dL])
def sgA (k : Nat) (ctx ind us dO dL nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m1) => sgB k ctx f ind us dO dL nPc (allocW m1 dL)
/-- The model of `nest_seed_of` at exec fuel `k + 1`. -/
def sgW (k : Nat) (m : Mem) (ctx hO hL ind us dO dL nPc : Word) : Option (List Word × Mem) :=
  sgA k ctx ind us dO dL nPc (posRecW m [1, rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8), hO, hL])

end L.Ind

end
