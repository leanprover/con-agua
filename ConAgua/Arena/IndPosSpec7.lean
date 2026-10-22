import ConAgua.Arena.IndPosSpec6

/-! # `nestSeedOf` (lane `indproofs2`, helper `pos`): a resolved class's parameters, each through
`replaceApps` then `replaceFVars (.keyMap params holes)`, written into a fresh slice. -/

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
theorem sgK1_big (h : 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) = none := by simp [sgK1, h]
theorem sgK1_ok (h : ¬ 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) =
    sgK2 k ctx f dO dL q j (rxW k m1 f y) := by rw [sgK1, if_neg h]
theorem sgK2_some : sgK2 k ctx f dO dL q j (some (z, m2)) =
    sgGoW k (m2.set64 IW (q + j) z) ctx f dO dL q (j + 1) := by rw [sgK2]
end arms
attribute [ind_grind] sgGoW_done sgGoW_step sgK1_big sgK1_ok sgK2_some

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

/-- The lookups of `nest_seed_of`. -/
structure SgLook (p : Prog) : Prop where
  cr : CrLook p
  go : p.lookup "nest_seed_of_go" = some nestSeedOfGoL
  so : p.lookup "nest_seed_of" = some nestSeedOfL

section spec
variable (p : Prog) (L : SgLook p)

include L in
theorem posRp_spec (k : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ posRpW k s₀.mem no nl us b nn e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have C := L.cr
  cases k with
  | zero => rw [invoke_eq _ C.ra]; simp only [callFn, replaceApps]; vcgen [exec] <;> grind
  | succ k => exact replaceApps_spec p C.rx.hl C.rx.hk C.raf C.rap C.rgo C.rnd C.rcl C.ra k s₀ no nl us b nn e

include L in
theorem sgGo_spec (k : Nat) : ∀ (s₀ : St) (ctx f dO dL q j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_seed_of_go" [ctx, f, dO, dL, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ sgGoW k s₀.mem ctx f dO dL q j = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx f dO dL q j
    rw [invoke_eq _ L.go]; simp only [callFn, nestSeedOfGoL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx f dO dL q j
    have hrx := (rxSpec_all p L.cr.rx k).2.2.2.2.2.2.2
    rw [invoke_eq _ L.go]
    simp only [callFn, nestSeedOfGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        posRp_spec p L k, hrx, ih] <;>
      finish (gen := 20) [rdW_eq]

include L in
theorem nestSeedOf_spec (k : Nat) (s₀ : St) (ctx hO hL ind us dO dL nPc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_seed_of" [ctx, hO, hL, ind, us, dO, dL, nPc]
    ⦃fun r s' => LocEq s' s₀ ∧ sgW k s₀.mem ctx hO hL ind us dO dL nPc = some (r, s'.mem); ⊤⦄ := by
  have R := L.cr.rx
  rw [invoke_eq _ L.so]
  simp only [callFn, nestSeedOfL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      posRec5_specW p R.ha R.h5 k, posRec4_specW p R.ha R.h4 k, iwAlloc_specW p R.ha k, sgGo_spec p L k] <;>
    finish (gen := 20) [sgW, sgA, sgB, sgC, rdW_eq]

end spec

end L.Ind
