import ConAgua.Arena.Abs1Refine
import ConAgua.Arena.IndPartsSpec.EqW
import ConRon.Bridge.Grind

/-!
# EqWDec

`tkArgs`, `tkTele`, `eqW_dec`.
-/

noncomputable section

/-!
# `RecCheck`: `targetK53`, the relational side (lane `indproofs3`, helper `rec`)

The twin split at the L functions' boundaries (`tkTele`, `tkHeads`, `tkArgs`, verbatim pieces of
`targetK53`; `tk53_eq` puts them back together), each simulated by its word model.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin's pieces -/

/-- `targetK53`'s argument check. -/
def tkArgs (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx) (Mc : TargetMajor) (I' : NIdx)
    (us' : LsIdx) (la ma : List EIdx) : AM Bool := do
  let le ← (la.drop Mc.nPc).mapM ConRon.Arena.eraseFVarTys
  let me ← (ma.drop Mc.nPc).mapM ConRon.Arena.eraseFVarTys
  if le != me then pure false
  else
    let lp := la.take Mc.nPc
    let hd ← ConRon.Arena.internConstE I' us'
    let app ← ConRon.Arena.mkAppN hd lp
    if ← ConRon.Arena.nestOcc p.memberNames 0 0 app then
      ConRon.Arena.targetClassMatch V fe p formerTys Mc.pfvs Mc.lvls Mc.ds us' lp
    else pure false

/-- `targetK53`'s telescope check. -/
def tkTele (teleW tele : List EIdx) : AM Bool := do
  let ew ← teleW.mapM fun b => ConRon.Arena.eraseFVarTys b
  let et ← tele.mapM fun b => ConRon.Arena.eraseFVarTys b
  pure (ew == et)

/-! ## `erase_each`, `target_k53_tele` simulated -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- Word-slice equality of two decoded handle slices is the lists' equality. -/
theorem eqW_dec {n : Nat} {m : Mem} {o1 l1 o2 l2 e : Word} {xs1 xs2 : List EIdx}
    (h : eqW n m o1 l1 o2 l2 = some e)
    (h1 : decHL m o1.toNat l1.toNat = some xs1) (hb1 : o1.toNat + l1.toNat < 2 ^ 64)
    (h2 : decHL m o2.toNat l2.toNat = some xs2) (hb2 : o2.toNat + l2.toNat < 2 ^ 64) :
    e = if xs1 = xs2 then 1 else 0 := by
  obtain ⟨ws1, s1, e1, hw1⟩ := slR_of_decHL m _ _ _ h1 hb1
  obtain ⟨ws2, s2, e2, hw2⟩ := slR_of_decHL m _ _ _ h2 hb2
  simp only [UInt64.ofNat_toNat] at s1 s2
  rw [eqW_ok n m o1 l1 o2 l2 e ws1 ws2 s1 s2 h, e1, e2]
  have : ws1 = ws2 ↔ ws1.map (fun w => (decI w : EIdx)) = ws2.map decI := by
    constructor
    · intro h; rw [h]
    · intro h
      apply List.ext_getElem
      · simpa using congrArg List.length h
      · intro i hi1 hi2
        have := congrArg (·[i]?) h
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
          Option.map_some, Option.some.injEq] at this
        exact decE_inj _ _ (hw1 _ (List.getElem_mem hi1)) (hw2 _ (List.getElem_mem hi2)) this
  by_cases hq : ws1 = ws2
  · simp [hq]
  · rw [ite_eq_right hq, ite_eq_right (fun h => hq (this.mpr h))]

end rel

end L.Ind

end
end
