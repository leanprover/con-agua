import ConAgua.Arena.IndPosSpec.CanonW
import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.IndGrindAttr

/-!
# GgW

`snocW_words`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `sl_snoc` over words -/

/-- **`sl_snoc` keeps the stage relation**: the pool grew by the new slice, whose words are the
source's and `x` (any words: pointers too). -/
theorem snocW_words {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word}
    (h : snocW n m o l x = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ (r.headD 0).toNat = iwTop m ∧
      (r.tail.headD 0).toNat = l.toNat + 1 ∧ iwTop m' = iwTop m + l.toNat + 1 ∧
      (∀ i < l.toNat, (m'.arr64 IW)[iwTop m + i]? = (m.arr64 IW)[o.toNat + i]?) ∧
      (m'.arr64 IW)[iwTop m + l.toNat]? = some x := by
  obtain ⟨hr, hl1, hqt, -, hg, htop, hget⟩ := snocW_core h hS.iw.2.2.1 hS.iw.2.2.2.2 hsrc
  subst hr
  refine ⟨snocW_stage h hS, hg, by simp [hqt], by simp [hl1], by omega, fun i hi => ?_, ?_⟩
  · rw [hget, ite_eq_right (by omega), ite_eq_left (by omega)]; congr 2; omega
  · rw [hget, ite_eq_left rfl]

end L.Ind

end
