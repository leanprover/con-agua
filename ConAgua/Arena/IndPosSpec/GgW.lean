import ConAgua.Arena.IndPosSpec.NestOccAny
import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.IndGrindAttr

/-!
# GgW

`snocW_words`, `nitWf`, `ggW`, `ggK1`, `ggK2`, `ggK3` and the lemmas only they use.
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
  obtain ⟨hr, hl1, hqt, -, hg, htop, hget⟩ := snocW_core h hS.2.2.2.1 hS.2.2.2.2.2 hsrc
  subst hr
  refine ⟨snocW_stage h hS, hg, by simp [hqt], by simp [hl1], by omega, fun i hi => ?_, ?_⟩
  · rw [hget, ite_eq_right (by omega), ite_eq_left (by omega)]; congr 2; omega
  · rw [hget, ite_eq_left rfl]

/-- `nest_inst_type` at any exec fuel. -/
def nitWf (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, hi, key => nitW cR k m vis ctx hi key

mutual
def ggW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, hi, us, dO, dL, cO, cL, gO, gL =>
    if cL = 0 then some ([gO, gL], m)
    else ggK1 cR k vis ctx hi us dO dL cO cL gO gL (rdW (m.arr64 IW) cO)
      (posRecW m [rdW (m.arr64 IW) cO, us, dO, dL])
def ggK1 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL gO gL c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => ggK2 cR k vis ctx hi us dO dL cO cL gO gL c (nitWf cR k m1 vis ctx hi key)
def ggK2 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL gO gL c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ggK3 cR k vis ctx hi us dO dL cO cL gO gL (posRecW m2 [c, r2.tail.headD 0])
def ggK3 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL gO gL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (pr, m3) => ggK4 cR k vis ctx hi us dO dL cO cL (snocW k m3 gO gL pr)
def ggK4 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ggW cR k m4 vis ctx hi us dO dL (cO + 1) (cL - 1) (r4.headD 0) (r4.tail.headD 0)
end

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 : Mem) (vis ctx hi us dO dL cO cL gO gL c key pr : Word) (r2 r4 : List Word)
theorem ggW_nil (h : cL = 0) : ggW cR (k + 1) m vis ctx hi us dO dL cO cL gO gL = some ([gO, gL], m) := by
  simp [ggW, h]
theorem ggW_cons (h : ¬ cL = 0) : ggW cR (k + 1) m vis ctx hi us dO dL cO cL gO gL =
    ggK1 cR k vis ctx hi us dO dL cO cL gO gL (rdW (m.arr64 IW) cO)
      (posRecW m [rdW (m.arr64 IW) cO, us, dO, dL]) := by simp [ggW, h]
theorem ggK1_some : ggK1 cR k vis ctx hi us dO dL cO cL gO gL c (some (key, m1)) =
    ggK2 cR k vis ctx hi us dO dL cO cL gO gL c (nitWf cR k m1 vis ctx hi key) := by rw [ggK1]
theorem ggK2_some : ggK2 cR k vis ctx hi us dO dL cO cL gO gL c (some (r2, m2)) =
    ggK3 cR k vis ctx hi us dO dL cO cL gO gL (posRecW m2 [c, r2.tail.headD 0]) := by rw [ggK2]
theorem ggK3_some : ggK3 cR k vis ctx hi us dO dL cO cL gO gL (some (pr, m3)) =
    ggK4 cR k vis ctx hi us dO dL cO cL (snocW k m3 gO gL pr) := by rw [ggK3]
theorem ggK4_some : ggK4 cR k vis ctx hi us dO dL cO cL (some (r4, m4)) =
    ggW cR k m4 vis ctx hi us dO dL (cO + 1) (cL - 1) (r4.headD 0) (r4.tail.headD 0) := by rw [ggK4]
end arms
attribute [ind_grind] ggW_nil ggW_cons ggK1_some ggK2_some ggK3_some ggK4_some

end L.Ind

end
