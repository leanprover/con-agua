module

import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all Init.Data.List.Control
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.IndPosSpec.NestOccAny

@[expose] public section

/-!
# NtyW

`noaW_ok` and the lemmas only it uses.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem noaW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis no nl lo hi : Word) (names : List NIdx)
    (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (xs : List EIdx) (r : List Word),
    noaW k m no nl lo hi off l = some (r, m') → StageR dn vis fe m a →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m off.toNat l.toNat = some xs → (∀ j < l.toNat, off.toNat + j < iwTop m) → PosMR m →
    ∃ b, (xs.anyM (fun x => ConRon.Arena.nestOcc names lo.toNat hi.toNat x)).run a = .ok (b, a) ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  induction k with
  | zero => intro m m' a off l xs r h; simp [noaW] at h
  | succ k ih =>
    intro m m' a off l xs r h hS hn hnb hxs hxb hP
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases hl0 : l = 0
    · rw [noaW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : xs = [] := by simpa [decHL, hslice?] using hxs.symm
      subst this
      exact ⟨false, rfl, hS, IWGrow.refl _, rfl, hP⟩
    rw [noaW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hxs2 := hxs
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hxs2
    obtain ⟨x, hx, xs', hxs', rfl⟩ := hxs2
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hxb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨mp0, hM0⟩ := hP.no
    rcases hno : noConstWf k m no nl lo hi (rdW (m.arr64 IW) off) with _ | ⟨b1, m1⟩ <;> rw [hno] at h; · simp [noaK] at h
    obtain ⟨c1, hrun1, hc1, hM1, hS1, hg1, hf1⟩ := noConstWf_ok k dn fe vis m m1 a no nl lo hi _ b1 names mp0 hno hS hxH
      hn (by omega) hM0
    have hP1 := hP.setNo hf1 ⟨∅, hM1⟩
    rw [decE_eq, hxd] at hrun1
    rw [List.anyM_cons]
    by_cases hb : b1 ≠ 0
    · rw [noaK_hit (h := hb)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : c1 = true := by rw [← hc1]; simpa using hb
      subst this
      refine ⟨true, ?_, hS1, hg1, rfl, hP1⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]; rfl
    · rw [noaK_miss (h := hb)] at h
      have : c1 = false := by rw [← hc1]; simpa using hb
      subst this
      obtain ⟨b, hrun, hS', hg', hr, hP'⟩ := ih m1 m' a (off + 1) (l - 1) xs' r h hS1
        (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hn) (by have := hg1.iw; omega)
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow hg1) (fun j hj => by have := hxb (j + 1) (by omega); omega)]
            simpa [decHL] using hxs')
        (fun j hj => by rw [hoff1, hl1] at *; have := hxb (j + 1) (by omega); have := hg1.iw; omega) hP1
      refine ⟨b, ?_, hS', hg1.trans hg', hr, hP'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ite_false]
      exact hrun

end L.Ind

end

end
