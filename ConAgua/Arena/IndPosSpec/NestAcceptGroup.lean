import ConAgua.Arena.IndPosSpec.GgW
import ConAgua.Arena.IndPosSpec.GrpAt
import ConAgua.Arena.IndPosSpec.NkcW

/-!
# NestAcceptGroup: `ConRon.Arena.nestAcceptGroup`

The refinement theorems `nestAcceptGroup_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem KsB.nil (m : Mem) (o : Nat) : KsB m o 0 [] := by simp [KsB, DecB, decPL]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Pointer slices decoded below the tops, element by element -/

section pslice
variable {α : Type} {f : Mem → Nat → Option α}

/-- **Two pointer slices concatenated** (`sl_append`). -/
theorem pos2_decB_append (hf : ∀ q, OMono (fun m => f m q)) {m m' : Mem} {o1 l1 o2 l2 q : Nat}
    {xs ys : List α} (h1 : DecB (fun m => decPL m (f m) o1 l1) m xs)
    (h2 : DecB (fun m => decPL m (f m) o2 l2) m ys) (hg : IWGrow m m') (hq : q + l1 + l2 ≤ iwTop m')
    (hw1 : ∀ i < l1, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o1 + i]?)
    (hw2 : ∀ i < l2, (m'.arr64 IW)[q + l1 + i]? = (m.arr64 IW)[o2 + i]?) :
    DecB (fun m => decPL m (f m) q (l1 + l2)) m' (xs ++ ys) := by
  obtain ⟨hl1, he1⟩ := pos2_decB_elems h1
  obtain ⟨hl2, he2⟩ := pos2_decB_elems h2
  have := pos2_decB_of_elems (m := m') (o := q) (xs := xs ++ ys) (f := f) fun j hj => by
    simp only [List.length_append] at hj
    by_cases hjl : j < xs.length
    · obtain ⟨v, a, b, c⟩ := he1 j hjl
      refine ⟨v, by omega, ?_, by rw [List.getElem_append_left hjl]; exact (DecB.grow (hf v) hg c)⟩
      simp only [iwN, nat?, iwA] at b ⊢; rw [hw1 j (by omega)]; exact b
    · obtain ⟨v, a, b, c⟩ := he2 (j - xs.length) (by omega)
      refine ⟨v, by omega, ?_, by rw [List.getElem_append_right (by omega)]; exact (DecB.grow (hf v) hg c)⟩
      simp only [iwN, nat?, iwA] at b ⊢
      have := hw2 (j - xs.length) (by omega)
      rw [show q + l1 + (j - xs.length) = q + j by omega] at this
      rw [this]; exact b
  simpa [hl1, hl2] using this

end pslice

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_accept_group` is `nestAcceptGroup`** over the decoded group and key slice. -/
theorem nagW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL : Word) (ds : List EIdx)
    (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL kO kL : Word) (grp : List (NIdx × EIdx))
    (keys : Array NestKey) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    KsB m kO.toNat kL.toNat keys.toList → kO.toNat + kL.toNat ≤ iwTop m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      KsB m' (r.headD 0).toNat (r.tail.headD 0).toNat (nestAcceptGroup (decI us) ds grp keys).toList ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a gO gL kO kL grp keys r h; simp [nagW] at h
  | succ n ih =>
    intro m m' a gO gL kO kL grp keys r h hS hds hgl hgb hgrp hks hkb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hg0 : gL = 0
    · rw [nagW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨hS, IWGrow.refl _, by simpa [nestAcceptGroup] using hks, by simpa using hkb⟩
    rw [nagW_cons (h := hg0)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, h1, h2, h3, h4, h5, -, -, -⟩ := hgrp 0 (by simp)
    have hrw : rdW (m.arr64 IW) gO = w := by simp only [Nat.add_zero] at h1; simp [rdW, h1]
    have hrc : rdW (m.arr64 IW) w = cw := by simp [rdW, h3]
    rw [hrw, hrc] at h
    simp only [List.getElem_cons_zero] at h5
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [nagK1] at h
    rw [nagK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec h4 hus (by omega) hget1 hds1
    have hks1 := hks.grow hg1
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := word_add_toNat (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hgrp' : GrpAt m1 (gO + 1).toNat grp' := by
      rw [hgO1]
      have g1 := hgrp.grow (by simpa using hgb) hg1
      intro i hi
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := g1 (i + 1) (by simp; omega)
      exact ⟨a1, a2, a3, by rw [show UInt64.toNat gO + 1 + i = UInt64.toNat gO + (i + 1) by omega]; exact a4, a5, a6, a7, by simpa using a8, a9, a10,
        by simpa using a11⟩
    rcases hc : nkcW n m1 kO kL key with _ | b <;> rw [hc] at h; · simp [nagK2] at h
    have hb := nkcW_ok key _ n m1 kO kL b keys.toList hc hks1 hK htop1
    rw [h5] at hb
    by_cases hbn : b ≠ 0
    · rw [nagK2_hit (h := hbn)] at h
      have hin : keys.toList.contains ⟨c, decI us, ds⟩ = true := by
        cases e : keys.toList.contains ⟨c, decI us, ds⟩ with
        | true => rfl
        | false => rw [e] at hb; exact absurd hb (by simpa using hbn)
      obtain ⟨hS', hg', hk', hb'⟩ := ih m1 m' a (gO + 1) (gL - 1) kO kL grp' keys r h hS1 hds1 hgL1
        (by rw [hgO1]; have := hg1.1; omega) hgrp' hks1 (by have := hg1.1; omega)
      refine ⟨hS', hg1.trans hg', ?_, hb'⟩
      simp only [nestAcceptGroup, ← Array.contains_toList, hin, ite_true]
      exact hk'
    · rw [nagK2_miss (h := hbn)] at h
      have hout : keys.toList.contains ⟨c, decI us, ds⟩ = false := by
        cases e : keys.toList.contains ⟨c, decI us, ds⟩ with
        | false => rfl
        | true => rw [e] at hb; simp at hbn hb; rw [hbn] at hb; exact absurd hb (by decide)
      rcases hsn : snocW n m1 kO kL key with _ | ⟨r2, m2⟩ <;> rw [hsn] at h; · simp [nagK3] at h
      rw [nagK3_some] at h
      obtain ⟨hS2, hg2, hr0, hr1, ht2, hw2, hx2⟩ := snocW_words hsn hS1 (by have := hg1.1; omega)
      have hks2 : KsB m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat (keys.push ⟨c, decI us, ds⟩).toList := by
        rw [hr0, hr1, Array.toList_push]
        exact pos2_decB_snoc decNK_mono hks1 hg2 (by omega) hw2 hx2 (by rw [← h5]; exact DecB.grow (decNK_mono _) hg2 hK)
      obtain ⟨hS', hg', hk', hb'⟩ := ih m2 m' a (gO + 1) (gL - 1) _ _ grp' _ r h hS2
        (DecB.grow (OMono.decHL _ _) hg2 hds1) hgL1
        (by rw [hgO1]; have := hg1.1; have := hg2.1; omega) (hgrp'.grow (by rw [hgO1]; have := hg1.1; omega) hg2) hks2
        (by rw [hr0, hr1]; omega)
      refine ⟨hS', (hg1.trans hg2).trans hg', ?_, hb'⟩
      simp only [nestAcceptGroup, ← Array.contains_toList, hout, Bool.false_eq_true, ite_false]
      exact hk'

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_accept_group` refines `nestAcceptGroup`** (a pure twin: the key slice it returns
decodes as the accepted keys). -/
@[refines ConRon.Arena.nestAcceptGroup]
theorem nestAcceptGroup_refines (p : Prog) (L : NagLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL gO gL kO kL : Word)
    (ds : List EIdx) (grp : List (NIdx × EIdx)) (keys : Array NestKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hus : H us) (hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (hgl : gL.toNat = grp.length) (hgb : gO.toNat + grp.length ≤ iwTop s₀.mem)
    (hgrp : GrpAt s₀.mem gO.toNat grp) (hks : KsB s₀.mem kO.toNat kL.toNat keys.toList)
    (hkb : kO.toNat + kL.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_accept_group" [us, dO, dL, gO, gL, kO, kL]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      KsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat (nestAcceptGroup (decI us) ds grp keys).toList ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (nestAcceptGroup_spec p L n s₀ us dO dL gO gL kO kL) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨h1, h2, h3, h4⟩ := nagW_ok dn vis fe us dO dL ds hus n _ _ a₀ gO gL kO kL grp keys _ hm hS hds hgl hgb
    hgrp hks hkb
  exact ⟨hlc, h1, h2, by simpa using h3, by simpa using h4⟩

end L.Ind

end
