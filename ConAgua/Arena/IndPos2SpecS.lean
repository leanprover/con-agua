import ConAgua.Arena.IndPos2SpecR

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the relational steps,
`nest_fields` and `nest_ctors_walk`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `Π` handle's view: its domain and body, decoded. -/
theorem pos2_forall_view {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {w : Word} (hS : StageR dn vis fe m a) (hw : H w) (h6 : w >>> 28 = 6) (hne : eViewW m w ≠ []) :
    ∃ d b, eViewW m w = [6, d, b, 0] ∧ H d ∧ H b ∧
      (viewBind (decI w)).run a = .ok (some (decI d, decI b), a) ∧ (decI w : EIdx).tag = ETag.forallE := by
  obtain ⟨hvok, hew⟩ := eViewW_forall m w h6 hne
  obtain ⟨-, hty, hb⟩ := view_forall m a hS.1.arena.1 w hw hvok h6
  have hvb := viewBind_forall m a hS.1.arena.1 w hw hvok h6
  exact ⟨_, _, hew, hty, hb, by rw [viewBind_run']; simp only [← decE_eq]; rw [hvb],
    (decE_tag_forall w hw).mpr h6⟩

theorem pos2_word_add {x y : Word} (h : ¬ x + y < x) : (x + y).toNat = x.toNat + y.toNat := by
  rcases Nat.lt_or_ge (x.toNat + y.toNat) (2 ^ 64) with hl | hl
  · exact word_add_toNat hl
  · exfalso; apply h; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
    have := x.toNat_lt; have := y.toNat_lt; omega

theorem pos2_word_succ {x : Word} (h : ¬ x + 1 = 0) : (x + 1).toNat = x.toNat + 1 := by
  rcases Nat.lt_or_ge (x.toNat + 1) (2 ^ 64) with hl | hl
  · exact word_add_toNat (by simpa using hl)
  · exfalso; apply h; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; have := x.toNat_lt; simp; omega

theorem pos2_word_pred {x : Word} (h : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

section steps
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hM : PosMemo dn vis fe)
  (hcs : CtorSums fe)

include hM in
theorem fieldsOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    FieldsOK dn vis fe (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds r h hS hW hcur hns hks hkb hnd hndb
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbFieldsW_succ] at h
  by_cases h0 : nF = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst h0
    refine ⟨(ks, nds, decI cur, NS), a, by rw [ConRon.Arena.nestFields.eq_def]; rfl, hS, IWGrow.refl _, hks, hkb, hnd, hndb,
      hcur, rfl, hns, by simp, by simp, by simp⟩
  rw [if_neg h0] at h
  by_cases h6 : cur >>> 28 ≠ 6
  · rw [if_pos h6] at h; cases h
  rw [if_neg h6] at h
  have h6' : cur >>> 28 = 6 := by simpa using h6
  by_cases hov : base + j < base
  · rw [if_pos hov] at h; cases h
  rw [if_neg hov] at h
  by_cases hov1 : base + j + 1 = 0
  · rw [if_pos hov1] at h; cases h
  rw [if_neg hov1] at h
  by_cases hev : eViewW m cur = []
  · rw [if_pos hev] at h; cases h
  rw [if_neg hev] at h
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hcur h6' hev
  rw [hv] at h
  simp only [List.tail_cons, List.headD_cons] at h
  have hbj : (base + j).toNat = base.toNat + j.toNat := pos2_word_add hov
  have hbj1 : (base + j + 1).toNat = base.toNat + j.toNat + 1 := by rw [pos2_word_succ hov1, hbj]
  obtain ⟨nF', hnF'⟩ : ∃ nF', nF.toNat = nF' + 1 := ⟨nF.toNat - 1, by
    have : nF.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  -- the field's domain walked
  cases hp : nbPosW n m vis ctx fu po pl (base + j) 0 d ns with
  | none => rw [hp] at h; simp [nbFieldsK1] at h
  | some pr =>
  obtain ⟨rp, m1⟩ := pr
  rw [hp, nbFieldsK1_some] at h
  simp only [List.tail_cons, List.headD_cons] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hk1, hnd1H, hnd1, hns1⟩ := hPos m m1 a ctx fu po pl (base + j) 0 d ns c prog NS rp
    hp hS hW hd hns
  -- the field's variable
  cases hfv : fvinternW m1 (base + j) d with
  | none => rw [hfv] at h; simp [nbFieldsK2] at h
  | some pr2 =>
  obtain ⟨fv, m2⟩ := pr2
  rw [hfv, nbFieldsK2_some] at h
  by_cases hfvb : 4294967296 ≤ fv
  · rw [if_pos hfvb] at h; cases h
  rw [if_neg hfvb] at h
  simp only [List.tail_cons, List.headD_cons] at h
  have hfvH : H fv := by
    have : ¬ (4294967296 : Word).toNat ≤ fv.toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (base + j) d hd hfv
  -- the body opened
  cases hin : stubM "instantiate1_fast" m2 [CWF, b, fv, 0] with
  | none => rw [hin] at h; simp [nbFieldsK3] at h
  | some pr3 =>
  obtain ⟨rb, m3⟩ := pr3
  rw [hin, nbFieldsK3_some] at h
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := instantiate1Fast_spec dn vis fe CWF b fv 0 hb hfvH m2 m3 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have hg13 := (hg1.trans hg2).trans hg3
  -- the kind and the walked domain appended
  cases hs1 : snocW n m3 kO kL (rp.headD 0) with
  | none => rw [hs1] at h; simp [nbFieldsK4] at h
  | some pr4 =>
  obtain ⟨rk, m4⟩ := pr4
  rw [hs1, nbFieldsK4_some] at h
  obtain ⟨hS4, hg4, hk40, hk41, ht4, hw4, hx4⟩ := snocW_words hs1 hS3 (by have := hg13.1; omega)
  have hks4 : KlB m4 (rk.headD 0).toNat (rk.tail.headD 0).toNat (ks ++ [x1.1]) := by
    rw [hk40, hk41]
    exact KlB.snoc ((hks.grow hg13)) hg4 (by omega) hw4 hx4 hk1
  cases hs2 : snocW n m4 dO dL (rp.tail.headD 0) with
  | none => rw [hs2] at h; simp [nbFieldsK5] at h
  | some pr5 =>
  obtain ⟨rd, m5⟩ := pr5
  rw [hs2, nbFieldsK5_some] at h
  have hg14 := hg13.trans hg4
  obtain ⟨hrd, hnd5, hg5, -, hl5, ht5⟩ := snocW_decK hs2 hS4.2.2.2.1 hS4.2.2.2.2.2 (by have := hg14.1; omega)
    hnd1H (by rw [decHL_agree (RdS.of_grow hg14) (fun i hi => by omega)]; exact hnd)
  have hS5 := snocW_stage hs2 hS4
  have hg15 := hg14.trans hg5
  -- the rest of the fields
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (by have := (base + j + 1).toNat_lt; simp; omega)
  have hnF1 : (nF - 1).toNat = nF' := by rw [pos2_word_pred h0]; omega
  obtain ⟨x, a', hrun, hS', hg', hK', hKb', hD', hDb', hcH', hcd', hns', hl1, hl2, hov'⟩ :=
    hFields m5 m' a3 ctx fu po pl base (nF - 1) (j + 1) (rb.headD 0) (rp.tail.tail.headD 0) (rk.headD 0)
      (rk.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) c prog x1.2.2 (ks ++ [x1.1]) (nds ++ [decI (rp.tail.headD 0)])
      r h hS5 (hW.grow (hg15.trans (IWGrow.refl _))) (by simpa using hb2H)
      ((hns1.grow (hg2.trans hg3) (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow (hg4.trans hg5)
        (Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1))
      (hks4.grow hg5) (by rw [hk40, hk41]; have := hg5.1; omega)
      (by rw [hrd]; simpa using hnd5) (by rw [hrd]; simp only [List.headD_cons, List.tail_cons]; omega)
  refine ⟨x, a', ?_, hS', hg15.trans hg', hK', hKb', hD', hDb', hcH', hcd', hns', ?_, ?_, ?_⟩
  · rw [hnF', ConRon.Arena.nestFields.eq_def]
    simp only [htag, beq_self_eq_true, if_true, StateT.run_bind, hvb, except_ok_bind]
    have e1 := hrun1; simp only [hbj, UInt64.toNat_zero] at e1
    have e2 : (internFVarE (base.toNat + j.toNat) (decI d)).run a1 = .ok (decI fv, a2) := by
      simpa [internFVarE, hbj, decE_eq] using hrun2
    have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI fv) 0).run a2 = .ok (b2, a3) := by simpa using hrun3
    rw [e1]; simp only [except_ok_bind]; rw [e2]; simp only [except_ok_bind]; rw [e3]; simp only [except_ok_bind]
    rw [hnF1, hj1, hb2d, hnd1] at hrun
    exact hrun
  · rw [hl1]; simp; omega
  · rw [hl2]; simp; omega
  · right; rcases hov' with h' | h'
    · rw [hnF1] at h'; subst h'; have := (base + j + 1).toNat_lt; omega
    · rw [hj1, hnF1] at h'; omega

end steps

end L.Ind
