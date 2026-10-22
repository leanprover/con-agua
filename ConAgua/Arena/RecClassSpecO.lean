import ConAgua.Arena.RecClassSpecN

/-!
# `RecClass`: `classGenRule` — the relational lemmas (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The minor premise's slot -/

/-- The slot `classGenRule` looks for. -/
def rec2SlotHit (c : Nat) (C : NIdx) : ClassSlot → Bool
  | .minor c' C' _ => c' == c && C' == C
  | .motive _ => false

theorem fsgW_ok (n : Nat) : ∀ (m m' : Mem) (so sl j c cn : Word) (r : List Word) (slots : List ClassSlot),
    fsgW n m so sl j c cn = some (r, m') → decPL m (decCS m) so.toNat sl.toNat = some slots →
    (m.arr64 IW).size < 2 ^ 64 → H cn → j.toNat ≤ sl.toNat →
    ∀ P : Nat × ClassSlot → Bool, (∀ k s', P (k, s') = rec2SlotHit c.toNat (decI cn) s') →
    m' = m ∧
      (((List.range' j.toNat (sl.toNat - j.toNat)).zip (slots.drop j.toNat)).find? P = none → r.headD 0 = 0) ∧
      (∀ k s', ((List.range' j.toNat (sl.toNat - j.toNat)).zip (slots.drop j.toNat)).find? P = some (k, s') →
        r.headD 0 = 1 ∧ r.tail.headD 0 = UInt64.ofNat k) := by
  induction n with
  | zero => intro m m' so sl j c cn r slots h; simp [fsgW] at h
  | succ n ih =>
  intro m m' so sl j c cn r slots h hsl hsz hcn hj P hP
  have hlen := decPL_length m hsl
  by_cases hend : sl ≤ j
  · rw [fsgW_end (h := hend)] at h
    cases h
    have : sl.toNat - j.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hend; omega
    refine ⟨rfl, fun _ => rfl, fun k s' e => ?_⟩
    rw [this] at e; simp at e
  have hlt : j.toNat < sl.toNat := by
    have : ¬ sl.toNat ≤ j.toNat := fun x => hend (UInt64.le_iff_toNat_le.mpr x)
    omega
  obtain ⟨p, hp, hdp⟩ := decPL_getH m hsl j.toNat hlt
  have plt := (iwN_rdW hp (by have := iwN_lt hp; omega)).2
  have hp' : (UInt64.ofNat p : Word).toNat = p := UInt64.toNat_ofNat_of_lt' plt
  have ep : rdW (m.arr64 IW) (so + j) = UInt64.ofNat p := by
    have := (rec2RdN (w := so) (k := j.toNat) hp hsz).1; simpa using this
  have hzip : (List.range' j.toNat (sl.toNat - j.toNat)).zip (slots.drop j.toNat) =
      (j.toNat, slots[j.toNat]'(by omega)) ::
        (List.range' (j.toNat + 1) (sl.toNat - (j + 1).toNat)).zip (slots.drop (j + 1).toNat) := by
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; have := sl.toNat_lt; omega
    rw [hj1, show sl.toNat - j.toNat = (sl.toNat - (j.toNat + 1)) + 1 by omega, List.range'_succ,
      List.drop_eq_getElem_cons (by omega)]
    rfl
  -- the slot's words
  have hcond : (rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j)) = 1 ∧
      rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 1) = c ∧ rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 2) = cn) ↔
      rec2SlotHit c.toNat (decI cn) (slots[j.toNat]'(by omega)) = true := by
    rw [ep]
    generalize slots[j.toNat]'(by omega) = sl0 at hdp
    cases sl0 with
    | motive key =>
      have h0 := rec2DecCS_mot hdp
      obtain ⟨e0, -⟩ := rec2RdN (w := UInt64.ofNat p) (k := 0) (by simpa [hp'] using h0) hsz
      simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e0
      simp [rec2SlotHit, e0]
    | minor c' C ihs =>
      obtain ⟨h1, hc, hC⟩ := rec2DecCS_min hdp
      obtain ⟨e1, -⟩ := rec2RdN (w := UInt64.ofNat p) (k := 0) (by simpa [hp'] using h1) hsz
      obtain ⟨ec, tc⟩ := rec2RdN (w := UInt64.ofNat p) (k := 1) (by rw [hp']; exact hc) hsz
      obtain ⟨cw, ecw, hcwH, hcwd⟩ := iwH_rdW_at (w := UInt64.ofNat p) (k := 2) (by rw [hp']; exact hC) hsz
      simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero, show UInt64.ofNat 1 = (1 : Word) from rfl,
        show UInt64.ofNat 2 = (2 : Word) from rfl] at e1 ec ecw
      rw [e1, ec, ecw]
      have c'lt := (iwN_rdW_at (w := UInt64.ofNat p) (k := 1) (by rw [hp']; exact hc) hsz).2
      simp only [rec2SlotHit, Bool.and_eq_true, beq_iff_eq, true_and]
      constructor
      · rintro ⟨e1', e2'⟩
        refine ⟨?_, ?_⟩
        · rw [← e1']; exact tc.symm
        · rw [← hcwd, e2']
      · rintro ⟨e1', e2'⟩
        refine ⟨?_, rec2DecI_inj hcwH hcn (by rw [hcwd, e2'])⟩
        apply UInt64.toNat_inj.mp; rw [tc, e1']
  rw [hzip, List.find?_cons, hP]
  by_cases hh : rec2SlotHit c.toNat (decI cn) (slots[j.toNat]'(by omega)) = true
  · rw [fsgW_hit (h := hend) (h2 := hcond.mpr hh)] at h
    cases h
    refine ⟨rfl, fun e => ?_, fun k s' e => ?_⟩
    · simp [hh] at e
    · simp [hh] at e; obtain ⟨rfl, -⟩ := e; exact ⟨rfl, by simp⟩
  · rw [fsgW_miss (h := hend) (h2 := fun x => hh (hcond.mp x))] at h
    cases hr : fsgW n m so sl (j + 1) c cn with
    | none => rw [hr] at h; cases h
    | some rm =>
    obtain ⟨r', m''⟩ := rm
    rw [hr, fcK_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; have := sl.toNat_lt; omega
    obtain ⟨hm, h1, h2⟩ := ih m m'' so sl (j + 1) c cn r' slots hr hsl hsz hcn (by omega) P hP
    simp only [Bool.not_eq_true] at hh
    simp only [hh, if_false]
    rw [hj1] at h1 h2
    rw [hj1]
    simp only [List.headD_cons, List.tail_cons]
    exact ⟨hm, h1, h2⟩

/-! ## The prefix variables -/

theorem pvW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (g rP : Word)
    (hns : G.nP + G.slots.length < 2 ^ 64) (f : Nat → AM EIdx)
    (hf : ∀ i, f i = if i < G.nP then ConRon.Arena.exprGetD G.params i else G.slotVar (i - G.nP)) (n : Nat) :
    ∀ (m : Mem) (a : AState) (i : Word), StageR dn vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    i.toNat ≤ rP.toNat →
    RSim (pvW n m g rP i) ((List.range' i.toNat (rP.toNat - i.toNat)).mapM f) a
      (fun b a' xs => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
        decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some xs ∧
        (b.1.headD 0).toNat + (b.1.tail.headD 0).toNat ≤ iwTop b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [pvW] at hb
  | succ n ih =>
  intro m a i hS hG hi
  have hsz := hS.2.2.2.1
  by_cases hend : rP ≤ i
  · rw [pvW_end (h := hend)]
    have : rP.toNat - i.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hend; omega
    rw [this]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩
  have hlt : i.toNat < rP.toNat := by
    have : ¬ rP.toNat ≤ i.toNat := fun x => hend (UInt64.le_iff_toNat_le.mpr x)
    omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; have := rP.toNat_lt; omega
  rw [pvW_step (h := hend), show rP.toNat - i.toNat = (rP.toNat - (i.toNat + 1)) + 1 by omega, List.range'_succ,
    List.mapM_cons, hf]
  obtain ⟨hnP, -⟩ := rec2CG_get (hG.get (decCG_mono _))
  obtain ⟨e0, t0⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl] at e0
  rw [e0]
  have hy : RSim (if i < UInt64.ofNat G.nP then
        fuelW n (exprGetDW m (rdW (m.arr64 IW) (g + 1)) (rdW (m.arr64 IW) (g + 2)) i)
      else slotVarW m g (i - UInt64.ofNat G.nP))
      (if i.toNat < G.nP then ConRon.Arena.exprGetD G.params i.toNat else G.slotVar (i.toNat - G.nP)) a
      (KP dn vis fe m decW0E) := by
    by_cases hp : i.toNat < G.nP
    · have hw : i < UInt64.ofNat G.nP := UInt64.lt_iff_toNat_lt.mpr (by rw [t0]; exact hp)
      rw [if_pos hw, if_pos hp]
      have hG' : decCG (truncM m) g.toNat = some G := hG
      simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hG'
      obtain ⟨nP, hnP', ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, hGe⟩ := hG'
      obtain ⟨o1, l1, h1, h2, hpd⟩ := decAt_some hps
      obtain ⟨-, h1m⟩ := rec2IwN_trunc h1
      obtain ⟨-, h2m⟩ := rec2IwN_trunc h2
      obtain ⟨e1, t1⟩ := rec2RdN (w := g) (k := 1) h1m hsz
      obtain ⟨e2, t2⟩ := rec2RdN (w := g) (k := 2) (by simpa [Nat.add_assoc] using h2m) hsz
      simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1 e2
      rw [e1, e2]
      have hpdB : DecB (fun m => (decHL m o1 l1 : Option (List EIdx))) m G.params := by rw [← hGe]; exact hpd
      have o1lt := (iwN_rdW h1m (by have := iwN_lt h1m; omega)).2
      exact rec2SimExprGetD n hS (by rw [t1, t2]; exact hpdB.get (OMono.decHL _ _))
        (by rw [t1, t2]; exact rec2DecB_HL_bound hpdB hsz hS.2.1 o1lt)
    · have hw : ¬ i < UInt64.ofNat G.nP := fun x => hp (by have := UInt64.lt_iff_toNat_lt.mp x; rwa [t0] at this)
      rw [if_neg hw, if_neg hp]
      have hsub : (i - UInt64.ofNat G.nP).toNat = i.toNat - G.nP := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [t0]; omega)), t0]
      rintro ⟨r, m'⟩ h
      have hgt : g.toNat < iwTop m := by have := (rec2CG_parts hG).2.1; omega
      obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := slotVarW_ok dn vis fe m m' a g _ G r hS hnP hgt
        (by rw [hsub]; omega) h
      rw [hsub] at hrun
      exact ⟨x, a', hrun, hS', hg', h1, h2⟩
  refine RSim.bind (K := pvK1 n (fun m1 => pvW n m1 g rP (i + 1))) rfl hy ?_
  rintro ⟨r1, m1⟩ y a1 - ⟨hS1, hg1, hyH, hyd⟩
  dsimp only at hS1 hg1 hyH hyd
  subst hyd
  rw [pvK1_some]
  have hr := ih m1 a1 (i + 1) hS1 (hG.grow (decCG_mono _) hg1) (by omega)
  rw [hi1] at hr
  refine RSim.bind (K := pvK2 n (r1.headD 0)) rfl hr ?_
  rintro ⟨r2, m2⟩ ys a2 - ⟨hS2, hg2, hd2, hb2⟩
  dsimp only at hS2 hg2 hd2 hb2
  rw [pvK2_some]
  refine RSim.lstep (K := fcK) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hyH hd2
  rw [fcK_some]
  exact RSim.pure_some ⟨hS3, hg1.trans (hg2.trans hg3), by simpa using hd3, by simp; omega⟩

end L.Ind
