import ConAgua.Arena.RecClassSpec.ClassGenRule

/-!
# RuW

`rec2DecB_HL_bound`, `pvW_step'`, `rec2SlotHit`, `fsgW_ok`, `pvW_afr`, `pvW_sim` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Empty slices at any offset -/

/-- A slice that is empty or below the top. -/
theorem rec2DecB_HL_bound {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hS : (m.arr64 IW).size < 2 ^ 64)
    (ht : iwTop m ≤ (m.arr64 IW).size) (ho : o < 2 ^ 64) : o + l < 2 ^ 64 := by
  by_cases hl : l = 0
  · omega
  · have := rec2DecB_HL_top h hl; omega

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The step of `pvW` with the two reads of `v` as one call argument. -/
theorem pvW_step' {n : Nat} {m : Mem} {g rP i : Word} (h : ¬ rP ≤ i) : pvW (n + 1) m g rP i =
    pvW.k_expr_get_d n g rP i
      (if i < rdW (m.arr64 IW) (g + 0) then
        fuelW n (exprGetDW m (rdW (m.arr64 IW) (g + 1)) (rdW (m.arr64 IW) (g + 2)) i)
      else slotVarW m g (i - rdW (m.arr64 IW) (g + 0))) := by
  by_cases hc : i < rdW (m.arr64 IW) (g + 0)
  · rw [pvW.arm2 (hc1 := h) (hc2 := hc), ite_eq_left hc]
  · rw [pvW.arm3 (hc1 := h) (hc2 := hc), ite_eq_right hc]

end L.Ind

end

end

section

noncomputable section

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
  · rw [fsgW.arm1 (hc1 := hend)] at h
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
  · rw [fsgW.arm2 (hc1 := hend) (hc2 := hcond.mpr hh)] at h
    cases h
    refine ⟨rfl, fun e => ?_, fun k s' e => ?_⟩
    · simp [hh] at e
    · simp [hh] at e; obtain ⟨rfl, -⟩ := e; exact ⟨rfl, by simp⟩
  · rw [fsgW.arm3 (hc1 := hend) (hc2 := fun x => hh (hcond.mp x))] at h
    obtain ⟨⟨r', m''⟩, hr, h⟩ := of_K h rfl
    rw [fsgW.k_class_gen_rule_find_slot_go.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; have := sl.toNat_lt; omega
    obtain ⟨hm, h1, h2⟩ := ih m m'' so sl (j + 1) c cn r' slots hr hsl hsz hcn (by omega) P hP
    simp only [Bool.not_eq_true] at hh
    simp only [hh]
    rw [hj1] at h1 h2
    rw [hj1]
    simp only [List.headD_cons, List.tail_cons]
    exact ⟨hm, h1, h2⟩

/-! ## The prefix variables -/

theorem pvW_afr : ∀ (n : Nat) (m m' : Mem) (g rP i : Word) (r : List Word), pvW n m g rP i = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [pvW] at h
  | n + 1, m, m', g, rP, i, r, h => by
    by_cases he : rP ≤ i
    · rw [pvW.arm1 (hc1 := he)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [pvW_step' he] at h
    rcases hx : (if i < rdW (m.arr64 IW) (g + 0) then
        fuelW n (exprGetDW m (rdW (m.arr64 IW) (g + 1)) (rdW (m.arr64 IW) (g + 2)) i)
      else slotVarW m g (i - rdW (m.arr64 IW) (g + 0))) with _ | ⟨r1, m1⟩ <;> rw [hx] at h
    · rw [pvW.k_expr_get_d.none] at h; cases h
    rw [pvW.k_expr_get_d.arm1, pvW.j1.arm1] at h
    refine AFr.trans (m₂ := m1) ?_ ?_
    · split at hx
      · exact exprGetDF_afr hx
      · exact slotVarW_afr hx
    simp only [pvW.k_class_gen_rule_pvars_go.eq_def, pvW.k_sl_cons.eq_def] at h
    afr_auto h [pvW_afr n _ _ _ _ _ _, consW_afr]

theorem pvW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (g rP : Word)
    (_hns : G.nP + G.slots.length < 2 ^ 64) (f : Nat → AM EIdx)
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
  · rw [pvW.arm1 (hc1 := hend)]
    have : rP.toNat - i.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hend; omega
    rw [this]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩
  have hlt : i.toNat < rP.toNat := by
    have : ¬ rP.toNat ≤ i.toNat := fun x => hend (UInt64.le_iff_toNat_le.mpr x)
    omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; have := rP.toNat_lt; omega
  rw [pvW_step' hend, show rP.toNat - i.toNat = (rP.toNat - (i.toNat + 1)) + 1 by omega, List.range'_succ,
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
      rw [ite_eq_left hw, ite_eq_left hp]
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
      rw [ite_eq_right hw, ite_eq_right hp]
      have hsub : (i - UInt64.ofNat G.nP).toNat = i.toNat - G.nP := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [t0]; omega)), t0]
      rintro ⟨r, m'⟩ h
      have hgt : g.toNat < iwTop m := by have := (rec2CG_parts hG).2.1; omega
      obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := slotVarW_ok dn vis fe m m' a g _ G r hS hnP hgt
        (by rw [hsub]; have := i.toNat_lt; have := t0; omega) h
      rw [hsub] at hrun
      exact ⟨x, a', hrun, hS', hg', h1, h2⟩
  refine RSim.bind (K := pvW.k_expr_get_d n g rP i) (pvW.k_expr_get_d.none ..) hy ?_
  rintro ⟨r1, m1⟩ y a1 - ⟨hS1, hg1, hyH, hyd⟩
  dsimp only at hS1 hg1 hyH hyd
  subst hyd
  rw [pvW.k_expr_get_d.arm1, pvW.j1.arm1]
  have hr := ih m1 a1 (i + 1) hS1 (hG.grow (decCG_mono _) hg1) (by omega)
  rw [hi1] at hr
  refine RSim.bind (K := pvW.k_class_gen_rule_pvars_go n (r1.headD 0)) rfl hr ?_
  rintro ⟨r2, m2⟩ ys a2 - ⟨hS2, hg2, hd2, hb2⟩
  dsimp only at hS2 hg2 hd2 hb2
  rw [pvW.k_class_gen_rule_pvars_go.arm1]
  refine RSim.lstep (K := pvW.k_sl_cons) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hyH hd2
  rw [pvW.k_sl_cons.arm1]
  exact RSim.pure_some ⟨hS3, hg1.trans (hg2.trans hg3), by simpa using hd3,
    by simp only [List.headD_cons, List.tail_cons]; exact Nat.le_of_eq ht3⟩

/-! ## One recursive call -/

theorem rec2ClassRecOf_eq (rc : List Nat) (cs : List IConstantVal) (t : Nat) :
    ConRon.Arena.classRecOf rc cs t = crOf t rc cs := by
  simp only [ConRon.Arena.classRecOf]; exact crOf_eq t cs rc

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem c1W_sim {β γ : Type} (n : Nat) (m : Mem) (a : AState)
    (g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word)
    (G : ClassGen) (ws fvs pvars : List EIdx) (recCls : List Nat) (cvGs : List IConstantVal)
    (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (_hns : G.nP + G.slots.length < 2 ^ 64)
    (hws : decHL m wso.toNat wsl.toNat = some ws) (hwb : wso.toNat + wsl.toNat ≤ iwTop m)
    (hfvs : decHL m fvso.toNat fvsl.toNat = some fvs) (hfb : fvso.toNat + fvsl.toNat ≤ iwTop m)
    (hpv : decHL m pvo.toNat pvl.toNat = some pvars) (hpb : pvo.toNat + pvl.toNat ≤ iwTop m)
    (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK m)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (REST : EIdx → AM (Option γ))
    (Q : β → AState → Option γ → Prop)
    (hnone : ∀ m' a', StageR dn vis fe m' a' → IWGrow m m' → AbsOK m' →
      RSim (K (some ([0, 0], m'))) (pure none) a' Q)
    (hsome : ∀ m' a' w, StageR dn vis fe m' a' → IWGrow m m' → H w → AbsOK m' →
      RSim (K (some ([1, w], m'))) (REST (decI w)) a' Q) :
    RSim (K (c1W (n + 1) m g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e)) (do
      let w ← ConRon.Arena.exprGetD ws i.toNat
      let __do_lift ← G.ihParts t.toNat tele.toNat w e.toNat
      match __do_lift with
      | none => pure none
      | some (xs, idx) =>
        match ConRon.Arena.classRecOf recCls cvGs t.toNat with
        | none => pure none
        | some r => do
          let f ← ConRon.Arena.exprGetD fvs i.toNat
          let fx ← mkAppN f xs
          let rc ← internE (ENodeView.const r (decI rlvls))
          let app ← mkAppN rc (pvars ++ idx ++ [fx])
          let bs ← List.mapM G.binder xs
          let cll ← ConRon.Arena.closeLams bs e.toNat app
          REST cll) a Q := by
  rw [c1W_eq]
  refine RSim.bind (K := fun o => K (c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e o)) hK
    (RSim.withF (rec2SimExprGetD n hS hws (hS.lt64 hwb)) (fun _ hb => exprGetDF_afr hb)) ?_
  rintro ⟨r1, m1⟩ w a1 - ⟨⟨hS1, hg1, hwH, hwd⟩, hf1⟩
  have hA1 := hf1 hA
  dsimp only at hS1 hg1 hwH hwd
  subst hwd
  rw [c1K1_some]
  refine RSim.bind (K := fun o => K (c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e o)) hK
    (rec2SimIh n hS1 (hG.grow (decCG_mono _) hg1) t tele hwH e hA1) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨⟨hS2, hg2, ho⟩, hA2⟩
  dsimp only at hS2 hg2 ho
  have hg12 := hg1.trans hg2
  rcases o with _ | p2
  · rw [c1K2_fail (h := ho)]; exact hnone m2 a2 hS2 hg12 hA2
  obtain ⟨xs, idx⟩ := p2
  obtain ⟨h21, hxs, hxb, hidx, hidb⟩ := ho
  rw [c1K2_ok (h := by rw [h21]; decide)]
  dsimp only
  -- the recursor of the landing class (pure)
  refine RSim.lstep (K := fun o => K (c1K3 n fvso fvsl pvo pvl rlvls _ _ _ _ i e m2 o)) hK fun r3 h3 => ?_
  obtain ⟨g1, g2⟩ := classRecOfW_ok n m2 rco rcl cgo cgl t r3 recCls cvGs h3
    (hrc.stab (OMono.decNL _ _) m2 hg12) (hcg.stab (OMono.decPL (fun q => OMono.decCVp q) _ _) m2 hg12) hrcb hcgb
  rw [rec2ClassRecOf_eq]
  rcases hcr : crOf t.toNat recCls cvGs with _ | nm
  · have := g1 hcr; subst this; rw [c1K3_fail (h := rfl)]; exact hnone m2 a2 hS2 hg12 hA2
  obtain ⟨h31, hnH, hnd⟩ := g2 nm hcr
  rw [c1K3_ok (h := by rw [h31]; decide)]
  dsimp only
  rw [← hnd]
  -- `class_gen_rule_call1_tail`
  rcases n with _ | n
  · intro b hb; simp [c1tW, fcK, hK] at hb
  rw [c1tW.arm1]
  refine RSim.bind (K := fun o => K (fcK (c1tW.k_expr_get_d n pvo pvl rlvls _ _ _ _ _ e o))) hK
    (RSim.withF (rec2SimExprGetD n hS2 (by rw [decHL_grow hg12 hfb]; exact hfvs) (hS2.lt64 (Nat.le_trans hfb hg12.1)))
      (fun _ hb => exprGetDF_afr hb)) ?_
  rintro ⟨r4, m4⟩ f a4 - ⟨⟨hS4, hg4, hfH, hfd⟩, hf4⟩
  dsimp only at hS4 hg4 hfH hfd
  subst hfd
  rw [c1tW.k_expr_get_d.arm1]
  refine RSim.bind (K := fun o => K (fcK (c1tW.k_mk_app_n_f n pvo pvl rlvls _ _ _ _ _ e o))) hK
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hfH xs).sim ⟨hS4, by rw [decHL_grow hg4 hxb]; exact hxs⟩)
      (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r5, m5⟩ fx a5 - ⟨⟨hS5, hg5, hfxH, hfxd⟩, hf5⟩
  dsimp only at hS5 hg5 hfxH hfxd
  subst hfxd
  rw [c1tW.k_mk_app_n_f.arm1]
  have hg25 := hg4.trans hg5
  refine RSim.bind (K := fun o => K (fcK (c1tW.k_intern_const n pvo pvl _ _ _ _ e (r5.headD 0) o))) hK
    (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨rc, m6⟩ h6
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS5 _ rlvls hnH hrl h6
    exact ⟨decE rc, a', hrun, hS', hg, rfl, ceinternW_afr h6 (hf5 (hf4 hA2))⟩
  rintro ⟨rc, m6⟩ x a6 - ⟨hS6, hg6, rfl, hA6⟩
  dsimp only at hS6 hg6
  by_cases hbig : 4294967296 ≤ rc
  · rw [c1tW.k_intern_const.abort1 (hc1 := hbig)]; simp only [fcK, hK]; exact RSim.none
  rw [c1tW.k_intern_const.arm1 (hc1 := hbig)]
  have hrcH : H rc := by
    have : ¬ (4294967296 : Word).toNat ≤ rc.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg26 := hg25.trans hg6
  have hg06 := hg12.trans hg26
  refine RSim.lstep (K := fun o => K (fcK (c1tW.k_sl_append n _ _ e (r5.headD 0) rc o))) hK fun ⟨r7, m7⟩ h7 => ?_
  obtain ⟨hS7, hg7, hd7, hb7⟩ := rec2AppendW_dec h7 hS6
    (decHL_decB (by rw [decHL_grow hg06 hpb]; exact hpv) (Nat.le_trans hpb hg06.1))
    (by rw [decHL_grow hg26 hidb]; exact hidx) (Nat.le_trans hidb hg26.1)
  rw [c1tW.k_sl_append.arm1]
  refine RSim.lstep (K := fun o => K (fcK (c1tW.k_sl_snoc n _ _ e rc o))) hK fun ⟨r8, m8⟩ h8 => ?_
  obtain ⟨hr8, hd8, hg8, -, -, ht8⟩ := snocW_dec h8 hS7.2.2.2.1 hS7.2.2.2.2.2 hb7 hfxH hd7
  have hS8 := snocW_stage h8 hS7
  have hA8 := snocW_afr h8 (appendW_afr h7 hA6)
  rw [c1tW.k_sl_snoc.arm1, hr8]
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := fun o => K (fcK (c1tW.k_mk_app_n_f_2 n _ _ e o))) hK
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hrcH (pvars ++ idx ++ [decI (r5.headD 0)])).sim ⟨hS8, hd8⟩)
      (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r9, m9⟩ app a9 - ⟨⟨hS9, hg9, happH, happd⟩, hf9⟩
  dsimp only at hS9 hg9 happH happd
  subst happd
  rw [c1tW.k_mk_app_n_f_2.arm1, rec2MapM_genBinder]
  have hg29 := hg26.trans (hg7.trans (hg8.trans hg9))
  -- `class_gen_rule_call1_close`
  rcases n with _ | n
  · intro b hb; simp [c1cW, c1tW.k_class_gen_rule_call1_close, fcK, hK] at hb
  rw [c1cW.arm1]
  refine RSim.bind (K := fun o => K (fcK (c1tW.k_class_gen_rule_call1_close (c1cW.k_fvar_type_ds n e (r9.headD 0) o)))) hK
    (RSim.withF ((ftdsF_ok dn vis fe _ _ xs).sim
      ⟨hS9, by rw [decHL_grow hg29 hxb]; exact hxs, fun _ => Nat.le_trans hxb hg29.1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r10, m10⟩ bs a10 - ⟨⟨hS10, hg10, hbs, hbb⟩, hf10⟩
  dsimp only at hS10 hg10 hbs hbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hbs hbb
  by_cases hov : e + r10.tail.headD 0 < e
  · rw [c1cW.k_fvar_type_ds.abort1 (hc1 := hov)]; simp only [c1tW.k_class_gen_rule_call1_close, fcK, hK]; exact RSim.none
  rw [c1cW.k_fvar_type_ds.arm1 (hc1 := hov)]
  have hel : e.toNat + (r10.tail.headD 0).toNat < 2 ^ 64 := by
    have := nctAddNowrap (a := r10.tail.headD 0) (b := e) (by rwa [UInt64.add_comm]); omega
  refine RSim.bind (K := fun o => K (fcK (c1tW.k_class_gen_rule_call1_close (c1cW.k_close_lams o)))) hK (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m10 b.2 ∧ (b.1.headD 0).toNat < 2 ^ 32 ∧ decI (b.1.headD 0) = x ∧
      AbsOK b.2) ?_ ?_
  · rintro ⟨r11, m11⟩ h11
    obtain ⟨x, a', hrun, hS', hg, hx1, hx2, hA11⟩ := closeLamsW_ok dn vis fe n m10 m11 a10 _ _ e _ bs r11 h11 hS10
      happH hbs (hS10.lt64 hbb) hbb hel (hf10 (hf9 hA8))
    exact ⟨x, a', hrun, hS', hg, hx1, hx2, hA11⟩
  rintro ⟨r11, m11⟩ cll a11 - ⟨hS11, hg11, hcH, hcd, hA11⟩
  dsimp only at hS11 hg11 hcH hcd
  subst hcd
  simp only [c1cW.k_close_lams, c1tW.k_class_gen_rule_call1_close, fcK, List.headD_cons, List.tail_cons]
  exact hsome m11 a11 _ hS11 (hg12.trans (hg29.trans (hg10.trans hg11))) hcH hA11

end sims

/-! ## The calls -/

theorem cgW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (X : ClassCtor)
    (recCls : List Nat) (cvGs : List IConstantVal) (hns : G.nP + G.slots.length < 2 ^ 64)
    (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e : Word) (ws fvs pvars : List EIdx) (RP : Nat)
    (he : e.toNat = RP + X.nF) (hrl : H rlvls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (nn i : Word), StageR dn vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decCC m x.toNat) m X →
    decHL m wso.toNat wsl.toNat = some ws → wso.toNat + wsl.toNat ≤ iwTop m →
    decHL m fvso.toNat fvsl.toNat = some fvs → fvso.toNat + fvsl.toNat ≤ iwTop m →
    decHL m pvo.toNat pvl.toNat = some pvars → pvo.toNat + pvl.toNat ≤ iwTop m →
    DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls →
    DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs →
    i.toNat + nn.toNat < 2 ^ 64 → AbsOK m →
    RSim (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i)
      (classGenRule.callsGo G recCls cvGs (decI rlvls) X RP fvs ws pvars nn.toNat i.toNat) a
      (fun b a' o => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [cgW] at hb
  | succ n ih =>
  intro m a nn i hS hG hX hws hwb hfvs hfb hpv hpb hrc hcg hin hA
  have hsz := hS.2.2.2.1
  by_cases h0 : nn = 0
  · rw [cgW_end (h := h0)]
    subst h0
    rw [show (0 : Word).toNat = 0 from rfl, classGenRule.callsGo.eq_1]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, ⟨rfl, by simp [decHL, hslice?], by simp⟩, hA⟩
  obtain ⟨k, hk⟩ : ∃ k, nn.toNat = k + 1 :=
    ⟨nn.toNat - 1, by have : nn.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hn1 : (nn - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [hk, classGenRule.callsGo.eq_2]
  obtain ⟨hord, hrec⟩ := rec2IsTag (hX.get (decCC_mono _)) hsz (i := i)
  cases hkd : X.kinds.getD i.toNat .ordinary with
  | ordinary =>
    rw [cgW_ord (h := h0) (ht := hord hkd)]
    have hih := ih m a (nn - 1) (i + 1) hS hG hX hws hwb hfvs hfb hpv hpb hrc hcg (by omega) hA
    rw [hi1, hn1] at hih
    refine RSim.bindPure (K := isK3) rfl hih ?_
    rintro ⟨r, m'⟩ o a' - ⟨hS', hg', ho, hA'⟩
    refine RSim.pure_some ⟨hS', hg', ?_, hA'⟩
    cases o with
    | none => exact ho
    | some ihs => exact ho
  | recursive t tele =>
  obtain ⟨ht, et, tlt, ete, telelt⟩ := hrec t tele hkd
  have tt : (UInt64.ofNat t : Word).toNat = t := UInt64.toNat_ofNat_of_lt' tlt
  have tte : (UInt64.ofNat tele : Word).toNat = tele := UInt64.toNat_ofNat_of_lt' telelt
  dsimp only
  rw [← he, ← tt, ← tte]
  rw [cgW_rec (h := h0) (ht := ht), et, ete]
  rcases n with _ | n
  · intro b hb; simp [c1W, cgK1] at hb
  refine c1W_sim n m a g _ _ wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e G ws fvs pvars recCls cvGs
    hS hG hns hws hwb hfvs hfb hpv hpb hrl hrc hrcb hcg hcgb hA
    (cgK1 (n + 1) g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i) (by simp [cgK1]) _ _ ?_ ?_
  · intro m' a' hS' hg' hA'
    rw [cgK1_fail (h := rfl)]
    exact RSim.pure_some ⟨hS', hg', rfl, hA'⟩
  · intro m' a' w hS' hg' hw hA'
    rw [cgK1_ok (h := by simp)]
    simp only [List.tail_cons, List.headD_cons]
    have hih := ih m' a' (nn - 1) (i + 1) hS' (hG.grow (decCG_mono _) hg') (hX.grow (decCC_mono _) hg')
      (by rw [decHL_grow hg' hwb]; exact hws) (Nat.le_trans hwb hg'.1)
      (by rw [decHL_grow hg' hfb]; exact hfvs) (Nat.le_trans hfb hg'.1)
      (by rw [decHL_grow hg' hpb]; exact hpv) (Nat.le_trans hpb hg'.1)
      (hrc.grow (OMono.decNL _ _) hg') (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg') (by omega) hA'
    rw [hi1, hn1] at hih
    refine RSim.bind (K := isK2 (n + 1) w) rfl hih ?_
    rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
    dsimp only at hS2 hg2 ho
    rcases o with _ | ihs
    · rw [isK2_fail (h := ho)]; exact RSim.pure_some ⟨hS2, hg'.trans hg2, rfl, hA2⟩
    obtain ⟨h21, hd2, hb2⟩ := ho
    rw [isK2_ok (h := by rw [h21]; decide)]
    refine RSim.lstep (K := isK4) rfl fun ⟨r3, m3⟩ h3 => ?_
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hw hd2
    rw [isK4_some]
    exact RSim.pure_some ⟨hS3, hg'.trans (hg2.trans hg3), ⟨rfl, by simpa using hd3,
      by simp only [List.tail_cons, List.headD_cons]; exact Nat.le_of_eq ht3⟩, consW_afr h3 hA2⟩

/-! ## The closing -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem grcW_sim (n : Nat) (m : Mem) (a : AState) (g s fo fl ihso ihsl : Word) (G : ClassGen) (fvs ihs : List EIdx)
    (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hs : G.nP + s.toNat < 2 ^ 64)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m)
    (hA : AbsOK m) :
    RSim (grcW (n + 1) m g s fo fl ihso ihsl) (do
      let sv ← G.slotVar s.toNat
      let body ← mkAppN sv (fvs ++ ihs)
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeLams (G.pre ++ fbs) 0 body
      pure (some r)) a (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rw [grcW.arm1]
  have hsz := hS.2.2.2.1
  obtain ⟨hnP, -⟩ := rec2CG_get (hG.get (decCG_mono _))
  have hgt : g.toNat < iwTop m := by have := (rec2CG_parts hG).2.1; omega
  refine RSim.bind (K := grcW.k_class_gen_slot_var n g fo fl ihso ihsl) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ H (b.1.headD 0) ∧ decE (b.1.headD 0) = x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r, m'⟩ h
    obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := slotVarW_ok dn vis fe m m' a g s G r hS hnP hgt hs h
    exact ⟨x, a', hrun, hS', hg', h1, h2, slotVarW_afr h hA⟩
  rintro ⟨r1, m1⟩ sv a1 - ⟨hS1, hg1, hsvH, hsvd, hA1⟩
  dsimp only at hS1 hg1 hsvH hsvd
  subst hsvd
  rw [grcW.k_class_gen_slot_var.arm1]
  refine RSim.lstep (K := grcW.k_sl_append n g fo fl (r1.headD 0)) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (decHL_decB (by rw [decHL_grow hg1 hfb]; exact hfvs)
    (Nat.le_trans hfb hg1.1)) (by rw [decHL_grow hg1 hib]; exact hihs) (Nat.le_trans hib hg1.1)
  rw [grcW.k_sl_append.arm1]
  refine RSim.bind (K := grcW.k_mk_app_n_f n g fo fl) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hsvH (fvs ++ ihs)).sim ⟨hS2, hd2⟩) (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r3, m3⟩ body a3 - ⟨⟨hS3, hg3, hbH, hbd⟩, hf3⟩
  dsimp only at hS3 hg3 hbH hbd
  subst hbd
  rw [grcW.k_mk_app_n_f.arm1, rec2MapM_genBinder]
  have hg13 := hg1.trans (hg2.trans hg3)
  refine RSim.bind (K := grcW.k_fvar_type_ds n g (r3.headD 0)) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ fvs).sim
      ⟨hS3, by rw [decHL_grow hg13 hfb]; exact hfvs, fun _ => Nat.le_trans hfb hg13.1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r4, m4⟩ fbs a4 - ⟨⟨hS4, hg4, hfbs, hfbb⟩, hf4⟩
  dsimp only at hS4 hg4 hfbs hfbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hfbs hfbb
  rw [grcW.k_fvar_type_ds.arm1]
  have hg14 := hg13.trans hg4
  obtain ⟨-, -, -, -, -, ⟨o12, l12, h12, h13, hpre⟩⟩ := rec2CG_parts (hG.grow (decCG_mono _) (hg14))
  obtain ⟨e12, t12⟩ := rec2RdN (w := g) (k := 12) h12 hS4.2.2.2.1
  obtain ⟨e13, t13⟩ := rec2RdN (w := g) (k := 13) h13 hS4.2.2.2.1
  simp only [show UInt64.ofNat 12 = (12 : Word) from rfl, show UInt64.ofNat 13 = (13 : Word) from rfl] at e12 e13
  rw [e12, e13]
  refine RSim.lstep (K := grcW.k_sl_append_2 n (r3.headD 0)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, hb5⟩ := rec2AppendW_dec h5 hS4 (by rw [t12, t13]; exact hpre) hfbs hfbb
  rw [grcW.k_sl_append_2.arm1]
  refine RSim.bind (K := grcW.k_close_lams) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ (b.1.headD 0).toNat < 2 ^ 32 ∧ decI (b.1.headD 0) = x ∧
      AbsOK b.2) ?_ ?_
  · rintro ⟨r6, m6⟩ h6
    obtain ⟨x, a', hrun, hS', hg, hx1, hx2, hA6⟩ := closeLamsW_ok dn vis fe n m5 m6 a4 _ _ 0 _ _ r6 h6 hS5 hbH hd5
      (hS5.lt64 hb5) hb5 (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hS5.lt64 (by omega))
      (appendW_afr h5 (hf4 (hf3 (appendW_afr h2 hA1))))
    exact ⟨x, a', hrun, hS', hg, hx1, hx2, hA6⟩
  rintro ⟨r6, m6⟩ x a6 - ⟨hS6, hg6, hx1, hx2, hA6⟩
  rw [grcW.k_close_lams.arm1]
  exact RSim.pure_some ⟨⟨hS6, hg14.trans (hg5.trans hg6), rfl, by simpa using hx1, by simpa using hx2⟩, hA6⟩

end sims

/-! ## The rule -/

theorem ruW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem) (a : AState)
    (g rco rcl cgo cgl rlvls c x : Word) (G : ClassGen) (X : ClassCtor) (recCls : List Nat) (cvGs : List IConstantVal)
    (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK m) :
    RSim (ruW n m g rco rcl cgo cgl rlvls c x) (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [ruW_eq]
  unfold ConRon.Arena.classGenRule
  dsimp only
  have hsz := hS.2.2.2.1
  obtain ⟨-, hgt, -, -, -, ⟨o12, l12, h12, h13, hpre⟩⟩ := rec2CG_parts hG
  obtain ⟨e13, t13⟩ := rec2RdN (w := g) (k := 13) h13 hsz
  simp only [show UInt64.ofNat 13 = (13 : Word) from rfl] at e13
  rw [e13]
  have hlen : G.pre.length = l12 := decHL_length _ (hpre.get (OMono.decHL _ _))
  have hrP : (UInt64.ofNat l12 : Word).toNat = G.pre.length := by rw [t13, hlen]
  obtain ⟨nw, enw, hnwH, hnwd⟩ := rec2CCName (hX.get (decCC_mono _)) hsz
  rw [enw]
  obtain ⟨-, hslots⟩ := rec2CG_get (hG.get (decCG_mono _))
  obtain ⟨so, sl, hso, hsl', hsls⟩ := decAt_some hslots
  have hslen := decPL_length m hsls
  obtain ⟨e7, t7⟩ := rec2RdN (w := g) (k := 7) hso hsz
  obtain ⟨e8, t8⟩ := rec2RdN (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz
  simp only [show UInt64.ofNat 7 = (7 : Word) from rfl, show UInt64.ofNat 8 = (8 : Word) from rfl] at e7 e8
  rcases n with _ | n
  · intro b hb; simp [gfsW, ruK1] at hb
  rw [gfsW.arm1, e7, e8]
  refine RSim.lstep (K := fun o => ruK1 (n + 1) g rco rcl cgo cgl rlvls x (UInt64.ofNat l12) (gfsW.k_class_gen_rule_find_slot_go o)) rfl
    fun ⟨r1, m1⟩ h1 => ?_
  obtain ⟨hm1, hnone1, hsome1⟩ := fsgW_ok n m m1 _ _ 0 c nw r1 G.slots h1 (by rw [t7, t8]; exact hsls) hsz hnwH
    (by simp)
    (fun x_1 => match x_1 with
      | (_, sl) => match sl with
        | ClassSlot.minor c' C _ => c' == c.toNat && C == X.cv.name
        | ClassSlot.motive _ => false)
    (fun k s' => by cases s' <;> simp [rec2SlotHit, hnwd])
  subst hm1
  simp only [UInt64.toNat_zero, Nat.sub_zero, List.drop_zero, t8] at hnone1 hsome1
  simp only [← hslen, ← List.range_eq_range'] at hnone1 hsome1
  split
  next heq =>
    rw [gfsW.k_class_gen_rule_find_slot_go.arm1, ruK1_fail (h := by simpa using hnone1 heq)]
    exact RSim.pure_some ⟨⟨hS, IWGrow.refl _, rfl⟩, hA⟩
  next s0 sn heq =>
  obtain ⟨h11, h12'⟩ := hsome1 s0 sn heq
  rw [gfsW.k_class_gen_rule_find_slot_go.arm1, ruK1_ok (h := by simp only [List.headD_cons]; rw [h11]; decide)]
  simp only [List.tail_cons, List.headD_cons]
  rw [h12']
  have hs0 : s0 < G.slots.length := by simpa using (List.of_mem_zip (List.mem_of_find?_eq_some heq)).1
  have s0lt : s0 < 2 ^ 64 := by omega
  have ts0 : (UInt64.ofNat s0 : Word).toNat = s0 := UInt64.toNat_ofNat_of_lt' s0lt
  -- the constructor's fields
  obtain ⟨hnF, htyD, -⟩ := rec2CC_parts (hX.get (decCC_mono _))
  obtain ⟨enF, tnF⟩ := rec2RdN (w := x) (k := 1) hnF hsz
  obtain ⟨vD, evD, hvD, dvD⟩ := iwH_rdW_at (w := x) (k := 4) htyD hsz
  have nFlt := (iwN_rdW_at (w := x) (k := 1) hnF hsz).2
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at enF evD
  rw [enF, evD]
  have ho := simOpenPisF (k := UInt64.ofNat X.nF) (i := UInt64.ofNat l12) hS hA hvD
  rw [tnF, dvD, hrP] at ho
  refine RSim.bind (K := ruK2 (n + 1) g rco rcl cgo cgl rlvls x (UInt64.ofNat l12) (UInt64.ofNat s0)) rfl
    ho ?_
  rintro ⟨r2, m2⟩ o2 a2 - ⟨⟨hS2, hg2, ho2⟩, hA2⟩
  dsimp only at hS2 hg2 ho2
  rcases o2 with _ | p2
  · rw [ruK2_fail (h := ho2)]; exact RSim.pure_some ⟨⟨hS2, hg2, rfl⟩, hA2⟩
  obtain ⟨fvs, res⟩ := p2
  obtain ⟨h21, ⟨hfvs, hfb⟩, -, -⟩ := ho2
  simp only [getD_one, getD_two, Nat.reduceAdd] at hfvs hfb
  rw [ruK2_ok (h := by rw [h21]; decide), rbW.arm1]
  have hX2 := hX.stab (decCC_mono _) m2 hg2
  obtain ⟨-, -, htyN2⟩ := rec2CC_parts hX2
  obtain ⟨vN, evN, hvN, dvN⟩ := iwH_rdW_at (w := x) (k := 5) htyN2 hS2.2.2.2.1
  simp only [show UInt64.ofNat 5 = (5 : Word) from rfl] at evN
  rw [evN]
  refine RSim.bind (K := fun o => fcK (rbW.k_target_pi_doms_with n g rco rcl cgo cgl rlvls x _ _ _ _ o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m2 b.2 ∧ PdRes b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r3, m3⟩ h3
    obtain ⟨res', a', hrun, hS', hg, hres⟩ := pdW_ok dn vis fe n m2 m3 a2 _ _ vN r3 fvs h3 hS2 hvN hfvs
      (hS2.lt64 hfb) hfb
    rw [dvN] at hrun
    exact ⟨res', a', hrun, hS', hg, hres, pdW_afr _ _ _ _ _ _ _ h3 hA2⟩
  rintro ⟨r3, m3⟩ o3 a3 - ⟨hS3, hg3, ho3, hA3⟩
  dsimp only at hS3 hg3 ho3
  rcases o3 with _ | ws
  · rw [rbW.k_target_pi_doms_with.arm1 (hc1 := ho3), fcK_some]; exact RSim.pure_some ⟨⟨hS3, hg2.trans hg3, rfl⟩, hA3⟩
  obtain ⟨h31, hws, hwb⟩ := ho3
  rw [rbW.k_target_pi_doms_with.arm2 (hc1 := by rw [h31]; decide)]
  have hg23 := hg2.trans hg3
  have hpv := pvW_sim dn vis fe G g (UInt64.ofNat l12) hns
    (fun i => if i < G.nP then ConRon.Arena.exprGetD G.params i else G.slotVar (i - G.nP)) (fun _ => rfl) n m3 a3 0
    hS3 (hG.grow (decCG_mono _) hg23) (by simp)
  simp only [UInt64.toNat_zero, Nat.sub_zero, ← List.range_eq_range', hrP] at hpv
  refine RSim.bind (K := fun o => fcK (rbW.k_class_gen_rule_pvars_go n g rco rcl cgo cgl rlvls x _ _ _ _ _ _ o)) rfl
    (RSim.withF hpv (fun _ hb => pvW_afr _ _ _ _ _ _ _ hb)) ?_
  rintro ⟨r4, m4⟩ pvars a4 - ⟨⟨hS4, hg4, hpd, hpb⟩, hf4⟩
  have hA4 := hf4 hA3
  dsimp only at hS4 hg4 hpd hpb
  have hg24 := hg23.trans hg4
  have hm24 := hg3.trans hg4
  have hX4 := hX.stab (decCC_mono _) m4 hg24
  obtain ⟨hnF4, -, -⟩ := rec2CC_parts hX4
  obtain ⟨enF4, -⟩ := rec2RdN (w := x) (k := 1) hnF4 hS4.2.2.2.1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at enF4
  by_cases hov : UInt64.ofNat l12 + rdW (m4.arr64 IW) (x + 1) < UInt64.ofNat l12
  · rw [rbW.k_class_gen_rule_pvars_go.abort1 (hc1 := hov)]; exact RSim.none
  rw [rbW.k_class_gen_rule_pvars_go.arm1 (hc1 := hov), enF4]
  rw [enF4] at hov
  have he : (UInt64.ofNat l12 + UInt64.ofNat X.nF : Word).toNat = G.pre.length + X.nF := by
    have := nctAddNowrap (a := UInt64.ofNat X.nF) (b := UInt64.ofNat l12) (by rwa [UInt64.add_comm])
    rw [UInt64.toNat_add, hrP, tnF] at *; omega
  have hcg := cgW_sim dn vis fe G X recCls cvGs hns g x _ _ _ _ _ _ rlvls rco rcl cgo cgl _ ws fvs pvars G.pre.length
    he hrl hrcb hcgb n m4 a4 (UInt64.ofNat X.nF) 0 hS4 (hG.grow (decCG_mono _) hg24) (hX.grow (decCC_mono _) hg24)
    (by rw [decHL_grow hg4 hwb]; exact hws) (Nat.le_trans hwb hg4.1)
    (by rw [decHL_grow hm24 hfb]; exact hfvs) (Nat.le_trans hfb hm24.1) hpd hpb
    (hrc.grow (OMono.decNL _ _) hg24) (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg24)
    (by simp [tnF]; omega) hA4
  simp only [tnF, UInt64.toNat_zero] at hcg
  refine RSim.bind (K := fun o => fcK (rbW.k_class_gen_rule_calls_go n g (UInt64.ofNat s0) _ _ o)) rfl hcg ?_
  rintro ⟨r5, m5⟩ o5 a5 - ⟨hS5, hg5, ho5, hA5⟩
  dsimp only at hS5 hg5 ho5
  rcases o5 with _ | ihs
  · rw [rbW.k_class_gen_rule_calls_go.arm1 (hc1 := ho5), fcK_some]; exact RSim.pure_some ⟨⟨hS5, hg24.trans hg5, rfl⟩, hA5⟩
  obtain ⟨h51, hihs, hib⟩ := ho5
  rw [rbW.k_class_gen_rule_calls_go.arm2 (hc1 := by rw [h51]; decide)]
  have hg25 := hg24.trans hg5
  have hm25 := hm24.trans hg5
  rcases n with _ | n
  · intro b hb; simp [grcW, rbW.k_class_gen_rule_close, fcK] at hb
  have hc := grcW_sim (dn := dn) (vis := vis) (fe := fe) n m5 a5 g (UInt64.ofNat s0) _ _ _ _ G fvs ihs hS5
    (hG.grow (decCG_mono _) hg25) (by rw [ts0]; omega)
    (by rw [decHL_grow hm25 hfb]; exact hfvs) (Nat.le_trans hfb hm25.1) hihs hib hA5
  rw [ts0] at hc
  refine RSim.bindPure (K := fun o => fcK (rbW.k_class_gen_rule_close o)) rfl hc ?_
  rintro ⟨r6, m6⟩ o6 a6 - ⟨⟨hS6, hg6, ho6⟩, hA6⟩
  simp only [rbW.k_class_gen_rule_close.arm1, fcK_some]
  refine RSim.pure_some ⟨⟨hS6, hg25.trans hg6, ?_⟩, hA6⟩
  cases o6 with
  | none => exact ho6
  | some e => obtain ⟨h1, h2⟩ := ho6; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

end L.Ind

end

end
