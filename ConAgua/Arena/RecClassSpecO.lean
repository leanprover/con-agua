import ConAgua.Arena.RecClassSpecN

/-!
# `RecClass`: `classGenRule` — the relational lemmas (lane `indproofs2`, helper `rec2`)
-/


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
        (by rw [hsub]; have := i.toNat_lt; have := t0; omega) h
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
    (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hws : decHL m wso.toNat wsl.toNat = some ws) (hwb : wso.toNat + wsl.toNat ≤ iwTop m)
    (hfvs : decHL m fvso.toNat fvsl.toNat = some fvs) (hfb : fvso.toNat + fvsl.toNat ≤ iwTop m)
    (hpv : decHL m pvo.toNat pvl.toNat = some pvars) (hpb : pvo.toNat + pvl.toNat ≤ iwTop m)
    (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (REST : EIdx → AM (Option γ))
    (Q : β → AState → Option γ → Prop)
    (hnone : ∀ m' a', StageR dn vis fe m' a' → IWGrow m m' → RSim (K (some ([0, 0], m'))) (pure none) a' Q)
    (hsome : ∀ m' a' w, StageR dn vis fe m' a' → IWGrow m m' → H w →
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
    (rec2SimExprGetD n hS hws (hS.lt64 hwb)) ?_
  rintro ⟨r1, m1⟩ w a1 - ⟨hS1, hg1, hwH, hwd⟩
  dsimp only at hS1 hg1 hwH hwd
  subst hwd
  rw [c1K1_some]
  refine RSim.bind (K := fun o => K (c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e o)) hK
    (rec2SimIh n hS1 (hG.grow (decCG_mono _) hg1) t tele hwH e) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho⟩
  dsimp only at hS2 hg2 ho
  have hg12 := hg1.trans hg2
  cases o with
  | none => rw [c1K2_fail (h := ho)]; exact hnone m2 a2 hS2 hg12
  | some p2 =>
  obtain ⟨xs, idx⟩ := p2
  obtain ⟨h21, hxs, hxb, hidx, hidb⟩ := ho
  rw [c1K2_ok (h := by rw [h21]; decide)]
  dsimp only
  -- the recursor of the landing class (pure)
  refine RSim.lstep (K := fun o => K (c1K3 n fvso fvsl pvo pvl rlvls _ _ _ _ i e m2 o)) hK fun r3 h3 => ?_
  obtain ⟨g1, g2⟩ := classRecOfW_ok n m2 rco rcl cgo cgl t r3 recCls cvGs h3
    (hrc.stab (OMono.decNL _ _) m2 hg12) (hcg.stab (OMono.decPL (fun q => OMono.decCVp q) _ _) m2 hg12) hrcb hcgb
  rw [rec2ClassRecOf_eq]
  cases hcr : crOf t.toNat recCls cvGs with
  | none =>
    have := g1 hcr; subst this
    rw [c1K3_fail (h := rfl)]
    exact hnone m2 a2 hS2 hg12
  | some nm =>
  obtain ⟨h31, hnH, hnd⟩ := g2 nm hcr
  rw [c1K3_ok (h := by rw [h31]; decide)]
  dsimp only
  rw [← hnd]
  -- `class_gen_rule_call1_tail`
  cases n with
  | zero => intro b hb; simp [c1tW, fcK, hK] at hb
  | succ n =>
  rw [c1tW_eq]
  refine RSim.bind (K := fun o => K (fcK (c1tK1 n pvo pvl rlvls _ _ _ _ _ e o))) hK
    (rec2SimExprGetD n hS2 (by rw [decHL_grow hg12 hfb]; exact hfvs) (hS2.lt64 (Nat.le_trans hfb hg12.1))) ?_
  rintro ⟨r4, m4⟩ f a4 - ⟨hS4, hg4, hfH, hfd⟩
  dsimp only at hS4 hg4 hfH hfd
  subst hfd
  rw [c1tK1_some]
  refine RSim.bind (K := fun o => K (fcK (c1tK2 n pvo pvl rlvls _ _ _ _ _ e o))) hK
    ((mknF_ok dn vis fe _ _ _ hfH xs).sim ⟨hS4, by rw [decHL_grow hg4 hxb]; exact hxs⟩) ?_
  rintro ⟨r5, m5⟩ fx a5 - ⟨hS5, hg5, hfxH, hfxd⟩
  dsimp only at hS5 hg5 hfxH hfxd
  subst hfxd
  rw [c1tK2_some]
  have hg25 := hg4.trans hg5
  refine RSim.bind (K := fun o => K (fcK (c1tK3 n pvo pvl _ _ _ _ e (r5.headD 0) o))) hK
    (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ x = decE b.1) ?_ ?_
  · rintro ⟨rc, m6⟩ h6
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS5 _ rlvls hnH hrl h6
    exact ⟨decE rc, a', hrun, hS', hg, rfl⟩
  rintro ⟨rc, m6⟩ x a6 - ⟨hS6, hg6, rfl⟩
  dsimp only at hS6 hg6
  by_cases hbig : 4294967296 ≤ rc
  · rw [c1tK3_big (h := hbig)]; simp only [fcK, hK]; exact RSim.none
  rw [c1tK3_ok (h := hbig)]
  have hrcH : H rc := by
    have : ¬ (4294967296 : Word).toNat ≤ rc.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg26 := hg25.trans hg6
  have hg06 := hg12.trans hg26
  refine RSim.lstep (K := fun o => K (fcK (c1tK4 n _ _ e rc (r5.headD 0) o))) hK fun ⟨r7, m7⟩ h7 => ?_
  obtain ⟨hS7, hg7, hd7, hb7⟩ := rec2AppendW_dec h7 hS6
    (decHL_decB (by rw [decHL_grow hg06 hpb]; exact hpv) (Nat.le_trans hpb hg06.1))
    (by rw [decHL_grow hg26 hidb]; exact hidx) (Nat.le_trans hidb hg26.1)
  rw [c1tK4_some]
  refine RSim.lstep (K := fun o => K (fcK (c1tK5 n _ _ e rc o))) hK fun ⟨r8, m8⟩ h8 => ?_
  obtain ⟨hr8, hd8, hg8, -, -, ht8⟩ := snocW_dec h8 hS7.2.2.2.1 hS7.2.2.2.2.2 hb7 hfxH hd7
  have hS8 := snocW_stage h8 hS7
  rw [c1tK5_some, hr8]
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := fun o => K (fcK (c1tK6 n _ _ e o))) hK
    ((mknF_ok dn vis fe _ _ _ hrcH (pvars ++ idx ++ [decI (r5.headD 0)])).sim ⟨hS8, hd8⟩) ?_
  rintro ⟨r9, m9⟩ app a9 - ⟨hS9, hg9, happH, happd⟩
  dsimp only at hS9 hg9 happH happd
  subst happd
  rw [c1tK6_some, rec2MapM_genBinder]
  have hg29 := hg26.trans (hg7.trans (hg8.trans hg9))
  -- `class_gen_rule_call1_close`
  cases n with
  | zero => intro b hb; simp [c1cW, fcK, hK] at hb
  | succ n =>
  rw [c1cW_eq]
  refine RSim.bind (K := fun o => K (fcK (fcK (c1cK1 n e (r9.headD 0) o)))) hK
    ((ftdsF_ok dn vis fe _ _ xs).sim ⟨hS9, by rw [decHL_grow hg29 hxb]; exact hxs, fun _ => Nat.le_trans hxb hg29.1⟩) ?_
  rintro ⟨r10, m10⟩ bs a10 - ⟨hS10, hg10, hbs, hbb⟩
  dsimp only at hS10 hg10 hbs hbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hbs hbb
  by_cases hov : e + r10.tail.headD 0 < e
  · rw [c1cK1_big (h := hov)]; simp only [fcK, hK]; exact RSim.none
  rw [c1cK1_ok (h := hov)]
  have hel : e.toNat + (r10.tail.headD 0).toNat < 2 ^ 64 := by
    have : ¬ (e + r10.tail.headD 0).toNat < e.toNat := fun x => hov (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add] at this
    have h1 := e.toNat_lt; have h2 := (r10.tail.headD 0).toNat_lt
    omega
  refine RSim.bind (K := fun o => K (fcK (fcK (c1cK2 o)))) hK (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m10 b.2 ∧ (b.1.headD 0).toNat < 2 ^ 32 ∧ decI (b.1.headD 0) = x) ?_ ?_
  · rintro ⟨r11, m11⟩ h11
    obtain ⟨x, a', hrun, hS', hg, hx1, hx2⟩ := closeLamsW_ok dn vis fe n m10 m11 a10 _ _ e _ bs r11 h11 hS10
      happH hbs (hS10.lt64 hbb) hbb hel
    exact ⟨x, a', hrun, hS', hg, hx1, hx2⟩
  rintro ⟨r11, m11⟩ cll a11 - ⟨hS11, hg11, hcH, hcd⟩
  dsimp only at hS11 hg11 hcH hcd
  subst hcd
  simp only [c1cK2, fcK, List.headD_cons, List.tail_cons]
  exact hsome m11 a11 _ hS11 (hg12.trans (hg29.trans (hg10.trans hg11))) hcH

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
    i.toNat + nn.toNat < 2 ^ 64 →
    RSim (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i)
      (classGenRule.callsGo G recCls cvGs (decI rlvls) X RP fvs ws pvars nn.toNat i.toNat) a
      (fun b a' o => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o) := by
  induction n with
  | zero => intros; intro b hb; simp [cgW] at hb
  | succ n ih =>
  intro m a nn i hS hG hX hws hwb hfvs hfb hpv hpb hrc hcg hin
  have hsz := hS.2.2.2.1
  by_cases h0 : nn = 0
  · rw [cgW_end (h := h0)]
    subst h0
    rw [show (0 : Word).toNat = 0 from rfl, classGenRule.callsGo.eq_1]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, rfl, by simp [decHL, hslice?], by simp⟩
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
    have hih := ih m a (nn - 1) (i + 1) hS hG hX hws hwb hfvs hfb hpv hpb hrc hcg (by omega)
    rw [hi1, hn1] at hih
    refine RSim.bindPure (K := isK3) rfl hih ?_
    rintro ⟨r, m'⟩ o a' - ⟨hS', hg', ho⟩
    refine RSim.pure_some ⟨hS', hg', ?_⟩
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
  cases n with
  | zero => intro b hb; simp [c1W, cgK1] at hb
  | succ n =>
  refine c1W_sim n m a g _ _ wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e G ws fvs pvars recCls cvGs
    hS hG hns hws hwb hfvs hfb hpv hpb hrl hrc hrcb hcg hcgb
    (cgK1 (n + 1) g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i) (by simp [cgK1]) _ _ ?_ ?_
  · intro m' a' hS' hg'
    rw [cgK1_fail (h := rfl)]
    exact RSim.pure_some ⟨hS', hg', rfl⟩
  · intro m' a' w hS' hg' hw
    rw [cgK1_ok (h := by simp)]
    simp only [List.tail_cons, List.headD_cons]
    have hih := ih m' a' (nn - 1) (i + 1) hS' (hG.grow (decCG_mono _) hg') (hX.grow (decCC_mono _) hg')
      (by rw [decHL_grow hg' hwb]; exact hws) (Nat.le_trans hwb hg'.1)
      (by rw [decHL_grow hg' hfb]; exact hfvs) (Nat.le_trans hfb hg'.1)
      (by rw [decHL_grow hg' hpb]; exact hpv) (Nat.le_trans hpb hg'.1)
      (hrc.grow (OMono.decNL _ _) hg') (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg') (by omega)
    rw [hi1, hn1] at hih
    refine RSim.bind (K := isK2 (n + 1) w) rfl hih ?_
    rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho⟩
    dsimp only at hS2 hg2 ho
    cases o with
    | none =>
      rw [isK2_fail (h := ho)]
      exact RSim.pure_some ⟨hS2, hg'.trans hg2, rfl⟩
    | some ihs =>
    obtain ⟨h21, hd2, hb2⟩ := ho
    rw [isK2_ok (h := by rw [h21]; decide)]
    refine RSim.lstep (K := isK4) rfl fun ⟨r3, m3⟩ h3 => ?_
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hw hd2
    rw [isK4_some]
    exact RSim.pure_some ⟨hS3, hg'.trans (hg2.trans hg3), rfl, by simpa using hd3,
      by simp only [List.tail_cons, List.headD_cons]; exact Nat.le_of_eq ht3⟩

/-! ## The closing -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem grcW_sim (n : Nat) (m : Mem) (a : AState) (g s fo fl ihso ihsl : Word) (G : ClassGen) (fvs ihs : List EIdx)
    (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hs : G.nP + s.toNat < 2 ^ 64)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m) :
    RSim (grcW (n + 1) m g s fo fl ihso ihsl) (do
      let sv ← G.slotVar s.toNat
      let body ← mkAppN sv (fvs ++ ihs)
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeLams (G.pre ++ fbs) 0 body
      pure (some r)) a (KP dn vis fe m decOE) := by
  rw [grcW_eq]
  have hsz := hS.2.2.2.1
  obtain ⟨hnP, -⟩ := rec2CG_get (hG.get (decCG_mono _))
  have hgt : g.toNat < iwTop m := by have := (rec2CG_parts hG).2.1; omega
  refine RSim.bind (K := grcK1 n g fo fl ihso ihsl) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ H (b.1.headD 0) ∧ decE (b.1.headD 0) = x) ?_ ?_
  · rintro ⟨r, m'⟩ h
    obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := slotVarW_ok dn vis fe m m' a g s G r hS hnP hgt hs h
    exact ⟨x, a', hrun, hS', hg', h1, h2⟩
  rintro ⟨r1, m1⟩ sv a1 - ⟨hS1, hg1, hsvH, hsvd⟩
  dsimp only at hS1 hg1 hsvH hsvd
  subst hsvd
  rw [grcK1_some]
  refine RSim.lstep (K := grcK2 n g fo fl (r1.headD 0)) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (decHL_decB (by rw [decHL_grow hg1 hfb]; exact hfvs)
    (Nat.le_trans hfb hg1.1)) (by rw [decHL_grow hg1 hib]; exact hihs) (Nat.le_trans hib hg1.1)
  rw [grcK2_some]
  refine RSim.bind (K := grcK3 n g fo fl) rfl ((mknF_ok dn vis fe _ _ _ hsvH (fvs ++ ihs)).sim ⟨hS2, hd2⟩) ?_
  rintro ⟨r3, m3⟩ body a3 - ⟨hS3, hg3, hbH, hbd⟩
  dsimp only at hS3 hg3 hbH hbd
  subst hbd
  rw [grcK3_some, rec2MapM_genBinder]
  have hg13 := hg1.trans (hg2.trans hg3)
  refine RSim.bind (K := grcK4 n g (r3.headD 0)) rfl ((ftdsF_ok dn vis fe _ _ fvs).sim
    ⟨hS3, by rw [decHL_grow hg13 hfb]; exact hfvs, fun _ => Nat.le_trans hfb hg13.1⟩) ?_
  rintro ⟨r4, m4⟩ fbs a4 - ⟨hS4, hg4, hfbs, hfbb⟩
  dsimp only at hS4 hg4 hfbs hfbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hfbs hfbb
  rw [grcK4_some]
  have hg14 := hg13.trans hg4
  obtain ⟨-, -, -, -, -, ⟨o12, l12, h12, h13, hpre⟩⟩ := rec2CG_parts (hG.grow (decCG_mono _) (hg14))
  obtain ⟨e12, t12⟩ := rec2RdN (w := g) (k := 12) h12 hS4.2.2.2.1
  obtain ⟨e13, t13⟩ := rec2RdN (w := g) (k := 13) h13 hS4.2.2.2.1
  simp only [show UInt64.ofNat 12 = (12 : Word) from rfl, show UInt64.ofNat 13 = (13 : Word) from rfl] at e12 e13
  rw [e12, e13]
  refine RSim.lstep (K := grcK5 n (r3.headD 0)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, hb5⟩ := rec2AppendW_dec h5 hS4 (by rw [t12, t13]; exact hpre) hfbs hfbb
  rw [grcK5_some]
  refine RSim.bind (K := c1cK2) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ (b.1.headD 0).toNat < 2 ^ 32 ∧ decI (b.1.headD 0) = x) ?_ ?_
  · rintro ⟨r6, m6⟩ h6
    obtain ⟨x, a', hrun, hS', hg, hx1, hx2⟩ := closeLamsW_ok dn vis fe n m5 m6 a4 _ _ 0 _ _ r6 h6 hS5 hbH hd5
      (hS5.lt64 hb5) hb5 (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hS5.lt64 (by omega))
    exact ⟨x, a', hrun, hS', hg, hx1, hx2⟩
  rintro ⟨r6, m6⟩ x a6 - ⟨hS6, hg6, hx1, hx2⟩
  rw [c1cK2_some]
  exact RSim.pure_some ⟨hS6, hg14.trans (hg5.trans hg6), rfl, by simpa using hx1, by simpa using hx2⟩

end sims

/-! ## The rule -/

theorem ruW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem) (a : AState)
    (g rco rcl cgo cgl rlvls c x : Word) (G : ClassGen) (X : ClassCtor) (recCls : List Nat) (cvGs : List IConstantVal)
    (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) :
    RSim (ruW n m g rco rcl cgo cgl rlvls c x) (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a
      (KP dn vis fe m decOE) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
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
  cases n with
  | zero => intro b hb; simp [gfsW, ruK1] at hb
  | succ n =>
  rw [gfsW_eq, e7, e8]
  refine RSim.lstep (K := fun o => ruK1 (n + 1) g rco rcl cgo cgl rlvls x (UInt64.ofNat l12) (fcK o)) rfl
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
    rw [fcK_some, ruK1_fail (h := by simpa using hnone1 heq)]
    exact RSim.pure_some ⟨hS, IWGrow.refl _, rfl⟩
  next s0 sn heq =>
  obtain ⟨h11, h12'⟩ := hsome1 s0 sn heq
  rw [fcK_some, ruK1_ok (h := by simp only [List.headD_cons]; rw [h11]; decide)]
  simp only [List.tail_cons, List.headD_cons]
  rw [h12']
  have hs0 : s0 < G.slots.length := by
    have hm := List.mem_of_find?_eq_some heq
    have := (List.of_mem_zip hm).1
    simpa using this
  have s0lt : s0 < 2 ^ 64 := by omega
  have ts0 : (UInt64.ofNat s0 : Word).toNat = s0 := UInt64.toNat_ofNat_of_lt' s0lt
  -- the constructor's fields
  obtain ⟨hnF, htyD, -⟩ := rec2CC_parts (hX.get (decCC_mono _))
  obtain ⟨enF, tnF⟩ := rec2RdN (w := x) (k := 1) hnF hsz
  obtain ⟨vD, evD, hvD, dvD⟩ := iwH_rdW_at (w := x) (k := 4) htyD hsz
  have nFlt := (iwN_rdW_at (w := x) (k := 1) hnF hsz).2
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at enF evD
  rw [enF, evD]
  have ho := simOpenPis (k := UInt64.ofNat X.nF) (i := UInt64.ofNat l12) hS hvD
  rw [tnF, dvD, hrP] at ho
  refine RSim.bind (K := ruK2 (n + 1) g rco rcl cgo cgl rlvls x (UInt64.ofNat l12) (UInt64.ofNat s0)) rfl ho ?_
  rintro ⟨r2, m2⟩ o2 a2 - ⟨hS2, hg2, ho2⟩
  dsimp only at hS2 hg2 ho2
  cases o2 with
  | none =>
    rw [ruK2_fail (h := ho2)]
    exact RSim.pure_some ⟨hS2, hg2, rfl⟩
  | some p2 =>
  obtain ⟨fvs, res⟩ := p2
  obtain ⟨h21, ⟨hfvs, hfb⟩, -, -⟩ := ho2
  simp only [getD_one, getD_two, Nat.reduceAdd] at hfvs hfb
  rw [ruK2_ok (h := by rw [h21]; decide), rbW_eq]
  have hX2 := hX.stab (decCC_mono _) m2 hg2
  obtain ⟨-, -, htyN2⟩ := rec2CC_parts hX2
  obtain ⟨vN, evN, hvN, dvN⟩ := iwH_rdW_at (w := x) (k := 5) htyN2 hS2.2.2.2.1
  simp only [show UInt64.ofNat 5 = (5 : Word) from rfl] at evN
  rw [evN]
  refine RSim.bind (K := fun o => fcK (rbK1 n g rco rcl cgo cgl rlvls x _ _ _ _ o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m2 b.2 ∧ PdRes b.2 b.1 x) ?_ ?_
  · rintro ⟨r3, m3⟩ h3
    obtain ⟨res', a', hrun, hS', hg, hres⟩ := pdW_ok dn vis fe n m2 m3 a2 _ _ vN r3 fvs h3 hS2 hvN hfvs
      (hS2.lt64 hfb) hfb
    rw [dvN] at hrun
    exact ⟨res', a', hrun, hS', hg, hres⟩
  rintro ⟨r3, m3⟩ o3 a3 - ⟨hS3, hg3, ho3⟩
  dsimp only at hS3 hg3 ho3
  cases o3 with
  | none =>
    rw [rbK1_fail (h := ho3), fcK_some]
    exact RSim.pure_some ⟨hS3, hg2.trans hg3, rfl⟩
  | some ws =>
  obtain ⟨h31, hws, hwb⟩ := ho3
  rw [rbK1_ok (h := by rw [h31]; decide)]
  have hg23 := hg2.trans hg3
  have hpv := pvW_sim dn vis fe G g (UInt64.ofNat l12) hns
    (fun i => if i < G.nP then ConRon.Arena.exprGetD G.params i else G.slotVar (i - G.nP)) (fun _ => rfl) n m3 a3 0
    hS3 (hG.grow (decCG_mono _) hg23) (by simp)
  simp only [UInt64.toNat_zero, Nat.sub_zero, ← List.range_eq_range', hrP] at hpv
  refine RSim.bind (K := fun o => fcK (rbK2 n g rco rcl cgo cgl rlvls x _ _ _ _ _ _ o)) rfl hpv ?_
  rintro ⟨r4, m4⟩ pvars a4 - ⟨hS4, hg4, hpd, hpb⟩
  dsimp only at hS4 hg4 hpd hpb
  have hg24 := hg23.trans hg4
  have hm24 := hg3.trans hg4
  have hX4 := hX.stab (decCC_mono _) m4 hg24
  obtain ⟨hnF4, -, -⟩ := rec2CC_parts hX4
  obtain ⟨enF4, -⟩ := rec2RdN (w := x) (k := 1) hnF4 hS4.2.2.2.1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at enF4
  by_cases hov : UInt64.ofNat l12 + rdW (m4.arr64 IW) (x + 1) < UInt64.ofNat l12
  · rw [rbK2_big (h := hov)]; exact RSim.none
  rw [rbK2_ok (h := hov), enF4]
  rw [enF4] at hov
  have he : (UInt64.ofNat l12 + UInt64.ofNat X.nF : Word).toNat = G.pre.length + X.nF := by
    have : ¬ (UInt64.ofNat l12 + UInt64.ofNat X.nF : Word).toNat < (UInt64.ofNat l12 : Word).toNat :=
      fun x => hov (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add, hrP, tnF] at this ⊢
    have := (UInt64.ofNat l12 : Word).toNat_lt
    rw [hrP] at this
    omega
  have hcg := cgW_sim dn vis fe G X recCls cvGs hns g x _ _ _ _ _ _ rlvls rco rcl cgo cgl _ ws fvs pvars G.pre.length
    he hrl hrcb hcgb n m4 a4 (UInt64.ofNat X.nF) 0 hS4 (hG.grow (decCG_mono _) hg24) (hX.grow (decCC_mono _) hg24)
    (by rw [decHL_grow hg4 hwb]; exact hws) (Nat.le_trans hwb hg4.1)
    (by rw [decHL_grow hm24 hfb]; exact hfvs) (Nat.le_trans hfb hm24.1) hpd hpb
    (hrc.grow (OMono.decNL _ _) hg24) (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg24)
    (by simp [tnF]; omega)
  simp only [tnF, UInt64.toNat_zero] at hcg
  refine RSim.bind (K := fun o => fcK (rbK3 n g (UInt64.ofNat s0) _ _ o)) rfl hcg ?_
  rintro ⟨r5, m5⟩ o5 a5 - ⟨hS5, hg5, ho5⟩
  dsimp only at hS5 hg5 ho5
  cases o5 with
  | none =>
    rw [rbK3_fail (h := ho5), fcK_some]
    exact RSim.pure_some ⟨hS5, hg24.trans hg5, rfl⟩
  | some ihs =>
  obtain ⟨h51, hihs, hib⟩ := ho5
  rw [rbK3_ok (h := by rw [h51]; decide)]
  have hg25 := hg24.trans hg5
  have hm25 := hm24.trans hg5
  cases n with
  | zero => intro b hb; simp [grcW, fcK] at hb
  | succ n =>
  have hc := grcW_sim (dn := dn) (vis := vis) (fe := fe) n m5 a5 g (UInt64.ofNat s0) _ _ _ _ G fvs ihs hS5
    (hG.grow (decCG_mono _) hg25) (by rw [ts0]; omega)
    (by rw [decHL_grow hm25 hfb]; exact hfvs) (Nat.le_trans hfb hm25.1) hihs hib
  rw [ts0] at hc
  refine RSim.bindPure (K := fun o => fcK (fcK o)) rfl hc ?_
  rintro ⟨r6, m6⟩ o6 a6 - ⟨hS6, hg6, ho6⟩
  simp only [fcK_some]
  refine RSim.pure_some ⟨hS6, hg25.trans hg6, ?_⟩
  cases o6 with
  | none => exact ho6
  | some e => obtain ⟨h1, h2⟩ := ho6; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

/-- **`class_gen_rule` refines `classGenRule`** (through the stubs of `open_pis_at_fvars_f`,
`mk_app_n_f`, `fvar_type_ds`, `close_lams`'s `abstract1_fast`; the generator, the constructor record,
the classes of the recursors and the generated constants decoded below the tops). -/
@[refines ConRon.Arena.classGenRule]
theorem classGenRule_refines (p : Prog) (hp : RuProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g rco rcl cgo cgl rlvls c x : Word) (G : ClassGen)
    (X : ClassCtor) (recCls : List Nat) (cvGs : List IConstantVal) (hS : StageR dn vis fe s₀.mem a₀)
    (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) s₀.mem X) (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) s₀.mem cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule" [g, rco, rcl, cgo, cgl, rlvls, c, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a₀)
        (AM.res (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a₀); ⊤⦄ :=
  triple_post (classGenRule_spec p hp n s₀ g rco rcl cgo cgl rlvls c x) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (ruW_sim dn vis fe n _ a₀ g rco rcl cgo cgl rlvls c x G X recCls cvGs hS hG hns hX hrl hrc hrcb hcg hcgb).am hw⟩

end L.Ind
