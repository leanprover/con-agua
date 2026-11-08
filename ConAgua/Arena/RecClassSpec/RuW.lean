module

public import ConAgua.Arena.RecClassSpec.ClassGenRule
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpec.PdWAfr
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecClassSpec.Rec2AppendWDec
import all ConAgua.Arena.RecClass

@[expose] public section

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
        refine ⟨?_, decI_inj hcwH hcn (by rw [hcwd, e2'])⟩
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
    ∀ (m : Mem) (a : AState) (i : Word), StageR vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    i.toNat ≤ rP.toNat →
    RSim (pvW n m g rP i) ((List.range' i.toNat (rP.toNat - i.toNat)).mapM f) a
      (fun b a' xs => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧
        decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some xs ∧
        (b.1.headD 0).toNat + (b.1.tail.headD 0).toNat ≤ iwTop b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [pvW] at hb
  | succ n ih =>
  intro m a i hS hG hi
  have hsz := hS.iw.iwSize
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
        (by rw [t1, t2]; exact rec2DecB_HL_bound hpdB hsz hS.iw.iw o1lt)
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
    (hS : StageR vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (_hns : G.nP + G.slots.length < 2 ^ 64)
    (hws : decHL m wso.toNat wsl.toNat = some ws) (hwb : wso.toNat + wsl.toNat ≤ iwTop m)
    (hfvs : decHL m fvso.toNat fvsl.toNat = some fvs) (hfb : fvso.toNat + fvsl.toNat ≤ iwTop m)
    (hpv : decHL m pvo.toNat pvl.toNat = some pvars) (hpb : pvo.toNat + pvl.toNat ≤ iwTop m)
    (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK m)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (REST : EIdx → AM (Option γ))
    (Q : β → AState → Option γ → Prop)
    (hnone : ∀ m' a', StageR vis fe m' a' → IWGrow m m' → AbsOK m' →
      RSim (K (some ([0, 0], m'))) (pure none) a' Q)
    (hsome : ∀ m' a' w, StageR vis fe m' a' → IWGrow m m' → H w → AbsOK m' →
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
  sorry

end sims

/-! ## The calls -/

theorem cgW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (X : ClassCtor)
    (recCls : List Nat) (cvGs : List IConstantVal) (hns : G.nP + G.slots.length < 2 ^ 64)
    (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e : Word) (ws fvs pvars : List EIdx) (RP : Nat)
    (he : e.toNat = RP + X.nF) (hrl : H rlvls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (nn i : Word), StageR vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decCC m x.toNat) m X →
    decHL m wso.toNat wsl.toNat = some ws → wso.toNat + wsl.toNat ≤ iwTop m →
    decHL m fvso.toNat fvsl.toNat = some fvs → fvso.toNat + fvsl.toNat ≤ iwTop m →
    decHL m pvo.toNat pvl.toNat = some pvars → pvo.toNat + pvl.toNat ≤ iwTop m →
    DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls →
    DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs →
    i.toNat + nn.toNat < 2 ^ 64 → AbsOK m →
    RSim (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i)
      (classGenRule.callsGo G recCls cvGs (decI rlvls) X RP fvs ws pvars nn.toNat i.toNat) a
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [cgW] at hb
  | succ n ih =>
  intro m a nn i hS hG hX hws hwb hfvs hfb hpv hpb hrc hcg hin hA
  have hsz := hS.iw.iwSize
  by_cases h0 : nn = 0
  · rw [cgW.arm1 (hc1 := h0)]
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
    refine RSim.bindPure (K := cgW.k_class_gen_rule_calls_go_2) rfl hih ?_
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
  · intro b hb; simp [c1W, cgW.k_class_gen_rule_call1.none] at hb
  refine c1W_sim n m a g _ _ wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e G ws fvs pvars recCls cvGs
    hS hG hns hws hwb hfvs hfb hpv hpb hrl hrc hrcb hcg hcgb hA
    (cgW.k_class_gen_rule_call1 (n + 1) g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i)
    (by simp [cgW.k_class_gen_rule_call1.none]) _ _ ?_ ?_
  · intro m' a' hS' hg' hA'
    rw [cgW.k_class_gen_rule_call1.arm1 (hc1 := rfl)]
    exact RSim.pure_some ⟨hS', hg', rfl, hA'⟩
  · intro m' a' w hS' hg' hw hA'
    rw [cgW.k_class_gen_rule_call1.arm2 (hc1 := by simp)]
    simp only [List.tail_cons, List.headD_cons]
    have hih := ih m' a' (nn - 1) (i + 1) hS' (hG.grow (decCG_mono _) hg') (hX.grow (decCC_mono _) hg')
      (by rw [decHL_grow hg' hwb]; exact hws) (Nat.le_trans hwb hg'.iw)
      (by rw [decHL_grow hg' hfb]; exact hfvs) (Nat.le_trans hfb hg'.iw)
      (by rw [decHL_grow hg' hpb]; exact hpv) (Nat.le_trans hpb hg'.iw)
      (hrc.grow (OMono.decNL _ _) hg') (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg') (by omega) hA'
    rw [hi1, hn1] at hih
    refine RSim.bind (K := cgW.k_class_gen_rule_calls_go (n + 1) w) (by rw [cgW.k_class_gen_rule_calls_go.none]) hih ?_
    rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
    dsimp only at hS2 hg2 ho
    rcases o with _ | ihs
    · rw [cgW.k_class_gen_rule_calls_go.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨hS2, hg'.trans hg2, rfl, hA2⟩
    obtain ⟨h21, hd2, hb2⟩ := ho
    rw [cgW.k_class_gen_rule_calls_go.arm2 (hc1 := by rw [h21]; decide)]
    refine RSim.lstep (K := cgW.k_sl_cons) rfl fun ⟨r3, m3⟩ h3 => ?_
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hw hd2
    rw [cgW.k_sl_cons.arm1]
    exact RSim.pure_some ⟨hS3, hg'.trans (hg2.trans hg3), ⟨rfl, by simpa using hd3,
      by simp only [List.tail_cons, List.headD_cons]; exact Nat.le_of_eq ht3⟩, consW_afr h3 hA2⟩

/-! ## The closing -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem grcW_sim (n : Nat) (m : Mem) (a : AState) (g s fo fl ihso ihsl : Word) (G : ClassGen) (fvs ihs : List EIdx)
    (hS : StageR vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hs : G.nP + s.toNat < 2 ^ 64)
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
  have hsz := hS.iw.iwSize
  obtain ⟨hnP, -⟩ := rec2CG_get (hG.get (decCG_mono _))
  have hgt : g.toNat < iwTop m := by have := (rec2CG_parts hG).2.1; omega
  refine RSim.bind (K := grcW.k_class_gen_slot_var n g fo fl ihso ihsl) rfl (Q1 := fun b a' x =>
    StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ H (b.1.headD 0) ∧ decE (b.1.headD 0) = x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r, m'⟩ h
    obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := slotVarW_ok dn vis fe m m' a g s G r hS hnP hgt hs h
    exact ⟨x, a', hrun, hS', hg', h1, h2, slotVarW_afr h hA⟩
  rintro ⟨r1, m1⟩ sv a1 - ⟨hS1, hg1, hsvH, hsvd, hA1⟩
  dsimp only at hS1 hg1 hsvH hsvd
  subst hsvd
  rw [grcW.k_class_gen_slot_var.arm1]
  refine RSim.lstep (K := grcW.k_sl_append n g fo fl (r1.headD 0)) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (decHL_decB (by rw [decHL_grow hg1 hfb]; exact hfvs)
    (Nat.le_trans hfb hg1.iw)) (by rw [decHL_grow hg1 hib]; exact hihs) (Nat.le_trans hib hg1.iw)
  rw [grcW.k_sl_append.arm1]
  refine RSim.bind (K := grcW.k_mk_app_n_f n g fo fl) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hsvH (fvs ++ ihs)).sim ⟨hS2, hd2⟩) (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r3, m3⟩ body a3 - ⟨⟨hS3, hg3, hbH, hbd⟩, hf3⟩
  dsimp only at hS3 hg3 hbH hbd
  subst hbd
  rw [grcW.k_mk_app_n_f.arm1, rec2MapM_genBinder]
  have hg13 := hg1.trans (hg2.trans hg3)
  refine RSim.bind (K := grcW.k_fvar_type_ds n g (r3.headD 0)) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ fvs).sim
      ⟨hS3, by rw [decHL_grow hg13 hfb]; exact hfvs, fun _ => Nat.le_trans hfb hg13.iw⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r4, m4⟩ fbs a4 - ⟨⟨hS4, hg4, hfbs, hfbb⟩, hf4⟩
  dsimp only at hS4 hg4 hfbs hfbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hfbs hfbb
  rw [grcW.k_fvar_type_ds.arm1]
  have hg14 := hg13.trans hg4
  obtain ⟨-, -, -, -, -, ⟨o12, l12, h12, h13, hpre⟩⟩ := rec2CG_parts (hG.grow (decCG_mono _) (hg14))
  obtain ⟨e12, t12⟩ := rec2RdN (w := g) (k := 12) h12 hS4.iw.iwSize
  obtain ⟨e13, t13⟩ := rec2RdN (w := g) (k := 13) h13 hS4.iw.iwSize
  simp only [show UInt64.ofNat 12 = (12 : Word) from rfl, show UInt64.ofNat 13 = (13 : Word) from rfl] at e12 e13
  rw [e12, e13]
  refine RSim.lstep (K := grcW.k_sl_append_2 n (r3.headD 0)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, hb5⟩ := rec2AppendW_dec h5 hS4 (by rw [t12, t13]; exact hpre) hfbs hfbb
  rw [grcW.k_sl_append_2.arm1]
  refine RSim.bind (K := grcW.k_close_lams) rfl (Q1 := fun b a' x =>
    StageR vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ (b.1.headD 0).toNat < 2 ^ 32 ∧ decI (b.1.headD 0) = x ∧
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
    (hS : StageR vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK m) :
    RSim (ruW n m g rco rcl cgo cgl rlvls c x) (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  sorry

end L.Ind

end

end
