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
  sorry

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
  sorry

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
  sorry

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
