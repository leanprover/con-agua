module

public import ConAgua.Arena.BasisBlockT
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.IlpRd
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Specs
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.IndexLoops
import ConAgua.Arena.DeclCanonRules
import ConAgua.L.WordOff

@[expose] public section

/-!
# `pin_list_ok` refines `pinListOk` (lane `ronsync2`, stage 3)

`BasisL.lean`'s comparison of a block with its pin, `pin_list_ok(bo, bl, po, pl)` on two `IW`
slices of constant records: the copies (`pin_copies_ok`, each `pin_copy_ok` as `quot_pin_hit`
does it: the names, the pin at them, `pin_agrees`) and the links (`block_links_ok`: a
constructor's names against the former's, a recursor's rules' constructors linked through
`pin_link_ok`). The contract is `PinListOkRef` (`BasisBlockT.lean`); `pinListOkRef_of` proves it
from the program facts `PinListLProg`.
-/

noncomputable section

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## `pin_agrees` -/

theorem pinAgrees_eq_of_not_ind {x y : IConstantInfo}
    (h : ¬ ((∃ v c, x = .indInfo v c) ∧ ∃ v c, y = .indInfo v c)) :
    ConRon.Arena.pinAgrees x y = decide (x = y) := by
  cases x <;> cases y <;> simp_all [ConRon.Arena.pinAgrees]
  all_goals (rw [Bool.eq_iff_iff]; simp)

theorem ciD_ind {R : Nat → Option Word} {q : Nat} {v : IConstantVal} {c : IIndCaps}
    (h : decCI R q = some (.indInfo v c)) : ∃ w, R q = some w ∧ w.toNat = 3 := by
  obtain ⟨wk, e, hx⟩ := ciD h
  refine ⟨wk, e, ?_⟩
  rcases hx with ⟨k, _, _, h1⟩ | ⟨k, _, _, _, _, _, _, h1⟩ | ⟨k, _, _, h1⟩ | ⟨k, _⟩ |
    ⟨k, _, _, _, _, _, _, h1⟩ | ⟨k, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1⟩
  all_goals first | exact k | cases h1

/-- **`pin_agrees(c, d)` decides `pinAgrees`** (pure). -/
theorem pinAgreesW_ok {p : Prog} (hc : CanonProg p)
    (hp : p.lookup "pin_agrees" = some L.Ind.pinAgrees) {n : Nat} {m m' : Mem} {c d : Word}
    {r : List Word} {x y : IConstantInfo}
    (hx : decCI (erecP m) c.toNat = some x) (hy : decCI (erecP m) d.toNat = some y)
    (h : callW p n "pin_agrees" [c, d] m = some (r, m')) :
    m' = m ∧ (r.headD 0 ≠ 0 ↔ ConRon.Arena.pinAgrees x y = true) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAgrees_specW p hp n _ c d) h
  cases n with
  | zero => simp [pinAgreesW] at hW
  | succ n =>
  obtain ⟨wk, e, hxk⟩ := ciD hx
  obtain ⟨wk', e', hyk⟩ := ciD hy
  have r1 : erRd m c = wk := erRd_of _ _ e
  have r2 : erRd m d = wk' := erRd_of _ _ e'
  by_cases h3 : erRd m c = 3 ∧ erRd m d = 3
  · rw [pinAgreesW.arm1 p n m c d h3] at hW
    cases h1 : callW p n "cv_eq" [c + 1, d + 1] m with
    | none => rw [h1] at hW; simp [pinAgreesW.k_cv_eq] at hW
    | some x1 =>
    obtain ⟨r1', m1⟩ := x1
    obtain ⟨s1, rfl, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (cvEq_spec' p hc n _ (c + 1) (d + 1)) h1
    rw [h1] at hW; simp only [pinAgreesW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    refine ⟨hm.symm.trans hm1, ?_⟩
    rw [r1] at h3; rw [r2] at h3
    obtain ⟨rfl, rfl⟩ := h3
    rcases hxk with ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨-, cv, caps, hcv, -, rfl⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ <;>
      try (simp at k0)
    rcases hyk with ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨-, cv', caps', hcv', -, rfl⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ <;>
      try (simp at k0)
    have hb := cvEqB_ok' (erRdOK m) (p := c) (q := d) (k := 1) (kn := 1) rfl hcv hcv'
    simp only [List.headD_cons, hr1, hb, ConRon.Arena.pinAgrees, beq_iff_eq]
    by_cases hcc : cv = cv' <;> simp [hcc]
  · rw [pinAgreesW.eq_2] at hW; erw [ite_eq_right h3] at hW
    cases h1 : callW p n "ci_eq" [c, d] m with
    | none => rw [h1] at hW; simp [pinAgreesW.k_cv_eq] at hW
    | some x1 =>
    obtain ⟨r1', m1⟩ := x1
    obtain ⟨s1, rfl, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (ciEq_spec' p hc n _ c d) h1
    rw [h1] at hW; simp only [pinAgreesW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    refine ⟨hm.symm.trans hm1, ?_⟩
    have hni : ¬ ((∃ v c, x = .indInfo v c) ∧ ∃ v c, y = .indInfo v c) := by
      rintro ⟨⟨v, cp, rfl⟩, ⟨v', cp', rfl⟩⟩
      apply h3
      obtain ⟨w, e1, k0⟩ := ciD_ind hx
      obtain ⟨w', e1', k1⟩ := ciD_ind hy
      rw [r1, r2]
      rw [e] at e1; rw [e'] at e1'
      cases e1; cases e1'
      exact ⟨UInt64.toNat_inj.mp (by rw [k0]; rfl), UInt64.toNat_inj.mp (by rw [k1]; rfl)⟩
    have hb := ciEqB_ok (erRdOK m) hx hy
    simp only [List.headD_cons, hr1, hb, pinAgrees_eq_of_not_ind hni]
    by_cases hcc : x = y <;> simp [hcc]


/-! ## The program facts -/

/-- **The program `pin_list_ok` runs in**: the basis entry points' (`BasisLProg`) and the
comparison's functions. -/
structure PinListLProg (p : Prog) : Prop where
  basis : BasisLProg p
  pa : p.lookup "pin_agrees" = some L.Ind.pinAgrees
  pco : p.lookup "pin_copy_ok" = some L.Ind.pinCopyOk
  pcs : p.lookup "pin_copies_ok" = some L.Ind.pinCopiesOk
  plg : p.lookup "pin_link_go" = some L.Ind.pinLinkGo
  plo : p.lookup "pin_link_ok" = some L.Ind.pinLinkOk
  cn : p.lookup "const_named" = some L.Ind.constNamed
  rlo : p.lookup "rules_link_ok" = some L.Ind.rulesLinkOk
  blo : p.lookup "block_link_ok_at" = some L.Ind.blockLinkOkAt
  blg : p.lookup "block_links_ok_go" = some L.Ind.blockLinksOkGo
  bls : p.lookup "block_links_ok" = some L.Ind.blockLinksOk
  pl : p.lookup "pin_list_ok" = some L.Ind.pinListOk

theorem PinListLProg.canon {p : Prog} (h : PinListLProg p) : CanonProg p :=
  h.basis.rules.toQuotAtProg.canon

/-! ## `pin_copy_ok` -/

section copy
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- What the comparison's steps keep: the stage relation, the pools grown, the twin's state
well formed and its store extended. -/
def CmpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState)
    (r : List Word) (b : Bool) (m' : Mem) (a' : AState) : Prop :=
  StageT dn vis fe m' a' ∧ IWGrow m m' ∧ ConRon.Bridge.StateOK a' ∧ ConRon.Bridge.ReadOK a' ∧
    Ext a.store a'.store ∧ (r.headD 0 ≠ 0 ↔ b = true)

/-- **`pin_copy_ok(c, pin)` refines `pinCopyOk ci pc`**: `c`'s names (`cv_lps`, `sl_nodup`), their
count against the pin's, the pin at them (`ci_at_lps`) and `pin_agrees`. -/
theorem pinCopyOk_sim (hP : PinListLProg p) (n : Nat) {m : Mem} {a : AState} {c pin : Word}
    {ci pc : IConstantInfo} {C P : ConLeche.ConstantInfo}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hci : decCI (erecP m) c.toNat = some ci) (hpc : decCI (erecP m) pin.toNat = some pc)
    (hdc : Frontend.denoteCI a.store ci = some C) (hdp : Frontend.denoteCI a.store pc = some P) :
    Sim (callW p n "pin_copy_ok" [c, pin] m) (ConRon.Arena.pinCopyOk ci pc) a
      (fun r b m' a' => CmpPost dn vis fe m a r b m' a') := by
  have hQ := hP.basis.rules.toQuotAtProg
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinCopyOk_specW p hP.pco n _ c pin) h
  cases n with
  | zero => simp [pinCopyOkW] at hW
  | succ n =>
  rw [pinCopyOkW.arm1] at hW
  have hccv : decCV (erecP m) (c.toNat + 1) = some ci.toConstantVal := decCI_cvA hci
  have hpcv : decCV (erecP m) (pin.toNat + 1) = some pc.toConstantVal := decCI_cvA hpc
  obtain ⟨hsl, hlen, -⟩ := L.Arena.decCV_rd (erRdOK m) hccv
  obtain ⟨-, hplen, -⟩ := L.Arena.decCV_rd (erRdOK m) hpcv
  -- `cv_lps(c + 1)`
  cases h2 : callW p n "cv_lps" [c + 1] m with
  | none => rw [h2] at hW; simp [pinCopyOkW.k_cv_lps] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at hW; simp only [pinCopyOkW.k_cv_lps] at hW
  obtain ⟨s2, rfl, -, hW2, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (cvLps_specW p hQ.iwAlloc hQ.erCopy hQ.erToIw hQ.cvLps n _ (c + 1)) h2
  cases n with
  | zero => exact absurd hW2 (by simp [L.Arena.cvLpsW])
  | succ n0 =>
  rw [L.Arena.cvLpsW_step] at hW2
  have hW2' : erToIwW n0 m (erRd m (c + 2)) (erRd m (c + 3)) = some (r2, s2.mem) := by
    rw [← L.add_one_add_one, ← word_add12]; exact hW2
  obtain ⟨hS2, hg2, hdl2, htop2, -⟩ := erToIwW_stage hW2' hT.stage hsl
  have hf2 := erToIwW_iwFr hW2'
  have hT2 : StageT dn vis fe s2.mem a := StageT.of_iw hT hS2 hf2
  have hrd2 := erRd_congr (m := m) (m' := s2.mem) (hf2.arr _ (by decide) (by decide))
    (hf2.arr _ (by decide) (by decide))
  have he2 : erecP s2.mem = erecP m := erecP_frame hf2 (by decide) (by decide) (by decide) (by decide)
  -- `sl_nodup(io, il)`
  obtain ⟨ws, hws, hwsd, hwH⟩ := slR_of_decHL s2.mem _ _ _ hdl2
    (by have := (rdW (s2.mem.arr64 CTL) 200).toNat_lt; simp only [iwTop] at htop2; omega)
  simp only [UInt64.ofNat_toNat] at hws
  cases h3 : callW p (n0 + 1) "sl_nodup" [r2.headD 0, r2.tail.headD 0] s2.mem with
  | none => rw [h3] at hW; simp [pinCopyOkW.k_sl_nodup] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  obtain ⟨s3, rfl, -, hm3, hnd⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (slNodup_refines p hQ.slContains hQ.slNodup (n0 + 1) _ _ _ ws hws hwH) h3
  rw [h3] at hW; simp only [pinCopyOkW.k_sl_nodup] at hW
  simp only [hm3, hrd2] at hW
  rw [← hwsd] at hnd
  have hlen2 : ci.toConstantVal.levelParams.length = (r2.tail.headD 0).toNat := hslice?_lenR hdl2
  have hcond : (r3.headD 0 ≠ 0 ∧ r2.tail.headD 0 = erRd m (pin + 3)) ↔
      (nameNodup ci.toConstantVal.levelParams &&
        ci.toConstantVal.levelParams.length == pc.toConstantVal.levelParams.length) = true := by
    rw [Bool.and_eq_true, ← hnd, beq_iff_eq, hlen2, hplen, bne_iff_ne, ne_eq]
    exact and_congr_right fun _ => ⟨fun e => by rw [e], fun e => UInt64.toNat_inj.mp e⟩
  by_cases hc : r3.headD 0 ≠ 0 ∧ r2.tail.headD 0 = erRd m (pin + 3)
  case neg =>
    rw [ite_eq_right hc] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have e2 : s'.mem = s2.mem := by
      first | exact e.symm.trans hm3 | exact e.trans hm3 | exact e | exact e.symm
    have hc' := mt hcond.mpr hc
    refine ⟨false, a, ?_, ?_⟩
    · simp only [ConRon.Arena.pinCopyOk]
      rw [ite_eq_right (by simpa using hc')]; rfl
    · rw [e2]; exact ⟨hT2, hg2, hok, hr, Ext.refl _, by simp⟩
  rw [ite_eq_left hc] at hW
  -- `ci_at_lps(pin, EREC⦃c + 2⦄, EREC⦃c + 3⦄)`
  cases h4 : callW p (n0 + 1) "ci_at_lps" [pin, erRd m (c + 2), erRd m (c + 3)] s2.mem with
  | none => rw [h4] at hW; simp [pinCopyOkW.k_ci_at_lps] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4] at hW; simp only [pinCopyOkW.k_ci_at_lps] at hW
  have hps := (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hdc)).2.1
  obtain ⟨x, a4, hrun4, hT4, hg4, hx4⟩ :=
    (ciAtLpsSim_of hP.basis.rules.toCiProg (rulesAtSim_of hP.basis.rules)).ci (n0 + 1) vis fe s2.mem a
      _ _ _ pc ci.toConstantVal.levelParams _ P hT2 hok hr (by rw [he2]; exact hpc) hdp
      (by rw [he2]; exact hsl) hps r4 m4 h4
  obtain ⟨hst4, -⟩ := ConRon.Bridge.IConstantInfo.atLps_run hok hr hdp hps hrun4
  -- `pin_agrees(c, x)`
  cases h5 : callW p (n0 + 1) "pin_agrees" [c, r4.headD 0] m4 with
  | none => rw [h5] at hW; simp [pinCopyOkW.k_pin_agrees] at hW
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at hW; simp only [pinCopyOkW.k_pin_agrees, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  have hci4 : decCI (erecP m4) c.toNat = some ci := ArrExt.decCI hg4.ext (by rw [he2]; exact hci)
  obtain ⟨rfl, hb⟩ := pinAgreesW_ok hP.canon hP.pa hci4 hx4 h5
  refine ⟨ConRon.Arena.pinAgrees ci x, a4, ?_, ?_⟩
  · simp only [ConRon.Arena.pinCopyOk]
    rw [ite_eq_left (hcond.mp hc), StateT.run_bind, hrun4, exb]; rfl
  · rw [← e]
    exact ⟨hT4, hg2.trans hg4, hst4.ok, hst4.read, hst4.ext, by simpa using hb⟩

end copy


/-! ## `pin_copies_ok` -/

theorem CmpPost.refl {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {r : List Word} {b : Bool} (hT : StageT dn vis fe m a)
    (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a) (hb : r.headD 0 ≠ 0 ↔ b = true) :
    CmpPost dn vis fe m a r b m a := ⟨hT, IWGrow.refl m, hok, hr, Ext.refl _, hb⟩

theorem slice_len {m : Mem} {o l : Word} {xs : List IConstantInfo} (h : PSlR0 ciF xs o l m) :
    xs.length = l.toNat := L.Ind.decPL_length (truncM m) h.1

theorem PSlR.toR0 {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) : PSlR0 f xs o l m := ⟨h.dec, Or.inr h.bound⟩

section copies
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`pin_copies_ok(co, cl, po, pl)` refines `pinCopiesOk cs ps`**, pair by pair. -/
theorem pinCopiesOkW_ok (hP : PinListLProg p) : ∀ (n : Nat) (m m' : Mem) (a : AState)
    (co cl po pl : Word) (cs ps : List IConstantInfo) (r : List Word),
    StageT dn vis fe m a → ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a →
    PSlR0 ciF cs co cl m → PSlR0 ciF ps po pl m →
    (∃ B, Frontend.denoteCIList a.store cs = some B) →
    (∃ P, Frontend.denoteCIList a.store ps = some P) →
    pinCopiesOkW p n m co cl po pl = some (r, m') →
    ∃ b a', (ConRon.Arena.pinCopiesOk cs ps).run a = .ok (b, a') ∧
      CmpPost dn vis fe m a [r.headD 0] b m' a' := by
  intro n
  induction n with
  | zero => intro m m' a co cl po pl cs ps r _ _ _ _ _ _ _ h; simp [pinCopiesOkW] at h
  | succ n ih =>
  intro m m' a co cl po pl cs ps r hT hok hr hC hPs hdC hdP h
  have hsz := hT.stage.iw.iwSize
  have hlc := slice_len hC
  have hlp := slice_len hPs
  rw [pinCopiesOkW.eq_2] at h
  by_cases h1 : cl = 0 ∧ pl = 0
  · rw [ite_eq_left h1] at h; cases h
    obtain ⟨rfl, rfl⟩ := h1
    have e1 : cs = [] := List.eq_nil_of_length_eq_zero (by rw [hlc]; rfl)
    have e2 : ps = [] := List.eq_nil_of_length_eq_zero (by rw [hlp]; rfl)
    subst e1 e2
    exact ⟨true, a, rfl, CmpPost.refl hT hok hr (by simp)⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : cl = 0 ∨ pl = 0
  · rw [ite_eq_left h2] at h; cases h
    have hrun : (ConRon.Arena.pinCopiesOk cs ps).run a = .ok (false, a) := by
      rcases h2 with rfl | rfl
      · have e1 : cs = [] := List.eq_nil_of_length_eq_zero (by rw [hlc]; rfl)
        subst e1
        cases ps with
        | nil => exact absurd ⟨rfl, UInt64.toNat_inj.mp (by simpa using hlp.symm)⟩ h1
        | cons _ _ => rfl
      · have e2 : ps = [] := List.eq_nil_of_length_eq_zero (by rw [hlp]; rfl)
        subst e2
        cases cs with
        | nil => exact absurd ⟨UInt64.toNat_inj.mp (by simpa using hlc.symm), rfl⟩ h1
        | cons _ _ => rfl
    exact ⟨false, a, hrun, CmpPost.refl hT hok hr (by simp)⟩
  rw [ite_eq_right h2] at h
  have hcl : cl ≠ 0 := fun e => h2 (Or.inl e)
  have hpl : pl ≠ 0 := fun e => h2 (Or.inr e)
  obtain ⟨c, cs', rfl, hc, hC'⟩ := (hC.pslr hcl).uncons hcl hsz
  obtain ⟨q, ps', rfl, hq, hP'⟩ := (hPs.pslr hpl).uncons hpl hsz
  rw [decB_ciF] at hc hq
  obtain ⟨B, hB⟩ := hdC
  obtain ⟨PP, hPP⟩ := hdP
  obtain ⟨dc, dcs, hdc, hdcs, -⟩ := ConRon.Bridge.denoteCIList_cons hB
  obtain ⟨dq, dqs, hdq, hdqs, -⟩ := ConRon.Bridge.denoteCIList_cons hPP
  cases h3 : callW p n "pin_copy_ok" [rdW (m.arr64 IW) co, rdW (m.arr64 IW) po] m with
  | none => rw [h3] at h; simp [pinCopiesOkW.k_pin_copy_ok] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, pinCopiesOkW.k_pin_copy_ok.eq_2] at h
  obtain ⟨b3, a3, hrun3, hT3, hg3, hok3, hr3, hx3, hb3⟩ :=
    pinCopyOk_sim hP n hT hok hr hc hq hdc hdq r3 m3 h3
  have hstep : (ConRon.Arena.pinCopiesOk (c :: cs') (q :: ps')).run a =
      (if b3 then ConRon.Arena.pinCopiesOk cs' ps' else pure false).run a3 := by
    simp only [ConRon.Arena.pinCopiesOk, StateT.run_bind, hrun3, exb]
  by_cases h0 : r3.headD 0 = 0
  · rw [ite_eq_left h0] at h; cases h
    have : b3 = false := by cases b3 <;> simp_all
    subst this
    exact ⟨false, a3, by rw [hstep]; rfl, hT3, hg3, hok3, hr3, hx3, by simp⟩
  rw [ite_eq_right h0] at h
  have : b3 = true := hb3.mp h0
  subst this
  cases h4 : pinCopiesOkW p n m3 (co + 1) (cl - 1) (po + 1) (pl - 1) with
  | none => rw [h4] at h; simp [pinCopiesOkW.k_pin_copies_ok] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, pinCopiesOkW.k_pin_copies_ok.eq_2] at h
  cases h
  obtain ⟨b, a', hrun, hT', hg', hok', hr', hx', hb'⟩ :=
    ih m3 _ a3 _ _ _ _ cs' ps' r4 hT3 hok3 hr3 (hC'.toR0.grow ciF_mono hg3) (hP'.toR0.grow ciF_mono hg3)
      ⟨_, ConRon.Bridge.denoteCIList_mono hx3 _ _ hdcs⟩ ⟨_, ConRon.Bridge.denoteCIList_mono hx3 _ _ hdqs⟩ h4
  exact ⟨b, a', by rw [hstep]; exact hrun, hT', hg3.trans hg', hok', hr', hx3.trans hx', by simpa using hb'⟩

end copies


/-! ## `pin_link_ok`: the renaming on handles is con-leche's on names -/

/-- con-leche's `Level.subst` of a parameter at `.param` values, as a renaming of names (the
handle side's `canonNameMap`, on names). -/
def cnmN (ks vs : List ConLeche.Name) (n : ConLeche.Name) : ConLeche.Name :=
  match ks.findIdx? (fun k => k == n) with
  | some i => vs.getD i n
  | none => n

theorem subst_go_param : ∀ (ks vs : List ConLeche.Name) (n : ConLeche.Name),
    ConLeche.Level.subst.go ks (vs.map .param) n = .param (cnmN ks vs n)
  | [], vs, n => by simp [ConLeche.Level.subst.go, cnmN]
  | k :: ks, [], n => by
    simp only [List.map_nil, ConLeche.Level.subst.go, cnmN]
    split <;> simp
  | k :: ks, v :: vs, n => by
    simp only [List.map_cons, ConLeche.Level.subst.go]
    by_cases hk : k = n
    · subst hk; simp [cnmN, List.findIdx?_cons]
    · rw [ite_eq_right hk, subst_go_param ks vs n]
      have hb : (k == n) = false := by simpa using hk
      simp only [cnmN, List.findIdx?_cons, hb]
      cases ks.findIdx? (fun k => k == n) <;> simp

theorem canonNameMap_cnm {ns : ConRon.Arena.NStore} (hns : ConRon.Arena.NStoreWF ns)
    {ps cs : List NIdx} {psN csN : List ConLeche.Name}
    (hp : Frontend.denoteNList ns ps = some psN) (hc : Frontend.denoteNList ns cs = some csN)
    {n : NIdx} {nm : ConLeche.Name} (hn : ConRon.Arena.denoteN ns n = some nm) :
    ConRon.Arena.denoteN ns (ConRon.Arena.canonNameMap ps cs n) = some (cnmN psN csN nm) := by
  have hfi := ConRon.Bridge.canonFindIdx_denote hns ps psN hp n nm hn
  simp only [ConRon.Arena.canonNameMap, cnmN, hfi]
  cases psN.findIdx? (fun p => p == nm) with
  | none => exact hn
  | some i =>
    have hlen := ConRon.Bridge.denoteNList_length cs csN hc
    by_cases hi : i < cs.length
    · obtain ⟨hx, hd⟩ := ConRon.Bridge.denoteNList_get cs csN hc i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hx, Option.getD_some]
      exact hd
    · have h1 : cs[i]? = none := List.getElem?_eq_none (by omega)
      have h2 : csN[i]? = none := List.getElem?_eq_none (by omega)
      simp only [List.getD_eq_getElem?_getD, h1, h2, Option.getD_none]
      exact hn

theorem denoteNList_map_cnm {ns : ConRon.Arena.NStore} (hns : ConRon.Arena.NStoreWF ns)
    {ps cs : List NIdx} {psN csN : List ConLeche.Name}
    (hp : Frontend.denoteNList ns ps = some psN) (hc : Frontend.denoteNList ns cs = some csN) :
    ∀ (xs : List NIdx) (xsN : List ConLeche.Name), Frontend.denoteNList ns xs = some xsN →
      Frontend.denoteNList ns (xs.map (ConRon.Arena.canonNameMap ps cs)) = some (xsN.map (cnmN psN csN))
  | [], xsN, h => by simp [Frontend.denoteNList] at h ⊢; exact h
  | x :: xs, xsN, h => by
    cases hx : ConRon.Arena.denoteN ns x with
    | none => simp [Frontend.denoteNList, hx] at h
    | some nm =>
      cases hxs : Frontend.denoteNList ns xs with
      | none => simp [Frontend.denoteNList, hx, hxs] at h
      | some ys =>
        simp only [Frontend.denoteNList, hx, hxs, Option.some.injEq] at h
        subst h
        have := denoteNList_map_cnm hns hp hc xs ys hxs
        simp only [List.map_cons, Frontend.denoteNList, canonNameMap_cnm hns hp hc hx, this]

/-- **con-leche's `pinLinkOk` on the read-back names is the renaming test on handles.** -/
theorem pinLinkOk_handles {st : EStore} (hwf : StoreWF st) {R Rp C Cp : List NIdx}
    {RT RpT CT CpT : List ConLeche.Name}
    (hR : Frontend.denoteNList st.ns R = some RT) (hRp : Frontend.denoteNList st.ns Rp = some RpT)
    (hC : Frontend.denoteNList st.ns C = some CT) (hCp : Frontend.denoteNList st.ns Cp = some CpT) :
    ConLeche.pinLinkOk RT RpT CT CpT = decide (C = Cp.map (ConRon.Arena.canonNameMap Rp R)) := by
  obtain ⟨rk, hrk⟩ := hwf
  have hns : ConRon.Arena.NStoreWF st.ns := hrk.nsWF
  have hm := denoteNList_map_cnm hns hRp hR Cp CpT hCp
  have e1 : (CpT.map fun p => ConLeche.Level.subst RpT (RT.map ConLeche.Level.param) (.param p)) =
      (CpT.map (cnmN RpT RT)).map ConLeche.Level.param := by
    simp only [List.map_map]
    congr 1; funext p
    simp [ConLeche.Level.subst, subst_go_param]
  rw [ConLeche.pinLinkOk, e1]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have h' : CT = CpT.map (cnmN RpT RT) :=
      (List.map_inj_right (fun a b e => by cases e; rfl)).mp h
    rw [h'] at hC
    exact ConRon.Bridge.denoteNList_inj ⟨rk, hrk⟩ _ _ _ hC hm
  · intro h
    rw [h, hm] at hC
    cases hC; rfl

/-! ## `pin_link_go`, `pin_link_ok` -/

section link
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`pin_link_go` decides the renaming test** on the first `k` names (pure). -/
theorem pinLinkGoW_ok (hP : PinListLProg p) {m : Mem} {ro rl rpo rpl : Word} {R Rp : List NIdx}
    (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hR : decHL m ro.toNat rl.toNat = some R) (hRp : decHL m rpo.toNat rpl.toNat = some Rp) :
    ∀ (n : Nat) (co cpo k : Word) (C Cp : List NIdx) (r : List Word) (m' : Mem),
      decHL m co.toNat k.toNat = some C → decHL m cpo.toNat k.toNat = some Cp →
      pinLinkGoW p n m ro rl rpo rpl co cpo k = some (r, m') →
      m' = m ∧ (r.headD 0 ≠ 0 ↔ C = Cp.map (ConRon.Arena.canonNameMap Rp R)) := by
  have hc := hP.canon
  intro n
  induction n with
  | zero => intro co cpo k C Cp r m' _ _ h; simp [pinLinkGoW] at h
  | succ n ih =>
  intro co cpo k C Cp r m' hC hCp h
  rw [pinLinkGoW.eq_2] at h
  by_cases hk : k = 0
  · rw [ite_eq_left hk] at h; cases h
    subst hk
    have e1 : C = [] := by simpa [decHL, hslice?] using hC.symm
    have e2 : Cp = [] := by simpa [decHL, hslice?] using hCp.symm
    subst e1 e2
    exact ⟨rfl, by simp⟩
  rw [ite_eq_right hk] at h
  obtain ⟨w, C', rfl, hw, hwlt, hC'⟩ := decHL_cons hC hk (decHL_bnd m co k hC hsz)
  obtain ⟨v, Cp', rfl, hv, hvlt, hCp'⟩ := decHL_cons hCp hk (decHL_bnd m cpo k hCp hsz)
  cases h1 : callW p n "canon_name_map" [rpo, rpl, ro, rl, rdW (m.arr64 IW) cpo] m with
  | none => rw [h1] at h; simp [pinLinkGoW.k_canon_name_map] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hm1, hlt1, hd1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (canonNameMap_refines p (hc.get "sl_find") (hc.get "sl_getd") (hc.get "canon_name_map") n _
      rpo rpl ro rl _ Rp R hRp hR (decHL_bnd m rpo rpl hRp hsz) (decHL_bnd m ro rl hR hsz)
      (by rw [hv]; exact hvlt)) h1
  rw [h1, pinLinkGoW.k_canon_name_map.eq_2] at h
  simp only at hm1
  rw [hm1, hw] at h
  rw [hv] at hd1
  have hiff : (decI w : NIdx) = ConRon.Arena.canonNameMap Rp R (decI v) ↔ w = r1.headD 0 := by
    rw [← hd1]; exact decI_inj_iff hwlt hlt1
  by_cases hne : w ≠ r1.headD 0
  · rw [ite_eq_left hne] at h; cases h
    refine ⟨rfl, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, List.map_cons, List.cons.injEq, false_iff,
      not_and]
    exact fun e => absurd (hiff.mp e) hne
  rw [ite_eq_right hne] at h
  cases h2 : pinLinkGoW p n m ro rl rpo rpl (co + 1) (cpo + 1) (k - 1) with
  | none => rw [h2] at h; simp [pinLinkGoW.k_pin_link_go] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, pinLinkGoW.k_pin_link_go.eq_2] at h
  cases h
  obtain ⟨rfl, hb⟩ := ih _ _ _ C' Cp' r2 _ hC' hCp' h2
  refine ⟨rfl, ?_⟩
  simp only [List.headD_cons, List.map_cons, List.cons.injEq]
  rw [hb]
  exact ⟨fun e => ⟨hiff.mpr (Classical.not_not.mp hne), e⟩, fun e => e.2⟩

/-- **`pin_link_ok` decides the renaming test** (pure): the lengths, then `pin_link_go`. -/
theorem pinLinkOkW_ok (hP : PinListLProg p) {m : Mem} {ro rl rpo rpl : Word} {R Rp : List NIdx}
    (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hR : decHL m ro.toNat rl.toNat = some R) (hRp : decHL m rpo.toNat rpl.toNat = some Rp)
    {n : Nat} {co cl cpo cpl : Word} {C Cp : List NIdx} {r : List Word} {m' : Mem}
    (hC : decHL m co.toNat cl.toNat = some C) (hCp : decHL m cpo.toNat cpl.toNat = some Cp)
    (h : pinLinkOkLW p n m ro rl rpo rpl co cl cpo cpl = some (r, m')) :
    m' = m ∧ (r.headD 0 ≠ 0 ↔ C = Cp.map (ConRon.Arena.canonNameMap Rp R)) := by
  cases n with
  | zero => simp [pinLinkOkLW] at h
  | succ n =>
  by_cases hl : cl = cpl
  · subst hl
    rw [pinLinkOkLW.arm2 p n m _ _ _ _ _ _ _ _ rfl] at h
    cases h1 : callW p n "pin_link_go" [ro, rl, rpo, rpl, co, cpo, cl] m with
    | none => rw [h1] at h; simp [pinLinkOkLW.k_pin_link_go] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, pinLinkOkLW.k_pin_link_go.eq_2] at h
    cases h
    obtain ⟨s1, rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (pinLinkGo_specW p hP.plg n _ ro rl rpo rpl co cpo cl) h1
    obtain ⟨e, hb⟩ := pinLinkGoW_ok hP hsz hR hRp n co cpo cl C Cp r1 _ hC hCp hW
    exact ⟨e, by simpa using hb⟩
  · rw [pinLinkOkLW.arm1 p n m _ _ _ _ _ _ _ _ hl] at h
    cases h
    refine ⟨rfl, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff]
    intro e
    apply hl
    have h1 := decHL_length m hC
    have h2 := decHL_length m hCp
    rw [e, List.length_map] at h1
    exact UInt64.toNat_inj.mp (h1.symm.trans h2)

/-- **The twin's `pinLinkOk` on read-back handles**: its four name readbacks (the caches only),
the renaming test on handles. -/
theorem pinLinkOk_twin {m : Mem} {a : AState} (hT : StageT dn vis fe m a)
    (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a) {R Rp C Cp : List NIdx}
    {RT RpT CT CpT : List ConLeche.Name}
    (hR : Frontend.denoteNList a.store.ns R = some RT) (hRp : Frontend.denoteNList a.store.ns Rp = some RpT)
    (hC : Frontend.denoteNList a.store.ns C = some CT) (hCp : Frontend.denoteNList a.store.ns Cp = some CpT) :
    ∃ a', (ConRon.Arena.pinLinkOk R Rp C Cp).run a =
        .ok (decide (C = Cp.map (ConRon.Arena.canonNameMap Rp R)), a') ∧
      StageT dn vis fe m a' ∧ ConRon.Bridge.StateOK a' ∧ ConRon.Bridge.ReadOK a' ∧ Ext a.store a'.store := by
  obtain ⟨X1, h1, hc1⟩ := pr_readNamesM_run R a RT (denoteNList_mapM hR) hT.twin.den.readN
  obtain ⟨X2, h2, hc2⟩ := pr_readNamesM_run Rp { a with caches := { a.caches with readNC := X1 } } RpT
    (denoteNList_mapM hRp) hc1
  obtain ⟨X3, h3, hc3⟩ := pr_readNamesM_run C { a with caches := { a.caches with readNC := X2 } } CT
    (denoteNList_mapM hC) hc2
  obtain ⟨X4, h4, hc4⟩ := pr_readNamesM_run Cp { a with caches := { a.caches with readNC := X3 } } CpT
    (denoteNList_mapM hCp) hc3
  have hrun : (ConRon.Arena.pinLinkOk R Rp C Cp).run a =
      .ok (ConLeche.pinLinkOk RT RpT CT CpT, { a with caches := { a.caches with readNC := X4 } }) := by
    simp only [ConRon.Arena.pinLinkOk, StateT.run_bind, h1, except_ok_bind, h2, h3, h4]; rfl
  obtain ⟨hs, -⟩ := ConRon.Bridge.pinLinkOk_run hok hr hR hRp hC hCp hrun
  refine ⟨_, by rw [hrun, pinLinkOk_handles hok.wf hR hRp hC hCp], ?_, hs.ok, hs.read, hs.ext⟩
  exact (((hT.readNC X1 hc1).readNC X2 hc2).readNC X3 hc3).readNC X4 hc4

end link

/-! ## `const_named`, `cv_lps` -/

/-- What `const_named` returns for `constNamed?`'s answer. -/
def NamedR (m : Mem) : Option IConstantInfo → List Word → Prop
  | none, r => r.headD 0 = 0
  | some ci, r => r.headD 0 = 1 ∧ decCI (erecP m) (r.tail.headD 0).toNat = some ci

/-- **`const_named(o, l, n)` finds `constNamed? cs n`** (pure). -/
theorem constNamedW_ok {m : Mem} (hsz : (m.arr64 IW).size < 2 ^ 64) {nw : Word}
    (hnw : nw.toNat < 2 ^ 32) :
    ∀ (n : Nat) (o l : Word) (cs : List IConstantInfo) (r : List Word) (m' : Mem),
      PSlR0 ciF cs o l m → constNamedW n m o l nw = some (r, m') →
      m' = m ∧ NamedR m (ConRon.Arena.constNamed? cs (decI nw)) r := by
  intro n
  induction n with
  | zero => intro o l cs r m' _ h; simp [constNamedW] at h
  | succ n ih =>
  intro o l cs r m' hC h
  by_cases hl : l = 0
  · subst hl
    rw [constNamedW.eq_2, ite_eq_left rfl] at h; cases h
    have e1 : cs = [] := List.eq_nil_of_length_eq_zero (by rw [slice_len hC]; rfl)
    subst e1
    exact ⟨rfl, rfl⟩
  obtain ⟨c, cs', rfl, hc, hC'⟩ := (hC.pslr hl).uncons hl hsz
  rw [decB_ciF] at hc
  obtain ⟨w, hw, hwlt, hname⟩ := decCI_name hc
  have hrd : erRd m (rdW (m.arr64 IW) o + 1) = w := (erRdOK m).at 1 rfl hw
  by_cases he : erRd m (rdW (m.arr64 IW) o + 1) = nw
  · rw [constNamedW.arm2 n m o l nw hl he] at h; cases h
    have hb : (c.name == decI nw) = true := by rw [hname, ← hrd, he]; simp
    refine ⟨rfl, ?_⟩
    simp only [ConRon.Arena.constNamed?, List.find?_cons, hb]
    exact ⟨rfl, hc⟩
  · rw [constNamedW.arm3 n m o l nw hl he] at h
    cases h1 : constNamedW n m (o + 1) (l - 1) nw with
    | none => rw [h1] at h; simp [constNamedW.k_const_named] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, constNamedW.k_const_named.eq_2] at h; cases h
    obtain ⟨rfl, hr⟩ := ih _ _ cs' r1 _ hC'.toR0 h1
    have hne : (decI w : NIdx) ≠ decI nw := fun e => he (hrd.trans ((decI_inj_iff hwlt hnw).mp e))
    have hb : (c.name == decI nw) = false := by rw [hname]; simpa using hne
    refine ⟨rfl, ?_⟩
    simp only [ConRon.Arena.constNamed?, List.find?_cons, hb]
    simp only [ConRon.Arena.constNamed?] at hr
    cases e : List.find? (fun c => c.name == decI nw) cs' <;> rw [e] at hr <;> simpa [NamedR] using hr

/-- A constant `constNamed?` finds in a denoted list is denoted. -/
theorem constNamed_den {st : EStore} :
    ∀ (cs : List IConstantInfo) (B : List ConLeche.ConstantInfo) (nm : NIdx) (c : IConstantInfo),
      Frontend.denoteCIList st cs = some B → ConRon.Arena.constNamed? cs nm = some c →
      ∃ x, Frontend.denoteCI st c = some x
  | [], _, _, _, _, h => by simp [ConRon.Arena.constNamed?] at h
  | y :: ys, B, nm, c, hB, h => by
    obtain ⟨x, xs, hx, hxs, -⟩ := ConRon.Bridge.denoteCIList_cons hB
    simp only [ConRon.Arena.constNamed?, List.find?_cons] at h
    split at h
    · cases h; exact ⟨x, hx⟩
    · exact constNamed_den ys xs nm c hxs h

/-- A name slice decoded below the top. -/
structure NSl (xs : List NIdx) (o l : Word) (m : Mem) : Prop where
  dec : decHL m o.toNat l.toNat = some xs
  bound : o.toNat + l.toNat ≤ iwTop m

theorem NSl.grow {xs : List NIdx} {o l : Word} {m m' : Mem} (h : NSl xs o l m) (hg : IWGrow m m') :
    NSl xs o l m' := ⟨decHL_grow' hg h.bound h.dec, Nat.le_trans h.bound hg.iw⟩

section cvl
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`cv_lps(c + 1)`** copies `c`'s names to a fresh `IW` slice; the records are untouched. -/
theorem cvLps_sim (hP : PinListLProg p) {n : Nat} {m m2 : Mem} {a : AState} {c : Word}
    {r2 : List Word} {ci : IConstantInfo} (hT : StageT dn vis fe m a)
    (hci : decCI (erecP m) c.toNat = some ci) (h : callW p n "cv_lps" [c + 1] m = some (r2, m2)) :
    StageT dn vis fe m2 a ∧ IWGrow m m2 ∧ erecP m2 = erecP m ∧ (∀ x, erRd m2 x = erRd m x) ∧
      NSl ci.toConstantVal.levelParams (r2.headD 0) (r2.tail.headD 0) m2 := by
  have hQ := hP.basis.rules.toQuotAtProg
  have hccv : decCV (erecP m) (c.toNat + 1) = some ci.toConstantVal := decCI_cvA hci
  obtain ⟨hsl, -, -⟩ := L.Arena.decCV_rd (erRdOK m) hccv
  obtain ⟨s2, rfl, -, hW2, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (cvLps_specW p hQ.iwAlloc hQ.erCopy hQ.erToIw hQ.cvLps n _ (c + 1)) h
  cases n with
  | zero => exact absurd hW2 (by simp [L.Arena.cvLpsW])
  | succ n0 =>
  rw [L.Arena.cvLpsW_step] at hW2
  have hW2' : erToIwW n0 m (erRd m (c + 2)) (erRd m (c + 3)) = some (r2, s2.mem) := by
    rw [← L.add_one_add_one, ← word_add12]; exact hW2
  obtain ⟨hS2, hg2, hdl2, htop2, -⟩ := erToIwW_stage hW2' hT.stage hsl
  have hf2 := erToIwW_iwFr hW2'
  exact ⟨StageT.of_iw hT hS2 hf2, hg2,
    erecP_frame hf2 (by decide) (by decide) (by decide) (by decide),
    erRd_congr (hf2.arr _ (by decide) (by decide)) (hf2.arr _ (by decide) (by decide)),
    hdl2, Nat.le_of_eq htop2⟩

end cvl

/-! ## `rules_link_ok` -/

section rules
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`rules_link_ok` refines `rulesLinkOk`**, rule by rule. -/
theorem rulesLinkOkW_ok (hP : PinListLProg p) {block pins : List IConstantInfo}
    {bo bl po pl ro rl rpo rpl : Word} {R Rp : List NIdx} :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (qo ql : Word) (rules : List IRecRule) (r : List Word),
    StageT dn vis fe m a → ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a →
    PSlR0 ciF block bo bl m → PSlR0 ciF pins po pl m → NSl R ro rl m → NSl Rp rpo rpl m →
    (∃ B, Frontend.denoteCIList a.store block = some B) →
    (∃ P, Frontend.denoteCIList a.store pins = some P) →
    (∃ RT, Frontend.denoteNList a.store.ns R = some RT) →
    (∃ RpT, Frontend.denoteNList a.store.ns Rp = some RpT) →
    decRules (erecP m) qo.toNat ql.toNat = some rules →
    rulesLinkOkW p n m bo bl po pl ro rl rpo rpl qo ql = some (r, m') →
    ∃ b a', (ConRon.Arena.rulesLinkOk block pins R Rp rules).run a = .ok (b, a') ∧
      CmpPost dn vis fe m a [r.headD 0] b m' a' := by
  intro n
  induction n with
  | zero => intro m m' a qo ql rules r _ _ _ _ _ _ _ _ _ _ _ _ h; simp [rulesLinkOkW] at h
  | succ n ih =>
  intro m m' a qo ql rules r hT hok hr hB hPs hR hRp hdB hdP hdR hdRp hrs h
  have hsz := hT.stage.iw.iwSize
  rw [rulesLinkOkW.eq_2] at h
  by_cases hq : ql = 0
  · rw [ite_eq_left hq] at h; cases h
    subst hq
    simp only [decRules, show (0 : Word).toNat = 0 from rfl, List.range_zero, List.mapM_nil,
      Option.pure_def, Option.some.injEq] at hrs
    subst hrs
    exact ⟨true, a, rfl, CmpPost.refl hT hok hr (by simp)⟩
  rw [ite_eq_right hq] at h
  obtain ⟨k, hk⟩ : ∃ k, ql.toNat = k + 1 :=
    ⟨ql.toNat - 1, by have : ql.toNat ≠ 0 := fun e => hq (UInt64.toNat_inj.mp e); omega⟩
  rw [hk, decRules_succ] at hrs
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hrs
  obtain ⟨rl0, hrl, rls, hrls, rfl⟩ := hrs
  obtain ⟨wq, hwq, hwqlt, hctor⟩ := hd?_some (decRule_ctor hrl)
  have hrd : rdW (m.arr64 (tierA EREC (qo >>> 40))) (qo &&& 1099511627775) = wq := erRd_of qo wq hwq
  rw [hrd] at h
  -- `const_named(bo, bl, EREC⦃qo⦄)`
  cases h1 : callW p n "const_named" [bo, bl, wq] m with
  | none => rw [h1] at h; simp [rulesLinkOkW.k_const_named] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (constNamed_specW p hP.cn n _ bo bl wq) h1
  obtain ⟨e1, hn1⟩ := constNamedW_ok hsz hwqlt n bo bl block r1 _ hB hW1
  rw [h1, rulesLinkOkW.k_const_named.eq_2, e1, hrd] at h
  -- `const_named(po, pl, EREC⦃qo⦄)`
  cases h2 : callW p n "const_named" [po, pl, wq] m with
  | none => rw [h2] at h; simp [rulesLinkOkW.k_const_named_2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (constNamed_specW p hP.cn n _ po pl wq) h2
  obtain ⟨e2, hn2⟩ := constNamedW_ok hsz hwqlt n po pl pins r2 _ hPs hW2
  rw [h2, rulesLinkOkW.k_const_named_2.eq_2, e2] at h
  by_cases hz : r1.headD 0 = 0 ∨ r2.headD 0 = 0
  · rw [ite_eq_left hz] at h; cases h
    refine ⟨false, a, ?_, CmpPost.refl hT hok hr (by simp)⟩
    simp only [ConRon.Arena.rulesLinkOk, hctor]
    cases x1 : ConRon.Arena.constNamed? block (decI wq) with
    | none => rfl
    | some C =>
    cases x2 : ConRon.Arena.constNamed? pins (decI wq) with
    | none => rfl
    | some Cp =>
    rw [x1] at hn1; rw [x2] at hn2
    rcases hz with hz | hz
    · rw [hn1.1] at hz; cases hz
    · rw [hn2.1] at hz; cases hz
  rw [ite_eq_right hz] at h
  obtain ⟨hz1, hz2⟩ : r1.headD 0 ≠ 0 ∧ r2.headD 0 ≠ 0 := not_or.mp hz
  obtain ⟨C, x1⟩ : ∃ C, ConRon.Arena.constNamed? block (decI wq) = some C := by
    cases x1 : ConRon.Arena.constNamed? block (decI wq) with
    | none => rw [x1] at hn1; exact absurd hn1 hz1
    | some C => exact ⟨C, rfl⟩
  obtain ⟨Cp, x2⟩ : ∃ Cp, ConRon.Arena.constNamed? pins (decI wq) = some Cp := by
    cases x2 : ConRon.Arena.constNamed? pins (decI wq) with
    | none => rw [x2] at hn2; exact absurd hn2 hz2
    | some Cp => exact ⟨Cp, rfl⟩
  rw [x1] at hn1; rw [x2] at hn2
  -- `cv_lps(c + 1)`, `cv_lps(d + 1)`
  cases h3 : callW p n "cv_lps" [r1.tail.headD 0 + 1] m with
  | none => rw [h3] at h; simp [rulesLinkOkW.k_cv_lps] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  obtain ⟨hT3, hg3, he3, -, hN3⟩ := cvLps_sim hP hT hn1.2 h3
  rw [h3, rulesLinkOkW.k_cv_lps.eq_2] at h
  cases h4 : callW p n "cv_lps" [r2.tail.headD 0 + 1] m3 with
  | none => rw [h4] at h; simp [rulesLinkOkW.k_cv_lps_2] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  obtain ⟨hT4, hg4, he4, -, hN4⟩ := cvLps_sim hP hT3 (by rw [he3]; exact hn2.2) h4
  rw [h4, rulesLinkOkW.k_cv_lps_2.eq_2] at h
  -- `pin_link_ok(ro, rl, rpo, rpl, co, cl, so, sl)`
  have hg34 := hg3.trans hg4
  cases h5 : callW p n "pin_link_ok"
      [ro, rl, rpo, rpl, r3.headD 0, r3.tail.headD 0, r4.headD 0, r4.tail.headD 0] m4 with
  | none => rw [h5] at h; simp [rulesLinkOkW.k_pin_link_ok] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (pinLinkOkL_specW p hP.plo n _ ro rl rpo rpl _ _ _ _) h5
  obtain ⟨e5, hb5⟩ := pinLinkOkW_ok hP hT4.stage.iw.iwSize (hR.grow hg34).dec (hRp.grow hg34).dec
    (hN3.grow hg4).dec hN4.dec hW5
  obtain ⟨Bd, hBd⟩ := hdB
  obtain ⟨Pd, hPd⟩ := hdP
  obtain ⟨RT, hRT⟩ := hdR
  obtain ⟨RpT, hRpT⟩ := hdRp
  obtain ⟨xC, hxC⟩ := constNamed_den block Bd _ C hBd x1
  obtain ⟨xCp, hxCp⟩ := constNamed_den pins Pd _ Cp hPd x2
  obtain ⟨a5, hrun5, hT5, hok5, hr5, hx5⟩ := pinLinkOk_twin hT4 hok hr hRT hRpT
    (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hxC)).2.1
    (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hxCp)).2.1
  have hstep : (ConRon.Arena.rulesLinkOk block pins R Rp (rl0 :: rls)).run a =
      (if decide (C.toConstantVal.levelParams =
          Cp.toConstantVal.levelParams.map (ConRon.Arena.canonNameMap Rp R)) then
        ConRon.Arena.rulesLinkOk block pins R Rp rls else pure false).run a5 := by
    simp only [ConRon.Arena.rulesLinkOk, hctor, x1, x2, StateT.run_bind, hrun5, exb]
  rw [h5, rulesLinkOkW.k_pin_link_ok.eq_2] at h
  by_cases h0 : r5.headD 0 = 0
  · rw [ite_eq_left h0] at h; cases h
    have hf : ¬ C.toConstantVal.levelParams =
        Cp.toConstantVal.levelParams.map (ConRon.Arena.canonNameMap Rp R) := fun e => hb5.mpr e h0
    refine ⟨false, a5, by rw [hstep, decide_eq_false hf]; rfl, ?_⟩
    rw [e5]
    exact ⟨hT5, hg34, hok5, hr5, hx5, by simp⟩
  rw [ite_eq_right h0] at h
  have ht : C.toConstantVal.levelParams =
      Cp.toConstantVal.levelParams.map (ConRon.Arena.canonNameMap Rp R) := hb5.mp h0
  rw [e5] at h
  cases h6 : rulesLinkOkW p n m4 bo bl po pl ro rl rpo rpl (qo + 11) (ql - 1) with
  | none => rw [h6] at h; simp [rulesLinkOkW.k_rules_link_ok] at h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6, rulesLinkOkW.k_rules_link_ok.eq_2] at h
  cases h
  have hql : (ql - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  have hrs6 : decRules (erecP m4) (qo + 11).toNat (ql - 1).toNat = some rls := by
    rw [he4, he3, hql]; exact decRules_shift hrls (erRdOK m).lt
  obtain ⟨b, a', hrun, hT', hg', hok', hr', hx', hb'⟩ :=
    ih m4 _ a5 (qo + 11) (ql - 1) rls r6 hT5 hok5 hr5 (hB.grow ciF_mono hg34) (hPs.grow ciF_mono hg34)
      (hR.grow hg34) (hRp.grow hg34) ⟨_, ConRon.Bridge.denoteCIList_mono hx5 _ _ hBd⟩
      ⟨_, ConRon.Bridge.denoteCIList_mono hx5 _ _ hPd⟩ ⟨_, ConRon.Bridge.denoteNListE_ext hx5 _ _ hRT⟩
      ⟨_, ConRon.Bridge.denoteNListE_ext hx5 _ _ hRpT⟩ hrs6 h6
  refine ⟨b, a', by rw [hstep, decide_eq_true ht]; exact hrun, hT', hg34.trans hg', hok', hr',
    hx5.trans hx', by simpa using hb'⟩

end rules

/-! ## `block_link_ok_at`, `block_links_ok_go`, `block_links_ok` -/

theorem kindW {m : Mem} {c : Word} {ci : IConstantInfo} (h : decCI (erecP m) c.toNat = some ci) :
    (erRd m c).toNat = ciKindQ ci := by
  obtain ⟨wk, e, -⟩ := ciD h
  rw [erRd_of c wk e]; exact decCI_kindW h e

theorem kindW_eq {m : Mem} {c : Word} {ci : IConstantInfo} (h : decCI (erecP m) c.toNat = some ci)
    (k : Word) : erRd m c = k ↔ ciKindQ ci = k.toNat := by
  rw [← kindW h]; exact ⟨fun e => by rw [e], fun e => UInt64.toNat_inj.mp e⟩

/-- A recursor record's rules, at the words its record holds. -/
theorem decCI_rec_rules {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {mi rp : Nat} {k : Bool} {rules : List IRecRule}
    (h : decCI R q.toNat = some (.recInfo cv mi rp k rules)) :
    decRules R (rd (q + 7)).toNat (rd (q + 8)).toNat = some rules := by
  obtain ⟨wk, -, hx⟩ := ciD h
  rcases hx with ⟨-, _, _, h1⟩ | ⟨-, _, _, _, _, _, _, h1⟩ | ⟨-, _, _, h1⟩ | ⟨-, _, _, _, _, h1⟩ |
    ⟨-, _, _, _, _, _, _, h1⟩ | ⟨-, cv', mi', rp', o, cnt, k', rules', -, -, -, ho, hcnt, -, hrules, h1⟩
  all_goals (try (cases h1; done))
  cases h1
  simp only [nat?, Option.map_eq_some_iff] at ho hcnt
  obtain ⟨w7, hw7, rfl⟩ := ho
  obtain ⟨w8, hw8, rfl⟩ := hcnt
  rw [hR.at 7 rfl hw7, hR.at 8 rfl hw8]
  exact hrules

section links
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`block_link_ok_at` refines `blockLinkOkAt`**: one pair. -/
theorem blockLinkOkAtW_ok (hP : PinListLProg p) {block pins : List IConstantInfo}
    {bo bl po pl fo fl : Word} {former : List NIdx} {n : Nat} {m m' : Mem} {a : AState}
    {c q : Word} {ci pi : IConstantInfo} {r : List Word}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hB : PSlR0 ciF block bo bl m) (hPs : PSlR0 ciF pins po pl m)
    (hdB : ∃ B, Frontend.denoteCIList a.store block = some B)
    (hdP : ∃ P, Frontend.denoteCIList a.store pins = some P)
    (hfo : hslice? (erecP m) fo.toNat fl.toNat = some former)
    (hci : decCI (erecP m) c.toNat = some ci) (hpi : decCI (erecP m) q.toNat = some pi)
    (hdc : ∃ x, Frontend.denoteCI a.store ci = some x) (hdp : ∃ x, Frontend.denoteCI a.store pi = some x)
    (h : blockLinkOkAtW p n m bo bl po pl fo fl c q = some (r, m')) :
    ∃ b a', (ConRon.Arena.blockLinkOkAt block pins former ci pi).run a = .ok (b, a') ∧
      CmpPost dn vis fe m a [r.headD 0] b m' a' := by
  cases n with
  | zero => simp [blockLinkOkAtW] at h
  | succ n =>
  by_cases k4 : erRd m c = 4
  · rw [blockLinkOkAtW.arm1 p n m bo bl po pl fo fl c q k4] at h; simp only [erRd_foldN] at h
    have hk := (kindW_eq hci 4).mp k4
    obtain ⟨cv, np, nf, rfl⟩ : ∃ cv np nf, ci = .ctorInfo cv np nf := by
      cases ci <;> simp [ciKindQ] at hk
      exact ⟨_, _, _, rfl⟩
    have hccv : decCV (erecP m) (c.toNat + 1) = some cv := decCI_cvA hci
    obtain ⟨hsl, -, -⟩ := L.Arena.decCV_rd (erRdOK m) hccv
    cases h1 : callW p n "er_sl_eq" [erRd m (c + 2), erRd m (c + 3), fo, fl] m with
    | none => rw [h1] at h; simp [blockLinkOkAtW.k_er_sl_eq] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    obtain ⟨s1, rfl, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (erSlEq_spec p hP.canon n _ _ _ _ _) h1
    rw [h1, blockLinkOkAtW.k_er_sl_eq.eq_2] at h; cases h
    have hb := erSlEqB_ok (erRdOK m) hsl hfo
    have hr1' : r1.headD 0 = if decide (cv.levelParams = former) then 1 else 0 := by
      rw [← hb]; exact hr1
    refine ⟨cv.levelParams == former, a, rfl, ?_⟩
    rw [hm1]
    refine CmpPost.refl hT hok hr ?_
    simp only [List.headD_cons, hr1']
    by_cases e : cv.levelParams = former <;> simp [e]
  by_cases k5 : erRd m c = 5 ∧ erRd m q = 5
  · rw [blockLinkOkAtW.arm2 p n m bo bl po pl fo fl c q k4 k5] at h
    have hk1 := (kindW_eq hci 5).mp k5.1
    have hk2 := (kindW_eq hpi 5).mp k5.2
    obtain ⟨cv, mi, rp, kk, rs, rfl⟩ : ∃ cv mi rp kk rs, ci = .recInfo cv mi rp kk rs := by
      cases ci <;> simp [ciKindQ] at hk1
      exact ⟨_, _, _, _, _, rfl⟩
    obtain ⟨cvp, mip, rpp, kkp, rsp, rfl⟩ : ∃ cv mi rp kk rs, pi = .recInfo cv mi rp kk rs := by
      cases pi <;> simp [ciKindQ] at hk2
      exact ⟨_, _, _, _, _, rfl⟩
    have hrules := decCI_rec_rules (erRdOK m) hpi
    cases h3 : callW p n "cv_lps" [c + 1] m with
    | none => rw [h3] at h; simp [blockLinkOkAtW.k_cv_lps] at h
    | some x3 =>
    obtain ⟨r3, m3⟩ := x3
    obtain ⟨hT3, hg3, he3, hrd3, hN3⟩ := cvLps_sim hP hT hci h3
    rw [h3, blockLinkOkAtW.k_cv_lps.eq_2] at h
    cases h4 : callW p n "cv_lps" [q + 1] m3 with
    | none => rw [h4] at h; simp [blockLinkOkAtW.k_cv_lps_2] at h
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    obtain ⟨hT4, hg4, he4, hrd4, hN4⟩ := cvLps_sim hP hT3 (by rw [he3]; exact hpi) h4
    rw [h4, blockLinkOkAtW.k_cv_lps_2.eq_2] at h
    have e7 : rdW (m4.arr64 (tierA EREC ((q + 7) >>> 40))) ((q + 7) &&& 1099511627775) =
        erRd m (q + 7) := (hrd4 _).trans (hrd3 _)
    have e8 : rdW (m4.arr64 (tierA EREC ((q + 8) >>> 40))) ((q + 8) &&& 1099511627775) =
        erRd m (q + 8) := (hrd4 _).trans (hrd3 _)
    rw [e7, e8] at h
    have hg34 := hg3.trans hg4
    cases h5 : callW p n "rules_link_ok" [bo, bl, po, pl, r3.headD 0, r3.tail.headD 0, r4.headD 0,
        r4.tail.headD 0, erRd m (q + 7), erRd m (q + 8)] m4 with
    | none => rw [h5] at h; simp [blockLinkOkAtW.k_er_sl_eq] at h
    | some x5 =>
    obtain ⟨r5, m5⟩ := x5
    rw [h5, blockLinkOkAtW.k_er_sl_eq.eq_2] at h; cases h
    obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (rulesLinkOk_specW p hP.rlo n _ _ _ _ _ _ _ _ _ _ _) h5
    obtain ⟨xc, hxc⟩ := hdc
    obtain ⟨xp, hxp⟩ := hdp
    obtain ⟨b, a', hrun, hT', hg', hok', hr', hx', hb'⟩ := rulesLinkOkW_ok hP n m4 _ a _ _ rsp r5 hT4
      hok hr (hB.grow ciF_mono hg34) (hPs.grow ciF_mono hg34) (hN3.grow hg4) hN4 hdB hdP
      ⟨_, (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hxc)).2.1⟩
      ⟨_, (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hxp)).2.1⟩
      (by rw [he4, he3]; exact hrules) hW5
    exact ⟨b, a', hrun, hT', hg34.trans hg', hok', hr', hx', by simpa using hb'⟩
  rw [blockLinkOkAtW.arm3 p n m bo bl po pl fo fl c q k4 k5] at h; cases h
  refine ⟨true, a, ?_, CmpPost.refl hT hok hr (by simp)⟩
  have kc : ciKindQ ci ≠ 4 := fun e => k4 ((kindW_eq hci 4).mpr e)
  have kp : ¬ (ciKindQ ci = 5 ∧ ciKindQ pi = 5) := fun ⟨e1, e2⟩ =>
    k5 ⟨(kindW_eq hci 5).mpr e1, (kindW_eq hpi 5).mpr e2⟩
  cases ci <;> cases pi <;> first | rfl | (exfalso; simp [ciKindQ] at kc kp)

/-- **`block_links_ok_go` refines `blockLinksOkGo`**, pair by pair. -/
theorem blockLinksOkGoW_ok (hP : PinListLProg p) {block pins : List IConstantInfo}
    {bo bl po pl fo fl : Word} {former : List NIdx} :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (co cl qo ql : Word) (cs ps : List IConstantInfo)
      (r : List Word),
    StageT dn vis fe m a → ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a →
    PSlR0 ciF block bo bl m → PSlR0 ciF pins po pl m → PSlR0 ciF cs co cl m → PSlR0 ciF ps qo ql m →
    (∃ B, Frontend.denoteCIList a.store block = some B) →
    (∃ P, Frontend.denoteCIList a.store pins = some P) →
    (∃ Z, Frontend.denoteCIList a.store cs = some Z) →
    (∃ Q, Frontend.denoteCIList a.store ps = some Q) →
    hslice? (erecP m) fo.toNat fl.toNat = some former →
    blockLinksOkGoW p n m bo bl po pl fo fl co cl qo ql = some (r, m') →
    ∃ b a', (ConRon.Arena.blockLinksOkGo block pins former cs ps).run a = .ok (b, a') ∧
      CmpPost dn vis fe m a [r.headD 0] b m' a' := by
  intro n
  induction n with
  | zero => intro m m' a co cl qo ql cs ps r _ _ _ _ _ _ _ _ _ _ _ _ h; simp [blockLinksOkGoW] at h
  | succ n ih =>
  intro m m' a co cl qo ql cs ps r hT hok hr hB hPs hC hQ hdB hdP hdC hdQ hfo h
  have hsz := hT.stage.iw.iwSize
  rw [blockLinksOkGoW.eq_2] at h
  by_cases h1 : cl = 0 ∨ ql = 0
  · rw [ite_eq_left h1] at h; cases h
    refine ⟨true, a, ?_, CmpPost.refl hT hok hr (by simp)⟩
    rcases h1 with rfl | rfl
    · have e1 : cs = [] := List.eq_nil_of_length_eq_zero (by rw [slice_len hC]; rfl)
      subst e1; rfl
    · have e2 : ps = [] := List.eq_nil_of_length_eq_zero (by rw [slice_len hQ]; rfl)
      subst e2; cases cs <;> rfl
  rw [ite_eq_right h1] at h
  have hcl : cl ≠ 0 := fun e => h1 (Or.inl e)
  have hql : ql ≠ 0 := fun e => h1 (Or.inr e)
  obtain ⟨c, cs', rfl, hc, hC'⟩ := (hC.pslr hcl).uncons hcl hsz
  obtain ⟨q, ps', rfl, hq, hQ'⟩ := (hQ.pslr hql).uncons hql hsz
  rw [decB_ciF] at hc hq
  obtain ⟨Z, hZ⟩ := hdC
  obtain ⟨Q, hQd⟩ := hdQ
  obtain ⟨dc, dcs, hdc, hdcs, -⟩ := ConRon.Bridge.denoteCIList_cons hZ
  obtain ⟨dq, dqs, hdq, hdqs, -⟩ := ConRon.Bridge.denoteCIList_cons hQd
  cases h2 : callW p n "block_link_ok_at"
      [bo, bl, po, pl, fo, fl, rdW (m.arr64 IW) co, rdW (m.arr64 IW) qo] m with
  | none => rw [h2] at h; simp [blockLinksOkGoW.k_block_link_ok_at] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockLinkOkAt_specW p hP.blo n _ _ _ _ _ _ _ _ _) h2
  obtain ⟨b2, a2, hrun2, hT2, hg2, hok2, hr2, hx2, hb2⟩ :=
    blockLinkOkAtW_ok hP hT hok hr hB hPs hdB hdP hfo hc hq ⟨_, hdc⟩ ⟨_, hdq⟩ hW2
  rw [h2, blockLinksOkGoW.k_block_link_ok_at.eq_2] at h
  have hstep : (ConRon.Arena.blockLinksOkGo block pins former (c :: cs') (q :: ps')).run a =
      (if b2 then ConRon.Arena.blockLinksOkGo block pins former cs' ps' else pure false).run a2 := by
    simp only [ConRon.Arena.blockLinksOkGo, StateT.run_bind, hrun2, exb]
  by_cases h0 : r2.headD 0 = 0
  · rw [ite_eq_left h0] at h; cases h
    have : b2 = false := by cases b2 <;> simp_all
    subst this
    exact ⟨false, a2, by rw [hstep]; rfl, hT2, hg2, hok2, hr2, hx2, by simp⟩
  rw [ite_eq_right h0] at h
  have : b2 = true := (hb2.mp (by simpa using h0))
  subst this
  cases h3 : blockLinksOkGoW p n s2.mem bo bl po pl fo fl (co + 1) (cl - 1) (qo + 1) (ql - 1) with
  | none => rw [h3] at h; simp [blockLinksOkGoW.k_block_links_ok_go] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, blockLinksOkGoW.k_block_links_ok_go.eq_2] at h
  cases h
  obtain ⟨b, a', hrun, hT', hg', hok', hr', hx', hb'⟩ :=
    ih s2.mem _ a2 _ _ _ _ cs' ps' r3 hT2 hok2 hr2 (hB.grow ciF_mono hg2) (hPs.grow ciF_mono hg2)
      (hC'.toR0.grow ciF_mono hg2) (hQ'.toR0.grow ciF_mono hg2)
      (let ⟨_, hB'⟩ := hdB; ⟨_, ConRon.Bridge.denoteCIList_mono hx2 _ _ hB'⟩)
      (let ⟨_, hP'⟩ := hdP; ⟨_, ConRon.Bridge.denoteCIList_mono hx2 _ _ hP'⟩)
      ⟨_, ConRon.Bridge.denoteCIList_mono hx2 _ _ hdcs⟩ ⟨_, ConRon.Bridge.denoteCIList_mono hx2 _ _ hdqs⟩
      (hg2.ext.hslice? hfo) h3
  exact ⟨b, a', by rw [hstep]; exact hrun, hT', hg2.trans hg', hok', hr', hx2.trans hx',
    by simpa using hb'⟩

end links

section top
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`block_links_ok` refines `blockLinksOk`**: the former's names (the first member's), then
`block_links_ok_go` over the two slices. -/
theorem blockLinksOkW_ok (hP : PinListLProg p) {n : Nat} {m m' : Mem} {a : AState}
    {bo bl po pl : Word} {block pins : List IConstantInfo} {r : List Word}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hB : PSlR0 ciF block bo bl m) (hPs : PSlR0 ciF pins po pl m)
    (hdB : ∃ B, Frontend.denoteCIList a.store block = some B)
    (hdP : ∃ P, Frontend.denoteCIList a.store pins = some P)
    (h : blockLinksOkW p n m bo bl po pl = some (r, m')) :
    ∃ b a', (ConRon.Arena.blockLinksOk block pins).run a = .ok (b, a') ∧
      CmpPost dn vis fe m a [r.headD 0] b m' a' := by
  cases n with
  | zero => simp [blockLinksOkW] at h
  | succ n =>
  rw [blockLinksOkW.eq_2] at h
  obtain ⟨fo, fl, hfo, hj⟩ : ∃ fo fl : Word, hslice? (erecP m) fo.toNat fl.toNat =
      some ((block.head?.map (·.toConstantVal.levelParams)).getD []) ∧
      blockLinksOkW.j1 p n bo bl po pl fo fl m = some (r, m') := by
    by_cases hbl : bl ≠ 0
    · rw [ite_eq_left hbl] at h
      obtain ⟨c, cs', rfl, hc, -⟩ := (hB.pslr hbl).uncons hbl hT.stage.iw.iwSize
      rw [decB_ciF] at hc
      obtain ⟨hsl, -, -⟩ := L.Arena.decCV_rd (erRdOK m) (decCI_cvA hc)
      exact ⟨_, _, hsl, h⟩
    · rw [ite_eq_right hbl] at h
      have e1 : block = [] := List.eq_nil_of_length_eq_zero (by
        rw [slice_len hB, Classical.not_not.mp hbl]; rfl)
      subst e1
      exact ⟨0, 0, by simp [hslice?], h⟩
  rw [blockLinksOkW.j1.eq_1] at hj
  cases h1 : callW p n "block_links_ok_go" [bo, bl, po, pl, fo, fl, bo, bl, po, pl] m with
  | none => rw [h1] at hj; simp [blockLinksOkW.k_block_links_ok_go] at hj
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, blockLinksOkW.k_block_links_ok_go.eq_2] at hj; cases hj
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockLinksOkGo_specW p hP.blg n _ _ _ _ _ _ _ _ _ _ _) h1
  obtain ⟨b, a', hrun, hpost⟩ := blockLinksOkGoW_ok hP n m _ a bo bl po pl block pins r1 hT hok hr
    hB hPs hB hPs hdB hdP hdB hdP hfo hW1
  exact ⟨b, a', hrun, by simpa using hpost⟩

/-- A block decoded by `basisDec` is a pointer slice below the top unless empty. -/
theorem basisDec_pslr0 {m : Mem} {o l : Word} {xs : List IConstantInfo}
    (h : DecB (basisDec dn o.toNat l.toNat) m xs) : PSlR0 ciF xs o l m := by
  refine ⟨h, ?_⟩
  by_cases hl : l = 0
  · exact Or.inl hl
  right
  have hD : decPL (truncM m) (fun q => decCI (erA (truncM m)) q) o.toNat l.toNat = some xs := h
  have hl0 : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp e)
  obtain ⟨v, hv, -⟩ := decPL_get' hD (l.toNat - 1) (by omega)
  simp only [iwN, nat?, Option.map_eq_some_iff] at hv
  obtain ⟨w, hw, -⟩ := hv
  have := (truncM_iw_get hw).1
  omega

/-- **`pin_list_ok` refines `pinListOk`**: the copies (`pin_copies_ok`), then the links
(`block_links_ok`). -/
theorem pinListOkRef_of (hP : PinListLProg p) : PinListOkRef p := by
  intro dn vis fe io il po pl block pins n m a r m' ⟨hT, hok, hr, hdb, hdp, hB, hPd⟩ h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinListOkL_specW p hP.pl n _ io il po pl) h
  rw [hs'] at hW
  cases n with
  | zero => simp [pinListOkLW] at hW
  | succ n =>
  rw [pinListOkLW.arm1] at hW
  have hBs : PSlR0 ciF block io il m := basisDec_pslr0 hdb
  have hPs : PSlR0 ciF pins po pl m := basisDec_pslr0 hdp
  cases h1 : callW p n "pin_copies_ok" [io, il, po, pl] m with
  | none => rw [h1] at hW; simp [pinListOkLW.k_pin_copies_ok] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinCopiesOk_specW p hP.pcs n _ io il po pl) h1
  obtain ⟨b1, a1, hrun1, hT1, hg1, hok1, hr1, hx1, hb1⟩ :=
    pinCopiesOkW_ok hP n m _ a io il po pl block pins r1 hT hok hr hBs hPs hB hPd hW1
  rw [h1, pinListOkLW.k_pin_copies_ok.eq_2] at hW
  have hstep : (ConRon.Arena.pinListOk block pins).run a =
      (if b1 then ConRon.Arena.blockLinksOk block pins else pure false).run a1 := by
    simp only [ConRon.Arena.pinListOk, StateT.run_bind, hrun1, exb]
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at hW; cases hW
    have : b1 = false := by cases b1 <;> simp_all
    subst this
    exact ⟨false, a1, by rw [hstep]; rfl, hT1, hg1, by simp⟩
  rw [ite_eq_right h0] at hW
  have : b1 = true := hb1.mp (by simpa using h0)
  subst this
  cases h2 : callW p n "block_links_ok" [io, il, po, pl] s1.mem with
  | none => rw [h2] at hW; simp [pinListOkLW.k_block_links_ok] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, pinListOkLW.k_block_links_ok.arm1] at hW; cases hW
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockLinksOk_specW p hP.bls n _ io il po pl) h2
  obtain ⟨b, a', hrun, hT', hg', -, -, -, hb'⟩ := blockLinksOkW_ok hP hT1 hok1 hr1
    (hBs.grow ciF_mono hg1) (hPs.grow ciF_mono hg1)
    (let ⟨_, h⟩ := hB; ⟨_, ConRon.Bridge.denoteCIList_mono hx1 _ _ h⟩)
    (let ⟨_, h⟩ := hPd; ⟨_, ConRon.Bridge.denoteCIList_mono hx1 _ _ h⟩) hW2
  exact ⟨b, a', by rw [hstep]; exact hrun, hT', hg1.trans hg', by simpa using hb'⟩

end top

end L.Ind
