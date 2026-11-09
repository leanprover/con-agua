module

public import ConAgua.Arena.BasisBlockT
public import ConAgua.Arena.DeclBasisRef
import ConAgua.Arena.QuotRecW
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndTwin
import ConAgua.Arena.IlpRd
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.DeclCvg
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Inv

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
  have r1 : erRdT m c = wk := erRdT_of _ _ e
  have r2 : erRdT m d = wk' := erRdT_of _ _ e'
  by_cases h3 : erRdT m c = 3 ∧ erRdT m d = 3
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
    simp only [List.headD_cons, hr1, hm1, hb, ConRon.Arena.pinAgrees, beq_iff_eq]
    by_cases hcc : cv = cv' <;> simp [hcc]
  · rw [pinAgreesW.eq_2, if_neg h3] at hW
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
    simp only [List.headD_cons, hr1, hm1, hb, pinAgrees_eq_of_not_ind hni]
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
  have hW2' : erToIwW n0 m (erRdT m (c + 2)) (erRdT m (c + 3)) = some (r2, s2.mem) := by
    rw [← word_add11, ← word_add12]; exact hW2
  obtain ⟨hS2, hg2, hdl2, htop2, -⟩ := erToIwW_stage hW2' hT.stage hsl
  have hf2 := erToIwW_iwFr hW2'
  have hT2 : StageT dn vis fe s2.mem a := StageT.of_iw hT hS2 hf2
  have hrd2 := erRdT_congr (m := m) (m' := s2.mem) (hf2.arr _ (by decide) (by decide))
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
  have hcond : (r3.headD 0 ≠ 0 ∧ r2.tail.headD 0 = erRdT m (pin + 3)) ↔
      (nameNodup ci.toConstantVal.levelParams &&
        ci.toConstantVal.levelParams.length == pc.toConstantVal.levelParams.length) = true := by
    rw [Bool.and_eq_true, ← hnd, beq_iff_eq, hlen2, hplen, bne_iff_ne, ne_eq]
    exact and_congr_right fun _ => ⟨fun e => by rw [e], fun e => UInt64.toNat_inj.mp e⟩
  by_cases hc : r3.headD 0 ≠ 0 ∧ r2.tail.headD 0 = erRdT m (pin + 3)
  case neg =>
    rw [if_neg hc] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have e2 : s'.mem = s2.mem := by
      first | exact e.symm.trans hm3 | exact e.trans hm3 | exact e | exact e.symm
    have hc' := mt hcond.mpr hc
    refine ⟨false, a, ?_, ?_⟩
    · simp only [ConRon.Arena.pinCopyOk]
      rw [if_neg (by simpa using hc')]; rfl
    · rw [e2]; exact ⟨hT2, hg2, hok, hr, Ext.refl _, by simp⟩
  rw [if_pos hc] at hW
  -- `ci_at_lps(pin, EREC⦃c + 2⦄, EREC⦃c + 3⦄)`
  cases h4 : callW p (n0 + 1) "ci_at_lps" [pin, erRdT m (c + 2), erRdT m (c + 3)] s2.mem with
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
    rw [if_pos (hcond.mp hc), StateT.run_bind, hrun4, exb]; rfl
  · rw [← e]
    exact ⟨hT4, hg2.trans hg4, hst4.ok, hst4.read, hst4.ext, by simpa using hb⟩

end copy


/-! ## `pin_copies_ok` -/

theorem CmpPost.refl {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {r : List Word} {b : Bool} (hT : StageT dn vis fe m a)
    (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a) (hb : r.headD 0 ≠ 0 ↔ b = true) :
    CmpPost dn vis fe m a r b m a := ⟨hT, IWGrow.refl m, hok, hr, Ext.refl _, hb⟩

theorem slice_len {m : Mem} {o l : Word} {xs : List IConstantInfo} (h : PSlR ciF xs o l m) :
    xs.length = l.toNat := L.Ind.decPL_length (truncM m) h.dec

section copies
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`pin_copies_ok(co, cl, po, pl)` refines `pinCopiesOk cs ps`**, pair by pair. -/
theorem pinCopiesOkW_ok (hP : PinListLProg p) : ∀ (n : Nat) (m m' : Mem) (a : AState)
    (co cl po pl : Word) (cs ps : List IConstantInfo) (r : List Word),
    StageT dn vis fe m a → ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a →
    PSlR ciF cs co cl m → PSlR ciF ps po pl m →
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
  · rw [if_pos h1] at h; cases h
    obtain ⟨rfl, rfl⟩ := h1
    have e1 : cs = [] := List.eq_nil_of_length_eq_zero (by rw [hlc]; rfl)
    have e2 : ps = [] := List.eq_nil_of_length_eq_zero (by rw [hlp]; rfl)
    subst e1 e2
    exact ⟨true, a, rfl, CmpPost.refl hT hok hr (by simp)⟩
  rw [if_neg h1] at h
  by_cases h2 : cl = 0 ∨ pl = 0
  · rw [if_pos h2] at h; cases h
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
  rw [if_neg h2] at h
  have hcl : cl ≠ 0 := fun e => h2 (Or.inl e)
  have hpl : pl ≠ 0 := fun e => h2 (Or.inr e)
  obtain ⟨c, cs', rfl, hc, hC'⟩ := hC.uncons hcl hsz
  obtain ⟨q, ps', rfl, hq, hP'⟩ := hPs.uncons hpl hsz
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
  · rw [if_pos h0] at h; cases h
    have : b3 = false := by cases b3 <;> simp_all
    subst this
    exact ⟨false, a3, by rw [hstep]; rfl, hT3, hg3, hok3, hr3, hx3, by simp⟩
  rw [if_neg h0] at h
  have : b3 = true := hb3.mp h0
  subst this
  cases h4 : pinCopiesOkW p n m3 (co + 1) (cl - 1) (po + 1) (pl - 1) with
  | none => rw [h4] at h; simp [pinCopiesOkW.k_pin_copies_ok] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, pinCopiesOkW.k_pin_copies_ok.eq_2] at h
  cases h
  obtain ⟨b, a', hrun, hT', hg', hok', hr', hx', hb'⟩ :=
    ih m3 _ a3 _ _ _ _ cs' ps' r4 hT3 hok3 hr3 (hC'.grow ciF_mono hg3) (hP'.grow ciF_mono hg3)
      ⟨_, ConRon.Bridge.denoteCIList_mono hx3 _ _ hdcs⟩ ⟨_, ConRon.Bridge.denoteCIList_mono hx3 _ _ hdqs⟩ h4
  exact ⟨b, a', by rw [hstep]; exact hrun, hT', hg3.trans hg', hok', hr', hx3.trans hx', by simpa using hb'⟩

end copies

end L.Ind
