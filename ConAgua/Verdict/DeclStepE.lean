import ConAgua.Verdict.DeclCdE

/-!
# The verdict claims of `install_value`, `install_step_go`, `install_step`, `install_decl_step`
(lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt DeclAtF IndDeclAt CVAt dw decCIs)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK PersDecl PersPinSets PExt)

local notation "V" => ConLeche.CheckMode.verified

l_model installValue_specE (p : Prog) (hf : p.lookup "install_value" = some installValueL)
  fns [hf ↦ installValueE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installStepGo_specE (p : Prog) (hf : p.lookup "install_step_go" = some installStepGoL)
  fns [hf ↦ installStepGoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installStep_specE (p : Prog) (hf : p.lookup "install_step" = some installStepL)
  fns [hf ↦ installStepE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installDeclStep_specE (p : Prog) (hf : p.lookup "install_decl_step" = some installDeclStepL)
  fns [hf ↦ installDeclStepE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section iv
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **`install_value`'s error claim, the common part**: the header's and (for `vk ≠ 1`) the value
guards' failures claim the twin's; the other callees claim nothing. -/
theorem ivE_core {p : Prog} (hP : IvProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hivE : IvgE p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m : Mem} {i ck vk : Word} {ds : Array IDeclaration} {ci : IConstantInfo} {env : ConLeche.Env}
    {c : ConLeche.ConstantVal}
    (hS : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hci : stepCI ck.toNat ds[i.toNat] = some ci)
    (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store (stepCV ds[i.toNat]) = some c) (hCr : L.Stubs.CrOK m)
    {e : Err} (hc : callE p n "install_value" [i, vis, ck, vk] m = .error e)
    (hn : n ≤ 2 ^ 62) :
    ErrClaim (do installHeader fe (stepCV ds[i.toNat])
                 if vk ≠ 1 then installValueGuards fe (stepCV ds[i.toNat]) (stepVal ds[i.toNat])
                 else pure () : AM Unit) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installValue_specE p hP.iv n ⟨m, Locals.init []⟩ i vis ck vk) hc
    (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [installValueE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installValueE.arm1] at hW
  cases h1 : callE p n "erec_ci" [i, ck] m with
  | error e1 =>
    rw [h1, installValueE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, installValueE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hP.recP n ⟨m, Locals.init []⟩ i ck) h1
  subst hs1
  have hCr1 := CrOK.frame hCr (erecCiW_frame hW1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ := erecCiW_okT hW1 hS hD hi hci
  generalize hq : r1.headD 0 = q at hW hci1 hcv1 hval1 htop1
  have hb : q.toNat + 8 < 2 ^ 64 := by
    have h1 := hS1.stage.2.2.1; have h2 := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  cases h2 : callE p n "install_header" [vis, q + 1] s1.mem with
  | error e2 =>
    rw [h2, installValueE.k_install_header.none] at hW; cases hW
    exact ErrClaim.bind_left (ihE_okT hP.ih hap hkp hnv h2 hS1 (by rw [hq1]; exact hcv1)
      (by rw [hq1]; omega) (denoteCV_lps hcvd) hCr1)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callE
    (ih_specW p hP.ih (realCall p) (realCall_spec p) n ⟨s1.mem, Locals.init []⟩ vis (q + 1)) h2
  subst hs2
  obtain ⟨a2, hrun2, hS2, hg2, -, -⟩ :=
    ihW_okT hap hkp.crf hW2 hS1 (by rw [hq1]; exact hcv1) (by rw [hq1]; omega) (denoteCV_lps hcvd) hCr1
  have hlps2 : ∃ ks, (stepCV ds[i.toNat]).levelParams.mapM (denoteN a2.store.ns) = some ks := by
    obtain ⟨hstep, -⟩ := ConRon.Bridge.installHeader_bridge hfold hcvd hrun2
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hstep.ext)
  refine ErrClaim.bind_right hrun2 ?_
  by_cases hv1 : vk ≠ 1
  · rw [installValueE.k_install_header.arm1 p _ _ _ _ _ _ hv1] at hW
    rw [if_pos hv1]
    have hval2 : hd? (erecP s2.mem) (q.toNat + 5) = some (stepVal ds[i.toNat]) :=
      ArrExt.hd? (IWGrow.erecPExt hg2) hval1
    obtain ⟨wv, hwv, hwvl, hwvd⟩ := hd?_some hval2
    have hq5 : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
    have ev : rdW (s2.mem.arr64 EREC) (q + 5) = wv := rdW_of_get? hq5.symm (erecP_get hwv)
    rw [ev] at hW
    cases h3 : callE p n "install_value_guards" [vis, q + 1, wv] s2.mem with
    | error e3 =>
      rw [h3, installValueE.k_install_value_guards.none] at hW; cases hW
      have hcv2 : decCV (erA s2.mem) (q + 1).toNat = some (stepCV ds[i.toNat]) := by
        rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt (hg2)) hcv1
      rw [hwvd]
      exact hivE h3 hS2 hcv2 (by rw [hq1]; omega) hwvl hlps2 hCr2
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, installValueE.k_install_value_guards.arm1, installValueE.j1.arm1] at hW
    cases h4 : callE p n "env_push" [vis, q] m3 with
    | error e4 =>
      rw [h4, installValueE.k_env_push.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, installValueE.k_env_push.arm1] at hW
    cases h5 : callE p n "erec_vg" [q, vk] m4 with
    | error e5 =>
      rw [h5, installValueE.k_erec_vg.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h5
    | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, installValueE.k_erec_vg.arm1] at hW
    cases hW
  · rw [installValueE.k_install_header.arm2 p _ _ _ _ _ _ (by simpa using hv1), installValueE.j1.arm1] at hW
    rw [if_neg hv1]
    cases h4 : callE p n "env_push" [vis, q] s2.mem with
    | error e4 =>
      rw [h4, installValueE.k_env_push.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, installValueE.k_env_push.arm1] at hW
    cases h5 : callE p n "erec_vg" [q, vk] m4 with
    | error e5 =>
      rw [h5, installValueE.k_erec_vg.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h5
    | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, installValueE.k_erec_vg.arm1] at hW
    cases hW

/-- **`install_value`'s error claim under `StageT`** (`installValue_loopT`'s hypotheses). -/
theorem installValue_errT {p : Prog} (hP : IvProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hivE : IvgE p)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} {i ck vk : Word} (hi : i.toNat < ds.size)
    (hk : IvArgs ck vk (dsAt ds i))
    (hR : LoopR pins dn m a vis fe pend ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK V env fe a) (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x)
    (hCr : L.Stubs.CrOK m) {e : Err}
    (hc : callE p n "install_value" [i, vis, ck, vk] m = .error e) :
    ErrClaim (ivT fe (dsAt ds i)) a e := by
  have hd : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  rw [hd] at hk hden ⊢
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  cases hdi : ds[i.toNat] with
  | defnDecl cv v hint =>
    rw [hdi] at hk hx
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Frontend.denoteDecl] at hx
    split at hx
    · rename_i c' e' hcd he
      have := ivE_core (ci := .defnInfo cv v hint) hP hap hkp hnv hivE hS hR.decls hi
        (by rw [hdi]; rfl) hF (by rw [hdi]; exact hcd) hCr hc hn
      rw [hdi] at this
      simp only [stepCV, stepVal] at this
      have h' : ErrClaim (installHeader fe cv >>= fun _ => installValueGuards fe cv v) a e := by
        simpa using this
      simp only [ivT]
      rw [← bind_assoc]
      exact ErrClaim.bind_left h'
    · cases hx
  | thmDecl cv v =>
    rw [hdi] at hk hx
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Frontend.denoteDecl] at hx
    split at hx
    · rename_i c' e' hcd he
      have := ivE_core (ci := .thmInfo cv) hP hap hkp hnv hivE hS hR.decls hi
        (by rw [hdi]; rfl) hF (by rw [hdi]; exact hcd) hCr hc hn
      rw [hdi] at this
      simp only [stepCV, stepVal] at this
      have h' : ErrClaim (installHeader fe cv) a e := by simpa using this
      simp only [ivT]
      exact ErrClaim.bind_left h'
    · cases hx
  | opaqueDecl cv v =>
    rw [hdi] at hk hx
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Frontend.denoteDecl] at hx
    split at hx
    · rename_i c' e' hcd he
      have := ivE_core (ci := .axiomInfo cv) hP hap hkp hnv hivE hS hR.decls hi
        (by rw [hdi]; rfl) hF (by rw [hdi]; exact hcd) hCr hc hn
      rw [hdi] at this
      simp only [stepCV, stepVal] at this
      have h' : ErrClaim (installHeader fe cv >>= fun _ => installValueGuards fe cv v) a e := by
        simpa using this
      simp only [ivT]
      rw [← bind_assoc]
      exact ErrClaim.bind_left h'
    · cases hx
  | axiomDecl _ => rw [hdi] at hk; exact hk.elim
  | quotDecl _ _ => rw [hdi] at hk; exact hk.elim
  | indDecl _ _ => rw [hdi] at hk; exact hk.elim
  | basisDecl _ => rw [hdi] at hk; exact hk.elim

end iv

section istg
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `install_step_go` claims on failure under `StageT`** (the error half of
`installStepGo_specT`). -/
def InstallStepGoSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ConRon.Bridge.StateOK a →
    (∃ env, FoldOK V env fe a) →
    LoopR pins dn m a vis fe pend ds → TwinOK dn m a fe → pinW m 0 ≠ 0 →
    (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) →
    (∃ pinsP, PinsDenote a.store pins pinsP) → IndMemos m →
    ∀ e, callE p n "install_step_go" [i, vis] m = .error e →
    ErrClaim (installStepGo V pins fe (dsAt ds i)) a e

/-- **`install_step_go` fails only where `installStepGo` does** (through `check_decl`'s error
claim and `install_value`'s). -/
theorem installStepGo_errT {p : Prog} (hG : IstgProg p) (hP : IvProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hivE : IvgE p)
    (hCD : CheckDeclSpecE pins dn ds p) : InstallStepGoSpecE pins dn ds p := by
  intro n hn m a vis fe pend i hi hok0 hFo hR hTw hfl hden hPD hIM e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installStepGo_specE p hG.go n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [installStepGoE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installStepGoE.arm1] at hW
  cases h0 : callE p n "iw_reset" [] m with
  | error e0 =>
    rw [h0, installStepGoE.k_iw_reset.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h0
  | ok q0 =>
  obtain ⟨r0, m0'⟩ := q0
  rw [h0] at hW
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callE (iwReset_specW p hG.reset n ⟨m, Locals.init []⟩) h0
  rw [show iwResetW m = some ([], m.set64 CTL 200 0) from rfl] at hW0
  simp only [Option.some.injEq, Prod.mk.injEq] at hW0
  obtain ⟨-, hm0⟩ := hW0
  have hm0' : m0' = m.set64 CTL 200 0 := hs0.symm.trans hm0.symm
  subst hm0'
  have hR0 := hR.reset
  have hS0 : StageT dn vis fe (m.set64 CTL 200 0) a :=
    ⟨⟨hR0.check, hR0.iw⟩,
      hTw.frame (MemFrame.setCtl m 200 0) ⟨by simp, by simp⟩ ⟨by decide, by decide⟩
        ⟨by simp, by simp, by simp⟩ ⟨by decide, by decide, by decide⟩ ⟨by simp, by simp, by simp⟩
        ⟨by decide, by decide, by decide⟩,
      by rw [pinW_frame (MemFrame.setCtl m 200 0) (by simp)]; exact hfl⟩
  have hIM0 := hIM.setCtl 200 0 (by decide)
  generalize m.set64 CTL 200 0 = m1 at hW hR0 hS0 hIM0
  have hdecl : DeclAtF (m1.arr64 DECL) (m1.arr64 DLP) i.toNat (dsAt ds i) := by
    have := hR0.decls.recs i.toNat hi
    simpa [dsAt, Array.getD, hi] using this
  have h1 := hR0.decls.room
  have h2 := hR0.decls.dsize
  have hw0 : rdW (m1.arr64 DECL) (1 + 8 * i) = dw (m1.arr64 DECL) i.toNat 0 := by
    have : (1 + 8 * i).toNat = 1 + 8 * i.toNat + 0 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    simp [rdW, dw, this]
  have hw1 : rdW (m1.arr64 DECL) (2 + 8 * i) = dw (m1.arr64 DECL) i.toNat 1 := by
    have : (2 + 8 * i).toNat = 1 + 8 * i.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    simp [rdW, dw, this]
  rw [installStepGoE.k_iw_reset.eq_2, hw0] at hW
  -- the `check_decl` branch
  have cdbranch : ∀ {e' : Err}, installStepGoE.k_check_decl p (callE p n "check_decl" [i, vis] m1) = .error e' →
      ∀ T : AM (IFEnv × Option ValueGroup), (∀ ce, (cdT V pins fe (dsAt ds i)).run a = .error ce → T.run a = .error ce) →
      ErrClaim T a e' := by
    intro e' h T hT
    cases hc' : callE p n "check_decl" [i, vis] m1 with
    | error e1 =>
      rw [hc', installStepGoE.k_check_decl.none] at h; cases h
      have := hCD n hn' m1 a vis fe pend i hi hok0 hR0 hS0 hFo hden hPD hIM0 _ hc'
      refine ErrClaim.of_run_eq hT ?_
      exact ErrClaim.bind_left this
    | ok q =>
      obtain ⟨r, m2⟩ := q
      rw [hc', installStepGoE.k_check_decl.arm1] at h; cases h
  generalize hd : dsAt ds i = d at hdecl

  cases d with
  | axiomDecl cv =>
    obtain ⟨hk, -⟩ := hdecl
    rw [hk] at hW
    simp only [show (1 : Word) ≠ 2 by decide, show (1 : Word) ≠ 3 by decide,
      show (1 : Word) ≠ 4 by decide, if_false] at hW
    exact cdbranch hW _ (fun ce h => by rw [hd] at h; exact h)
  | quotDecl k cv =>
    obtain ⟨hk, -⟩ := hdecl
    rw [hk] at hW
    simp only [show (5 : Word) ≠ 2 by decide, show (5 : Word) ≠ 3 by decide,
      show (5 : Word) ≠ 4 by decide, if_false] at hW
    exact cdbranch hW _ (fun ce h => by rw [hd] at h; exact h)
  | indDecl b nP =>
    have hk : dw (m1.arr64 DECL) i.toNat 0 = 6 := hdecl.1
    rw [hk] at hW
    simp only [show (6 : Word) ≠ 2 by decide, show (6 : Word) ≠ 3 by decide,
      show (6 : Word) ≠ 4 by decide, if_false] at hW
    exact cdbranch hW _ (fun ce h => by rw [hd] at h; exact h)
  | basisDecl _ => exact absurd hdecl id
  | thmDecl cv v =>
    obtain ⟨hk, -⟩ := hdecl
    rw [hk] at hW
    simp only [show (3 : Word) ≠ 2 by decide, if_false, if_true] at hW
    cases hc' : callE p n "install_value" [i, vis, 2, 1] m1 with
    | error e1 =>
      rw [hc', installStepGoE.k_install_value.none] at hW; cases hW
      have := installValue_errT pins dn ds hP hap hkp hnv hivE hn' hi
        (by rw [hd]; exact ⟨rfl, rfl⟩) hR0 hS0 hFo hden hIM0.cr hc'
      rw [hd] at this
      exact this
    | ok q =>
      obtain ⟨r, m2⟩ := q
      rw [hc', installStepGoE.k_install_value.arm1] at hW; cases hW
  | defnDecl cv v hint =>
    obtain ⟨hk, hcv, -⟩ := hdecl
    rw [hk] at hW
    simp only [if_true] at hW
    cases hp : callE p n "pin_in" [rdW (m1.arr64 DECL) (2 + 8 * i) &&& 4294967295, 15, 30] m1 with
    | error e1 =>
      rw [hp, installStepGoE.k_pin_in.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) hp
    | ok q =>
      obtain ⟨r, m2⟩ := q
      rw [hp] at hW
      obtain ⟨s2, hs2, -, hm2, hW2⟩ := triple_of_callE
        (pinIn_specW p hG.pin n ⟨m1, Locals.init []⟩ _ 15 30) hp
      have hm2' : m1 = m2 := (hs2.symm.trans hm2).symm
      subst hm2'
      rw [hw1] at hW2
      have hF := hR0.check.pins.full (pinInW_flag hW2)
      have hiff := pinIn_contains hF hW2 (mask_lt _) (by decide) (by decide) (by decide)
      rw [decI_mask, hcv.1] at hiff
      have hT := installStepGo_defn V pins fe hF cv v hint
      rw [pinnedDefnL_eq] at hT
      by_cases hc0 : r.headD 0 ≠ 0
      · rw [installStepGoE.k_pin_in.arm1 p _ _ _ _ _ hc0] at hW
        have hpin : ((List.range' 15 15).map fun j => (decI (pinW m1 j) : NIdx)).contains cv.name =
            true := hiff.mp hc0
        rw [if_pos hpin] at hT
        exact cdbranch hW _ (fun ce h => by rw [hd] at h; rw [hT]; exact h)
      · have hc0' : r.headD 0 = 0 := by simpa using hc0
        rw [installStepGoE.k_pin_in.arm2 p _ _ _ _ _ hc0'] at hW
        have hpin : ¬ ((List.range' 15 15).map fun j => (decI (pinW m1 j) : NIdx)).contains cv.name =
            true := fun h' => hc0 (hiff.mpr h')
        rw [if_neg hpin] at hT
        cases hc' : callE p n "install_value" [i, vis, 1, 0] m1 with
        | error e1 =>
          rw [hc', installStepGoE.k_install_value.none] at hW; cases hW
          have := installValue_errT pins dn ds hP hap hkp hnv hivE hn' hi
            (by rw [hd]; exact ⟨rfl, rfl⟩) hR0 hS0 hFo hden hIM0.cr hc'
          rw [hd] at this
          refine ErrClaim.of_run_eq (T' := ivT fe (.defnDecl cv v hint)) ?_ this
          intro ce h; rw [hT]; exact h
        | ok q =>
          obtain ⟨r', m3⟩ := q
          rw [hc', installStepGoE.k_install_value.arm1] at hW; cases hW
  | opaqueDecl cv v =>
    obtain ⟨hk, hcv, -⟩ := hdecl
    rw [hk] at hW
    simp only [show (4 : Word) ≠ 2 by decide, show (4 : Word) ≠ 3 by decide, if_false,
      if_true] at hW
    cases hp : callE p n "pin_in" [rdW (m1.arr64 DECL) (2 + 8 * i) &&& 4294967295, 44, 46] m1 with
    | error e1 =>
      rw [hp, installStepGoE.k_pin_in_2.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) hp
    | ok q =>
      obtain ⟨r, m2⟩ := q
      rw [hp] at hW
      obtain ⟨s2, hs2, -, hm2, hW2⟩ := triple_of_callE
        (pinIn_specW p hG.pin n ⟨m1, Locals.init []⟩ _ 44 46) hp
      have hm2' : m1 = m2 := (hs2.symm.trans hm2).symm
      subst hm2'
      rw [hw1] at hW2
      have hF := hR0.check.pins.full (pinInW_flag hW2)
      have hiff := pinIn_contains hF hW2 (mask_lt _) (by decide) (by decide) (by decide)
      rw [decI_mask, hcv.1] at hiff
      have hT := installStepGo_opaque V pins fe hF cv v
      by_cases hc0 : r.headD 0 ≠ 0
      · rw [installStepGoE.k_pin_in_2.arm1 p _ _ _ _ _ hc0] at hW
        have hpin : ((List.range' 44 2).map fun j => (decI (pinW m1 j) : NIdx)).contains cv.name =
            true := hiff.mp hc0
        rw [if_pos (show (pinnedOpaqueL m1).contains cv.name = true from hpin)] at hT
        exact cdbranch hW _ (fun ce h => by rw [hd] at h; rw [hT]; exact h)
      · have hc0' : r.headD 0 = 0 := by simpa using hc0
        rw [installStepGoE.k_pin_in_2.arm2 p _ _ _ _ _ hc0'] at hW
        have hpin : ¬ ((List.range' 44 2).map fun j => (decI (pinW m1 j) : NIdx)).contains cv.name =
            true := fun h' => hc0 (hiff.mpr h')
        rw [if_neg (show ¬ (pinnedOpaqueL m1).contains cv.name = true from hpin)] at hT
        cases hc' : callE p n "install_value" [i, vis, 0, 2] m1 with
        | error e1 =>
          rw [hc', installStepGoE.k_install_value.none] at hW; cases hW
          have := installValue_errT pins dn ds hP hap hkp hnv hivE hn' hi
            (by rw [hd]; exact ⟨rfl, rfl⟩) hR0 hS0 hFo hden hIM0.cr hc'
          rw [hd] at this
          refine ErrClaim.of_run_eq (T' := ivT fe (.opaqueDecl cv v)) ?_ this
          intro ce h; rw [hT]; exact h
        | ok q =>
          obtain ⟨r', m3⟩ := q
          rw [hc', installStepGoE.k_install_value.arm1] at hW; cases hW

end istg

section ist
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `install_step` claims on failure under `StageT`** (the error half of
`installStep_pieces`'s hypotheses). -/
def InstallStepSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (i vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck), i.toNat < ds.size → ConRon.Bridge.StateOK a →
    a.store.scratchOn = false → LoopR pins dn m a vis fe pend ds → TwinOK dn m a fe →
    pinW m 0 ≠ 0 → (∃ env, FoldOK V env fe a) →
    (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) → PersDecl (dsAt ds i) →
    (∃ pinsP, PinsDenote a.store pins pinsP) → PersPinSets pins → IndMemos m →
    ∀ e, callE p n "install_step" [i, vis] m = .error e →
    ErrClaim (installStep V pins i.toNat fe pend (dsAt ds i)) a e

/-- **`install_step` fails only where `installStep` does**: the bracket's openings and the
promotions claim nothing; `install_step_go` by its claim. -/
theorem installStep_errT {p : Prog} (hb : BracketProg p) (hp : p.lookup "install_step" = some installStepL)
    (hnv : closedNV p L.Checker.nvFns = true)
    (hGo : InstallStepGoSpecE pins dn ds p) : InstallStepSpecE pins dn ds p := by
  intro n hn m a i vis fe pend hi hok hoff hR hTw hfl hF hden hpd hPD hpps hIM e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installStep_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hwf' : StoreWF (AM.st flushCaches a).store := by rw [flushCaches_st]; exact hok.wf
  have hoff' : (AM.st flushCaches a).store.scratchOn = false := by rw [flushCaches_st]; exact hoff
  have hFe : ∃ env, FoldOK V env fe (AM.st enterScratch (AM.st flushCaches a)) := by
    obtain ⟨env, h⟩ := hF
    exact ⟨env, by rw [enterScratch_st, flushCaches_st]; exact h.enter⟩
  have hde : ∃ x, Frontend.denoteDecl (AM.st enterScratch (AM.st flushCaches a)).store
      (dsAt ds i) = some x := by
    obtain ⟨x, h⟩ := hden
    exact ⟨x, by
      rw [enterScratch_st, flushCaches_st]
      exact ConRon.Bridge.denoteDecl_pext (PExt.enterScratch hok.wf) hpd h⟩
  have hPDe : ∃ pinsP, PinsDenote (AM.st enterScratch (AM.st flushCaches a)).store pins pinsP := by
    obtain ⟨q, h⟩ := hPD
    exact ⟨q, by
      rw [enterScratch_st, flushCaches_st]
      exact PinsDenote.pmono (PExt.enterScratch hok.wf) _ _ hpps h⟩
  cases n with
  | zero => rw [installStepE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installStepE.arm1] at hW
  simp only [installStep, bind_assoc]
  cases h0 : callE p n "tbl_cnt" [] m with
  | error e0 =>
    rw [h0, installStepE.k_tbl_cnt.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h0
  | ok q0 =>
  obtain ⟨r0, m0⟩ := q0
  rw [h0, installStepE.k_tbl_cnt.arm1] at hW
  obtain ⟨s0, hs0, hm0, -⟩ := triple_of_callE (tblCnt_spec p (hb.pr.get "tbl_cnt") n ⟨m, Locals.init []⟩) h0
  have hm0' : m0 = m := hs0.symm.trans hm0
  subst hm0'
  cases h1 : callE p n "flush_caches" [] m0 with
  | error e1 =>
    rw [h1, installStepE.k_flush_caches.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, installStepE.k_flush_caches.arm1] at hW
  obtain ⟨s1, hs1, -, hokF, hLF, hTF, hflF, hIMF⟩ := triple_of_callE
    (flush_loopW (pins := pins) dn ds p hb n ⟨m0, Locals.init []⟩ a vis fe pend hR hTw hfl hIM) h1
  subst hs1
  refine ErrClaim.bind_right (AM.run_of_ok _ _ hokF) ?_
  cases h2 : callE p n "scratch_enter" [] s1.mem with
  | error e2 =>
    rw [h2, installStepE.k_scratch_enter.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, installStepE.k_scratch_enter.arm1] at hW
  obtain ⟨s2, hs2, -, hokE, hLE, hTE, hflE, hIME⟩ := triple_of_callE
    (enter_loopW (pins := pins) dn ds p hb n ⟨s1.mem, Locals.init []⟩ (AM.st flushCaches a) vis fe pend
      hwf' hoff' hLF hTF hflF hIMF) h2
  subst hs2
  refine ErrClaim.bind_right (AM.run_of_ok _ _ hokE) ?_
  cases h3 : callE p n "install_step_go" [i, vis] s2.mem with
  | error e3 =>
    rw [h3, installStepE.k_install_step_go.none] at hW; cases hW
    exact ErrClaim.bind_left (hGo n hn' s2.mem _ vis fe pend i hi (TwinFold.enterAM hok) hFe hLE hTE
      hflE hde hPDe hIME _ h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at hW
  by_cases hf : r3.tail.headD 0 = 0
  · rw [installStepE.k_install_step_go.arm1 p _ _ _ _ _ _ hf] at hW
    cases h4 : callE p n "is_none" [vis, r3.headD 0, r0.headD 0] m3 with
    | error e4 =>
      rw [h4, installStepE.k_is_none.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, installStepE.k_is_none.arm1, installStepE.j1.arm1] at hW; cases hW
  · rw [installStepE.k_install_step_go.arm2 p _ _ _ _ _ _ hf] at hW
    cases h4 : callE p n "is_some" [i, vis, r3.headD 0, r0.headD 0, r3.tail.tail.headD 0] m3 with
    | error e4 =>
      rw [h4, installStepE.k_is_none.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, installStepE.k_is_none.arm1, installStepE.j1.arm1] at hW; cases hW

end ist

section ids
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `install_decl_step` claims on failure under `StageT`**: the twin's step reports
failures as values. -/
def InstallDeclStepSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (i vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck), i.toNat < ds.size → TwinFold pins ds fe pend a →
    LoopR pins dn m a vis fe pend ds → TwinOK dn m a fe → pinW m 0 ≠ 0 → IndMemos m →
    ∀ e, callE p n "install_decl_step" [i, vis] m = .error e →
    ErrClaimV (installDeclStep V pins (i.toNat, fe, pend) (dsAt ds i)) a e

/-- **`install_decl_step` fails only where `installDeclStep` does**: a rejected `And` pin is the
twin's value failure at the position, `install_step`'s failure the same. -/
theorem installDeclStep_errT {p : Prog} (hdc : LoopCallees dn p) (hFD : FrontDecls ds)
    (hnv : closedNV p L.Checker.nvFns = true)
    (hp : p.lookup "install_decl_step" = some installDeclStepL)
    (hSt : InstallStepSpecE pins dn ds p) : InstallDeclStepSpecE pins dn ds p := by
  intro n hn m a i vis fe pend hi hT hR hTw hfl hIM e hc hk0
  have hW := triple_of_callE_err (installDeclStep_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hpk : ConRon.Bridge.PinsOK a := by obtain ⟨_, hF, _⟩ := hT.fold; exact hF.check.pins
  have hF0 : ∃ env, FoldOK V env fe a := by obtain ⟨env, hF, _⟩ := hT.fold; exact ⟨env, hF⟩
  have e0 : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hden0 : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x := by
    rw [e0]; exact hT.denote hi
  have hpd : PersDecl (dsAt ds i) := by rw [e0]; exact hT.pd _ (by simp)
  have hPD0 : ∃ pinsP, PinsDenote a.store pins pinsP := hT.pinsD
  have hpps : PersPinSets pins := hT.pp
  cases n with
  | zero => rw [installDeclStepE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installDeclStepE.arm1] at hW
  cases h0 : callE p n "and_pin_ok" [i] m with
  | error e0' =>
    rw [h0, installDeclStepE.k_and_pin_ok.none] at hW; cases hW
    exact absurd (callE_nv hnv (declNv_mem _ (by decide +kernel)) _ _ _ h0) hk0
  | ok q0 =>
  obtain ⟨r0, m0⟩ := q0
  rw [h0] at hW
  obtain ⟨s0, hs0, -, hokA, hLA, hresA, hTwA, hflA, hoffA, hFA, hdenA, hPDA, hIMA⟩ := triple_of_callE
    (andPinOk_refinesT pins dn ds p hdc.leaf hdc.and_pin_ok hdc.andInd hdc.cd.crp.red.rom hdc.indIn
      hFD n ⟨m, Locals.init []⟩ a vis fe pend i hi hT.stateOK hpk hT.off hF0 hR hTw hfl hden0 hpd hPD0
      hpps hdc.indMemo hdc.crf hIM) h0
  subst hs0
  have hrunA := AM.run_of_ok _ _ hokA
  by_cases hz : r0.headD 0 = 0
  · rw [installDeclStepE.k_and_pin_ok.abort1 p _ _ _ _ _ hz] at hW; cases hW
    have hres : AM.res (andPinOk (dsAt ds i)) a = false := by rw [hresA, hz]; rfl
    rw [hres] at hrunA
    refine .inr ⟨.invalid "`And` must be the standard `And`", i.toNat, AState.abandoned, ?_, rfl⟩
    show (match (andPinOk (dsAt ds i)).run a with
      | .ok (true, s₁) => _
      | .ok (false, _) => _
      | .error e => _) = _
    rw [hrunA]
  rw [installDeclStepE.k_and_pin_ok.arm1 p _ _ _ _ _ hz] at hW
  have hres : AM.res (andPinOk (dsAt ds i)) a = true := by rw [hresA]; exact bne_iff_ne.mpr hz
  rw [hres] at hrunA
  have hokA' : ConRon.Bridge.StateOK (AM.st (andPinOk (dsAt ds i)) a) := by
    rw [e0]; exact hT.andPinAM hi (by rw [← e0]; exact hokA)
  cases h1 : callE p n "install_step" [i, vis] s0.mem with
  | error e1 =>
    rw [h1, installDeclStepE.k_install_step.none] at hW; cases hW
    obtain ⟨ce, hce, hcl⟩ := hSt n hn' s0.mem (AM.st (andPinOk (dsAt ds i)) a) i vis fe pend hi hokA'
      hoffA hLA hTwA hflA hFA hdenA hpd hPDA hpps hIMA _ h1 hk0
    refine .inr ⟨ce, i.toNat, AState.abandoned, ?_, hcl⟩
    show (match (andPinOk (dsAt ds i)).run a with
      | .ok (true, s₁) => _
      | .ok (false, _) => _
      | .error e => _) = _
    rw [hrunA]
    simp only [StateT.run] at hce ⊢
    show (match installStep V pins i.toNat fe pend (dsAt ds i) (AM.st (andPinOk (dsAt ds i)) a) with
      | .ok ((fe', pend'), s') => _
      | .error e => _) = _
    rw [hce]
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, installDeclStepE.k_install_step.arm1] at hW; cases hW

end ids

end L.Arena
