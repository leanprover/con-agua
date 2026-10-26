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
    (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
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

end L.Arena
