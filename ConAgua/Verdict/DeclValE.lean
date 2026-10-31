import ConAgua.Arena.RefWalk
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.DeclValT
import ConAgua.Arena.DeclStepSpec
import ConAgua.Verdict.LefRef
import ConAgua.Verdict.VCtx
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The verdict claims of `check_thm_val` and `check_value_group` (lane `verdicts-b`)

The unified models of `check_thm_val` and `check_value_group` and their refinements for both
outcomes (`tv_ref`, `cvg_ref`): a failing call of class `1`/`2` claims the twin's
`checkThmVal`/`checkValueGroup` fails with an error of that class, under the callees' error claims
(`TvCtx`, `CvgCtx`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-! ## The callees' error claims (hypotheses, discharged bottom-up) -/

/-- **`install_value_guards`' error claim under `StageT`** (`ivg_ref`'s error half, as a hypothesis shape). -/
def IvgE (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m : Mem} {q v : Word} {cv : IConstantVal} {e : Err},
    callE p n "install_value_guards" [vis, q, v] m = .error e → StageT dn vis fe m a →
    decCV (erA m) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 → v.toNat < 2 ^ 32 →
    (∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) → L.Stubs.CrOK m →
    ErrClaim (installValueGuards fe cv (decI v)) a e

/-- What `install_header`'s error arms assume: the no-verdict closure (`all_level_params_defined`,
`consts_resolve_ffast`) and `unresolved_consts_error`'s program. -/
structure IhCtx (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  uce : UceProg p

/-- **The model of `install_value_guards`, both outcomes**: `cv_lps` and the two closedness walks
lifted, `all_level_params_defined`, `consts_resolve_ffast` and `unresolved_consts_error` through
their runs. -/
l_model installValueGuards_specE (p : Prog) (hP : CvgProg p)
  fns [hP.ivg ↦ installValueGuardsE]
  specs [cvLps_specW p hP.alloc hP.copy hP.eti hP.lps n, lbbF_spec p hP.bvb n, hffF_spec p hP.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `install_value_guards` gives besides the twin's run: the stage, the growth, the memo. -/
structure IvgPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  crOK : L.Stubs.CrOK m'

/-- **`install_value_guards` refines `installValueGuards`, both outcomes**, under `StageT`: the
copy by its frame (`StageT.of_iw`), the four walks by their `StageT` refinements
(`all_level_params_defined` by `apdF_okT`, the parameters' names read back at the entry;
`consts_resolve_ffast` by `crfF_okT`, its memo carried across), the consts-resolve site by
`uce_errClaim_lo`. -/
theorem ivg_ref {p : Prog} (hap : ApdF p) (hCrf : CrfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {q v : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hq : decCV (erA m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hv : v.toNat < 2 ^ 32) (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks)
    (hCr : L.Stubs.CrOK m) :
    RefE (IhCtx p) (installValueGuardsE p n m vis q v) (installValueGuards fe cv (decI v)) a
      (fun w _ a' => IvgPost dn vis fe m w.2 a') := by
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => rw [installValueGuardsE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [installValueGuardsE.arm1]
  simp only [installValueGuards, fail_bindAM]
  -- `cv_lps(q)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  dsimp only [installValueGuardsE.k_cv_lps]
  cases n with
  | zero => simp [cvLpsW] at h1
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h1
  obtain ⟨-, hr1t, hdec1, hS1R, hg1, htop1⟩ := erToIwW_stage h1 hS.stage hsrc
  have hS1 := StageT.of_iw hS hS1R (erToIwW_frame h1 hS.stage hsrc)
  have hCr1 := CrOK.frame hCr (erToIwW_frame h1 hS.stage hsrc) (by decide) (by decide)
  rw [hr1t]
  -- `loose_bvars_bounded_fast(4000000000, 0, v)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_okT dn vis fe 4000000000 0 v hv m1 m' a r h hS1)
    fun r2 x2 m2 a2 h2 hrun2 ⟨hS2, hg2, hx2, _⟩ => ?_
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  dsimp only [installValueGuardsE.k_loose_bvars_bounded_fast]
  refine RefE.guardIf rfl (fun hb2 => by rw [← hx2]; simpa using hb2)
    (fun hb2 => by rw [← hx2] at hb2; simpa using hb2) fun _ _ => ?_
  -- `has_fvar_fast(4000000000, v)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => hffF_okT dn vis fe 4000000000 v hv m2 m' a2 r h hS2)
    fun r3 x3 m3 a3 h3 hrun3 ⟨hS3, hg3, hx3, _⟩ => ?_
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  dsimp only [installValueGuardsE.k_has_fvar_fast]
  refine RefE.guardThen rfl (fun hb3 => by rw [← hx3]; simpa using hb3)
    (fun hb3 => by rw [← hx3] at hb3; simpa using hb3) fun _ _ => ?_
  -- `all_level_params_defined(o, l, v)`
  have hdec3 : decHL m3 (r1.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg2.trans hg3) (by omega), hdec1]; exact hsl
  have hst3 : a3.store = a.store := (hffF_store hrun3).trans (lbbF_store hrun2)
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h4 => ErrClaim.of_callE_nv hG.nv (L.Checker.nv_mem (by decide +kernel)) h4)
    (fun b h4 => apdF_okT dn vis fe (r1.headD 0) w2 v hv cv.levelParams m3 b.2 a3 b.1
      (apdF_of_callW hap h4) ⟨hS3, hdec3, by rw [hst3]; exact hlps⟩)
    fun r4 m4 x4 a4 h4 _ ⟨hS4, hg4, hx4, _⟩ => ?_
  have hCr4 := CrOK.frame hCr3 (apdF_frame (apdF_of_callW hap (callW_of_callE h4))) (by decide) (by decide)
  dsimp only [installValueGuardsE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb4 => by rw [← hx4]; simpa using hb4)
    (fun hb4 => by rw [← hx4] at hb4; simpa using hb4) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, v)`
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h5 => ErrClaim.of_callE_nv hG.nv (L.Checker.nv_mem (by decide +kernel)) h5)
    (fun b h5 => crfF_okT dn vis fe v hv m4 b.2 a4 b.1 (crfF_of_callW hCrf h5) ⟨hS4, hCr4.crMemo⟩)
    fun r5 m5 x5 a5 _ _ ⟨⟨hS5, hg5, hx5, _⟩, hCr5⟩ => ?_
  dsimp only [installValueGuardsE.k_consts_resolve_ffast]
  by_cases hb5 : r5.headD 0 = 0
  · rw [show x5 = false by rw [← hx5]; simpa using hb5, ite_eq_left hb5]
    refine RefE.ite_neg (by decide) ?_
    rcases h6 : callE p (n + 1) "unresolved_consts_error" [vis, v, 1] m5 with e6 | ⟨r6, m6⟩ <;>
      dsimp only [installValueGuardsE.k_unresolved_consts_error]
    · obtain ⟨M5, hC5⟩ := hS5.core
      exact fun hG => uce_errClaim_lo hG.uce hG.nv hC5 hv (by decide) h6 "value"
    · exact RefE.of_cls0 rfl
  rw [show x5 = true by rw [← hx5]; simpa using hb5, ite_eq_right hb5]
  exact RefE.ite_pos rfl (RefE.ret rfl
    ⟨hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hCr5.crOK⟩)

/-- **`install_value_guards`' error claim under `StageT`** (`ivg_ref`'s error half). -/
theorem ivgE_okT {p : Prog} (hP : CvgProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hU : UceProg p) : IvgE p :=
  fun hc hS hq hqb hv hlps hCr =>
    RefE.run_err (s₀ := ⟨_, Locals.init []⟩) (installValueGuards_specE p hP _ _ _ _ _) hnv
      ⟨hnv, hU⟩ (ivg_ref hap hkp.crf _ hS hq hqb hv hlps hCr) hc

/-! ## `check_thm_val(vis, c)` -/

/-- **The model of `check_thm_val`, both outcomes**: `pin_word`, `env_push` (outside the verdict
closure) through their `Option` models; the core stubs, `lvl_eq_fueled` and
`install_value_guards` through their runs. -/
l_model checkThmVal_specE (p : Prog) (hV : ValProg p)
  fns [hV.tv ↦ checkThmValE]
  specs [pinWord_specW p hV.cvg.pin n, callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_thm_val`'s error arms assume: the core stubs' and `install_value_guards`' claims,
`lvl_eq_c` outside the verdict closure (`lvl_eq_fueled`'s claim). -/
structure TvCtx (p : Prog) : Prop where
  core : CoreStubsE p
  ivg : IvgE p
  lvc : NVAt p "lvl_eq_c"

/-- What a value check that pushes (`check_thm_val`) or a declaration arm (`check_decl_thm`) gives
besides the twin's environment `fe'` (from `m`): the stage relation at it over the result word,
the core's memos, the growth. -/
structure ArmPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR dn r fe' m' a'
  memos : CoreMemos m'
  grow : IWGrow m m'

/-- **`check_thm_val` refines `checkThmVal .verified` under `StageT`, both outcomes**: the type not
a proposition and the type mismatch are the twin's `invalid`, the level comparison out of fuel its
`notImplemented` (`lef_ref`'s error half); the core stubs (`KnotStageProg`/`CoreStubsE`),
`lvl_eq_fueled` and `install_value_guards` through their runs; `pin_word`, `env_push` lifted. -/
theorem tv_ref {p : Prog} (hq : KnotStageProg p) (hV : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word}
    {cv : IConstantVal} {v : EIdx} (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some (.thmInfo cv))
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK m) :
    RefE (TvCtx p) (checkThmValE p n m vis c) (checkThmVal V fe cv v) a
      (fun x fe' a' => ArmPost dn m x.1 x.2 fe' a') := by
  have hL := hq.knot.lvc
  have hcv := decCI_cvTA hci (.inl rfl)
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.iw
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have h00 : (0 : Word).toNat = 0 := rfl
  cases n with
  | zero => rw [checkThmValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkThmValE.arm1, ev, et, checkThmVal_eq]
  -- the type's type
  rcases h1 : callE p n "infer_type_core" [vis, 0, wt] m with e1 | ⟨r1, m1⟩
  · rw [checkThmValE.k_infer_type_core.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.inferTypeCore n hn' hS 0 wt hwtl _ h1
    rw [h00, ← hty] at this
    exact this
  rw [checkThmValE.k_infer_type_core.arm1]
  have h1' := callW_of_callE h1
  have hCr1 := hkp.call (im_mem _ rfl) h1' hCr
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS 0 wt hwtl r1 m1 h1'
  have hrun1' := hrun1
  rw [h00, ← hty] at hrun1'
  refine RefE.bind_right hrun1' ?_
  -- its sort
  rcases h2 : callE p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with e2 | ⟨r2, m2⟩
  · rw [checkThmValE.k_ensure_sort_core.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2
    rw [h00, hx1] at this
    exact this
  rw [checkThmValE.k_ensure_sort_core.arm1]
  have h2' := callW_of_callE h2
  have hCr2 := hkp.call (im_mem _ rfl) h2' hCr1
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2'
  have hrun2' := hrun2
  rw [h00, hx1] at hrun2'
  refine RefE.bind_right hrun2' ?_
  -- the zero level
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  have hF := hS2.stage.check.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  have h3 : pinWordW m2 53 = some ([pinW m2 53], m2) := by
    simp only [pinWordW, hflag, ite_false, hz]
  rw [h3, liftE_some, checkThmValE.k_pin_word.arm1]
  simp only [List.headD_cons]
  refine RefE.bind_right (pinZeroLevel_run hF) ?_
  -- the two levels read back
  obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe)
    (d := (0 : Word).toNat) (e := decI (r1.headD 0)) hrun2
  obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
  rw [← hx2] at hdu
  obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
  rw [hF.zeroLevel] at hdz
  -- the comparison
  have hsL := lefE_spec p hV.lef n ⟨m2, Locals.init []⟩ (r2.headD 0) (pinW m2 53)
  have hRL := lef_ref hq.closed hL n hS2 hx2l hF.lv_lt.2.1 hdu hdz
  rw [← hx2, lefT_bind]
  rcases h4 : callE p n "lvl_eq_fueled" [r2.headD 0, pinW m2 53] m2 with e4 | ⟨r4, m4⟩
  · rw [checkThmValE.k_lvl_eq_fueled.none]
    exact RefE.bind_left fun hG => RefE.run_err hsL trivial hG.lvc hRL h4
  have hCr4 := hkp.call (im_mem _ rfl) (callW_of_callE h4) hCr2
  obtain ⟨s4, hs4, -, b4, a4, hrunT, ⟨hrun4, hr4, hS4, hg4, -, -⟩⟩ := RefE.run_ok hsL hRL h4
  subst hs4
  dsimp only at hS4 hg4 hr4
  have hrun4' := hrun4
  refine RefE.bind_right hrunT ?_
  by_cases hb4 : r4.headD 0 = 0
  · -- the type is not a proposition
    rw [checkThmValE.k_lvl_eq_fueled.abort1 p n vis c wv wt r4 _ hb4]
    have : b4 = false := by
      cases b4
      · rfl
      · exact absurd hr4 (by rw [hb4]; decide)
    subst this
    exact RefE.bind_left fun _ => ErrClaim.fail _ _ rfl
  rw [checkThmValE.k_lvl_eq_fueled.arm1 p n vis c wv wt r4 _ hb4]
  have ex4 : b4 = true := by
    cases b4
    · exact absurd hr4 (by simpa using hb4)
    · rfl
  subst ex4
  show RefE _ _ (dvT fe cv (decI wv) (.thmInfo cv) "type mismatch in theorem") a4 _
  unfold dvT
  -- the parameters' names read back at the guards: the prefix extends the store
  have hlps4 : ∃ ks, cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hrun1' hrun2'
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4'
      (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
    rw [hst4]
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
  have hg14 := hg1.trans (hg2.trans hg4)
  have hcv4 : decCV (erA s4.mem) (c + 1).toNat = some cv := by
    rw [hc1]; exact ArrExt.decCV (IWGrow.erecExt hg14) hcv
  -- the value's guards
  rcases h5 : callE p n "install_value_guards" [vis, c + 1, wv] s4.mem with e5 | ⟨r5, m5⟩
  · rw [checkThmValE.k_install_value_guards.none]
    exact RefE.bind_left fun hG => hG.ivg h5 hS4 hcv4 (by rw [hc1]; omega) hwvl hlps4 hCr4
  rw [checkThmValE.k_install_value_guards.arm1]
  obtain ⟨s5, hs5, -, _, a5, hrun5, hS5, hg5, -⟩ := RefE.run_ok
    (s₀ := ⟨s4.mem, Locals.init []⟩)
    (installValueGuards_specE p hV.cvg n _ vis (c + 1) wv)
    (ivg_ref hap hkp.crf n hS4 hcv4 (by rw [hc1]; omega) hwvl hlps4 hCr4) h5
  subst hs5
  refine RefE.bind_right hrun5 ?_
  -- the value's type
  rcases h7 : callE p n "infer_type_core" [vis, 0, wv] s5.mem with e7 | ⟨r7, m7⟩
  · rw [checkThmValE.k_infer_type_core_2.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.inferTypeCore n hn' hS5 0 wv hwvl _ h7
    rw [h00] at this
    exact this
  rw [checkThmValE.k_infer_type_core_2.arm1]
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7l, hx7⟩ :=
    hq.inferTypeCore_sim n hn' hS5 0 wv hwvl r7 m7 (callW_of_callE h7)
  rw [h00] at hrun7
  refine RefE.bind_right hrun7 ?_
  -- the comparison with the declared type
  rcases h8 : callE p n "is_def_eq_core" [vis, 0, r7.headD 0, wt] m7 with e8 | ⟨r8, m8⟩
  · rw [checkThmValE.k_is_def_eq_core.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8
    rw [h00, hx7, ← hty] at this
    exact this
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8⟩ :=
    hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl r8 m8 (callW_of_callE h8)
  rw [h00, hx7, ← hty] at hrun8
  refine RefE.bind_right hrun8 ?_
  by_cases hb8 : r8.headD 0 = 0
  · -- the type mismatch
    rw [checkThmValE.k_is_def_eq_core.abort1 p n vis c r8 m8 hb8]
    have ex8 : x8 = false := by rw [← hx8, decBool, hb8]; rfl
    rw [ex8]
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [checkThmValE.k_is_def_eq_core.arm1 p n vis c r8 m8 hb8]
  have ex8 : x8 = true := by rw [← hx8]; simpa [decBool] using hb8
  rw [ex8]
  -- the push
  have hg18 := hg14.trans (hg5.trans (hg7.trans hg8))
  have hci8 := ArrExt.decCI (IWGrow.erecPExt hg18) hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci8
  have hw : (rdW (m8.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  rcases h9 : callW p n "env_push" [vis, c] m8 with _ | ⟨r9, m9⟩
  · rw [liftE_none, checkThmValE.k_env_push.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, checkThmValE.k_env_push.arm1]
  obtain ⟨s9, hs9, -, hW9⟩ := triple_of_callW (s₀ := ⟨m8, Locals.init []⟩)
    (envPush_specW p hV.rcp n ⟨m8, Locals.init []⟩ vis c hw) h9
  subst hs9
  obtain ⟨hS9, hg9⟩ := envPushW_ok hW9 hS8.stage hci8
  have hM9 : CoreMemos s9.mem := hS8.twin.memos.frame (envPushW_frame hW9)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact RefE.ret rfl ⟨by simpa using hS9, hM9, hg18.trans hg9⟩


/-! ## `check_value_group(vis, g)` -/

/- The `simp` recipe with `locals` (the locals evaluated before `simp_all`): 4 s; `finish`
(`gen 20`, `instances 4000`) took 45 s. -/
/-- **The model of `check_value_group`, both outcomes**: `iw_reset`, `pin_word`, `lvl_eq_c`
(outside the verdict closure) through their `Option` models; the core stubs and
`install_value_guards` through their runs. -/
l_model checkValueGroup_specE (p : Prog) (hP : CvgProg p)
  fns [hP.cvg ↦ checkValueGroupE]
  specs [iwReset_specW p hP.reset n, pinWord_specW p hP.pin n, callW_spec p n "lvl_eq_c"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_value_group`'s error claims assume: the core stubs' and `install_value_guards`'
claims. -/
structure CvgCtx (p : Prog) : Prop where
  core : CoreStubsE p
  ivg : IvgE p

/-- What `check_value_group` gives besides the twin's run (from `m`): `StageT` after it, the
growth from the memory after `iw_reset`, the memo of `consts_resolve_ffast`. -/
structure CvgPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow (m.set64 CTL 200 0) m'
  cr : L.Stubs.CrOK m'

/-- **`check_value_group` refines `checkValueGroup .verified` under `StageT`, both outcomes**:
the program's own core (`KnotStageProg`; the core stubs' claims); for a theorem, the level
comparison (`lvl_eq_c` answers `0`: the twin's `liftFueled` on `none`; `1`: not a proposition)
and `install_value_guards` (`ivg_ref`, its claim); the type mismatch (the three kinds' codes, all
the twin's `invalid`). -/
theorem cvg_ref {p : Prog} (hq : KnotStageProg p) (hP : CvgProg p) (hL : LvlCacheProg p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {g : Word} {vg : ValueGroup}
    (hS : StageT dn vis fe m a) (hg : decVG (erecP m) g.toNat = some vg) (hCr : L.Stubs.CrOK m)
    (hthm : vg.kind = .thm → ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store vg.cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type) :
    RefE (CvgCtx p) (checkValueGroupE p n m vis g) (checkValueGroup V fe vg) a
      (fun v _ a' => CvgPost dn vis fe m v.2 a') := by
  cases n with
  | zero => rw [checkValueGroupE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkValueGroupE.arm1, show iwResetW m = some ([], m.set64 CTL 200 0) from rfl, liftE_some,
    checkValueGroupE.k_iw_reset.arm1]
  have hCr0 : L.Stubs.CrOK (m.set64 CTL 200 0) :=
    CrOK.frame hCr (MemFrame.setCtl m 200 0) (by simp) (by decide)
  have hS0 := iwReset_stageT hS
  have hP0 : erecP (m.set64 CTL 200 0) = erecP m := erecP_reset m
  generalize hm0 : m.set64 CTL 200 0 = m0 at hCr0 hS0 hP0
  rw [← hP0] at hg
  have hEs := hS0.stage.iw.erSize
  obtain ⟨⟨wk, hwk, hvk⟩, hcv, wj, hwj, hwjl, hjv⟩ := decVG_words hg
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hb5 : g.toNat + 5 < (m0.arr64 EREC).size := by
    have := (Array.getElem?_eq_some_iff.mp (erecP_get hwj)).1; exact this
  have et : rdW (m0.arr64 EREC) (g + 4) = wt :=
    rdW_of_get? (k := g.toNat + 4) (by rw [UInt64.toNat_add]; simp; omega)
      (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have ev : rdW (m0.arr64 EREC) (g + 5) = wj :=
    rdW_of_get? (k := g.toNat + 5) (by rw [UInt64.toNat_add]; simp; omega) (erecP_get hwj)
  rw [et, ev]
  have h00 : (0 : Word).toNat = 0 := rfl
  unfold checkValueGroup
  -- `infer_type_core(vis, 0, t)`
  rcases h1 : callE p n "infer_type_core" [vis, 0, wt] m0 with e1 | ⟨r1, m1⟩
  · rw [checkValueGroupE.k_infer_type_core.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.inferTypeCore n hn' hS0 0 wt hwtl _ h1
    rwa [h00, ← hty] at this
  rw [checkValueGroupE.k_infer_type_core.arm1]
  have h1' := callW_of_callE h1
  have hCr1 := hkp.call (im_mem _ rfl) h1' hCr0
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS0 0 wt hwtl r1 m1 h1'
  rw [h00, ← hty] at hrun1
  refine RefE.bind_right hrun1 ?_
  -- `ensure_sort_core(vis, 0, st)`
  rcases h2 : callE p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with e2 | ⟨r2, m2⟩
  · rw [checkValueGroupE.k_ensure_sort_core.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2
    rwa [h00, hx1] at this
  have h2' := callW_of_callE h2
  have hCr2 := hkp.call (im_mem _ rfl) h2' hCr1
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2'
  rw [h00, hx1] at hrun2
  refine RefE.bind_right hrun2 ?_
  have hext2 : ArrExt (erecP m0) (erA m2) := IWGrow.erecExt (hg1.trans hg2)
  have ek : rdW (m2.arr64 EREC) g = wk := rdW_of_get? rfl (hext2 _ _ hwk)
  -- the tail: `infer_type_core(vis, 0, v)`, `is_def_eq_core(vis, 0, vt, t)`, the mismatch
  have tail : ∀ (m5 : Mem) (a5 : AState), StageT dn vis fe m5 a5 → IWGrow m0 m5 →
      L.Stubs.CrOK m5 →
      RefE (CvgCtx p) (checkValueGroupE.j1 p n vis g wt wj m5) (do
          let vtype ← inferTypeCore V fe checkFuel 0 vg.jv
          let b ← isDefEqCore V fe checkFuel 0 vtype vg.cv.type
          if b = true then pure ()
            else fail (CheckError.invalid (toString "type mismatch in " ++ toString vg.kind.word)) :
          AM Unit) a5 (fun v _ a' => CvgPost dn vis fe m v.2 a') := by
    intro m5 a5 hS5 hg5 hCr5
    rw [checkValueGroupE.j1.arm1]
    rcases h7 : callE p n "infer_type_core" [vis, 0, wj] m5 with e7 | ⟨r7, m7⟩
    · rw [checkValueGroupE.k_infer_type_core_2.none]
      refine RefE.bind_left fun hG => ?_
      have := hG.core.inferTypeCore n hn' hS5 0 wj hwjl _ h7
      rwa [h00, ← hjv] at this
    rw [checkValueGroupE.k_infer_type_core_2.arm1]
    have h7' := callW_of_callE h7
    obtain ⟨x7, a7, hrun7, hS7, hg7, hx7l, hx7⟩ := hq.inferTypeCore_sim n hn' hS5 0 wj hwjl r7 m7 h7'
    rw [h00, ← hjv] at hrun7
    refine RefE.bind_right hrun7 ?_
    rcases h8 : callE p n "is_def_eq_core" [vis, 0, r7.headD 0, wt] m7 with e8 | ⟨r8, m8⟩
    · rw [checkValueGroupE.k_is_def_eq_core.none]
      refine RefE.bind_left fun hG => ?_
      have := hG.core.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8
      rwa [h00, hx7, ← hty] at this
    have h8' := callW_of_callE h8
    have hCr8 := hkp.call (im_mem _ rfl) h8' (hkp.call (im_mem _ rfl) h7' hCr5)
    obtain ⟨x8, a8, hrun8, hS8, hg8, hx8⟩ :=
      hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl r8 m8 h8'
    rw [h00, hx7, ← hty] at hrun8
    refine RefE.bind_right hrun8 ?_
    by_cases hb8 : r8.headD 0 = 0
    · have ex8 : x8 = false := by rw [← hx8, decBool, hb8]; rfl
      rw [ex8]
      by_cases k1 : rdW (m8.arr64 EREC) g = 1
      · rw [checkValueGroupE.k_is_def_eq_core.abort1 p g r8 m8 hb8 k1]
        exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
      by_cases k2 : rdW (m8.arr64 EREC) g = 2
      · rw [checkValueGroupE.k_is_def_eq_core.abort2 p g r8 m8 hb8 k1 k2]
        exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
      · rw [checkValueGroupE.k_is_def_eq_core.abort3 p g r8 m8 hb8 k1 k2]
        exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
    rw [checkValueGroupE.k_is_def_eq_core.arm1 p g r8 m8 hb8]
    have ex8 : x8 = true := by rw [← hx8]; simpa [decBool] using hb8
    rw [ex8]
    exact RefE.ite_pos rfl (RefE.ret rfl ⟨hS8, hm0 ▸ hg5.trans (hg7.trans hg8), hCr8⟩)
  by_cases hk1 : wk = 1
  · -- a theorem: the proposition test and the value's guards
    subst hk1
    have hkind : vg.kind = .thm := by simpa [decVK] using hvk.symm
    rw [checkValueGroupE.k_ensure_sort_core.arm1 p n vis g wt wj r2 m2 ek]
    have hb : (vg.kind == ValueKind.thm) = true := by rw [hkind]; rfl
    refine RefE.ite_pos hb ?_
    have hflag : pinW m2 0 ≠ 0 := hS2.flag
    have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
    simp only [pinWordW, hflag, ite_false, liftE_some, checkValueGroupE.k_pin_word.arm1,
      List.headD_cons, hz]
    have hF := hS2.stage.check.pins.full hflag
    refine RefE.bind_right (pinZeroLevel_run hF) ?_
    -- the two levels read back: the sort's level, the pinned zero
    obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe) (d := 0)
      (e := x1) hrun2
    obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
    rw [← hx2] at hdu
    obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
    rw [hF.zeroLevel] at hdz
    -- `lvl_eq_c(u, zr)`
    rcases h4 : callW p n "lvl_eq_c" [r2.headD 0, pinW m2 53] m2 with _ | ⟨r4, m4⟩
    · rw [liftE_none, checkValueGroupE.k_lvl_eq_c.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    have hCr4 := hkp.call (im_mem _ rfl) h4 hCr2
    obtain ⟨x4, a4, hrun4, hS4, hg4, hdec4⟩ :=
      lvlEqC_simTE p hq.closed hL n hS2 (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 lu lz hdu hdz
        r4 m4 h4
    rw [hx2] at hrun4
    refine RefE.bind_right hrun4 ?_
    unfold decLvlEq at hdec4
    by_cases c0 : r4.headD 0 = 0
    · -- out of fuel: the twin's `liftFueled` on `none`
      rw [checkValueGroupE.k_lvl_eq_c.abort1 p n vis g wt wj r4 m4 c0]
      have hx : x4 = none := by
        rw [c0] at hdec4
        rcases x4 with _ | _ | _ <;> first | rfl | exact absurd hdec4 (by decide)
      subst hx
      exact RefE.bind_left fun _ => ErrClaim.fail _ _ rfl
    by_cases c1 : r4.headD 0 = 1
    · -- not a proposition
      rw [checkValueGroupE.k_lvl_eq_c.abort2 p n vis g wt wj r4 m4 c0 c1]
      have hx : x4 = some false := by
        rw [c1] at hdec4
        rcases x4 with _ | _ | _ <;> first | rfl | exact absurd hdec4 (by decide)
      subst hx
      exact RefE.bind_right (a₁ := a4) rfl
        (RefE.ite_neg (by decide) (RefE.bind_left fun _ => ErrClaim.fail _ _ rfl))
    by_cases c2' : r4.headD 0 ≠ 2
    · rw [checkValueGroupE.k_lvl_eq_c.abort3 p n vis g wt wj r4 m4 c0 c1 c2']
      exact RefE.of_cls0 rfl
    have c2 : r4.headD 0 = 2 := Classical.not_not.mp c2'
    rw [checkValueGroupE.k_lvl_eq_c.arm1 p n vis g wt wj r4 m4 c0 c1 c2]
    have hx : x4 = some true := by
      rw [c2] at hdec4
      rcases x4 with _ | _ | _ <;> first | rfl | exact absurd hdec4 (by decide)
    subst hx
    refine RefE.bind_right (a₁ := a4) rfl (RefE.ite_pos rfl ?_)
    -- the parameters' names read back at the guards: the prefix extends the store
    have hlps4 : ∃ ks, vg.cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
      obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hthm hkind
      obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hrun1 hrun2
      obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
        (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
      rw [hst4]
      exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
    have hg1' : (g + 1).toNat = g.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hcv4 : decCV (erA m4) (g + 1).toNat = some vg.cv := by
      rw [hg1']
      exact ArrExt.decCV (IWGrow.erecExt (hg1.trans (hg2.trans hg4))) hcv
    -- `install_value_guards(vis, g + 1, v)`
    rcases h5 : callE p n "install_value_guards" [vis, g + 1, wj] m4 with e5 | ⟨r5, m5⟩
    · rw [checkValueGroupE.k_install_value_guards.none, hjv]
      exact RefE.bind_left fun hG => hG.ivg h5 hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4
    rw [checkValueGroupE.k_install_value_guards.arm1]
    obtain ⟨s5, hs5, -, _, a5, hrun5, hS5, hg5, hCr5⟩ := RefE.run_ok
      (s₀ := ⟨m4, Locals.init []⟩)
      (installValueGuards_specE p hP n _ vis (g + 1) wj)
      (ivg_ref hap hkp.crf n hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4) h5
    subst hs5
    rw [← hjv] at hrun5
    exact RefE.bind_right hrun5 (tail _ _ hS5 (hg1.trans (hg2.trans (hg4.trans hg5))) hCr5)
  · rw [checkValueGroupE.k_ensure_sort_core.arm2 p n vis g wt wj r2 m2 (by rw [ek]; exact hk1)]
    have hkind : vg.kind ≠ .thm := by
      intro hk; rw [hk] at hvk
      have : wk.toNat = 1 := by
        unfold decVK at hvk; split at hvk <;> simp_all
      exact hk1 (UInt64.toNat_inj.mp (by simpa using this))
    have hb : (vg.kind == ValueKind.thm) = false := by
      revert hkind; cases vg.kind <;> decide
    exact RefE.ite_neg (by rw [hb]; decide) (tail m2 a2 hS2 (hg1.trans hg2) hCr2)

end L.Arena
