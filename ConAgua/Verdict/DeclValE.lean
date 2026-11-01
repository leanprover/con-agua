module

import ConAgua.Arena.DeclCvgT
public import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndRealMemoCrT
public import ConAgua.Arena.IndRealApdT
public import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.DeclValT
import ConAgua.Arena.DeclStepSpec
public import ConAgua.Verdict.LefRef
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.IndRealLvlT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.LvlGrow
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Core.Walks.Cached
public import ConAgua.Arena.KnotEntry
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclStep

@[expose] public section

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
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
  refine RefE.splitNot (fun hb5 => by rw [← hx5]; simpa using hb5)
    (fun hb5 => by rw [← hx5] at hb5; simpa using hb5) (fun _ _ => ?_) fun _ _ => RefE.ret rfl
      ⟨hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hCr5.crOK⟩
  rcases h6 : callE p (n + 1) "unresolved_consts_error" [vis, v, 1] m5 with e6 | ⟨r6, m6⟩ <;>
    dsimp only [installValueGuardsE.k_unresolved_consts_error]
  · obtain ⟨M5, hC5⟩ := hS5.core
    exact fun hG => uce_errClaim_lo hG.uce hG.nv hC5 hv (by decide) h6 "value"
  · exact RefE.of_cls0 rfl

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
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
  cases n with
  | zero => rw [checkThmValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkThmValE.arm1, ev, et, checkThmVal_eq, hty]
  -- the type's type
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h1 => hG.core.inferTypeCore n hn' hS 0 wt hwtl _ h1)
    (fun b h1 => hq.inferTypeCore_sim n hn' hS 0 wt hwtl b.1 b.2 h1)
    fun r1 m1 x1 a1 h1 hrun1 ⟨hS1, hg1, hx1l, hx1⟩ => ?_
  dsimp only [checkThmValE.k_infer_type_core]
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  subst hx1
  -- its sort
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h2 => hG.core.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2)
    (fun b h2 => hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 hrun2 ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  dsimp only [checkThmValE.k_ensure_sort_core]
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  -- the zero level
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  have hF := hS2.stage.check.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  have h3 : pinWordW m2 53 = some ([pinW m2 53], m2) := by
    simp only [pinWordW, hflag, ite_false, hz]
  rw [h3, liftE_some]
  dsimp only [checkThmValE.k_pin_word]
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
  rw [← hx2, lefT_bind]
  refine RefE.bindRun (s₀ := ⟨m2, Locals.init []⟩) (fun _ => rfl)
    (lefE_spec p hV.lef n ⟨m2, Locals.init []⟩ (r2.headD 0) (pinW m2 53)) (fun _ => trivial)
    (fun hG => hG.lvc) (lef_ref hq.closed hL n hS2 hx2l hF.lv_lt.2.1 hdu hdz)
    fun r4 s4 b4 a4 h4 _ _ ⟨hrun4, hr4, hS4, hg4, _, _⟩ => ?_
  dsimp only at hS4 hg4 hr4
  have hCr4 := hkp.call (im_mem _ rfl) (callW_of_callE h4) hCr2
  dsimp only [checkThmValE.k_lvl_eq_fueled]
  -- the type is not a proposition
  refine RefE.guard rfl (fun hb4 => by cases b4; rfl; exact absurd hr4 (by rw [hb4]; decide))
    (fun hb => by subst hb; simpa using hr4) fun _ hb => ?_
  subst hb
  show RefE _ _ (dvT fe cv (decI wv) (.thmInfo cv) "type mismatch in theorem") a4 _
  unfold dvT
  -- the parameters' names read back at the guards: the prefix extends the store
  have hlps4 : ∃ ks, cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws (by rw [hty]; exact hrun1) hrun2
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
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
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h7 => hG.core.inferTypeCore n hn' hS5 0 wv hwvl _ h7)
    (fun b h7 => hq.inferTypeCore_sim n hn' hS5 0 wv hwvl b.1 b.2 h7)
    fun r7 m7 x7 a7 _ _ ⟨hS7, hg7, hx7l, hx7⟩ => ?_
  dsimp only [checkThmValE.k_infer_type_core_2]
  subst hx7
  rw [hty]
  -- the comparison with the declared type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h8 => hG.core.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8)
    (fun b h8 => hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl b.1 b.2 h8)
    fun r8 m8 x8 a8 _ _ ⟨hS8, hg8, hx8⟩ => ?_
  dsimp only [checkThmValE.k_is_def_eq_core]
  -- the type mismatch
  refine RefE.guard rfl (fun hb8 => by rw [← hx8, decBool, hb8]; rfl)
    (fun hb8 => by rw [← hx8] at hb8; simpa [decBool] using hb8) fun _ _ => ?_
  -- the push
  have hg18 := hg14.trans (hg5.trans (hg7.trans hg8))
  have hci8 := ArrExt.decCI (IWGrow.erecPExt hg18) hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci8
  have hw : (rdW (m8.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r9 m9 h9 => ?_
  dsimp only [checkThmValE.k_env_push]
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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
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
  unfold checkValueGroup
  rw [hty, hjv]
  -- `infer_type_core(vis, 0, t)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h1 => hG.core.inferTypeCore n hn' hS0 0 wt hwtl _ h1)
    (fun b h1 => hq.inferTypeCore_sim n hn' hS0 0 wt hwtl b.1 b.2 h1)
    fun r1 m1 x1 a1 h1 hrun1 ⟨hS1, hg1, hx1l, hx1⟩ => ?_
  dsimp only [checkValueGroupE.k_infer_type_core]
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr0
  subst hx1
  -- `ensure_sort_core(vis, 0, st)`
  refine RefE.bindCall (fun _ => checkValueGroupE.k_ensure_sort_core.none ..)
    (fun hG _ h2 => hG.core.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2)
    (fun b h2 => hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 hrun2 ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  subst hx2
  have hext2 : ArrExt (erecP m0) (erA m2) := IWGrow.erecExt (hg1.trans hg2)
  have ek : rdW (m2.arr64 EREC) g = wk := rdW_of_get? rfl (hext2 _ _ hwk)
  -- the tail: `infer_type_core(vis, 0, v)`, `is_def_eq_core(vis, 0, vt, t)`, the mismatch
  have tail : ∀ (m5 : Mem) (a5 : AState), StageT dn vis fe m5 a5 → IWGrow m0 m5 →
      L.Stubs.CrOK m5 →
      RefE (CvgCtx p) (checkValueGroupE.j1 p n vis g wt wj m5) (do
          let vtype ← inferTypeCore V fe checkFuel 0 (decI wj)
          let b ← isDefEqCore V fe checkFuel 0 vtype (decI wt)
          if b = true then pure ()
            else fail (CheckError.invalid (toString "type mismatch in " ++ toString vg.kind.word)) :
          AM Unit) a5 (fun v _ a' => CvgPost dn vis fe m v.2 a') := by
    intro m5 a5 hS5 hg5 hCr5
    rw [checkValueGroupE.j1.arm1]
    refine RefE.bindCall (fun _ => rfl) (fun hG _ h7 => hG.core.inferTypeCore n hn' hS5 0 wj hwjl _ h7)
      (fun b h7 => hq.inferTypeCore_sim n hn' hS5 0 wj hwjl b.1 b.2 h7)
      fun r7 m7 x7 a7 h7 _ ⟨hS7, hg7, hx7l, hx7⟩ => ?_
    dsimp only [checkValueGroupE.k_infer_type_core_2]
    subst hx7
    refine RefE.bindCall (fun _ => checkValueGroupE.k_is_def_eq_core.none ..)
      (fun hG _ h8 => hG.core.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8)
      (fun b h8 => hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl b.1 b.2 h8)
      fun r8 m8 x8 a8 h8 _ ⟨hS8, hg8, hx8⟩ => ?_
    have hCr8 := hkp.call (im_mem _ rfl) (callW_of_callE h8) (hkp.call (im_mem _ rfl) (callW_of_callE h7) hCr5)
    rw [checkValueGroupE.k_is_def_eq_core.eq_2]
    refine RefE.splitNot (fun hb8 => by rw [← hx8, decBool, hb8]; decide)
      (fun hb8 => by rw [← hx8] at hb8; simpa [decBool] using hb8)
      (fun _ _ => by split <;> (try split) <;> exact fun _ => ErrClaim.fail _ _ rfl)
      fun _ _ => RefE.ret rfl ⟨hS8, hm0 ▸ hg5.trans (hg7.trans hg8), hCr8⟩
  -- a theorem: the proposition test and the value's guards; otherwise the tail
  have hkd : wk = 1 ↔ (vg.kind == ValueKind.thm) = true := by
    rw [← UInt64.toNat_inj]; unfold decVK at hvk; split at hvk <;> grind
  rw [checkValueGroupE.k_ensure_sort_core.eq_2, ek]
  refine RefE.split hkd.mp hkd.mpr (fun hk1 _ => ?_) fun _ _ => tail m2 a2 hS2 (hg1.trans hg2) hCr2
  subst hk1
  have hkind : vg.kind = .thm := by simpa [decVK] using hvk.symm
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  simp only [pinWordW, hflag, ite_false, liftE_some, checkValueGroupE.k_pin_word.arm1,
    List.headD_cons, hz]
  have hF := hS2.stage.check.pins.full hflag
  refine RefE.bind_right (pinZeroLevel_run hF) ?_
  -- the two levels read back: the sort's level, the pinned zero
  obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe) (d := 0)
    (e := decI (r1.headD 0)) hrun2
  obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
  obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
  rw [hF.zeroLevel] at hdz
  -- `lvl_eq_c(u, zr)`
  refine RefE.bindSim (fun _ => checkValueGroupE.k_lvl_eq_c.none ..)
    (lvlEqC_simTE p hq.closed hL n hS2 (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 lu lz hdu hdz)
    fun r4 x4 m4 a4 h4 hrun4 ⟨hS4, hg4, hdec4⟩ => ?_
  have hCr4 := hkp.call (im_mem _ rfl) h4 hCr2
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
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws (by rw [hty]; exact hrun1) hrun2
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
  · rw [checkValueGroupE.k_install_value_guards.none]
    exact RefE.bind_left fun hG => hG.ivg h5 hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4
  rw [checkValueGroupE.k_install_value_guards.arm1]
  obtain ⟨s5, hs5, -, _, a5, hrun5, hS5, hg5, hCr5⟩ := RefE.run_ok
    (s₀ := ⟨m4, Locals.init []⟩)
    (installValueGuards_specE p hP n _ vis (g + 1) wj)
    (ivg_ref hap hkp.crf n hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4) h5
  subst hs5
  exact RefE.bind_right hrun5 (tail _ _ hS5 (hg1.trans (hg2.trans (hg4.trans hg5))) hCr5)

end L.Arena
