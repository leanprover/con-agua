module

import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Checker.Base
public import ConAgua.Arena.IndT.Sum3
public import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.IndT.SumSteps
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.CheckSumCtor
import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import ConLeche.Verify.BridgeWfImp
import ConRon.Bridge.Inductives.SumInstall
public import ConAgua.Arena.IndSumSpec.SumProg
public import ConAgua.Arena.IndT.Install1
import ConLeche.Verify.Denote.IndFrame
public import ConRon.Bridge.Inductives.Rel
import all ConAgua.Arena.IndSum
import ConAgua.L.WordOff
import ConAgua.Arena.RecClassSpec.IhW

@[expose] public section


/-!
# `check_sum_ctor` and `check_sum_ctor_tail`: one model and one refinement each

`ctorE`, `ctlE` (`l_model … unified`) and `ctor_ref`, `ctl_ref` (`RefE`, both outcomes), from `StageC`
and con-ron's preconditions of `checkSumCtor_spec` (the family's name and level parameters, the
result sort, the two constant values and both environments denote; the pre-block environment's
`IFEnvOKS`), the twin side transcribed from that spec's proof. The tail (`cscTailT`, `ctl_ref`): the
fields opened past the parameters (`openPisAtFvarsF_run`), the family head (`paramLevels_spec`,
`internConstE_run`), the residual's spine (`getAppFn_run`, `getAppArgs_run`), the resolution tests
(`fieldDomsResolve_spec`, `idxArgsResolve_spec`), the field sorts (`fsorts_ref`, con-ron's
`checkStructFieldSortsI_spec` on its run for the `CoreStep`). The callees outside the verdict closure
are lifted; `check_constant_val`, `check_struct_doms_at`, the tail and the field sorts are unified
callees, so `G` is `VerdictCtx` for the tail and `VerdictCtxU` (`ccv_ref`'s) for `check_sum_ctor`.
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true

/-- **The model of `check_sum_ctor_tail`, both outcomes**: the field sorts by their unified model,
the other callees (outside the verdict closure) lifted. -/
l_model ctlE_spec (p : Prog) (hP : SumProg p)
  fns [hP.htail ↦ ctlE]
  specs [callW_spec p n "open_pis_at_fvars_f", callW_spec p n "param_levels", callW_spec p n "intern_const",
    callW_spec p n "get_app_fn_f", callW_spec p n "get_app_args_f", callW_spec p n "sl_eq",
    callW_spec p n "field_doms_resolve", callW_spec p n "idx_args_resolve",
    fsortsE_spec p hP.hcfs hP.ad.ftd hP.hfsb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_sum_ctor`, both outcomes**: the constant check, the domains and the tail by
their unified models, the other callees (outside the verdict closure) lifted. -/
l_model ctorE_spec (p : Prog) (hP : SumProg p) (hV : CcvProg p)
  fns [hP.hctor ↦ ctorE]
  specs [checkConstantVal_specE p hV n, callW_spec p n "strip_pis", callW_spec p n "struct_ctor_resid_ok",
    callW_spec p n "open_pis_at_fvars_f", callW_spec p n "fvar_type_ds", sdomsE_spec p hP.hsd n,
    ctlE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)

/-- What `check_sum_ctor_tail` gives besides the twin's `(cvCa, sorts)` `x` (from `m`, `a`): the
stage, the growth, the constant unchanged, the sorts as the `IW` slice `r = [o, l]`, `AbsOK`, the
twin's core step. -/
structure CtlPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

include hq henv hOpf hLC hLT in
/-- **`check_sum_ctor_tail` refines the tail of `checkSumCtor .verified` (`cscTailT`), both
outcomes** (twin side: the tail of con-ron's `checkSumCtor_spec`'s proof): its callees outside the
verdict closure lifted, the field sorts by `fsorts_ref`. -/
theorem ctl_ref (hP : SumProg p) (hcr : CrfF p) (m : Nat) (hn : m + 1 ≤ 2 ^ 62) (m0 : Mem)
    (a : AState) (T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) (lps : List NIdx)
    (cq1 : List EIdx) (hC : StageC dn vis fe env m0 a) (hT : H T)
    (hlps : decHL m0 lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m0)
    (hcq : decHL m0 cqO.toNat cqL.toNat = some cq1) (hcqb : cqO.toNat + cqL.toNat ≤ iwTop m0)
    (hcqB : H cqB) (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64)
    (hnf : nP.toNat + nF.toNat < 2 ^ 64) (hA : AbsOK m0)
    {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {crestP : ConLeche.Expr}
    (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP)
    (hcqBP : denoteE a.store (decI cqB) = some crestP) (hwsc : ConLeche.Expr.WScoped nP.toNat crestP) :
    RefE (VerdictCtx p) (ctlE p (m + 1) m0 vis vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB)
      (cscTailT fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0)
        (lg != 0) nF.toNat (cq1, decI cqB)) a
      (fun v _ a' => CtlPost dn vis fe env m0 a v.2 a') := by
  rw [ctlE.arm1]; unfold cscTailT
  have k0 := InsAt.refl hC hA
  refine RefE.bindSim (fun _ => rfl) (opf_step hOpf k0 hcqB rfl hcqBP) fun rx o m1 a1 _ _ ⟨k1, ho, hdo⟩ => ?_
  dsimp only [ctlE.k_open_pis_at_fvars_f]
  refine RefE.guardOpt (by decide) ho.1 ho.2 fun ⟨xl1, xb⟩ hq0 _ => ?_
  obtain ⟨hxl, hxlb, hxb, rfl, xfvsP, xrestP, hxq, hxfvs, hxrest⟩ := hdo _ _ hq0
  refine RefE.bindSim (fun _ => rfl) (pl_step hP k1 (k1.decHL hlps hlb) (k1.top hlb)
    (ConRon.Bridge.denoteNListE_ext k1.core.ext _ _ hlpsP)) fun ru us m2 a2 _ _ ⟨k2, hu, rfl, husP⟩ => ?_
  dsimp only [ctlE.k_param_levels]
  refine RefE.bindSim (fun _ => rfl) (ic_step hP k2 hT hu
    (ConRon.Bridge.denoteN_ext hTP (k1.trans k2).core.ext) husP) fun rh hd m3 a3 _ _ h3 => ?_
  obtain ⟨k3, rfl, hhd⟩ := h3
  dsimp only [ctlE.k_intern_const]
  refine RefE.abort0 rfl fun hbig => ?_
  have k13 := k2.trans k3
  refine RefE.bindSim (fun _ => rfl) (gaf_step hP k3 hxb (ConRon.Bridge.denote_ext hxrest k13.core.ext))
    fun rf xfn m4 a4 _ _ ⟨k4, hf32, rfl, hfn⟩ => ?_
  dsimp only [ctlE.k_get_app_fn_f]
  refine RefE.bindSim (fun _ => rfl) (gaa_step hP k4 hxb (ConRon.Bridge.denote_ext hxrest (k13.trans k4).core.ext))
    fun ra args m5 a5 _ _ ⟨k5, hargs, hab, hargsP⟩ => ?_
  dsimp only [ctlE.k_get_app_args_f]
  have k05 := (k1.trans k13).trans (k4.trans k5)
  have k15 := k13.trans (k4.trans k5)
  have hlen := decHL_length m5 hargs
  have hrh : (rh.headD 0).toNat < 2 ^ 32 := by
    have : ¬ (4294967296 : Nat) ≤ (rh.headD 0).toNat := hbig
    omega
  rw [decI_beq _ _ hf32 hrh]
  by_cases hle : nP ≤ ra.tail.headD 0
  · rw [ite_eq_left (by rw [ite_eq_left hle])]
    have hle2 : nP.toNat ≤ (ra.tail.headD 0).toNat := UInt64.le_iff_toNat_le.mp hle
    refine RefE.onlySim (fun _ => rfl) (slEq_step hP k5.stage.stage (decHL_take hargs _ hle2)
      (by omega) (k05.decHL hcq hcqb) (k05.top hcqb)) fun re m6 ⟨hm6, hre⟩ => ?_
    subst hm6
    dsimp only [ctlE.k_sl_eq]
    dsimp only [ctlE.j1]
    refine RefE.guard (by decide) (fun hc => ?_) (fun hb => ?_) fun _ _ => ?_
    · grind
    · grind
    · have k16 := k15.trans (InsAt.refl k5.stage k5.abs)
      have hxfvs5 := ConRon.Bridge.denoteEList_ext k15.core.ext _ _ hxfvs
      refine RefE.bindSim (fun _ => rfl) (fdr_step hP hcr k5 (k15.decHL hxl hxlb) (k15.top hxlb)
        hxfvs5) fun r7 b1 m7 a7 _ _ ⟨k7, hb1⟩ => ?_
      dsimp only [ctlE.k_field_doms_resolve]
      refine RefE.guard (by decide) hb1.1 hb1.2 fun _ hb => ?_
      have hao' : (ra.headD 0 + nP).toNat = (ra.headD 0).toNat + nP.toNat :=
        L.toNat_add_of_lt _ _ (by have := k5.stage.stage.lt64 hab; omega)
      have halp : (ra.tail.headD 0 - nP).toNat = (ra.tail.headD 0).toNat - nP.toNat :=
        UInt64.toNat_sub_of_le _ _ hle
      have hdrop := decHL_drop nP.toNat (k7.decHL hargs hab) hle2
      rw [← hao', ← halp] at hdrop
      refine RefE.bindSim (fun _ => rfl) (iar_step hP hcr k7 hdrop (by rw [hao', halp]; have := k7.grow.iw; omega)
        (ConRon.Bridge.Inductives.denoteEList_drop (ConRon.Bridge.denoteEList_ext k7.core.ext _ _ hargsP) _))
        fun r8 b2 m8 a8 _ _ ⟨k8, hb2⟩ => ?_
      dsimp only [ctlE.k_idx_args_resolve]
      refine RefE.guard (by decide) hb2.1 hb2.2 fun _ hb' => ?_
      have k58 := k7.trans k8
      have k18 := k15.trans k58
      rcases m with _ | m'
      · rw [fsortsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
      have hxpos : ∀ i, i < nF.toNat → ∀ x, xfvsP[i]? = some x →
          ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD :=
        fun i _ x hx => ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hwsc i x hx
      have hxfvs8 := ConRon.Bridge.denoteEList_ext k18.core.ext _ _ hxfvs
      have hidx8 := ConRon.Bridge.Inductives.denoteEList_drop
        (ConRon.Bridge.denoteEList_ext k58.core.ext _ _ hargsP) nP.toNat
      have k08 := k1.trans k18
      rw [← bind_pure (checkStructFieldSortsI _ _ _ _ _ _ _ _ _)]
      refine RefE.bindE (fun _ => rfl) id (fsorts_ref hq henv hLC hLT hP.hg hP.hpw hP.het hP.hcn (m' + 1) (by omega)
        m8 a8 isP lg rs nP _ _ _ _ nF m8 xl1 (args.drop nP.toNat) xfvsP k8.stage k8.abs (IWGrow.refl _)
        (k18.decHL hxl hxlb)
        (k18.top hxlb) (k8.decHL hdrop (by rw [hao', halp]; have := k7.grow.iw; omega))
        (k8.top (by rw [hao', halp]; have := k7.grow.iw; omega)) hrs
        ⟨rsP, ConRon.Bridge.denoteL_ext hrsP k08.core.ext⟩ hnf hxfvs8 hxpos) fun v u a9 hr9 hR9 => ?_
      obtain ⟨c9, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
        ConRon.Bridge.CoreSpec.of_core henv (isP != 0) (lg != 0) (decI rs) rsP nP.toNat xl1
        (args.drop nP.toNat) xfvsP (xrestP.getAppArgs.drop nP.toNat) nF.toNat hxpos a8 a9 u k8.stage.check
        ⟨ConRon.Bridge.denoteL_ext hrsP k08.core.ext, hxfvs8, hidx8⟩ hr9
      exact RefE.ret rfl ⟨hR9.stage, k08.grow.trans hR9.grow, hR9.abs, k08.core.trans c9⟩
  · rw [ite_eq_right (by rw [ite_eq_right hle]; decide)]
    dsimp only [ctlE.j1]
    rw [ite_eq_left (Or.inr (Or.inr rfl))]
    exact RefE.twinFail (by decide) (by have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle); grind)

/-- What `check_sum_ctor` gives besides the twin's `(cvCa, sorts)` `x` (from `m`, `a`): the stage,
the growth, the constant returned unchanged, the sorts as the `IW` slice `r = [cv, o, l]`, `AbsOK`, the
twin's core step. -/
structure CtorPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

include hq henv hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctor` refines `checkSumCtor .verified`, both outcomes** (twin side: con-ron's
`checkSumCtor_spec`'s proof): the constant check (`ccv_ref`), the constructor's and the type former's
telescopes, the domains (`sds_ref`) and the tail (`ctl_ref`); the other callees (outside the verdict
closure) lifted. -/
theorem ctor_ref (hP : SumProg p) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn) (m : Nat)
    (hn : m + 1 ≤ 2 ^ 62) (m0 : Mem) (a : AState)
    (T lo ll nP nIdx rs isP lg cvCw nF cvTaw : Word) (lps : List NIdx)
    (cvC cvTa : IConstantVal) (hC : StageC dn vis fe env m0 a) (hT : H T)
    (hlps : decHL m0 lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m0)
    (hcv : DecB (fun m => decCVp m cvCw.toNat) m0 cvC)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) m0 cvTa)
    (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64) (hnf : nP.toNat + nF.toNat < 2 ^ 64)
    (hA : AbsOK m0)
    {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvCP cvTaP : ConLeche.ConstantVal}
    (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP)
    (hcvCP : Frontend.denoteCV a.store cvC = some cvCP)
    (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type) :
    RefE (VerdictCtxU p) (ctorE p (m + 1) m0 vis vis T lo ll nP nIdx rs isP lg cvCw nF cvTaw)
      (checkSumCtor V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvC nF.toNat cvTa) a
      (fun v _ a' => CtorPost dn vis fe env m0 a v.2 a') := by
  rw [ctorE.arm1, checkSumCtor_eq]
  obtain ⟨hcvx, -⟩ := rec3CVExt_of_trunc (show decCVp (truncM m0) cvCw.toNat = some cvC from hcv)
  have dcv : ∀ m', IWGrow m0 m' → decCVp m' cvCw.toNat = some cvC :=
    fun m' hg => (rec3CVExt_of_trunc (hcv.stab (OMono.decCVp _) m' hg)).2
  have dta : ∀ m', IWGrow m0 m' → decCVp m' cvTaw.toNat = some cvTa :=
    fun m' hg => (rec3CVExt_of_trunc (hta.stab (OMono.decCVp _) m' hg)).2
  refine RefE.bindE (fun _ => rfl) id (ccv_ref (n := m) (allow := 0) (allowRd := 0) (allowSorry := 0) hV hq hApd hCrk hcr hCS (by omega)
    hC.stageT (rec2DecCV_erecP (DecB.get (OMono.decCVp _) hcv) hcvx) hcvCP
    hA.cr.crOK) fun ⟨u1, m1⟩ _ a1 hr1 hP1 => ?_
  obtain ⟨c1, F₁, hF₁⟩ := ConRon.Bridge.checkConstantVal_bridge ConRon.Bridge.CoreSpec.of_core
    hC.check henv hcvCP hr1
  have k1 : InsAt dn vis fe env m0 a m1 a1 := ⟨StageC.of_T hP1.stage c1.ok, hP1.abs hA, hP1.grow, c1⟩
  have hcA := ConRon.Bridge.denoteCV_ext hcvCP c1.ext
  have hwsA : ConLeche.Expr.WScoped 0 cvCP.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  dsimp only [ctorE.k_check_constant_val]
  -- `strip_pis`
  obtain ⟨w1, hw1, hw1l, hw1d⟩ := sumTypeWord (dcv m1 k1.grow)
  rw [show rdW (m1.arr64 (tierA EREC ((cvCw + CV.type) >>> 40))) (cvCw + CV.type &&& 1099511627775) = w1
    from hw1]
  refine RefE.bindSim (fun _ => rfl) (strip_step hP k1 hw1l (L.toNat_add_of_lt _ _ hnf) hw1d
    (ConRon.Bridge.denoteCV_type hcA)) fun r2 o2 m2 a2 _ _ ⟨k2, ho2, hdo2⟩ => ?_
  dsimp only [ctorE.k_strip_pis]
  refine RefE.guardOpt (by decide) ho2.1 ho2.2 fun ⟨sl, cb⟩ hq2 _ => ?_
  obtain ⟨hcb, rfl, cbP, hcbP⟩ := hdo2 _ _ hq2
  have k02 := k1.trans k2
  -- `struct_ctor_resid_ok`
  refine RefE.bindSim (fun _ => rfl) (sr_step hP k2 hT hcb (k02.decHL hlps hlb) (k02.top hlb) (by omega) hni
    (ConRon.Bridge.denoteN_ext hTP k02.core.ext) (ConRon.Bridge.denoteNListE_ext k02.core.ext _ _ hlpsP) hcbP)
    fun r3 b3 m3 a3 _ _ ⟨k3, hb3⟩ => ?_
  dsimp only [ctorE.k_struct_ctor_resid_ok]
  refine RefE.guard (by decide) hb3.1 hb3.2 fun _ _ => ?_
  have k03 := k02.trans k3
  -- the constructor's opened telescope
  obtain ⟨w3, hw3, hw3l, hw3d⟩ := sumTypeWord (dcv m3 k03.grow)
  rw [show rdW (m3.arr64 (tierA EREC ((cvCw + CV.type) >>> 40))) (cvCw + CV.type &&& 1099511627775) = w3
    from hw3]
  refine RefE.bindSim (fun _ => rfl) (opf_step hOpf k3 hw3l hw3d
    (ConRon.Bridge.denote_ext (ConRon.Bridge.denoteCV_type hcA) (k2.trans k3).core.ext))
    fun r4 o4 m4 a4 _ _ ⟨k4, ho4, hdo4⟩ => ?_
  dsimp only [ctorE.k_open_pis_at_fvars_f]
  refine RefE.guardOpt (by decide) ho4.1 ho4.2 fun ⟨cl, cqb⟩ hq4 _ => ?_
  obtain ⟨hcl, hclb, hcqB, rfl, cfvsP, crestP, hcq, hcfvs, hcrest⟩ := hdo4 _ _ hq4
  have k04 := k03.trans k4
  -- the type former's opened telescope
  obtain ⟨w5, hw5, hw5l, hw5d⟩ := sumTypeWord (dta m4 k04.grow)
  rw [show rdW (m4.arr64 (tierA EREC ((cvTaw + CV.type) >>> 40))) (cvTaw + CV.type &&& 1099511627775) = w5
    from hw5]
  refine RefE.bindSim (fun _ => rfl) (opf_step hOpf k4 hw5l hw5d
    (ConRon.Bridge.denote_ext (ConRon.Bridge.denoteCV_type hcvTaP) k04.core.ext))
    fun r5 o5 m5 a5 _ _ ⟨k5, ho5, hdo5⟩ => ?_
  dsimp only [ctorE.k_open_pis_at_fvars_f_2]
  refine RefE.guardOpt (by decide) ho5.1 ho5.2 fun ⟨tl, tb⟩ hq5 _ => ?_
  obtain ⟨htl, htlb, _, _, tfvsP, _, htq, htfvs, _⟩ := hdo5 _ _ hq5
  -- `fvar_type_ds`
  refine RefE.bindSim (fun _ => rfl) (ftds_step hP k5 htl htlb htfvs) fun r6 tdoms m6 a6 _ _ ⟨k6, htd, htdb, hdoms⟩ => ?_
  dsimp only [ctorE.k_fvar_type_ds]
  -- `check_struct_doms_at`
  have k46 := k5.trans k6
  have hcfvs6 := ConRon.Bridge.denoteEList_ext k46.core.ext _ _ hcfvs
  have hws7 : ∀ i, i < nP.toNat → ∀ x y, cfvsP[i]? = some x →
      (tfvsP.map ConLeche.Expr.fvarTypeD)[i]? = some y →
      ConLeche.Expr.WScoped ((0 : Word).toNat + i) x.fvarTypeD ∧
        ConLeche.Expr.WScoped ((0 : Word).toNat + i) y := by
    intro i _ x y hx hy
    refine ⟨ConRon.Bridge.Inductives.openers_typeD_WScoped hcq hwsA i x hx, ?_⟩
    rw [List.getElem?_map] at hy
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact ConRon.Bridge.Inductives.openers_typeD_WScoped htq hws i z hz
  have hclb6 := k46.top hclb
  have k06 := k04.trans k46
  refine RefE.bindE (fun _ => rfl) (fun hG => hG.core) (sds_ref hq henv hP.hg hP.ad.ftd m (by omega) m6 a6 0 _ _ _ _
    nP cl tdoms cfvsP (tfvsP.map ConLeche.Expr.fvarTypeD) k6.stage k6.abs (k46.decHL hcl hclb) htd
    (k6.stage.stage.lt64 hclb6) (k6.stage.stage.lt64 htdb) hclb6 htdb
    (by simp only [UInt64.toNat_zero, Nat.zero_add]; have := k6.stage.stage.lt64 hclb6; omega)
    hcfvs6 hdoms hws7) fun ⟨u7, m7⟩ _ a7 hr7 hR7 => ?_
  obtain ⟨c7, -⟩ := ConRon.Bridge.Inductives.checkStructDomsAt_spec fe ConRon.Bridge.CoreSpec.of_core
    henv 0 cl tdoms cfvsP (tfvsP.map ConLeche.Expr.fvarTypeD) nP.toNat
    (fun i hi x y hx hy => hws7 i hi x y hx hy) a6 a7 _ k6.stage.check
    ⟨hcfvs6, hdoms⟩ hr7
  have k07 := k06.trans ⟨hR7.stage, hR7.abs, hR7.grow, c7⟩
  have k47 := k46.trans ⟨hR7.stage, hR7.abs, hR7.grow, c7⟩
  dsimp only [ctorE.k_check_struct_doms_at]
  -- the tail
  have hwsc : ConLeche.Expr.WScoped nP.toNat crestP := by
    simpa using (ConLeche.openPisAtFvars_WScoped _ _ _ hcq hwsA).2
  rcases m with _ | m'
  · rw [ctlE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  exact RefE.lastE (K := ctorE.k_check_sum_ctor_tail p) (fun _ => rfl) (fun _ => rfl) (·.toVerdictCtx)
    (ctl_ref hq henv hOpf hLC hLT hP hcr m' (by omega) m7 a7 T lo ll nP nIdx rs isP lg nF _ _ _ lps cl
      k07.stage hT (k07.decHL hlps hlb) (k07.top hlb) (k47.decHL hcl hclb) (k47.top hclb) hcqB hrs hni hnf
      k07.abs (ConRon.Bridge.denoteN_ext hTP k07.core.ext) (ConRon.Bridge.denoteNListE_ext k07.core.ext _ _ hlpsP)
      (ConRon.Bridge.denoteL_ext hrsP k07.core.ext) (ConRon.Bridge.denote_ext hcrest k47.core.ext) hwsc)
    fun v x a8 _ hR8 => ⟨hR8.stage, k07.grow.trans hR8.grow, hR8.abs, k07.core.trans hR8.core⟩

include hq henv hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctor` refines `checkSumCtor .verified`** under `StageC` (the knot's core calls;
the inputs' denotations as con-ron's `checkSumCtor_spec` asks), at the stage's own view: the
pre-block environment is the one `checkBlockCtors` passes, its `fe₁` twice. -/
@[refines ConRon.Arena.checkSumCtor]
theorem checkSumCtor_refinesC (hP : SumProg p) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn)
    (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (T lo ll nP nIdx rs isP lg cvCw nF cvTaw : Word) (lps : List NIdx)
    (cvC cvTa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀) (hT : H T)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hcv : DecB (fun m => decCVp m cvCw.toNat) s₀.mem cvC)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) s₀.mem cvTa)
    (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64) (hnf : nP.toNat + nF.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem)
    {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvCP cvTaP : ConLeche.ConstantVal}
    (hTP : denoteN a₀.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    (hrsP : denoteL a₀.store.ls (decI rs) = some rsP)
    (hcvCP : Frontend.denoteCV a₀.store cvC = some cvCP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_sum_ctor"
      [vis, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvCw, nF, cvTaw]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (checkSumCtor V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvC nF.toNat cvTa) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumCtor V fe fe (decI T) lps
        nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvC nF.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (ctorE_spec p hP hV (n + 1) s₀ vis vis T lo ll nP nIdx rs isP lg cvCw nF cvTaw)
      (ctor_ref hq henv hOpf hLC hLT hApd hCrk hP hV hcr hCS n hn _ a₀ T lo ll nP nIdx rs isP lg cvCw nF
        cvTaw lps cvC cvTa hC hT hlps hlb hcv hta hrs hni hnf hA hTP hlpsP hrsP hcvCP hcvTaP hws))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
      obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
