module

import ConAgua.Verdict.PosTopE2
import ConAgua.Verdict.PosTopE4
import ConAgua.Arena.IndT.Install6
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.CheckStructFieldSortsISucc
import ConAgua.Arena.IndT.PosFields
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConLeche.Verify.Cached.BlockRunC
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.PosWalks
public import ConAgua.Verdict.PosTopE1
public import ConAgua.Arena.IndT.PassCS
public import ConAgua.Arena.IndT.PosMc
public import ConAgua.Arena.IndT.PosFkc
import all ConAgua.Arena.IndInstall
import ConAgua.Arena.IndT.PosAll
import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.IndInstallSpec.DomsW

@[expose] public section

/-!
# `check_block_positivity` (lane `ronsync2`, stage 3)

`check_block_positivity`'s unified model `cbpE`, its refinement for both outcomes `cbp_ref` under
`BkSt` (its twin side as con-ron's `checkBlockPositivity_spec`): the walk's context by
`block_nest_ctx`'s contract (`BncRefS`), the members' constructors (`block_shape_member_ctors`,
`mctorsW_dec`, with their slices' bounds from `ShapeSl`), `nest_uniform` (`nu_ref`), the fresh
state (L only), `nest_root` (`nrt_ref`, the walk by `nbRef_all`), `pin_word(53)`, `lvl_eq_true`
(`lvlEqC_simC`), the fields' universes (`iaa_ref`). `posRefS_of`: `PosRefS` through the call;
`checkBlockPositivity_refinesC` its ok half as a triple.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dCtors dOutss dState)

noncomputable section

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`check_block_positivity`'s unified model**: the callees outside the verdict closure lifted,
`nest_uniform` and `nest_root` through their unified models, `check_abs_ctor_sorts_all` through its
run (its ok half needs the call's frame, `PosMR.ofClosed`). -/
l_model cbpE_spec (p : Prog) (hP : PosBlkProg p)
  fns [hP.cbp ↦ cbpE list]
  specs [callW_spec p n "block_nest_ctx", nuE_spec p hP.nu hP.nuCs hP.nuP n,
    callW_spec p n "check_block_positivity_init", nrtE_spec p hP.rs n, callW_spec p n "pin_word",
    callW_spec p n "lvl_eq_true", callW_spec p n "check_block_positivity_nfs"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_block_positivity` gives besides the twin's outputs and walk state `x` (from `m`,
`a`): the stage, the growth, the walk memos, `AbsOK`, the root frame's kinds and the walk state's
layout. -/
structure CbpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (m' : Mem)
    (x : List (List (List NestFieldKind × EIdx)) × NestState) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  pos : PosMR m'
  abs : AbsOK m'
  kinds : PSlR decKSS (ConRon.Arena.nestOutKinds x.1) (r.headD 0) (r.tail.headD 0) m'
  ns : NSB m' (r.tail.tail.headD 0) x.2

section sim
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)

set_option maxRecDepth 20000 in
include hq hIlpf henv hOpf hLC hLT hApd in
/-- **`check_block_positivity` refines `checkBlockPositivity`, both outcomes** under `BkSt`
(con-ron's `checkBlockPositivity_spec`'s preconditions), its `block_nest_ctx` call by its contract
(`BncRefS`): the members' constructors (`mctorsW_dec`, with their bounds from `ShapeSl`),
`nest_uniform` (`nu_ref`), the fresh state (L only), `nest_root` (`nrt_ref`, the walk's refinements
by `nbRef_all`), `pin_word(53)`, `lvl_eq_true`, the fields' universes (`iaa_ref`). -/
theorem cbp_ref (hP : PosBlkProg p) (hMc : McLook p) (hF : FtProg p) (hFk : FkcProg p) (hWt : WhnfTopE p)
    (hbnc : BncRefS (VerdictCtxU p) p dn) (hk : ∀ f ∈ posKeepCalleesC, AbsKeep p f)
    (hPos : ∀ {k : Nat} {vs : List Word} {m m' : Mem} {r : List Word},
      callW p k "check_abs_ctor_sorts_all" vs m = some (r, m') → PosMR m → PosMR m') (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp : Word} {bs : BlockShape} {bsP : ConLeche.BlockShape}
    (hB : BkSt dn vis fe env m a) (hqd : DecB (fun m => decBS m pp.toNat) m bs) (hsl : ShapeSl m pp)
    (hdP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hT : ∀ cv ∈ bsP.formers, ConLeche.Expr.WScoped 0 cv.type)
    (hct : ∀ cs ∈ bsP.memberCtors, ∀ c ∈ cs, ConLeche.Expr.WScoped 0 c.1.type) :
    RefE (VerdictCtxU p) (cbpE p n m vis pp) (ConRon.Arena.checkBlockPositivity V fe bs) a
      (fun v x a' => CbpPost dn vis fe env m v.1 v.2 x a') := by
  rcases n with _ | n
  · rw [cbpE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cbpE.eq_2]
  unfold ConRon.Arena.checkBlockPositivity
  have hcssP := ConRon.Bridge.Inductives.memberCtors_denote hdP
  have hcl : ∀ cs ∈ bsP.memberCtors, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => ConLeche.Cached.ws0_hasFvar (hct cs hcs c hc)
  -- the walk's context
  refine RefE.bindLift (fun _ => cbpE.k_block_nest_ctx.none ..) fun r1 m1 h1 => ?_
  have hb := hbnc n (by omega) vis fe env m a pp bs bsP hB henv hqd hsl hdP hT
  rw [callE_of_callW h1] at hb
  obtain ⟨⟨c, holes⟩, a1, hrun1, hB1, hg1, hc1, hU1, hho1, hhob1, hhi1, hpn1⟩ := hb
  obtain ⟨c1, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, -, hnh, -⟩, -⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec fe henv bs bsP hT a a1 (c, holes) hB.c.check hdP hrun1
  dsimp only at hctx hholes hhw hpar hnh
  refine ⟨_, _, hrun1, ?_⟩
  rw [cbpE.k_block_nest_ctx.arm1]
  -- the members' constructors (L only)
  rcases hmc : callE p n "block_shape_member_ctors" [pp] m1 with e | ⟨r2, m2⟩
  · rw [cbpE.k_block_shape_member_ctors.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) hmc
  rw [cbpE.k_block_shape_member_ctors.arm1]
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockShapeMemberCtors_spec p hMc.ha hMc.hc hMc.hp n _ pp) (callW_of_callE hmc)
  have hS1 := hB1.c.stage
  have hq1 := hqd.grow (decBS_mono _) hg1
  have hsl1 := hsl.grow' hqd hg1
  obtain ⟨hr2, hcss2, hg2, hfr2, hroom2⟩ := mctorsW_dec hW2 hS1.iw.iwSize hS1.iw.ctl
    (ShapeSl.membersB hq1 hsl1) hsl1
  rw [hr2]
  simp only [List.headD_cons, List.tail_cons]
  generalize hcaO : rdW (m1.arr64 CTL) 200 = caO at hcss2
  generalize hcaL : (UInt64.ofNat bs.k : Word) = caL at hcss2
  have hS2 : StageR vis fe s2.mem a1 := stage_frame_iw hS1 hfr2 hroom2
  have hA2 : AbsOK s2.mem := AFr.of_frame hfr2 (by decide) (by decide) hB1.abs
  have hP2 : PosMR s2.mem := hB1.ind.stage.pos.fr (MFr.of_iw hfr2)
  have hC2 : StageC dn vis fe env s2.mem a1 := hB1.c.of_pstep hS2 hA2 (PStep.refl hB1.c.check.state)
  have hU2 := hU1.grow hg2
  obtain ⟨hlen, hcb2, hcss2'⟩ := pos3_cssAt hcss2
  -- `nest_uniform`
  have hcss1P := ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP
  have hPc : ∀ cs ∈ bs.memberCtors, ∀ x ∈ cs, ∃ cvP, Frontend.denoteCV a1.store x.1 = some cvP := by
    intro cs hcs x hx
    obtain ⟨y, hy⟩ := L.Arena.mapM_some_mem _ _ hcss1P cs hcs
    obtain ⟨z, hz⟩ := L.Arena.mapM_some_mem _ _ hy x hx
    simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hz
    obtain ⟨cvP, hcvP', -⟩ := hz
    exact ⟨cvP, hcvP'⟩
  have hnu := nu_ref dn fe vis (r1.headD 0) c hhi1
    (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store)
    (fun cvv => ∃ cvP, Frontend.denoteCV a1.store cvv = some cvP)
    (fun _ a' _ cvv hJ hPx _ _ m1' a1' _ b hpd hrun hS1' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨cvP, hcvP'⟩ := hPx
      obtain ⟨-, -, hty⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP'
      obtain ⟨hcn, -⟩ := ConRon.Bridge.Inductives.dCtx_fields
        (ConRon.Bridge.Inductives.dCtx_ext _ hxm _ _ hctx)
      obtain ⟨p1', -⟩ := ConRon.Bridge.Inductives.piDomsOcc_spec c.names ctxP.names c.nP (c.hiAt 0) c.nP
        cvv.type cvP.type a' a1' b hCm.check.state ⟨hcn, ConRon.Bridge.denote_ext hty hxm⟩ hrun
      exact IlpRd.realC hIlpf (hCm.of_pstep hS1' (pdoW_afr _ _ _ _ _ _ _ _ _ _ hpd hAm) p1'))
    (fun _ _ _ a' a'' _ cvv _ _ hJ hPx _ hrun hS' hA' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨cvP, hcvP'⟩ := hPx
      obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.nestUniformOk_spec (env := env) (fe := fe)
        env.find? c ctxP cvv cvP a' a'' _ hCm.check
        ⟨ConRon.Bridge.Inductives.dCtx_ext _ hxm _ _ hctx, ConRon.Bridge.denoteCV_ext hcvP' hxm⟩ hrun
      have hAm' := hA' nuAfr hAm
      exact ⟨hCm.of_cstep hS' hAm' c3, hAm', hxm.trans c3.ext⟩)
    n hS2 ⟨hC2, hA2, ConRon.Arena.Ext.refl _⟩ hPc hU2 hlen hcss2' hP2
  refine RefE.bindE (fun _ => cbpE.k_nest_uniform.none ..) (fun hG => hG.nv) hnu
    fun ⟨r3, m3⟩ _ a3 hrun3 ⟨hS3, hg3, hP3, hJ3⟩ => ?_
  dsimp only at hS3 hg3 hP3 hJ3
  rw [cbpE.k_nest_uniform.arm1]
  obtain ⟨c3, -, -, -⟩ := ConRon.Bridge.Inductives.nestUniform_spec (env := env) (fe := fe)
    env.find? c ctxP bs.memberCtors bsP.memberCtors a1 _ _ hB1.c.check
    ⟨hctx, hcss1P⟩ hrun3
  have hA3 : AbsOK m3 := hJ3.2.1
  have hC3 := hC2.of_cstep hS3 hA3 c3
  -- the empty state (L only)
  refine RefE.onlySim (fun _ => cbpE.k_check_block_positivity_init.none ..) (fun _ _ h => h) fun r4 m4 h4 => ?_
  rw [cbpE.k_check_block_positivity_init.arm1]
  obtain ⟨hS4, hg4, hf4, hns4⟩ := pos3_init hP h4 hS3
  have hA4 : AbsOK m4 := hk _ (by simp [posKeepCalleesC]) _ _ _ _ _ h4 hA3
  have hC4 := hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state)
  have hg24 := hg3.trans hg4
  -- the root frame
  have hx13 := c1.ext.trans c3.ext
  have hcssP3 := ConRon.Bridge.Inductives.dCtors_ext.list hx13 _ _ hcssP
  have hctx3 := ConRon.Bridge.Inductives.dCtx_ext _ c3.ext _ _ hctx
  have hholes3 := ConRon.Bridge.denoteEList_ext c3.ext _ _ hholes
  have hlenP : ctxP.names.length ≤ holesP.length := by
    rw [ConLeche.nestHoles_length hnh]; exact Nat.le_refl _
  have hg14 := hg2.trans hg24
  have hnrt := nrt_ref hP.rs dn vis fe henv (nbRef_all hP.rs.nb hq hIlpf hLC hF hFk henv)
    (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0) c holes hctxOk (fun y hy => (hhw y hy).1) hlenP hpar
    n (by omega) m4 a3 caO caL (r4.headD 0) 0 0 bs.memberCtors {} [] bsP.memberCtors {} [] hC4 (hU1.grow hg14) hhi1
    hpn1 (by rw [L.Ind.decHL_grow hg14 hhob1]; exact hho1) (Nat.le_trans hhob1 hg14.iw) hlen
    (Nat.le_trans hcb2 hg24.iw) (hcss2'.grow hg24) hns4 (by simp [RootOutsB, DecB, decPL]) (by simp)
    (hP3.fr hf4) hA4 hctx3 hholes3 hcssP3 (by simp [dState]) rfl hcl
  refine RefE.bindE (fun _ => cbpE.k_nest_root.none ..) (fun hG => (⟨hG.nv, hG.core, hWt⟩ : NbG p)) hnrt
    fun ⟨r5, m5⟩ ⟨outs, ns⟩ a5 hrun5 ⟨hC5, hg5, hO5, hOb5, hns5, hP5, hA5, c5⟩ => ?_
  dsimp only at hC5 hg5 hO5 hOb5 hns5 hP5 hA5
  rw [cbpE.k_nest_root.arm1]
  obtain ⟨-, ⟨outsP, nsP⟩, ⟨houts, -, hwN⟩, -⟩ := ConRon.Bridge.Inductives.nestRoot_spec coreSpecV henv
    hctxOk holes holesP (fun y hy => (hhw y hy).1) hlenP hpar bs.memberCtors bsP.memberCtors {} {} [] [] hcl
    _ a5 (outs, ns) hC4.check ⟨hctx3, hholes3, hcssP3, by simp [dState], rfl⟩ hrun5
  simp only [List.nil_append] at houts
  dsimp only at houts hwN
  have hS5 := hC5.stage
  have hg15 := hg14.trans hg5
  -- `pin_word(53)`
  refine RefE.bindLift (fun _ => cbpE.k_pin_word.none ..) fun r6 m6 h6 => ?_
  obtain ⟨s6, rfl, -, hm6, hz6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (pinWord_specV p hP.pin n _ 53) h6
  simp only at hm6 hz6
  rw [hm6]
  obtain ⟨hrunz, hzH⟩ := pinZero_stage hS5 hz6
  obtain ⟨-, hz⟩ := ConRon.Bridge.Inductives.zeroLevel_run hC5.check.pins hrunz
  refine ⟨_, _, hrunz, ?_⟩
  rw [cbpE.k_pin_word.arm1]
  -- `lvl_eq_true`
  obtain ⟨huH, hue⟩ := installCtxWord9 (hc1.grow (decCtx_mono _) hg15) hS5.iw.iwSize
  refine RefE.bindLift (fun _ => cbpE.k_lvl_eq_true.none ..) fun r7 m7 h7 => ?_
  obtain ⟨s7, rfl, -, he7⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (eqTrue_specC p hP.eqt (realCall p) (realCall_spec p) n _ _ _) h7
  simp only at he7
  rcases n with _ | n
  · simp [eqTrueC] at he7
  rw [eqTrueC_succ] at he7
  rcases hs7 : realCall p n "lvl_eq_c" [rdW (m5.arr64 IW) (r1.headD 0 + 9), r6.headD 0] m5 with _ | ⟨r7', m7'⟩ <;>
    rw [hs7] at he7
  · simp [eqTrueK] at he7
  rw [eqTrueK_some] at he7
  obtain ⟨hr7, hm7⟩ := Prod.mk.inj (Option.some.inj he7)
  subst hm7
  obtain ⟨namesP, lpsP, paramsP, sortP, formersP, hceq, -, -, -, hsort, -, -⟩ :=
    ConRon.Bridge.Inductives.dCtx_inv hctx
  have hfind : ctxP.find? = env.find? := by rw [hceq]
  have hx15 := c3.ext.trans c5.ext
  have hsort' : ConRon.Arena.denoteL a5.store.ls (decI (rdW (m5.arr64 IW) (r1.headD 0 + 9))) =
      some ctxP.sort := by
    rw [hue, hceq]; exact ConRon.Bridge.denoteL_ext hsort hx15
  obtain ⟨y, a7, hrun7, hC7, hg7, hy7, hA7, -⟩ :=
    lvlEqC_simC p hq.closed hLC n hC5 hA5 _ _ huH hzH _ _ hsort' hz r7' s7.mem hs7
  have hS7 := hC7.stage
  have hP7 : PosMR s7.mem := hP5.ofCore hq.closed (by decide) hs7
  obtain ⟨c6, -⟩ := ConRon.Bridge.Inductives.lvlEq?_crun hC5.check hsort' hz hrun7
  have hb7 : (r7.headD 0 != 0) = (y == some true) := by
    rw [← hr7]
    simp only [decLvlEq] at hy7
    rcases y with _ | _ | _ <;> simp_all
  rw [hue] at hrun7
  refine ⟨_, _, hrun7, ?_⟩
  rw [cbpE.k_lvl_eq_true.arm1]
  -- the fields' universes at the holes
  have hg17 := hg15.trans hg7
  have hOb7 : (r5.headD 0).toNat + (r5.tail.headD 0).toNat ≤ iwTop s7.mem := Nat.le_trans hOb5 hg7.iw
  have hx17 := hx15.trans c6.ext
  have hiaa := iaa_ref hq henv hOpf hLC hLT hApd hP.abs (r1.headD 0) (r7.headD 0) c
    (y == some true) hb7 hhi1 (n + 1) (by omega) s7.mem a7 caO caL (r5.headD 0) (r5.tail.headD 0) bs.memberCtors
    outs bsP.memberCtors outsP hC7 hA7 (hc1.grow (decCtx_mono _) hg17)
    ((pos3_cns hcss2).grow decCNS_mono (hg24.trans (hg5.trans hg7)))
    ⟨hO5.grow hg7, Or.inr hOb7⟩ (by rw [hfind]; exact ConRon.Bridge.Inductives.dCtx_ext _ hx17 _ _ hctx)
    (ConRon.Bridge.Inductives.dCtors_ext.list (c1.ext.trans hx17) _ _ hcssP)
    (ConRon.Bridge.Inductives.dOutss_ext c6.ext _ _ houts) hwN
  have hsI := iaaE_spec p hP.abs.one hP.abs.abs hP.abs.all (n + 1) ⟨s7.mem, Locals.init []⟩ vis (r1.headD 0)
    (r7.headD 0) caO caL (r5.headD 0) (r5.tail.headD 0)
  refine RefE.bindRun (s₀ := ⟨s7.mem, Locals.init []⟩) (fun _ => cbpE.k_check_abs_ctor_sorts_all.none ..) hsI
    (fun hG => hG.nv) (fun hG => hG.toVerdictCtx) hiaa fun r8 s8 u8 a8 h8 _ hrun8 ⟨hC8, hg8, hA8, _⟩ => ?_
  rw [cbpE.k_check_abs_ctor_sorts_all.arm1]
  have hP8 : PosMR s8.mem := hPos (callW_of_callE h8) hP7
  refine RefE.ret rfl ⟨hC8, (hg1.trans hg17).trans hg8, hP8, hA8, ⟨?_, ?_⟩, ?_⟩
  · exact pos3_kinds (hO5.grow (hg7.trans hg8))
  · exact Nat.le_trans hOb7 hg8.iw
  · simpa using hns5.grow (hg7.trans hg8) (Nat.lt_of_le_of_lt hS5.iw.iw hS5.iw.iwSize)

include hq hIlpf henv hOpf hLC hLT hApd in
/-- **`check_block_positivity` refines `checkBlockPositivity`** under `BkSt` (the ok half of
`cbp_ref`; con-ron's `checkBlockPositivity_spec`'s preconditions). -/
@[refines ConRon.Arena.checkBlockPositivity]
theorem checkBlockPositivity_refinesC (hP : PosBlkProg p) (hMc : McLook p) (hF : FtProg p) (hFk : FkcProg p)
    (hWt : WhnfTopE p) (hbnc : BncRefS (VerdictCtxU p) p dn) (hk : ∀ f ∈ posKeepCalleesC, AbsKeep p f)
    (hPos : ∀ {k : Nat} {vs : List Word} {m m' : Mem} {r : List Word},
      callW p k "check_abs_ctor_sorts_all" vs m = some (r, m') → PosMR m → PosMR m')
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (pp : Word) (bs : BlockShape)
    {bsP : ConLeche.BlockShape} (hB : BkSt dn vis fe env s₀.mem a₀)
    (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsl : ShapeSl s₀.mem pp)
    (hdP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hT : ∀ cv ∈ bsP.formers, ConLeche.Expr.WScoped 0 cv.type)
    (hct : ∀ cs ∈ bsP.memberCtors, ∀ c ∈ cs, ConLeche.Expr.WScoped 0 c.1.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_positivity" [vis, pp]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockPositivity V fe bs) a₀ ∧
      CbpPost dn vis fe env s₀.mem r s'.mem (AM.res (ConRon.Arena.checkBlockPositivity V fe bs) a₀)
        (AM.st (ConRon.Arena.checkBlockPositivity V fe bs) a₀); ⊤⦄ := by
  refine triple_post (RefE.triple (cbpE_spec p hP n s₀ vis pp)
    (cbp_ref hq hIlpf henv hOpf hLC hLT hApd hP hMc hF hFk hWt hbnc hk hPos n hn hB hqd hsl hdP hT hct)) ?_
  rintro r s' ⟨hl, x, a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact hR

end sim

/-- **`check_block_positivity`'s contract** (`PosRefS`): `cbp_ref` through the call, its
`block_nest_ctx` by `BncRefS`; the memos by `IndMemos.ofCall`. -/
theorem posRefS_of {p : Prog} {dn : NIdx → Option ConLeche.Name} (hq : KnotStageProg p) (hIlpf : IlpfF p)
    (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)
    (hP : PosBlkProg p) (hMc : McLook p) (hF : FtProg p) (hFk : FkcProg p) (hWt : WhnfTopE p)
    (hbnc : BncRefS (VerdictCtxU p) p dn) (hk : ∀ f ∈ posKeepCalleesC, AbsKeep p f)
    (hPos : ∀ {k : Nat} {vs : List Word} {m m' : Mem} {r : List Word},
      callW p k "check_abs_ctor_sorts_all" vs m = some (r, m') → PosMR m → PosMR m')
    (hK : WmKeep p "check_block_positivity") : PosRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a pp bs bsP hB henv hqd hsl hdP hT hct
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (cbpE_spec p hP n _ vis pp) (fun hG => hG.nv)
    (cbp_ref hq hIlpf henv hOpf hLC hLT hApd hP hMc hF hFk hWt hbnc hk hPos n hn hB hqd hsl hdP hT hct)
  refine RefE.callOk h fun ⟨r, m'⟩ x a' hc hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  exact ⟨⟨hR.stage, IndMemos.ofCall hK (callW_of_callE hc) hB.ind hR.pos hR.abs, hR.abs⟩, hR.grow, hR.kinds,
    hR.ns⟩

end L.Ind

end
