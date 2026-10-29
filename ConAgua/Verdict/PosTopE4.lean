import ConAgua.L.ModelGen
import ConAgua.Verdict.PosTopE1
import ConAgua.Arena.IndPosSpec.UnW2
import ConAgua.Arena.IndT.PosAll
/-!
# `nest_root`'s and `nest_seeds`' refinements (lane `verdicts-b`, helper `ia2`, fork `top`)

One refinement for both outcomes each: `nest_root`'s (`nrt_ref`, on its unified model `nrtE`) and
`nest_seeds`' (`nsd_ref`, on its unified model `nsdE`, defined here): the walk's
callees `nest_ctors`, `nest_cont_key` by the block's refinements (`nbRef_all`, both halves through
the run; the errors under `NbG`), `nest_inst_type` by `nit_ref`, the others claim nothing
(`nvFns`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dCtors dOut dOutss kindOf)

set_option experimental.vcgen true

noncomputable section

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- What `nest_root` gives besides the twin's outputs and state `x` (from `m`, `a`): the stage, the
growth, the outputs' slice at `r`, the state at `r[2]`, the frames, the core step. -/
structure NrtPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem)
    (a : AState) (r : List Word) (m' : Mem)
    (x : List (List (List NestFieldKind × EIdx)) × NestState) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  outs : RootOutsB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1
  outsb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
  ns : NSB m' (r.tail.tail.headD 0) x.2
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

section root
variable {p : Prog} (L : RsLook p)
  (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (ctx hO hL : Word) (c : NestCtx) (holes : List EIdx)
  {ctxP : ConLeche.NestCtx} (hc : ConLeche.NestCtxOk ctxP) {holesP : List ConLeche.Expr}
  (hholes : ∀ x ∈ holesP, ConLeche.Expr.WScoped (ctxP.hiAt 0) x)
  (hlen : ctxP.names.length ≤ holesP.length)
  (hpar : ∀ x ∈ ctxP.params, ConLeche.Expr.WScoped (ctxP.hiAt 0) x)

include L hq hIlpf hLC henv hc hholes hlen hpar in
/-- **`nest_root` refines `nestRoot`, both outcomes** (under `StageC`; `nest_ctors` through its
run, both halves from `nbRef_all`). -/
theorem nrt_ref : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (cO cL ns oO oL : Word)
    (css : List (List (IConstantVal × Nat))) (NS : NestState) (outss : List (List (List NestFieldKind × EIdx)))
    (cssP : List (List (ConLeche.ConstantVal × Nat))) (nsP : ConLeche.NestState)
    (outssP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))),
    StageC dn vis fe env m a → UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → c.params.length + c.names.length < 2 ^ 64 →
    decHL m hO.toNat hL.toNat = some holes → hO.toNat + hL.toNat ≤ iwTop m →
    cL.toNat = css.length → cO.toNat + css.length ≤ iwTop m → CssAt m cO.toNat css → NSB m ns NS →
    RootOutsB m oO.toNat oL.toNat outss → oO.toNat + oL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    dCtx a.store env.find? c = some ctxP → Frontend.denoteEList a.store holes = some holesP →
    css.mapM (dCtors a.store) = some cssP → dState a.store NS = some nsP → dOutss a.store outss = some outssP →
    (∀ cs ∈ cssP, ∀ x ∈ cs, x.1.type.hasFvar = false) →
    RefE (NbG p) (nrtE p n m vis ctx hO hL cO cL ns oO oL) (nestRoot V fe c holes css NS outss) a
      (fun v x a' => NrtPost dn vis fe env m a v.1 v.2 x a')
  | 0, _, m, a, cO, cL, ns, oO, oL, css, NS, outss, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _ => by
    rw [nrtE.eq_1]; exact RefE.of_cls0 rfl
  | n + 1, hn, m, a, cO, cL, ns, oO, oL, css, NS, outss, cssP, nsP, outssP, hC, hU, hhi, hpn, hho, hhob,
      hcl, hcb, hcss, hns, hout, houtb, hP, hA, hctx, hholesP, hcssP, hnsP, houtsP, hcF => by
    have hS := hC.stage
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases h0 : cL = 0
    · rw [nrtE.arm1 p n m vis ctx hO hL cO cL ns oO oL h0]
      subst h0
      have : css = [] := List.eq_nil_of_length_eq_zero (by simpa using hcl.symm)
      subst this
      exact RefE.ret (y := (outss, NS)) (by rw [ConRon.Arena.nestRoot.eq_def]; rfl)
        ⟨hC, IWGrow.refl _, by simpa using hout, by simpa using houtb, by simpa using hns, hP, hA,
          ConRon.Bridge.CoreStep.refl hC.check⟩
    rw [nrtE.arm2 p n m vis ctx hO hL cO cL ns oO oL h0]
    obtain ⟨cs, css', rfl⟩ : ∃ x css', css = x :: css' := by
      cases css with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hcl)) h0
      | cons x css' => exact ⟨x, css', rfl⟩
    simp only [List.length_cons] at hcl hcb
    -- the twin's member constructors
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hcssP
    rcases hc1 : dCtors a.store cs with _ | csP; · rw [hc1] at hcssP; simp at hcssP
    cases hcs1 : css'.mapM (dCtors a.store) with
    | none => rw [hc1, hcs1] at hcssP; simp at hcssP
    | some cssP' =>
    simp only [hc1, hcs1, Option.bind_some, Option.some.injEq] at hcssP
    subst hcssP
    obtain ⟨hcn, -, -, hpar', hlv, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
    have hhiP : c.hiAt 0 = ctxP.hiAt 0 := ConRon.Bridge.Inductives.hiAt_eq hctx 0
    obtain ⟨hdr, cO', cL', h0w, h1w, h2w, -, hhdr, hcl', hcb', hcsAt⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0w hcl' hcb' hcsAt
    rw [hcl'] at hcb'
    have rd0 : rdW (m.arr64 IW) cO = hdr := by simp [rdW, h0w]
    have rd1 : rdW (m.arr64 IW) hdr = cO' := by simp [rdW, h1w]
    have hdr1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by simp; omega)
    have rd2 : rdW (m.arr64 IW) (hdr + 1) = cL' := by simp [rdW, hdr1, h2w]
    -- the context's words
    obtain ⟨hn0, -, hpa0, -, -, hus0, husd0, -, -, -⟩ := ctx_fields hU.dec hU.inn htop
    have hne0 := ctx_names_end hU.dec hU.inn hU.sl htop
    have hpe0 := ctx_params_end hU.dec hU.inn hU.sl htop
    have hW : WCtx dn vis fe m ctx 0 0 c [] := ⟨hU, by simp [HSl, HolesAt], by simpa using hhi⟩
    have hhi0 : (nhiW m ctx 0).toNat = c.hiAt 0 := by simpa using hW.hi htop
    have hpl : (rdW (m.arr64 IW) (ctx + 8)).toNat = c.params.length := (pos2_hslice_get hpa0).1.symm
    have hCc : CtorsCtx m (rdW (m.arr64 IW) (ctx + 10)) (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8))
        (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) hO hL c.params c.names holes :=
      ⟨hus0, by show decHL (truncM m) _ _ = _; rw [decHL_truncM hpe0]; exact hpa0, hpe0, hn0, hne0,
        by rw [hpl]; exact hpn, hho, hhob⟩
    have hpre : CtorsPre a.store (decI (rdW (m.arr64 IW) (ctx + 10))) c.params c.names holes (nhiW m ctx 0).toNat
        (ctxP.lps.map .param) ctxP.params ctxP.names holesP :=
      ⟨by rw [husd0]; exact hlv, hpar', hcn, hholesP, by rw [hhi0, hhiP]; exact hpar,
        by rw [hhi0, hhiP]; exact hholes, hlen⟩
    rw [ConRon.Arena.nestRoot]
    -- `nest_ctx_hi_at`, `nest_ctors`
    rw [rd0, rd1, rd2]
    have hRef := (nbRef_all (dn := dn) (vis := vis) (fe := fe) L.nb hq hIlpf hLC henv n (by omega)).ctors m a ctx 1
      0 0 0 (nhiW m ctx 0) _ _ _ _ _ hO hL cO' cL' ns 0 0 c [] c.params c.names holes cs NS [] ctxP [] _ _ _ _ csP
      nsP [] hC hW hCc hcl' hcb' hcsAt hns (by simpa using OutsB.nil m 0) (by simp) hP hA hc hctx rfl hpre hc1
      (hcF csP List.mem_cons_self) hnsP rfl
    rcases h2 : callE p n "nest_ctors" [vis, ctx, 1, 0, 0, 0, nhiW m ctx 0, rdW (m.arr64 IW) (ctx + 10),
        rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8), rdW (m.arr64 IW) ctx,
        rdW (m.arr64 IW) (ctx + 1), hO, hL, cO', cL', ns, 0, 0] m with e2 | ⟨r1', m1⟩
    · rw [nrtE.k_nest_ctors.none]
      refine RefE.bind_left fun hG => ?_
      have hE := RefE.run_err (nctE_spec p L.nb.pctors n ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        True.intro hG hRef h2
      rw [hhi0, husd0] at hE
      simpa using hE
    rw [nrtE.k_nest_ctors.arm1]
    obtain ⟨s2, hs2, -, x1, a1, hrun1, hR1⟩ := RefE.run_ok
      (nctE_spec p L.nb.pctors n ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hRef h2
    rw [hs2] at hR1; dsimp only at hR1
    obtain ⟨hC1, hg1, hO1, hOb1, hns1, hP1, hA1, c1⟩ := hR1
    have hS1 := hC1.stage
    rw [hhi0, husd0] at hrun1
    have hrun1' : (nestCtors V fe c true 0 [] (c.hiAt 0) c.lvls c.params c.names holes cs NS []).run a =
        .ok (x1, a1) := by simpa using hrun1
    have hrun1P : (nestCtors V fe c true 0 [] (ctxP.hiAt 0) c.lvls c.params c.names holes cs NS []) a =
        .ok (x1, a1) := by rw [← hhiP]; exact hrun1'
    obtain ⟨-, v1, ⟨hv1, hns1P, -⟩, -⟩ := ConRon.Bridge.Inductives.nestCtors_spec coreSpecV henv true 0
      (fun crestP => ConLeche.nestPos (ConLeche.fueledOpsM V) env ctxP (ConLeche.whnfWalkFuel crestP))
      (fun _ => by simp) (fun crestP => by simpa using ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc _)
      [] [] (ctxP.hiAt 0) c.lvls _ c.params ctxP.params c.names ctxP.names holes holesP
      hpar hholes hlen cs csP NS nsP [] [] (hcF csP List.mem_cons_self) a a1 x1 hC.check
      ⟨hctx, rfl, hlv, hpar', hcn, hholesP, hc1, hnsP, rfl⟩ hrun1P
    simp only [List.nil_append] at hv1
    refine RefE.bind_right hrun1' ?_
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
    -- its record, appended
    rcases hr2 : posRecW m1 [r1'.headD 0, r1'.tail.headD 0] with _ | ⟨q, m2⟩
    · rw [liftE_none, nrtE.k_rec2.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, nrtE.k_rec2.arm1]
    obtain ⟨hS2, hg2, hq2, ht2, hget2⟩ := posRecW_stage hr2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    have hrec := pos2_outs_rec (q := q) (by omega) hget2 (hO1.grow hg2)
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
    rcases hsn : snocW n m2 oO oL q with _ | ⟨ro, m3⟩
    · rw [liftE_none, nrtE.k_sl_snoc.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, nrtE.k_sl_snoc.arm1]
    have hg12 := hg1.trans hg2
    obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hsn hS2 (by have := hg12.iw; omega)
    have hout3 : RootOutsB m3 (ro.headD 0).toNat (ro.tail.headD 0).toNat (outss ++ [x1.1]) := by
      rw [h30, h31]
      exact pos2_decB_snoc pos2_rootOuts_mono (hout.grow hg12) hg3 (by omega) hw3 hx3
        (DecB.grow (pos2_rootOuts_mono _) hg3 hrec)
    have hg13 := hg12.trans hg3
    have hcO1 : (cO + 1).toNat = cO.toNat + 1 := word_add_toNat (by simp; omega)
    have hcL1 : (cL - 1).toNat = css'.length := by rw [pos2_word_pred h0]; omega
    have hA3 : AbsOK m3 := snocW_afr hsn (posRecW_afr hr2 hA1)
    have hC3 : StageC dn vis fe env m3 a1 := hC1.of_pstep hS3 hA3 (PStep.refl hC1.check.state)
    -- the rest of the members
    have ih := nrt_ref n (by omega) m3 a1 (cO + 1) (cL - 1)
      (r1'.tail.tail.headD 0) (ro.headD 0) (ro.tail.headD 0) css' x1.2 (outss ++ [x1.1]) cssP' v1.2
      (outssP ++ [v1.1]) hC3 (hU.grow hg13) hhi hpn
      (by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by omega)]; exact hho)
      (by have := hg13.iw; omega) hcL1 (by rw [hcO1]; have := hg13.iw; omega)
      (by rw [hcO1]; exact (hcss.grow hg13).tail)
      ((hns1.grow hg2 htop1).grow hg3 htop2) hout3 (by rw [h30, h31]; omega)
      ((hP1.fr (posRecW_mfr hr2)).fr (snocW_mfr hsn)) hA3
      (dCtx_ext _ c1.ext _ _ hctx) (ConRon.Bridge.denoteEList_ext c1.ext _ _ hholesP)
      (ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcs1) hns1P
      (ConRon.Bridge.Inductives.mapM_option_append (ConRon.Bridge.Inductives.dOutss_ext c1.ext _ _ houtsP)
        (by simp [hv1]))
      (fun cs hcs => hcF cs (List.mem_cons_of_mem _ hcs))
    rcases hx : nrtE p n m3 vis ctx hO hL (cO + 1) (cL - 1) (r1'.tail.tail.headD 0) (ro.headD 0)
      (ro.tail.headD 0) with ε | ⟨r0, m0⟩ <;> rw [hx] at ih
    · rw [nrtE.k_nest_root.none]; exact ih
    · rw [nrtE.k_nest_root.arm1]
      obtain ⟨x, a', hrun, hR⟩ := ih
      exact RefE.ret hrun ⟨hR.stage, hg13.trans hR.grow, by simpa using hR.outs, by simpa using hR.outsb,
        by simpa using hR.ns, hR.pos, hR.abs, c1.trans hR.core⟩

end root

/-- `nest_seeds`' unified model: `nest_ctx_hi_at`, `nest_seeds_fuel` lifted, `nest_cont_key` as its
unified model, `nest_inst_type` through its run. -/
l_model nsdE_spec (p : Prog) (hL : RsLook p)
  fns [hL.pseeds ↦ nsdE list]
  specs [nestCtxHiAt_specE p hL.nb.ct.cr.rx.hi n, nestSeedsFuel_spec hL n, nitE_spec p hL.nb.nit n,
    nckE_spec p hL.nb.pkey n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `nest_seeds` gives besides the twin's state `x` (from `m`, `a`): the stage, the growth, the
state at `r[0]`, the frames, `AbsOK`, the core step. -/
structure NsdPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem)
    (a : AState) (r : List Word) (x : NestState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  ns : NSB m' (r.headD 0) x
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

section seeds
variable {p : Prog} (L : RsLook p)
  (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (ctx : Word) (c : NestCtx) {ctxP : ConLeche.NestCtx} (hc : ConLeche.NestCtxOk ctxP)

include L hq hIlpf hLC henv hc in
/-- **`nest_seeds` refines `nestSeeds`, both outcomes** under `StageC` (twin side: con-ron's
`nestSeeds_spec`; the seed's fuel by `seedFuel_spec`, its former by `nestInstType_spec`, the
instantiation met by `nestContKey_spec`; the errors under `NbG`: `nest_inst_type`'s (`nit_ref`),
`nest_cont_key`'s from `nbRef_all`). -/
theorem nsd_ref : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (sO sL ns : Word)
    (seeds : List (NestKey × Nat)) (NS : NestState)
    (seedsP : List (ConLeche.NestKey × Nat)) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a → UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → sL.toNat = seeds.length → SeedsAt m sO.toNat seeds → NSB m ns NS → PosMR m → AbsOK m →
    dCtx a.store env.find? c = some ctxP →
    seeds.mapM (fun k => (ConRon.Bridge.Inductives.dKey a.store k.1).map (·, k.2)) = some seedsP →
    dState a.store NS = some nsP → (∀ k ∈ seedsP, ∀ x ∈ k.1.ds, ConLeche.Expr.WScoped (ctxP.hiAt 0) x) →
    RefE (NbG p) (nsdE p n m vis ctx sO sL ns) (nestSeeds V fe c seeds NS) a
      (fun v x a' => NsdPost dn vis fe env m a v.1 x v.2 a') := by
  intro n
  induction n with
  | zero => intros; rw [nsdE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
    intro hn m a sO sL ns seeds NS seedsP nsP hC hU hhi hsl hsd hns hP hA hctx hseedsP hnsP hw
    have hS := hC.stage
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases h0 : sL = 0
    · rw [nsdE.arm1 p n m vis ctx sO sL ns h0]
      subst h0
      have : seeds = [] := List.eq_nil_of_length_eq_zero (by simpa using hsl.symm)
      subst this
      exact RefE.ret (by rw [ConRon.Arena.nestSeeds.eq_def]; rfl) ⟨hC, IWGrow.refl _, by simpa using hns, hP, hA,
        ConRon.Bridge.CoreStep.refl hC.check⟩
    rw [nsdE.arm2 p n m vis ctx sO sL ns h0]
    obtain ⟨⟨kk, nPcN⟩, seeds', rfl⟩ : ∃ x seeds', seeds = x :: seeds' := by
      cases seeds with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hsl)) h0
      | cons x seeds' => exact ⟨x, seeds', rfl⟩
    simp only [List.length_cons] at hsl
    -- the twin's key
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hseedsP
    rcases hk1 : (ConRon.Bridge.Inductives.dKey a.store kk).map (·, nPcN) with _ | kP; · rw [hk1] at hseedsP; simp at hseedsP
    cases hks1 : seeds'.mapM (fun k => (ConRon.Bridge.Inductives.dKey a.store k.1).map (·, k.2)) with
    | none => rw [hk1, hks1] at hseedsP; simp at hseedsP
    | some ksP' =>
    simp only [hk1, hks1, Option.bind_some, Option.some.injEq] at hseedsP
    subst hseedsP
    simp only [Option.map_eq_some_iff] at hk1
    obtain ⟨keyP, hkey, rfl⟩ := hk1
    obtain ⟨hkc, hkl, hkd⟩ := ConRon.Bridge.Inductives.dKey_inv hkey
    obtain ⟨sp, key, nPc, h0w, hsO, hsp1, h1w, h2w, hkd', hksl, hnpc⟩ := hsd 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0w hkd' hnpc
    have rd0 : rdW (m.arr64 IW) sO = sp := by simp [rdW, h0w]
    have rd1 : rdW (m.arr64 IW) sp = key := by simp [rdW, h1w]
    have hsp1' : (sp + 1).toNat = sp.toNat + 1 := word_add_toNat (by simp; omega)
    have rd2 : rdW (m.arr64 IW) (sp + 1) = nPc := by simp [rdW, hsp1', h2w]
    rw [rd0, rd1, rd2]
    obtain ⟨hnnH, hnnd, husH, husd, hdsd, hdsb, hk4⟩ := pos2_nk_fields hkd' htop
    obtain ⟨hk, hkin⟩ := pos2_nk_in hkd'
    obtain ⟨hdl, hdel⟩ := pos2_hslice_get hdsd
    rw [ConRon.Arena.nestSeeds]
    -- the fuel
    rcases hf : p2sfW n m (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) 0 SLACK with _ | ⟨rf, m1⟩
    · rw [liftE_none, nsdE.k_nest_seeds_fuel.none]; exact RefE.of_cls0 rfl
    rw [liftE_some, nsdE.k_nest_seeds_fuel.arm1]
    obtain ⟨a1, hfold, hS1, hg1, hP1⟩ := p2sfW_ok dn vis fe _ _ kk.ds m hdl hdel hksl n m m1 a 0 SLACK rf hf hS
      (IWGrow.refl _) (by simp) hP
    have hA1 := p2sfW_afr _ _ _ _ _ _ _ _ hf hA
    have hfold' : (kk.ds.foldlM (fun a d => do
        let w ← ConRon.Arena.whnfWalkFuel d
        pure (max a w)) fuelSlack).run a = .ok ((rf.headD 0).toNat, a1) := by
      simp only [UInt64.toNat_zero, List.drop_zero] at hfold
      exact hfold
    obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.seedFuel_spec kk.ds keyP.ds fuelSlack a a1 _ hC.check.state hkd hfold'
    have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
    refine RefE.bind_right hfold' ?_
    have hW : WCtx dn vis fe m ctx 0 0 c [] := ⟨hU, by simp [HSl, HolesAt], by simpa using hhi⟩
    have hhi0 : (nhiW m ctx 0).toNat = c.hiAt 0 := by simpa using hW.hi htop
    have hkd1 : decNK m1 key.toNat = some kk := hkd'.get (decNK_mono _) |>.symm ▸ (hkd'.stab (decNK_mono _) m1 hg1)
    have hkin1 := (pos2_nk_in (hkd'.grow (decNK_mono _) hg1)).2
    have hksl1 : NKSl m1 key := (hsd.grow hg1 htop) 0 (by simp) |>.elim fun _ h' => by
        obtain ⟨key', nPc', h0', -, -, h1', -, -, hksl', -⟩ := h'
        have : (m1.arr64 IW)[sO.toNat]? = some sp := by rw [hg1.iwGet _ (by omega)]; exact h0w
        simp only [Nat.add_zero] at h0'
        rw [this] at h0'; cases h0'
        rw [hg1.iwGet _ (by omega), h1w] at h1'; cases h1'
        exact hksl'
    -- the instance's type
    have hN := nit_ref L.nb.nit hq.closed hIlpf hLC n hC1 hA1 hhi0 (hU.grow hg1) hkd1 hkin1 hksl1 hP1
      (dCtx_ext _ p1.ext _ _ hctx) (ConRon.Bridge.Inductives.dKey_ext p1.ext _ _ hkey)
    rcases h3 : nitE p n m1 vis ctx (nhiW m ctx 0) key with e3 | ⟨r2, m2⟩ <;> rw [h3] at hN
    · rw [nsdE.k_nest_inst_type.none]; exact RefE.bind_left fun hG => hN hG.nv
    rw [nsdE.k_nest_inst_type.arm1]
    obtain ⟨x2, a2, hrun2, hS2, hg2, -, hctyH, hctyd, hP2, hA2⟩ := hN
    have c1 := p1.toCore hC.check
    obtain ⟨c2, niP, ⟨-, hni2, hni3⟩, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec hc c (c.hiAt 0) kk keyP
      a1 a2 x2 c1.ok ⟨dCtx_ext _ p1.ext _ _ hctx, ConRon.Bridge.Inductives.dKey_ext p1.ext _ _ hkey⟩ hrun2
    have c12 := c1.trans c2
    have hx02 := c12.ext
    have hC2 : StageC dn vis fe env m2 a2 := hC.of_cstep hS2 hA2 c12
    have hg12 := hg1.trans hg2
    have hksl2 : (rdW (m.arr64 IW) (key + 2)).toNat + (rdW (m.arr64 IW) (key + 3)).toNat ≤ iwTop m2 :=
      Nat.le_trans hksl hg12.iw
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
    refine RefE.bind_right hrun2 ?_
    obtain ⟨xn, xc⟩ := x2
    -- the container instance
    have e0 : rdW (m2.arr64 IW) key = rdW (m.arr64 IW) key := pos2_rd_grow hg12 (by omega)
    have e1 := pos2_key_rd hg12 htop hk4 (j := 1) (by omega)
    have e2 := pos2_key_rd hg12 htop hk4 (j := 2) (by omega)
    have e3 := pos2_key_rd hg12 htop hk4 (j := 3) (by omega)
    rw [show (key + 1 : Word) = key + UInt64.ofNat 1 from rfl, show (key + 2 : Word) = key + UInt64.ofNat 2 from rfl,
      show (key + 3 : Word) = key + UInt64.ofNat 3 from rfl, e0, e1, e2, e3]
    have hdsB : DecB (fun m' => (decHL m' (rdW (m.arr64 IW) (key + UInt64.ofNat 2)).toNat
        (rdW (m.arr64 IW) (key + UInt64.ofNat 3)).toNat : Option (List EIdx))) m2 kk.ds := by
      show decHL (truncM m2) _ _ = _; rw [decHL_truncM (by simpa using hksl2)]
      rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by simpa using hdsb j hj)]; simpa using hdsd
    have hnnd' : decI (rdW (m.arr64 IW) key) = kk.cname := hnnd
    have husd' : decI (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) = kk.lvls := husd
    have hK := (nbRef_all (dn := dn) (vis := vis) (fe := fe) L.nb hq hIlpf hLC henv n (by omega)).key m2 a2 ctx
      (rf.headD 0) 0 0 0 (rdW (m.arr64 IW) key) (rdW (m.arr64 IW) (key + UInt64.ofNat 1))
      (rdW (m.arr64 IW) (key + UInt64.ofNat 2)) (rdW (m.arr64 IW) (key + UInt64.ofNat 3)) nPc (r2.tail.headD 0) ns
      c [] kk.ds NS ctxP [] keyP.cname keyP.lvls keyP.ds niP.2 nsP
      hC2 (hW.grow hg12) hnnH husH hdsB (by simpa using hksl2) hctyH (hns.grow hg12 htop) hP2 hA2
      hc (dCtx_ext _ hx02 _ _ hctx) rfl (by rw [hnnd']; exact ConRon.Bridge.denoteN_ext hkc hx02)
      (by rw [husd']; exact ConRon.Bridge.denoteLs_ext hkl hx02) (ConRon.Bridge.denoteEList_ext hx02 _ _ hkd)
      (by rw [hctyd]; exact hni2) (dState_ext hx02 _ _ hnsP) (by simpa using hw _ List.mem_cons_self) hni3
    rw [hnnd', husd', hctyd, hnpc] at hK
    rcases h4 : nckE p n m2 vis ctx (rf.headD 0) 0 0 0 (rdW (m.arr64 IW) key)
        (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) (rdW (m.arr64 IW) (key + UInt64.ofNat 2))
        (rdW (m.arr64 IW) (key + UInt64.ofNat 3)) nPc (r2.tail.headD 0) ns with e4 | ⟨r3, m3⟩ <;> rw [h4] at hK
    · rw [nsdE.k_nest_cont_key.none]; exact RefE.bind_left hK
    obtain ⟨x3, a3, hrun3, hR3⟩ := hK
    dsimp only at hR3
    obtain ⟨hC3, hg3, -, hns3, hP3, hA3, c3⟩ := hR3
    have hg13 := hg12.trans hg3
    have hsO1 : (sO + 1).toNat = sO.toNat + 1 := word_add_toNat (by simp; omega)
    have hsL1 : (sL - 1).toNat = seeds'.length := by rw [pos2_word_pred h0]; omega
    have hx03 := c12.ext.trans c3.ext
    obtain ⟨-, v1, ⟨-, hns1P⟩, -⟩ := ConRon.Bridge.Inductives.nestContKey_spec coreSpecV henv hc
      (ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc _)
      [] [] 0 kk.cname keyP.cname kk.lvls keyP.lvls kk.ds keyP.ds nPcN xc niP.2 NS nsP
      (by simpa using hw _ List.mem_cons_self) hni3 a2 a3 x3 c12.ok
      ⟨dCtx_ext _ hx02 _ _ hctx, rfl, ConRon.Bridge.denoteN_ext hkc hx02, ConRon.Bridge.denoteLs_ext hkl hx02,
        ConRon.Bridge.denoteEList_ext hx02 _ _ hkd, hni2, dState_ext hx02 _ _ hnsP⟩ hrun3
    refine RefE.bind_right hrun3 ?_
    rw [nsdE.k_nest_cont_key.arm1]
    have ih' := ih (by omega) m3 a3 (sO + 1) (sL - 1) (r3.tail.headD 0) seeds' x3.2 ksP' v1.2 hC3 (hU.grow hg13) hhi
      hsL1 (by rw [hsO1]; exact (hsd.grow hg13 htop).tail) hns3 hP3 hA3 (dCtx_ext _ hx03 _ _ hctx)
      (ConRon.Bridge.Inductives.mapM_option_ext (fun a b h => by
          simp only [Option.map_eq_some_iff] at h ⊢
          obtain ⟨x, hx, rfl⟩ := h
          exact ⟨x, ConRon.Bridge.Inductives.dKey_ext hx03 _ _ hx, rfl⟩) _ _ hks1)
      hns1P (fun k hk x hx => hw k (List.mem_cons_of_mem _ hk) x hx)
    rcases hx : nsdE p n m3 vis ctx (sO + 1) (sL - 1) (r3.tail.headD 0) with ε | ⟨r0, m0⟩ <;> rw [hx] at ih'
    · rw [nsdE.k_nest_seeds.none]; exact ih'
    rw [nsdE.k_nest_seeds.arm1]
    obtain ⟨x, a', hrun, hR⟩ := ih'
    exact RefE.ret hrun ⟨hR.stage, hg13.trans hR.grow, hR.ns, hR.pos, hR.abs, (c12.trans c3).trans hR.core⟩

end seeds

end L.Ind

end
