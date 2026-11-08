module

public import ConAgua.Verdict.IndBTka
import ConAgua.Arena.IndT.RecGen19
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.RecCheckK53
import ConAgua.Arena.RecCheckSpec.Tka
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecCheckSpec.TmFields
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# `target_k53_heads`, `target_k53`: one model and one refinement each, for both outcomes

`tkhE`, `tkE` (`l_model … unified`): `target_k53_args` and `target_k53_heads` through their
unified models (`tkaE`, `tkhE`), the callees outside the verdict closure (`get_app_fn_f`,
`get_app_args_f`, `e_view`, `strip_pis`, `target_k53_tele`) through their `Option` models.
`tkh_ref` and `tk_ref` refine `tkHeads` and `targetK53` for both outcomes (`tka_ref` below them);
`tk_ref`'s ok half is `targetK53_refinesC` and `class_nodes_agree`'s ok refinement (`RecGen23`,
through the run), its error half `class_nodes_agree`'s refinement (`cna_ref`, `RecGen23`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

-- `finish (gen := 20)`: the generation depth (the default 8 leaves four paths open; `simp […]`
-- passes too, about 1 s slower)
l_model tkhE_spec (p : Prog) (hL : K53Look p)
  fns [hL.tkh ↦ tkhE]
  specs [gafF_spec p hL.ad n, gaaF_spec p hL.ad n, eView_spec p hL.hv n, tkaE_spec p hL n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [] gen 20 heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model tkE_spec (p : Prog) (hL : K53Look p)
  fns [hL.tk ↦ tkE]
  specs [stripPis_specF p hL.strip n, tte_spec p hL n, tkhE_spec p hL n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_k53_heads` refines `tkHeads`, both outcomes** (twin side: con-ron's
`targetK53_spec`, the heads' part: read-only steps, then `tka_ref`). -/
theorem tkh_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {q fto ftl Mc leafW majDom : Word}
    {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hl : H leafW) (hmj : H majDom) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {lwP mdP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hlwP : denoteE a.store (decE leafW) = some lwP) (hmdP : denoteE a.store (decE majDom) = some mdP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (tkhE p n m vis q fto ftl Mc leafW majDom)
      (tkHeads fe bs formerTys TM (decE leafW) (decE majDom)) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  sorry

include hq henv in
/-- **`target_k53` refines `targetK53`, both outcomes** (twin side: con-ron's `targetK53_spec`'s
proof): `stripPis`, the telescope check (`tkTele_cstep`), then `tkh_ref`. -/
theorem tk_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {q fto ftl Mc teo tel majDom f : Word}
    {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {tele : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (htl : HSl0 m teo tel tele) (hmj : H majDom) (hf : H f) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (htlP : Frontend.denoteEList a.store tele = some teleP)
    (hmdP : denoteE a.store (decE majDom) = some mdP) (hfP : denoteE a.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (tkE p n m vis q fto ftl Mc teo tel majDom f)
      (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  sorry

include hq henv in
/-- **`target_k53` refines `targetK53`** under `StageC` (`tk_ref`'s ok half; the knot's core calls;
the inputs' denotations and scoping as con-ron's `targetK53_spec` asks). -/
@[refines ConRon.Arena.targetK53]
theorem targetK53_refinesC (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl Mc teo tel majDom f : Word)
    (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor) (tele : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hMc : DecB (fun m => decTM m Mc.toNat) s₀.mem TM) (htl : HSl0 s₀.mem teo tel tele)
    (hmj : H majDom) (hf : H f) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hMcP : dMajor a₀.store TM = some McP)
    (htlP : Frontend.denoteEList a₀.store tele = some teleP)
    (hmdP : denoteE a₀.store (decE majDom) = some mdP) (hfP : denoteE a₀.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53" [vis, q, fto, ftl, Mc, teo, tel, majDom, f]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tkE_spec p L n s₀ vis q fto ftl Mc teo tel majDom f)
    (tk_ref hq henv n hn hC hA hbs hft hftb hMc htl hmj hf hP hsh hftP hMcP htlP hmdP hfP hformer hMs)) ?_
  rintro r s' ⟨hl', c, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hR.res, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind
