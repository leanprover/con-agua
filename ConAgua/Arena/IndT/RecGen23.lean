module

import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Verdict.IndBK53
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.PdWAfr
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Inductives.GenRec
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.RecGenSpec.PdWMfr
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# `class_nodes_agree`: one model, one refinement

`class_nodes_agree`'s unified model (`cnaE`) and its refinement for both outcomes (`cna_ref`, the
loop `cnaLoop_ref`), under `StageC` and
the inputs' denotations con-ron's `classNodesAgree_spec` asks; its twin side transcribed from that
spec's proof: `targetPiDomsWith` (`targetPiDomsWith_spec`, a `PSpec`), the field read, then
`target_k53` (`tk_ref` on its unified model, con-ron's `targetK53_spec` on its run for the
extension). `classNodesAgree_refinesC` is its ok half (`RefE.triple`).
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`class_nodes_agree`'s unified model**: `target_pi_doms_with` (outside the verdict closure)
lifted, `target_k53` by its unified model. -/
l_model cnaE_spec (p : Prog) (P : CnaProg p)
  fns [P.cna ↦ cnaE] specs [callW_spec p n "target_pi_doms_with", tkE_spec p P.k53 n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The class family's walk package -/

/-- **The walk's package from `(m₀, a₀)` to `(m, a)`** (the class functions, docs/design/refgen.md
§6): the stage, `AbsOK`, `RcMR`, the `IW` growth and the twin's core step. -/
structure RcAt (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m₀ : Mem) (a₀ : AState) (m : Mem) (a : AState) : Prop where
  stage : StageC dn vis fe env m a
  abs : AbsOK m
  rc : RcMR m
  grow : IWGrow m₀ m

namespace RcAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {m₀ m₁ m : Mem} {a₀ a₁ a : AState}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem refl (h : StageC dn vis fe env m a) (hA : AbsOK m) (hP : RcMR m) : RcAt dn vis fe env m a m a :=
  ⟨h, hA, hP, IWGrow.refl _, CoreStep.refl h.check⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem trans (h₁ : RcAt dn vis fe env m₀ a₀ m₁ a₁) (h₂ : RcAt dn vis fe env m₁ a₁ m a) :
    RcAt dn vis fe env m₀ a₀ m a :=
  ⟨h₂.stage, h₂.abs, h₂.rc, h₁.grow.trans h₂.grow, h₁.core.trans h₂.core⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A step that con-ron calls a `PStep`. -/
theorem pstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR vis fe m a) (hA : AbsOK m) (hP : RcMR m)
    (hg : IWGrow m₀ m) (hp : PStep a₀ a) : RcAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_pstep hS hA hp, hA, hP, hg, hp.toCore h.check⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A core step. -/
theorem cstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR vis fe m a) (hA : AbsOK m) (hP : RcMR m)
    (hg : IWGrow m₀ m) (hc : CoreStep V env fe a₀ a) : RcAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_check hS hA hc.ok hc.ext, hA, hP, hg, hc⟩
-/

end RcAt

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (P : CnaProg p)
  (vis q fto ftl mc teo tel leaf fvo fvl i eo el : Word) (bs : BlockShape) (formerTys : List EIdx)
  (TM : TargetMajor) (tele fvs : List EIdx)
  {pP : ConLeche.BlockShape} {formerTysP teleP fvsP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
  {leafP : ConLeche.Expr}

/-- What `class_nodes_agree` gives besides the twin's run (from `m`). -/
structure CnaPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'

include hq henv P in
/-- **`class_nodes_agree`'s loop refines `classNodesAgree`, both outcomes** (twin side: con-ron's
`classNodesAgree_spec`'s list induction; `target_k53` by `tk_ref`). -/
theorem cnaLoop_ref (k : Nat) (hk : k ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState) (j : Word)
    (es : List NestCtorNf) (esP : List ConLeche.NestCtorNf),
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs →
    decHL m fto.toNat ftl.toNat = some formerTys →
    fto.toNat + ftl.toNat ≤ iwTop m → DecB (fun m => decTM m mc.toNat) m TM → HSl0 m teo tel tele →
    H leaf → decHL m fvo.toNat fvl.toNat = some fvs → fvo.toNat + fvl.toNat ≤ iwTop m →
    j ≤ el → PSlR decNCN es (eo + j) (el - j) m → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    dMajor a.store TM = some McP → Frontend.denoteEList a.store tele = some teleP →
    denoteE a.store (decE leaf) = some leafP → Frontend.denoteEList a.store fvs = some fvsP →
    es.mapM (dCtorNf a.store) = some esP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) → ConLeche.Cached.TargetMajScoped McP →
    RefE (VerdictCtx p) (cnaE.loop1 p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j)
      (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a
      (fun m' _ a' => CnaPost dn vis fe env m m' a') := by
  sorry

include hq henv P in
/-- **`class_nodes_agree` refines `classNodesAgree`, both outcomes** (`cnaLoop_ref` from the first
entry). -/
theorem cna_ref (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState)
    (es : List NestCtorNf) (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hMc : DecB (fun m => decTM m mc.toNat) m TM) (htl : HSl0 m teo tel tele) (hl : H leaf)
    (hfv : decHL m fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hes : PSlR decNCN es eo el m) (hP : RcMR m) {esP : List ConLeche.NestCtorNf}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP) (htlP : Frontend.denoteEList a.store tele = some teleP)
    (hlP : denoteE a.store (decE leaf) = some leafP)
    (hfvP : Frontend.denoteEList a.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (cnaE p n m vis q fto ftl mc teo tel leaf fvo fvl i eo el)
      (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a
      (fun v _ a' => CnaPost dn vis fe env m v.2 a') := by
  rcases n with _ | n
  · rw [cnaE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cnaE.arm1]
  have h := cnaLoop_ref hq henv P vis q fto ftl mc teo tel leaf fvo fvl i eo el bs formerTys TM tele fvs
    (n + 1) hn m a 0 es esP hC hA hbs hft hftb hMc htl hl hfv hfvb UInt64.zero_le (by simpa using hes)
    hP hsh hftP hMcP htlP hlP hfvP hesP hformer hMs
  rcases h1 : cnaE.loop1 p (n + 1) m vis q fto ftl mc teo tel leaf fvo fvl i eo el 0 with e1 | m1 <;>
    rw [h1] at h
  · rw [cnaE.k_loop1.none]; exact h
  · rw [cnaE.k_loop1.arm1]; exact h

include hq henv P in
/-- **`class_nodes_agree` refines `classNodesAgree`** under `StageC` (the knot's core calls; the
inputs' denotations and scoping as con-ron's `classNodesAgree_spec` asks). -/
@[refines ConRon.Arena.classNodesAgree]
theorem classNodesAgree_refinesC (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (es : List NestCtorNf) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hMc : DecB (fun m => decTM m mc.toNat) s₀.mem TM) (htl : HSl0 s₀.mem teo tel tele) (hl : H leaf)
    (hfv : decHL s₀.mem fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hes : PSlR decNCN es eo el s₀.mem) (hP : RcMR s₀.mem) {esP : List ConLeche.NestCtorNf}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hMcP : dMajor a₀.store TM = some McP) (htlP : Frontend.denoteEList a₀.store tele = some teleP)
    (hlP : denoteE a₀.store (decE leaf) = some leafP)
    (hfvP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a₀.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_nodes_agree"
      [vis, q, fto, ftl, mc, teo, tel, leaf, fvo, fvl, i, eo, el]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cnaE_spec p P n s₀ vis q fto ftl mc teo tel leaf fvo fvl i eo el)
    (cna_ref hq henv P vis q fto ftl mc teo tel leaf fvo fvl i eo el bs formerTys TM tele fvs n hn s₀.mem a₀
      es hC hA hbs hft hftb hMc htl hl hfv hfvb hes hP hsh hftP hMcP htlP hlP hfvP hesP hformer hMs)) ?_
  rintro r s' ⟨hl', u, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind

end
