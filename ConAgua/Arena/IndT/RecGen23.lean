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
  core : CoreStep V env fe a₀ a

namespace RcAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {m₀ m₁ m : Mem} {a₀ a₁ a : AState}

theorem refl (h : StageC dn vis fe env m a) (hA : AbsOK m) (hP : RcMR m) : RcAt dn vis fe env m a m a :=
  ⟨h, hA, hP, IWGrow.refl _, CoreStep.refl h.check⟩

theorem trans (h₁ : RcAt dn vis fe env m₀ a₀ m₁ a₁) (h₂ : RcAt dn vis fe env m₁ a₁ m a) :
    RcAt dn vis fe env m₀ a₀ m a :=
  ⟨h₂.stage, h₂.abs, h₂.rc, h₁.grow.trans h₂.grow, h₁.core.trans h₂.core⟩

/-- A step that con-ron calls a `PStep`. -/
theorem pstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR vis fe m a) (hA : AbsOK m) (hP : RcMR m)
    (hg : IWGrow m₀ m) (hp : PStep a₀ a) : RcAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_pstep hS hA hp, hA, hP, hg, hp.toCore h.check⟩

/-- A core step. -/
theorem cstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR vis fe m a) (hA : AbsOK m) (hP : RcMR m)
    (hg : IWGrow m₀ m) (hc : CoreStep V env fe a₀ a) : RcAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_check hS hA hc.ok hc.ext, hA, hP, hg, hc⟩

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
  induction k with
  | zero => intros; rw [cnaE.loop1.eq_def]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a j es esP hC hA hbs hft hftb hMc htl hl hfv hfvb hje hes hP hsh hftP hMcP htlP hlP
    hfvP hesP hformer hMs
  have hS := hC.stage
  by_cases hj : j < el
  rotate_left
  · rw [cnaE.loop1.arm2 p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j hj]
    have hjl : el - j = 0 := by
      apply UInt64.toNat_inj.mp
      have h1 : el.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
      have h2 : j.toNat ≤ el.toNat := UInt64.le_iff_toNat_le.mp hje
      rw [UInt64.toNat_sub_of_le _ _ hje]; simp <;> omega
    have : es = [] := by
      have := decPL_length _ (hes.1.get (OMono.decPL decNCN_mono _ _)); rw [hjl] at this; simpa using this
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl _, hP, hA⟩
  rw [cnaE.loop1.arm1 p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j hj]
  have hsz := hS.iw.iwSize
  have hne : el - j ≠ 0 := by
    intro h0
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_sub_of_le _ _ hje] at this; simp at this; omega
  obtain ⟨nf, es', rfl, hnf0, hes'⟩ := hes.uncons hne hsz
  obtain ⟨nfP, esP', rfl, hnfP, hesP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hesP
  have hety := (ConRon.Bridge.Inductives.RC.dCtorNf_inv hnfP).2.2.2
  generalize hE : rdW (m.arr64 IW) (eo + j) = ew at hnf0 ⊢
  obtain ⟨htyH, htyD⟩ := decNCN_ty hnf0 hsz
  rw [ConRon.Arena.classNodesAgree]
  -- `target_pi_doms_with`
  refine RefE.bindLift (fun _ => cnaE.k_target_pi_doms_with.none ..) fun r1 m1 h1 => ?_
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetPiDomsWith_spec p P.hv P.hc P.ha P.hsc P.pd P.hi1 k _ fvo fvl (rdW (m.arr64 IW) (ew + 4))) h1
  simp only at hs1 hw1
  subst hs1
  obtain ⟨res, a1, run1, hS1, hg1, hpd⟩ := pdW_ok dn vis fe k _ _ a _ _ _ r1 fvs hw1 hS htyH hfv
    (hS.lt64 hfvb) hfvb
  rw [htyD] at run1
  obtain ⟨q1, ho⟩ := ConRon.Bridge.Inductives.targetPiDomsWith_spec fvs fvsP nf.ty nfP.ty a a1 res
    hC.check.state ⟨hfvP, hety⟩ run1
  have k1 := RcAt.pstep hC hS1 (pdW_afr _ _ _ _ _ _ _ hw1 hA) (hP.fr (pdW_mfr _ _ _ _ _ _ _ hw1)) hg1 q1
  have hdoms := ConRon.Bridge.Inductives.ROp_REL_getD ho
  refine ⟨_, _, run1, ?_⟩
  dsimp only
  rcases res with _ | ds
  · rw [cnaE.k_target_pi_doms_with.arm1 (hc1 := hpd), cnaE.j1.abort1 (hc1 := UInt64.zero_le) ..]
    simp only [Option.getD_none, List.getElem?_nil]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  obtain ⟨h1', hdd, hdb⟩ := hpd
  rw [cnaE.k_target_pi_doms_with.arm2 (hc1 := by rw [h1']; decide)]
  have hlen := decHL_length _ hdd
  by_cases hsh' : r1.tail.tail.headD 0 ≤ i
  · rw [cnaE.j1.abort1 (hc1 := hsh')]
    simp only [Option.getD_some, List.getElem?_eq_none (by rw [hlen]; exact UInt64.le_iff_toNat_le.mp hsh')]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  rw [cnaE.j1.arm1 (hc1 := hsh')]
  have hi : i.toNat < (r1.tail.tail.headD 0).toNat := by
    exact Nat.lt_of_not_le (fun hc => hsh' (UInt64.le_iff_toNat_le.mpr hc))
  have hdb64 := hS1.lt64 hdb
  obtain ⟨w, hw, hwH, hwD⟩ := decHL_get' hdd i.toNat hi (by omega)
  have hadd : r1.tail.headD 0 + i = UInt64.ofNat ((r1.tail.headD 0).toNat + i.toNat) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
  rw [hadd, hw]
  have hget : ds[i.toNat]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hi)]; rw [hwD]
  rw [← decE_eq] at hget
  obtain ⟨fP, -, hfd⟩ := (ConRon.Bridge.Inductives.denoteEList_getElem? hdoms i.toNat).2 _ hget
  simp only [Option.getD_some, hget]
  -- `target_k53`
  refine RefE.bindE (fun _ => cnaE.k_target_k53.none ..) id (tk_ref hq henv k (by omega) k1.stage k1.abs
    (hbs.grow hg1) (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.iw; omega) (hMc.grow (decTM_mono _) hg1)
    (htl.grow hg1) hl hwH k1.rc
    (ConRon.Bridge.Inductives.dShape_ext k1.core.ext _ _ hsh) (denoteEList_ext k1.core.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext k1.core.ext _ _ hMcP) (denoteEList_ext k1.core.ext _ _ htlP)
    (denote_ext hlP k1.core.ext) hfd hformer hMs) fun ⟨b, m2⟩ c a2 run2 hR2 => ?_
  dsimp only at hR2
  have hc : (b != 0) = c := hR2.res
  obtain ⟨c2', -⟩ := ConRon.Bridge.Inductives.targetK53_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys formerTysP TM McP tele teleP (decE leaf) (decE w) leafP fP hformer hMs
    a1 a2 c k1.stage.check
    ⟨ConRon.Bridge.Inductives.dShape_ext k1.core.ext _ _ hsh, denoteEList_ext k1.core.ext _ _ hftP,
      ConRon.Bridge.Inductives.dMajor_ext k1.core.ext _ _ hMcP, denoteEList_ext k1.core.ext _ _ htlP,
      denote_ext hlP k1.core.ext, hfd⟩ run2
  have k2 := RcAt.cstep k1.stage hR2.stage.stage hR2.abs hR2.rc hR2.grow c2'
  refine RefE.ofArms (fun h => cnaE.k_target_k53.abort1 (hc1 := h) ..) (fun h => cnaE.k_target_k53.arm1 (hc1 := h) ..)
    (RefE.guardIf (by decide) (fun hb => by rw [← hc, hb]; rfl) (fun hcf => by simpa [hcf] using hc) fun _ _ => ?_)
  have k12 := k1.trans k2
  have hj1 : j + 1 ≤ el := by
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    apply UInt64.le_iff_toNat_le.mpr; rw [UInt64.toNat_add]; simp <;> omega
  have hes2 : PSlR decNCN es' (eo + (j + 1)) (el - (j + 1)) m2 := by
    rw [show eo + (j + 1) = eo + j + 1 by grind, show el - (j + 1) = el - j - 1 by grind]
    exact hes'.grow (fun q => decNCN_mono q) k12.grow
  exact RefE.mono (ih (by omega) m2 a2 (j + 1) es' esP' k2.stage k2.abs
    (hbs.grow k12.grow)
    (by rw [decHL_grow k12.grow hftb]; exact hft) (by have := k12.grow.iw; omega) (hMc.grow (decTM_mono _) k12.grow)
    (htl.grow k12.grow) hl (by rw [decHL_grow k12.grow hfvb]; exact hfv) (by have := k12.grow.iw; omega) hj1 hes2
    k2.rc (ConRon.Bridge.Inductives.dShape_ext k12.core.ext _ _ hsh) (denoteEList_ext k12.core.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext k12.core.ext _ _ hMcP) (denoteEList_ext k12.core.ext _ _ htlP)
    (denote_ext hlP k12.core.ext) (denoteEList_ext k12.core.ext _ _ hfvP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list k12.core.ext _ _ hesP') hformer hMs)
    fun _ _ _ h => ⟨h.stage, k12.grow.trans h.grow, h.rc, h.abs⟩

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
