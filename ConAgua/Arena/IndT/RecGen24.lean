module

public import ConAgua.Arena.IndT.RecGen23
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Inductives.GenRec
public import ConAgua.Arena.RecGenSpec.CfaFv
public import ConAgua.Arena.RecStab
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# `class_fields_agree`: one model, one refinement

`class_fields_agree`'s unified model (`cfaE`) and its refinement for both outcomes (`cfa_ref`, the
loop `cfaLoop_ref`), under `StageC` and
the inputs' denotations con-ron's `classFieldsAgree_spec` asks; its twin side transcribed from that
spec's proof: `exprGetD` (`exprGetD_spec`), `fvarTypeD` and `stripPis` (read-only), `targetMajorAt`
(`targetMajorAt_spec`), `classLeafAt` (`classLeafAt_spec`), then `cna_ref` (con-ron's
`classNodesAgree_spec` on its run for the extension).
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
/-- **`class_fields_agree`'s unified model**: the callees outside the verdict closure lifted,
`class_nodes_agree` by its unified model. -/
l_model cfaE_spec (p : Prog) (P : CfaProg p)
  fns [P.cfa ↦ cfaE]
  specs [callW_spec p n "intern_bvar", callW_spec p n "fvar_type_d", callW_spec p n "strip_pis",
    callW_spec p n "target_major_at", callW_spec p n "class_leaf_at", cnaE_spec p P.toCnaProg n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem leafAtW_afr {m m' : Mem} {mm leaf : Word} {r : List Word} (h : leafAtW m mm leaf = some (r, m')) :
    AFr m m' := by
  simp only [leafAtW] at h
  rcases h1 : gafF m [CWF, leaf] with _ | x
  · rw [h1] at h; cases h
  obtain ⟨r1, m1⟩ := x
  simp only [h1] at h
  refine (gafF_afr h1).trans ?_
  have hm : m' = m1 := by
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  rw [hm]; exact AFr.refl _

theorem cfaFv_afr {p : Prog} (P : CfaProg p) {k : Nat} {m m0 : Mem} {fvo fvl i : Word} {r0 : List Word}
    (h : cfaFv p k m fvo fvl i = some (r0, m0)) : AFr m m0 := by
  by_cases hi : i < fvl
  · rw [cfaFv_in (h := hi)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact AFr.refl _
  · rw [cfaFv_out (h := hi)] at h
    obtain ⟨s0, rfl, -, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internBVar_spec p P.bf P.bp P.ib k _ 0) h
    exact binternW_afr hb

/-- **`target_major_at`'s step** (two call sites: `cfaLoop_ref`, `cxo_ref`): the twin's
`targetMajorAt`, the package, the major's record at the result word and its denotation. -/
theorem tma_step {p : Prog} (P : CfaProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m₀ m : Mem} {a₀ a : AState} {n : Nat} (hk : RcAt dn vis fe env m₀ a₀ m a)
    {mo ml c : Word} {t : Nat} (ht : c.toNat = t) {ms : List TargetMajor} {MsP : List ConLeche.TargetMajor}
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) :
    Sim (callW p n "target_major_at" [mo, ml, c] m) (ConRon.Arena.targetMajorAt ms t) a
      fun r tm m' a' => RcAt dn vis fe env m a m' a' ∧
        DecB (fun m => decTM m (r.headD 0).toNat) m' tm ∧ dMajor a'.store tm = some (MsP.getD t default) := by
  sorry

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (P : CfaProg p)
  (vis q fto ftl mo ml fvo fvl eo el ko kl : Word) (bs : BlockShape) (formerTys : List EIdx)
  (ms : List TargetMajor) (fvs : List EIdx) (es : List NestCtorNf) (ks : List ClassField)
  {pP : ConLeche.BlockShape} {formerTysP fvsP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {esP : List ConLeche.NestCtorNf}

include hq henv P in
/-- **`class_fields_agree`'s loop refines `classFieldsAgree`, both outcomes** (twin side: con-ron's
`classFieldsAgree_spec`'s list induction; `class_nodes_agree` by `cna_ref`). -/
theorem cfaLoop_ref (k : Nat) (hk : k ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState) (j i : Word),
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs →
    decHL m fto.toNat ftl.toNat = some formerTys →
    fto.toNat + ftl.toNat ≤ iwTop m → DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms →
    mo.toNat + ml.toNat < 2 ^ 64 →
    decHL m fvo.toNat fvl.toNat = some fvs → fvo.toNat + fvl.toNat ≤ iwTop m →
    PSlR decNCN es eo el m → SPL decCF m ko.toNat kl.toNat ks → j ≤ kl →
    i.toNat + (kl.toNat - j.toNat) < 2 ^ 64 → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ms.mapM (dMajor a.store) = some MsP → Frontend.denoteEList a.store fvs = some fvsP →
    es.mapM (dCtorNf a.store) = some esP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) → (∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) →
    RefE (VerdictCtx p) (cfaE.loop1 p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i)
      (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i.toNat (ks.drop j.toNat)) a
      (fun m' _ a' => CnaPost dn vis fe env m m' a') := by
  sorry

include hq henv P in
/-- **`class_fields_agree` refines `classFieldsAgree`, both outcomes** (`cfaLoop_ref` from the
first field). -/
theorem cfa_ref (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (i0 : Word)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hfv : decHL m fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hes : PSlR decNCN es eo el m) (hks : SPL decCF m ko.toNat kl.toNat ks)
    (hi : i0.toNat + kl.toNat < 2 ^ 64) (hP : RcMR m)
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) (hfvP : Frontend.denoteEList a.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (cfaE p n m vis q fto ftl mo ml fvo fvl eo el i0 ko kl)
      (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a
      (fun v _ a' => CnaPost dn vis fe env m v.2 a') := by
  rcases n with _ | n
  · rw [cfaE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cfaE.arm1]
  have h := cfaLoop_ref hq henv P vis q fto ftl mo ml fvo fvl eo el ko kl bs formerTys ms fvs es ks
    (n + 1) hn m a 0 i0 hC hA hbs hft hftb hms hmsb hfv hfvb hes hks UInt64.zero_le
    (by simpa using hi) hP hsh hftP hmsP hfvP hesP hformer hMs
  simp only [UInt64.toNat_zero, List.drop_zero] at h
  rcases h1 : cfaE.loop1 p (n + 1) m vis q fto ftl mo ml fvo fvl eo el ko kl 0 i0 with e1 | m1 <;>
    rw [h1] at h
  · rw [cfaE.k_loop1.none]; exact h
  · rw [cfaE.k_loop1.arm1]; exact h

include hq henv P in
/-- **`class_fields_agree` refines `classFieldsAgree`** under `StageC` (the knot's core calls; the
inputs' denotations and scoping as con-ron's `classFieldsAgree_spec` asks). -/
@[refines ConRon.Arena.classFieldsAgree]
theorem classFieldsAgree_refinesC (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (i0 : Word)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hfv : decHL s₀.mem fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hes : PSlR decNCN es eo el s₀.mem) (hks : SPL decCF s₀.mem ko.toNat kl.toNat ks)
    (hi : i0.toNat + kl.toNat < 2 ^ 64) (hP : RcMR s₀.mem)
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP) (hfvP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a₀.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_agree"
      [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, i0, ko, kl]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cfaE_spec p P n s₀ vis q fto ftl mo ml fvo fvl eo el i0 ko kl)
    (cfa_ref hq henv P vis q fto ftl mo ml fvo fvl eo el ko kl bs formerTys ms fvs es ks n hn s₀.mem a₀ i0
      hC hA hbs hft hftb hms hmsb hfv hfvb hes hks hi hP hsh hftP hmsP hfvP hesP hformer hMs)) ?_
  rintro r s' ⟨hl', u, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind

end
