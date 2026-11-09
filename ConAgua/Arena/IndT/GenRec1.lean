module

import ConAgua.Arena.IndT.RecGen28
import ConAgua.Arena.IndInstallSpec.GpbWSimF
public import ConRon.Bridge.Inductives.GenRec
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecCheckSpec.EraseFVarTys
public import ConAgua.Arena.IndT.RecGen28Models
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.RecClassSpec.ClassNPcOf
public import ConAgua.Arena.RecGenSpec.DecCNWords
public import ConAgua.Arena.TwinStep
public import ConAgua.Verdict.VCtx

@[expose] public section

/-!
# `genRecCheck` under `StageC`, part 1 (lane `indstaget`, helper `grc`)

What the refinements of `gen_rec_check_prep` and `gen_rec_check` (`GenRec2`, `GenRec3`) read:
`StageC.of_checkE` (`StageC` at another view and environment, from con-ron's `CheckOK` there) and
`cnfs_ref` (`classes_nfs` for both outcomes, under `StageC`, with the classes' constructors'
level-parameter slices as a conditional field, `classesNfs_refinesLp`'s); its ok half
`classesNfs_refinesC`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`StageC` at another view and environment**: the stage relation there, `CheckOK` there, the
memory's half from `AbsOK` and the store's extension. -/
theorem StageC.of_checkE {dn : NIdx → Option ConLeche.Name} {vis vis' : Word} {fe fe' : IFEnv}
    {env env' : ConLeche.Env} {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR vis' fe' m' a') (hA : AbsOK m') (hck : ConRon.Bridge.CheckOK V env' fe' a')
    (hx : ConRon.Arena.Ext a.store a'.store) : StageC dn vis' fe' env' m' a' :=
  ⟨hS, hck,
    ⟨hA.wk.2.1, hA.wk.2.2.1, hA.wk.2.2.2.1, ⟨hA.il, hA.ab, hA.wk.1⟩,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.wk.2.2.2.2⟩
-/

/-- What `classes_nfs` gives besides the twin's classes `ys` (from `m`): the result slice, the stage,
the growth, the memos, `AbsOK`. -/
structure CnfsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (m' : Mem) (ys : List TargetMajor) (a' : AState) : Prop where
  slice : PSlR decTM ys (r.headD 0) (r.tail.headD 0) m'
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'

/-- **`classes_nfs` refines `classesNfs`, both outcomes** (under `StageC`, the inputs' denotations and
scoping as con-ron's `classesNfs_spec` asks): `iw_alloc` (class `0` on failure), then the loop
(`cns_ref`). -/
theorem cnfs_ref {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis q fto ftl tblo tbll mo ml : Word}
    {bs : BlockShape} {formerTys : List EIdx} {tbl : List NestCtorNf} {ms : List TargetMajor}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hbs : BSOK m q.toNat bs)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tblo tbll m) (hms : PSlR decTM ms mo ml m) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor} (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP) (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (cnfsE p n m vis q fto ftl tblo tbll mo ml)
      (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a
      (fun v ys a' => CnfsPost dn vis fe env m v.1 v.2 ys a') := by
  sorry

/-- **`classes_nfs` refines `classesNfs`** under `StageC` (`cnfs_ref`'s ok half). -/
@[refines ConRon.Arena.classesNfs]
theorem classesNfs_refinesC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor} (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP) (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀ ∧
      PSlR decTM (AM.res (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cnfsE_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml)
    (cnfs_ref hkp henv P n hn hC hA hbs hft hftb htbl hms hP hsh hftP htblP hmsP hformer hMs)) ?_
  rintro r s' ⟨hl, ys, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres]; exact hR.slice, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩


end L.Ind
