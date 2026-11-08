module

import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndSumSpec.SoaW
import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.RecCheckSpec.TargetMajorDefault
import ConAgua.Arena.RecCheckSpec.Tmn
public import ConAgua.Verdict.IndBTcm
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecCheckSpec.TmFields
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
public import ConAgua.Arena.RecGenSpec.DecB
import all ConAgua.Arena.RecCheck

@[expose] public section
/-!
# `target_major_nfs`: one model and one refinement for both outcomes

`tmnE` (`l_model … unified`): the recursive call through the model itself, `target_class_match`
through its unified model (`tcmE`), `ctors_have_name` and `sl_cons` (outside the verdict closure)
through their `Option` models. `tmn_ref` refines `targetMajorNfs` for both outcomes; its ok half
is `targetMajorNfs_refinesC`, and `classes_nfs`' loop's refinement (`cns_ref`, `IndT/RecGen28`)
reads both halves from the run.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmnE_spec (p : Prog) (hL : TmnLook p)
  fns [hL.tmn ↦ tmnE]
  specs [ctorsHaveName_spec p hL.chn n, tcmE_spec p hL.tcm n,
    slCons_specW p hL.tcm.ha hL.tcm.ic hL.tcm.sc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `target_major_nfs` gives besides the twin's result `ys` (from `m`, the table `nfs` at
`nfo`, `nfl`): the kept entries' slice, the stage invariant, the growth; and, when the table's
pointers are those of `mb`, where the kept slice lies and that its pointers are `mb`'s too. -/
structure TmnPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (nfo nfl : Word) (nfs : List NestCtorNf) (r : List Word) (m' : Mem)
    (ys : List NestCtorNf) (a' : AState) : Prop where
  slice : PSlR decNCN ys (r.headD 0) (r.tail.headD 0) m'
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'
  ptrs : ∀ mb ps, decNL m nfo.toNat nfl.toNat = some ps → PtrsB mb ps nfs →
    (r.tail.headD 0 = 0 ∨ iwTop m ≤ (r.headD 0).toNat) ∧
    ∃ ps', decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ps' ∧ PtrsB mb ps' ys

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_major_nfs` refines `targetMajorNfs`, both outcomes** (twin side: con-ron's
`targetMajorNfs_spec`'s list induction): the tail first (its `CoreStep` from con-ron's spec on the
tail's run), the name test (L only, `chnW_ok`), `targetClassMatch` (`tcm_ref`), the kept entry
consed (L only). -/
theorem tmn_ref (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ {m : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf} {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf},
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds →
    DecB (fun m => decPL m (decCN m) cto.toNat ctl.toNat) m ctors → cto.toNat + ctl.toNat < 2 ^ 64 →
    PSlR decNCN nfs nfo nfl m → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    Frontend.denoteEList a.store pfvs = some pfvsP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → dCtors a.store ctors = some ctorsP →
    nfs.mapM (dCtorNf a.store) = some nfsP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    (∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) →
    RefE (VerdictCtx p) (tmnE p n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl)
      (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a
      (fun v ys a' => TmnPost dn vis fe env m nfo nfl nfs v.1 v.2 ys a') := by
  sorry

include hq henv in
/-- **`target_major_nfs` refines `targetMajorNfs`** under `StageC` (`tmn_ref`'s ok half). -/
@[refines ConRon.Arena.targetMajorNfs]
theorem targetMajorNfs_refinesC (hL : TmnLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word)
    (bs : BlockShape) (formerTys pfvs ds : List EIdx) (ctors : List (IConstantVal × Nat))
    (nfs : List NestCtorNf) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hus : H us)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (hct : PSlR decCN ctors cto ctl s₀.mem) (hnf : PSlR decNCN nfs nfo nfl s₀.mem) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP) (hctP : dCtors a₀.store ctors = some ctorsP)
    (hnfP : nfs.mapM (dCtorNf a₀.store) = some nfsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀ ∧
      PSlR decNCN (AM.res (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀)
        (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  sorry

end sims

end L.Ind

end
