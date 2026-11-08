module

import ConAgua.Arena.IndT.RecCheckK53
import ConAgua.Arena.RecCheckSpec.Tka
public import ConAgua.Verdict.IndBTcm
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecCheckSpec.EeW2
import ConAgua.Arena.RecCheckSpec.TmFields
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecCheckSpec.EeW
public import ConAgua.Arena.RecCheckSpec.EqWDec
public import ConAgua.Arena.RecCheckSpec.K53Look
import all ConAgua.Arena.RecCheck

@[expose] public section
/-!
# `target_k53_args`: one model and one refinement for both outcomes

`tkaE` (`l_model … unified`): `target_class_match` through its unified model (`tcmE`), the callees
outside the verdict closure (`erase_each`, `sl_eq`, `intern_const`, `mk_app_n_f`, the shape's
member names, `nest_occ`) through their `Option` models. `tka_ref` refines `tkArgs` (the arguments'
part of `targetK53`) for both outcomes; `target_k53_heads`' refinement reads it through the model.
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

-- `cut 3`: the code after the parameter count and the two index slices' `if`s has its own step
-- theorem (`tkaE_spec.tail`), so the step does not run through it once per slice combination
-- (21.5 s -> 4.9 s); `finish (gen := 20)`: the tail's generation depth (the default 8 leaves the
-- early `return 0` after `sl_eq` open)
l_model tkaE_spec (p : Prog) (hL : K53Look p)
  fns [hL.tka ↦ tkaE]
  specs [ee_spec p hL n, slEq_spec p hL.eq n, internConst_spec p hL.cf hL.cp hL.ic n, mknF_spec p hL.ad n,
    blockShapeMemberNames_spec p hL.tmn.tcm.ha hL.tmn.tcm.mnc hL.tmn.tcm.mn n, noF_spec p hL n,
    tcmE_spec p hL.tmn.tcm n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [] gen 20 heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem] cut 3

/-- `tkaE` after the parameter count, the two index slices as `if`s. -/
theorem tkaE_succ (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl Mc ip usp lao lal mao mal : Word) :
    tkaE p (n + 1) m vis q fto ftl Mc ip usp lao lal mao mal =
      tkaE.j2 p n vis q fto ftl Mc ip usp lao lal (rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4))
        (if mal < rdW (m.arr64 IW) (Mc + 4) then mao else mao + rdW (m.arr64 IW) (Mc + 4))
        (if mal < rdW (m.arr64 IW) (Mc + 4) then 0 else mal - rdW (m.arr64 IW) (Mc + 4)) m := by
  by_cases h1 : lal < rdW (m.arr64 IW) (Mc + 4) <;> by_cases h2 : mal < rdW (m.arr64 IW) (Mc + 4)
  · rw [tkaE.arm1 (hc1 := h1), tkaE.j1.arm1 (hc1 := h2), ite_eq_left h1, ite_eq_left h1, ite_eq_left h2, ite_eq_left h2]
  · rw [tkaE.arm1 (hc1 := h1), tkaE.j1.arm2 (hc1 := h2), ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, ite_eq_right h2]
  · rw [tkaE.arm2 (hc1 := h1), tkaE.j1.arm1 (hc1 := h2), ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]
  · rw [tkaE.arm2 (hc1 := h1), tkaE.j1.arm2 (hc1 := h2), ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]

/-- `tkaE` after `sl_eq` found the erased indices equal: the leaf's parameters as an `if`. -/
theorem tkaE_slEq (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (m : Mem) (e : Word)
    (he : e ≠ 0) :
    tkaE.k_sl_eq p n vis q fto ftl Mc ip usp lao lal K m (.ok e) =
      tkaE.j3 p n vis q fto ftl Mc ip usp lao (if lal < K then lal else K) m := by
  by_cases h : lal < K
  · rw [tkaE.k_sl_eq.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ he h, ite_eq_left h]
  · rw [tkaE.k_sl_eq.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ he h, ite_eq_right h]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_k53_args` refines `tkArgs`, both outcomes** (twin side: con-ron's `targetK53_spec`,
the arguments' part): the indices erased (`eraseAll_spec`), compared, the leaf's class
(`internConstE_run`, `mkAppN_run`; `nestOcc` read-only), then `targetClassMatch` (`tcm_ref`). -/
theorem tka_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q fto ftl Mc ip usp lao lal mao mal : Word}
    {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {la ma : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hip : H ip) (hus : H usp) (hla : HSl0 m lao lal la) (hma : HSl0 m mao mal ma) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP laP maP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {I'P : ConLeche.Name} {us'P : List ConLeche.Level}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hipP : denoteN a.store.ns (decI ip) = some I'P)
    (husP : denoteLs a.store.lss (decI usp) = some us'P)
    (hlaP : Frontend.denoteEList a.store la = some laP)
    (hmaP : Frontend.denoteEList a.store ma = some maP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (tkaE p n m vis q fto ftl Mc ip usp lao lal mao mal)
      (tkArgs fe bs formerTys TM (decI ip) (decI usp) la ma) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  sorry

end sims

end L.Ind
