module

public import ConRon.Bridge.Inductives.StructParts
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx
public import ConAgua.Verdict.IndBTpd
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConRon.Bridge.Inductives.RecCheck
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.RecCheckTpd
import ConAgua.Arena.RecCheckSpec.TmFields
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecCheckSpec.TcmLook
public import ConAgua.Arena.RecClassSpec.ClassNPcOf
import all ConAgua.Arena.RecCheck

@[expose] public section
/-!
# `target_class_match`: one model and one refinement for both outcomes

`tcmE` (`l_model … unified`): `target_params_def_eq` through its unified model (`pdeE`), the
callees outside the verdict closure (`lvls_eq_c`, the shape's member names and parameters, `param_levels`,
`target_holes`) through their `Option` models. `tcm_ref` refines `targetClassMatch` for both
outcomes; its ok half is `targetClassMatch_refinesC`; the callers' refinements (`tmn_ref`,
`tka_ref`) apply it to their unified models' calls.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tcmE_spec (p : Prog) (hL : TcmLook p)
  fns [hL.tcm ↦ tcmE]
  specs [callW_spec p n "lvls_eq_c", blockShapeMemberNames_spec p hL.ha hL.mnc hL.mn n,
    blockShapeLps_spec p hL.ha hL.erc hL.eri hL.lps n,
    plW_spec p hL.ha hL.ic hL.sc hL.sg hL.pf hL.pp hL.ip hL.plg hL.pl hL.il n,
    targetHoles_spec p hL.ff hL.fp hL.iff hL.ic hL.ha hL.sc hL.th n, pdeE_spec p hL.tp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `target_holes`' model keeps the arena. -/
theorem thW_afr : ∀ (n : Nat) {m m' : Mem} {tyo tyl base : Word} {r : List Word},
    thW n m tyo tyl base = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [thW] at h
  | n + 1, m, m', tyo, tyl, base, r, h => by
    by_cases hl : tyl = 0
    · rw [thW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact AFr.refl _
    rw [thW_cons (h := hl)] at h
    rcases hf : fvinternW m base (rdW (m.arr64 IW) tyo) with _ | ⟨v, m1⟩ <;> rw [hf] at h <;>
      try (simp only [thK1, reduceCtorEq] at h; done)
    by_cases hb : 4294967296 ≤ v
    · rw [thK1_big (h := hb)] at h; cases h
    rw [thK1_ok (h := hb)] at h
    rcases hg : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with _ | ⟨r2, m2⟩ <;> simp only [hg, thK2, reduceCtorEq] at h
    rcases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, thK3, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((fvinternW_afr hf).trans (thW_afr n hg)).trans (consW_afr hc)

/-- What `target_class_match` gives besides the twin's result `c` (from `m`): the result word, the
stage invariant, the growth. -/
structure TcmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : Word) (m' : Mem) (c : Bool) (a' : AState) : Prop where
  res : (r != 0) = c
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_class_match` refines `targetClassMatch`, both outcomes** (twin side: con-ron's
`targetClassMatch_spec`'s proof): `lvlsEq?` (`lvlsEqC_simC`), the shape's member names and
parameters (L only), `paramLevels`, `targetHoles`, then `targetParamsDefEq` (`pde_ref`). -/
theorem tcm_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl lvls edso edsl : Word} {bs : BlockShape}
    {formerTys pfvs ds eds : List EIdx} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hds : HSl0 m dso dsl ds) (heds : HSl0 m edso edsl eds)
    (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (husP : denoteLs a.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a.store ds = some dsP)
    (hlvP : denoteLs a.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    RefE (VerdictCtx p) (tcmE p n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl)
      (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  sorry

include hq henv in
/-- **`target_class_match` refines `targetClassMatch`** under `StageC` (`tcm_ref`'s ok half). -/
@[refines ConRon.Arena.targetClassMatch]
theorem targetClassMatch_refinesC (hL : TcmLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q fto ftl pfo pfl us dso dsl lvls edso edsl : Word)
    (bs : BlockShape) (formerTys pfvs ds eds : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (heds : HSl0 s₀.mem edso edsl eds) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP)
    (hlvP : denoteLs a₀.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a₀.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tcmE_spec p hL n s₀ vis q fto ftl pfo pfl us dso dsl lvls edso edsl)
    (tcm_ref hq henv n hn hC hA hbs hus hlv hft hftb hpf hds heds hP hsh hftP hpfP husP hdsP
      hlvP hedsP hformer hpw)) ?_
  rintro r s' ⟨hl', c, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hR.res, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind

end
