module

public import ConAgua.Arena.RecCheckSpec.DecHLTruncMBound
import ConAgua.Arena.IndT.Lift
public import ConRon.Bridge.Inductives.RecCheck
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.RecCheckSpec.RcLook
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.TwinStep
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# `target_pin_tys` (one model and one refinement for both outcomes), `target_major_pins`' model

`tptE` (`l_model … unified`): `infer_type_core` through its run, the recursion through the model.
`tpt_ref` refines `targetPinTys` for both outcomes; its ok half is `targetPinTys_refinesC`.

`tmpE` (`l_model … unified`): `target_pin_tys` through `tptE`, `intern_const` and `mk_app_n_f`
lifted, `infer_type_core` through its run. Its refinement is `tmp_ref` (`IndT/RecCheckPins`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tptE_spec (p : Prog) (hf : p.lookup "target_pin_tys" = some targetPinTys)
  fns [hf ↦ tptE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified

l_model tmpE_spec (p : Prog) (P : TmpProg p)
  fns [P.tmp ↦ tmpE]
  specs [tptE_spec p P.tpt n, internConst_spec p P.cf P.cp P.ic n, mknF_spec p P.ad n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `target_pin_tys` gives besides the twin's run (from `m`): the stage invariant, the growth,
the abstraction memos. -/
structure TptPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_pin_tys` refines `targetPinTys .verified`, both outcomes** (twin side: con-ron's
`targetPinTys_spec`'s proof): `inferTypeCore` (`inferC_rsim`, the core stubs' claim), then the
tail. -/
theorem tpt_ref (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m : Mem} {a : AState} {d xo xl : Word} {xs : List EIdx} {xsP : List ConLeche.Expr},
    StageC dn vis fe env m a → AbsOK m → HSl0 m xo xl xs →
    Frontend.denoteEList a.store xs = some xsP → (∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) →
    RefE (VerdictCtx p) (tptE p n m vis d xo xl) (ConRon.Arena.targetPinTys V fe d.toNat xs) a
      (fun v _ a' => TptPost dn vis fe env m v.2 a') := by
  sorry

include hq henv in
/-- **`target_pin_tys` refines `targetPinTys .verified`** under `StageC` (`tpt_ref`'s ok half; the
knot's `infer_type_core`; the parameters' denotations and scoping as con-ron's `targetPinTys_spec`
asks). -/
@[refines ConRon.Arena.targetPinTys]
theorem targetPinTys_refinesC (hp : p.lookup "target_pin_tys" = some targetPinTys) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (d xo xl : Word) (xs : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs)
    (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) {xsP : List ConLeche.Expr}
    (hxsP : Frontend.denoteEList a₀.store xs = some xsP)
    (hw : ∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pin_tys" [vis, d, xo, xl]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tptE_spec p hp n s₀ vis d xo xl)
    (tpt_ref hq henv n hn hC hA (HSl0.of hxs hbt) hxsP hw)) ?_
  rintro r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind

end
