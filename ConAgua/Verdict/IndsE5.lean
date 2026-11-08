module

public import ConAgua.Verdict.IndsE4
public import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.SumInstall
public import ConRon.Bridge.Inductives.BlockInstall
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall

@[expose] public section
/-!
# `check_block_agree`: one model and one refinement for both outcomes

`cbagE` (`l_model … unified`): member 0's telescope through its `Option` model, each member's
agreements through `cbaoE`. `cbag_ref` refines `checkBlockAgree` for both outcomes, by induction
on the fuel: member 0's unopened telescope is an internal abort, a member's agreements by
`cbao_ref`, the rest by induction. `checkBlockAgree_refinesC` is its ok half.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_agree`'s model, both outcomes**: member 0's telescope through its `Option`
model, each member's agreements through `cbaoE`. -/
l_model cbagE_spec (p : Prog) (hf : p.lookup "check_block_agree" = some checkBlockAgree)
  (ho : p.lookup "check_block_agree_one" = some checkBlockAgreeOne)
  (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
  fns [hf ↦ cbagE]
  specs [callW_spec p n "open_pis_at_fvars_f", cbaoE_spec p ho hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)

include hq henv hOpf hLC in
/-- **`check_block_agree` refines `checkBlockAgree`**, both outcomes (member 0's telescope opened
per member, as the twin does; the denotations as con-ron's `checkBlockAgree_specF` asks). -/
theorem cbag_ref (hP : AgreeProg p) (nP c0 s0 : Word) (cv0 : IConstantVal) {cv0P : ConLeche.ConstantVal}
    {s0P : ConLeche.Level} (h0 : ConLeche.Expr.WScoped 0 cv0P.type) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (rest : List (IConstantVal × LIdx))
      (cvsP : List (ConLeche.ConstantVal × ConLeche.Level)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCVp m c0.toNat) m cv0 → H s0 →
    PSlR decTele rest o l m →
    Frontend.denoteCV a.store cv0 = some cv0P → denoteL a.store.ls (decI s0) = some s0P →
    rest.mapM (ConRon.Bridge.Inductives.BI.dCvL a.store) = some cvsP →
    (∀ x ∈ cvsP, ConLeche.Expr.WScoped 0 x.1.type) →
    RefE (VerdictCtx p) (cbagE p n m vis nP c0 s0 o l)
      (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a
      (fun v _ a' => AgreePost dn vis fe env m a v.2 a') := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hq henv hOpf hLC in
/-- **`check_block_agree` refines `checkBlockAgree`** under `StageC` (the knot's
`is_def_eq_core`; the denotations as con-ron's `checkBlockAgree_specF` asks): member 0's constant
decoded below the tops, its sort a handle, the other members a slice of checked formers. -/
@[refines ConRon.Arena.checkBlockAgree]
theorem checkBlockAgree_refinesC (hP : AgreeProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP c0 s0 o l : Word)
    (cv0 : IConstantVal) (rest : List (IConstantVal × LIdx)) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hc0 : DecB (fun m => decCVp m c0.toNat) s₀.mem cv0) (hs0 : H s0)
    (hrest : PSlR decTele rest o l s₀.mem) {cv0P : ConLeche.ConstantVal} {s0P : ConLeche.Level}
    {cvsP : List (ConLeche.ConstantVal × ConLeche.Level)}
    (hc0P : Frontend.denoteCV a₀.store cv0 = some cv0P) (h0 : ConLeche.Expr.WScoped 0 cv0P.type)
    (hs0P : denoteL a₀.store.ls (decI s0) = some s0P)
    (hcvs : rest.mapM (ConRon.Bridge.Inductives.BI.dCvL a₀.store) = some cvsP)
    (hws : ∀ x ∈ cvsP, ConLeche.Expr.WScoped 0 x.1.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_agree" [vis, nP, c0, s0, o, l]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (cbagE_spec p hP.agree hP.one hP.lvl n s₀ vis nP c0 s0 o l)
    (cbag_ref hq henv hOpf hLC hP nP c0 s0 cv0 h0 n hn _ a₀ o l rest cvsP hC hA hc0 hs0 hrest hc0P hs0P hcvs hws))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ =>
      let ⟨hok, hst, _⟩ := AM.of_run_ok _ _ _ _ hrun
      ⟨hl, hok, hst ▸ hR.stage, hR.grow, hR.abs⟩
-/

end sims

end L.Ind
