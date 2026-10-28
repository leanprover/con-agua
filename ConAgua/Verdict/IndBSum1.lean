import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.GrindAttr
/-!
# Error refinements of the direct sums' field sorts (lane `verdicts-b`, helper `ib`)

`check_struct_field_sorts_i`'s claim as a `CoreSpecE` (from `fsorts_ref`, `Arena/IndT/Sum3`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hLC hLT hnv hcE in
/-- **`check_struct_field_sorts_i`'s error claim** (the hypotheses of
`checkStructFieldSortsI_refinesC`, and the core stubs' error claims): a failing call of class
`1`/`2` claims that the twin's `checkStructFieldSortsI` fails. -/
theorem checkStructFieldSortsI_claim (hg : p.lookup "sl_get" = some slGet)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
    (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
    (hia : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL) (hftd : FtdF p)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (isProp large s nP fo fl io il nW : Word)
    (fvs idxArgs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hidx : decHL s₀.mem io.toNat il.toNat = some idxArgs) (hib : io.toNat + il.toNat ≤ iwTop s₀.mem)
    (hs : H s) {sP : ConLeche.Level} (hsP : denoteL a₀.store.ls (decI s) = some sP)
    (hnj : nP.toNat + nW.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hws : ∀ i, i < nW.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    CoreSpecE p (n + 1) "check_struct_field_sorts_i" [vis, isProp, large, s, nP, fo, fl, io, il, nW]
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs nW.toNat)
      s₀ a₀ :=
  RefE.coreSpecE (fsortsE_spec p hp hgo hia hftd hb (n + 1) s₀ vis isProp large s nP fo fl io il nW) hnv ⟨hnv, hcE⟩
    (fsorts_ref hq henv hLC hLT hg hpw het hc n hn _ a₀ isProp large s nP fo fl io il nW fvs idxArgs hC hA
      hfvs hfb hidx hib hs hsP hnj hfP hws)

end sims

end L.Ind
