import ConAgua.Arena.IndPosSpec.PiBWStage
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# NtyLook

`viewLsLen_specE`, `NtyLook`, `NitLook`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_inst_type(_ty)`: word models -/

theorem viewLsLen_specE (p : Prog) (hl : p.lookup "ls_node" = some lsNode)
    (hp : p.lookup "view_ls_len" = some viewLsLenL) (n : Nat) (s₀ : St) (us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "view_ls_len" [us]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ lsNodeW s₀.mem us ≠ [] ∧
      r = [1, (lsNodeW s₀.mem us).tail.headD 0]; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, viewLsLenL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lsNode_spec p hl n] <;>
      finish (gen := 20)

/-- The lookups of `nest_inst_type_ty`. -/
structure NtyLook (p : Prog) : Prop where
  hi1 : I1Prog p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hls : p.lookup "ls_node" = some lsNode
  hvl : p.lookup "view_ls_len" = some viewLsLenL
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hv : p.lookup "e_view" = some eView
  hip : p.lookup "inst_pis_with" = some instPisWith
  hp : p.lookup "nest_inst_type_ty" = some nestInstTypeTyL
  hst : StripProg p

/-- The lookups of `nest_inst_type`. -/
structure NitLook (p : Prog) : Prop where
  ty : NtyLook p
  no : NoLook p
  hc2 : p.lookup "iw_copy" = some iwCopy
  hs : p.lookup "sl_cons" = some slCons
  hpb : p.lookup "pi_binders" = some piBinders
  hoa : p.lookup "nest_occ_any" = some nestOccAnyL
  hlf : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  hp : p.lookup "nest_inst_type" = some nestInstTypeL

end L.Ind

end
