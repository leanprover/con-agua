module

public import ConAgua.Arena.DeclArmAxiom
public import ConAgua.Arena.DeclNatGateSpec
public import ConAgua.Arena.DeclDivModSpec.RomPinSets
public import ConAgua.Arena.DeclArmLoop
public import ConAgua.Arena.DeclNatOpEq
public import ConAgua.Arena.DeclReducePin
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# `check_decl`'s arms at the loop's relation (lane `decls3`)

`check_decl(i, vis)` reads the record's kind word and calls one arm (`DeclStep.lean`). This file
has the program bundle `CheckDeclProg` the arms' proofs take and `substC0_of`. The arms' specs at
the loop's relation are the `StageT` ones in `CheckerT.lean` (`checkDecl_loopT`, lanes `loopt2`,
`loopt3`); their `StageR` versions (`ArmSpec`, with the quotient readers' preconditions open) are
gone with the interim contract.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_decl`'s proof takes. -/
structure CheckDeclProg (p : Prog) : Prop where
  cd : p.lookup "check_decl" = some checkDeclL
  ax : p.lookup "check_decl_axiom" = some checkDeclAxiom
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  th : p.lookup "check_decl_thm" = some checkDeclThm
  op : p.lookup "check_decl_opaque" = some checkDeclOpaque
  qu : p.lookup "check_decl_quot" = some checkDeclQuot
  arm : ArmProg p
  val : ValProg p
  crp : CrpProg p
  quot : QuotProg p
  axp : AxProg p
  /-- The definition arm's structural-`Nat` gate: its program (`DeclNatGateSpec.lean`'s
  `natGateSpec` proves `NatGateSpec` from these). -/
  natSub : NatSubProg' p
  natText : StepIn p natGateFns
  /-- The definition arm's `Nat.div`-family pin gate (helper `decls3-divmod`'s `divGateSpecD`
  proves `DivGateSpec` from these, with the walks' refinements `substC0_of`, `substCAll_of`): its
  program and its text's write set. -/
  dm : DmProg10 p
  dgClosed : StepIn p dgFns

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `subst_const0` at the walk fuel: helper `decls3-nat`'s `sc0_ref`. -/
theorem substC0_of {p : Prog} (hN : NatSubProg p) :
    ∀ dn vis fe, SubstC0 p dn vis fe := by
  sorry

-/

end L.Arena
