module

public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.DeclStep

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

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_decl`'s proof takes. -/
structure CheckDeclProg (p : Prog) : Prop where
  cd : p.lookup "check_decl" = some checkDeclL
  ax : p.lookup "check_decl_axiom" = some checkDeclAxiom
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  th : p.lookup "check_decl_thm" = some checkDeclThm
  op : p.lookup "check_decl_opaque" = some checkDeclOpaque
  qu : p.lookup "check_decl_quot" = some checkDeclQuot
  ckd : p.lookup "check_decl_kind" = some checkDeclKindL

end L.Arena
