module

public import ConAgua.Arena.DeclCanonLvl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon
public import ConAgua.Arena.IndView

@[expose] public section

/-!
# The canonical expression comparison in L (lane `decls3`, helper `decls3-canon`)

`canon_expr_eq` against `canonExprEq`. A literal is compared by handle in L and by value in the
twin: the two agree because the expression store hash-conses literals (`LitInj`, a hypothesis).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `canon_expr_eq`** (`ceW`). -/
l_model canonExprEq_spec (p : Prog) (hp : CanonProg p)
  fns [hp.get "canon_expr_eq" ↦ ceW]
  specs [eView_spec p (hp.get "e_view") n, canonLevelEq_spec p hp n, canonLevelsEq_spec p hp n]
  grind [arena_grind]

end L.Ind
