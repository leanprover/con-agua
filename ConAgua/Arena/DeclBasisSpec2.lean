module

import ConRon.Bridge.Checker.Basis
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.Pins

@[expose] public section

/-!
# `check_basis_decl(vis, kind)` refines `checkBasisDecl` (lane `decls3`)

The quotient block first requires the pinned `Eq` basis (`find_is` against `rom_ci(0)`, helper
`decls3-canon`'s `findIs_spec`), then the annotated block (`rom_basis_decls_a(kind)`) is installed
(`install_basis_decls`, `DeclBasisSpec.lean`). Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

end L.Arena
