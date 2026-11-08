module

import ConAgua.Arena.StrLitChar
import ConAgua.Arena.StrLitList
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DefEqMid
import ConAgua.Arena.InferBodyLet
import ConAgua.L.LocNF
import Std.Tactic.BVDecide.Normalize.Bool
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.StrLitBase
import all ConAgua.Arena.StrLit

@[expose] public section

/-!
# `str_lit_stored` under `CoreS`

`str_lit_stored(vis)` is `nat_lit_stored` and the presence of the seven string-support names
(con-leche task #480: what they are is the declarations' own check, `lit_shape_ok`). The proof of
the retired `str_lit_supported` chain went with it; this one is owed (lane ronsync2, stage 3).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section calls
variable (p : Prog) (hp : StrLitProg p)

/-- **`str_lit_stored(vis)` refines `strLitStored fe`.** -/
@[refines ConRon.Arena.strLitStored]
theorem strLitStored_core : StrLitStoredOK p := by
  sorry

end calls

end L.Arena
