module

public import ConAgua.Arena.IndexRel
public import ConAgua.Arena.CheckerL
public import ConAgua.Arena.EnvFlags
import all ConAgua.Arena.CheckerL
import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

@[expose] public section

/-!
# The frozen stream index: `lit_from`, `index_freeze`, `from_le`

The twin freezes a stream's index past its last record (`IStreamIndex.freeze`, upstream #579): the
ten literal names off the pin table into the base (`IFBase.lits`), and for each literal flag the
first counter from which a record's view holds its names (`litFrom`: `natFrom`, `strFrom`). L
writes the names into `CTL[162‥171]` and the thresholds into `CTL[172]`, `CTL[173]` (`optW`:
`FrozenR`); a job sets its flags by one comparison each (`fromLe`, `from_le`). Generated models
and their refinements.
-/

set_option experimental.vcgen true

open ConRon.Arena Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The models (generated) -/

/-- **`from_le` is its model** (generated). -/
l_model fromLe_specW (p : Prog) (hp : p.lookup "from_le" = some fromLeL)
  fns [hp ↦ fromLeW]
  grind [arena_grind]

/-- **`lit_from` is its model** (generated; the recursive call through its own run). -/
l_model litFrom_specW (p : Prog) (hp : p.lookup "lit_from" = some litFromL)
  fns [hp ↦ litFromW]
  specs [callW_spec p n "base_row_get", callW_spec p n "lit_from"]
  grind [arena_grind]

/-- **`index_freeze` is its model** (generated). -/
l_model indexFreeze_specW (p : Prog) (hp : p.lookup "index_freeze" = some indexFreezeL)
  fns [hp ↦ indexFreezeW]
  specs [callW_spec p n "pin_at", callW_spec p n "lit_from"]
  grind [arena_grind]

end L.Arena
