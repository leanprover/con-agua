import ConAgua.Arena.WhnfBase
import ConAgua.Checker.Entry
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen

/-!
# `basis_pin_hit(off, len)`: the loops and their models (lane `indproofs4`, helper `bph`)

`L.Checker.basisPinHitL` (`Checker/Entry.lean`) tries the kinds `0`‥`3` (`eqK`, `natK`, `emptyK`,
`falseK`): the pinned block (`rom_basis_decls(k)`, an `IW` slice), the name pre-filter (the
member names, word `1` of each constant record, compared pointwise: the inner loop), then the block
copied to `IW` (`er_to_iw`) and compared (`canon_eq_list`). The model `bphW` and its loops
(`bphW.loop1` over the kinds, `bphW.loop2` the name pre-filter) are generated (`l_model`).
The refinement is `IndRealBph2.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The model -/

l_model bph_specW (p : Prog) (hp : p.lookup "basis_pin_hit" = some L.Checker.basisPinHitL)
  fns [hp ↦ bphW list]
  specs [callW_spec p n "rom_basis_decls", callW_spec p n "er_to_iw", callW_spec p n "canon_eq_list"]
  grind [arena_grind] extra [ld64_rd_spec] simp []

end L.Ind
