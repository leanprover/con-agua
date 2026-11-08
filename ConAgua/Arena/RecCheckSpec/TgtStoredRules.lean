module

import ConAgua.Arena.IndSumSpec.TsrW
public import ConAgua.Arena.IndSumSpec.SumRules
public import ConAgua.Arena.RecCheckSpec.TsrLook

@[expose] public section

/-!
# TgtStoredRules: `ConRon.Arena.tgtStoredRules`

The refinement theorems `tgtStoredRules_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified


end L.Ind

end
