import ConAgua.Arena.IndInstallSpec9
import ConAgua.Arena.RecGenSpec.KofProg

/-!
# KeysProg

`KeysProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callee runs as `Sim`s -/

/-- The lookups of `check_block_classes_keys`. -/
structure KeysProg (p : Prog) : Prop extends KofProg p where
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  keys : p.lookup "check_block_classes_keys" = some checkBlockClassesKeys

end L.Ind

end
