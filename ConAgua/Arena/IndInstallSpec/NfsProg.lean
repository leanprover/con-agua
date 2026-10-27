import ConAgua.Arena.IndInstallSpec.Cons
import ConAgua.Arena.IndPosSpec.KlB
import ConAgua.Arena.IndPosSpec.UnW2

/-!
# NfsProg

`NfsProg`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_positivity_nfs_member` -/

/-- The lookups of the normal forms' builders. -/
structure NfsProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec2 : p.lookup "rec2" = some rec2
  mem : p.lookup "check_block_positivity_nfs_member" = some checkBlockPositivityNfsMember
  nfs : p.lookup "check_block_positivity_nfs" = some checkBlockPositivityNfs

end L.Ind
