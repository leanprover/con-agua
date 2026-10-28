import ConAgua.Arena.RecCheckSpec.TcmLook

/-!
# TcmF

`TmnLook`.
-/

noncomputable section


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of `target_major_nfs`. -/
structure TmnLook (p : Prog) : Prop where
  tcm : TcmLook p
  chn : p.lookup "ctors_have_name" = some ctorsHaveName
  tmn : p.lookup "target_major_nfs" = some targetMajorNfs

end L.Ind

end
end
