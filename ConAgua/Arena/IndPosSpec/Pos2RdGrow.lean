import ConAgua.Arena.IndIface

/-!
# Pos2RdGrow

`pos2_rd_grow`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem pos2_rd_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hx : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by simp only [rdW]; rw [hg.2.2.1 _ hx]

end L.Ind

end
