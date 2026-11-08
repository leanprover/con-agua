module

public import ConAgua.Arena.DeclRec

@[expose] public section

/-!
# `env_push`'s frame

The value checks end with `env_push`, which changes the environment; it writes the index rows,
`ECON` and `CTL[128]` only (`envPushW_frame`), so the core's memos (`CoreMemos`) stay well formed
across it.
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

end L.Arena
