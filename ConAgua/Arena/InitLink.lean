import ConAgua.Arena.DerRel
import ConAgua.Census.Attr

/-!
# The initial store (lane `front3`)

The twin's checker starts from `AState.init EStore.empty`; L starts from the harness's memory,
every array zeroed (`initMem`). `arenaD_init` relates the two: the L "code" for `EStore.empty` is
the zeroed memory. (Only the store: `ArenaD` says nothing about the memos, so `AState.init` and
`Memos.empty` stay with their callers.)
-/

namespace L.Arena

open ConRon.Arena

/-- **The zeroed L memory is the twin's empty store** (`arenaD_init`). -/
@[refines ConRon.Arena.EStore.empty]
theorem estoreEmpty_refines (sizes : List Nat) (hlen : 64 ≤ sizes.length)
    (hctl : 64 ≤ sizes[1]?.getD 0) (hpool : sizes[0]?.getD 0 < 2 ^ 63) :
    ArenaD (initMem sizes) (AState.init EStore.empty) :=
  arenaD_init sizes hlen hctl hpool

end L.Arena
