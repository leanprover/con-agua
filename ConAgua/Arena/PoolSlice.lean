
/-!
# Slices of the pool as keys

Moved into `ConAgua/Arena/LitRefine.lean` ("Slices of the pool as keys"): the `lit` store's own
`strVal` arm needs `sliceL` and the slice-key lemmas (`slice_key`, `slice_key_hash`) directly, next
to `eqW_iff`/`hashN_congr`, which `LitRefine.lean` already has, so there is no room for a separate
layer between it and this file. This file now just re-exports `LitRefine.lean` for the level-list
store (`LsRefine.lean`) and the name store's `str` table (`NStrRefine.lean`), which import it for
`sliceL`, `slice_key`, `slice_key_hash`, `Agree.sliceL` and (for `NStrRefine.lean`) `strWords`/
`strWords_inj`.
-/
