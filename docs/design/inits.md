# Lane `inits`: initial-state refinements

Census before: 9 real todo targets (initial states). After: 0; `todo` = `pending` in every phase.

`ConAgua/Arena/InitLink.lean`, all at `initMem sizes` (zeroed memory), each a `@[refines]`:
* `Memos.empty`: `MemosR` (from `arenaR_init`).
* `ModeMemos.empty`: the six `ModeR` relations, empty map, bank 0 and stored eager bank 1.
* `Caches.empty`: `CoreR` (all eleven core memos; needs `CTL` size >= 120, a stronger hypothesis than
  `arenaR_init`'s 64).
* `Pins.empty`: flag word 0 and `PinsR` (which at flag 0 relates every table; the claim is the flag).
* `AState.init`: `ArenaD` and `CoreR` and `PinsR` together at `AState.init EStore.empty`, plus the
  structural fact for every store.
* `IEnv.empty`: `envConsts` decodes to `IEnv.empty.consts`. `mkIFEnv`/`mkIFEnvGo`: `EnvR.init`.
* `IConstantInfo.name`: `decCI_name` restated (the name is the handle in word `p + 1` of the record).

The `orElseAttempt` cluster (5 targets) is n/a in `docs/not-needed.md` (D5: one pin variant).
