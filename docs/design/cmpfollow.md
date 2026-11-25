# Lane cmpfollow: follow-ups after compare2

Lane of 2026-11-25 (Opus): CmpVRoots removal, heartbeat profiling, POOL growth, a cheaper sequential bank switch (D57), tooling.

## 1. `Arena/CmpVRoots.lean` removed (17:10–17:40)

The 556-line copy of con-ron's `Bridge/Modular/Roots.lean` is gone; `Arena/CmpVCone.lean` and
`Arena/JustifyRef6.lean` use the vendored lemmas (`ConRon.Bridge.Modular.{NSeen, XRel,
names_exact, expr_exact, const_exact, table_exact}`). The vendored module failed at four sites, all
the toolchain's `do` elaborator (no `pure () >>=` left; as patch 0002): patch
`con-ron/0004-modular-roots-do.patch` (an `AM.bind_ok`/`AM.pure_ok`/`subst` triple dropped at
three sites, a `dsimp`/`simp` made `try`). Its imports `Modular.Rel` and `Modular.Worker` build
unpatched; the lakefile's `ConRonBridge` globs list the three modules (the rest of
`Bridge.Modular` stays out). Gates 16/16 OK.

## 2. `Final/CmpA.lean`, `Final/CmpC.lean` under the default `maxHeartbeats` (17:16–17:30)

Profiled with `-Dprofiler=true` and `trace.profiler` (`lake env lean`, one file at a time):

| file | before (limit, file wall) | after (limit, file wall) |
|---|---|---|
| `CmpA` | 1 600 000, 3.70 s (proof 3.20 s) | default, 1.62 s (proof 1.18 s) |
| `CmpC` | 3 200 000, 2.82 s | default, 2.82 s (no change needed) |

`CmpA`: 2.02 s of the proof was one `rw [← Code.label (i := 147) hC rfl]` (turning `at_ (Kc + 147)`
back into `label abiCmpDoneL` in a goal whose machine state is large: the rewrite abstracts over the
whole goal). Replaced by `Eq.mp (congrArg (Ev _ _) (Code.label …))` inside the `ev_congr`, no
rewrite. `CmpC` already elaborates under the default limit (1.7 s tactics, 2.0 s kernel: the
`hC.get (i := N) rfl` lookups into the stub list); its raised limit was a leftover.

## 5. Tooling (17:19–17:25)

* (a) `scripts/checker_prog.py` ends with step 5: it builds `ConAgua.Checker.Prog` and runs the
  closure generators `core_fns.py`, `loop_fns.py`, `leaf_fns.py`, `phaseb_fns.py`,
  `preloop_ws.py` in that order, each after building the modules its Lean script imports
  (`CoreErec`, `LoopFns`, `LeafFns`: `leaf_fns.lean` reads `loopFns`). `--no-build` or the new
  `--no-closures` skip it. On master (nothing stale) the whole script takes 1 m 40 s, the closure
  step about 50 s of it. The merge queue's `checkerProg` regeneration calls the script without
  flags, so a merge that regenerates the program also regenerates the lists (it stages `ConAgua`).
* (b) `e2e.write_conron_pins` (used by `diff-e2e.py --refs` and `e2e.py`) builds `ConRon.Dump.Pins`
  before its `lake env lean` (checked in this worktree with the olean deleted).

## 3. The compared run's extra 10.5 MB of `POOL` (17:20–17:30)

Data: `_tmp/compare2/mem-{flat,cmp}.txt` (H10's `mincore` per slot, MiB): slot 2 (`POOL`, tier 0)
14.7 flat, 25.2 compared, every other slot of the store equal. Cause: **the name strings of the
second file.** `apply_str` (`Front/Line.lean`) unescapes each `str` name line's string into the
pool at its top (`str_put_esc`) and then interns the node (`apply_nstr`); when the node exists
already (a hit) the slice stays in the pool, unreferenced: the pool is append-only (D10). Counted
from `initC.ndjson` (one pool word per byte, D11): its 172 206 `str` lines hold 1 395 133 bytes,
10.64 MiB as pool words, of which 23 790 distinct strings, 2.69 MiB. So:

* flat `Init`: 10.6 of the 14.7 MiB of `POOL` are name strings, **8.0 MiB of them dead** (a
  component like `add` is unescaped once per name ending in it);
* compared `Init` with itself: the solution's 172 206 lines all hit, **+10.6 MiB, all dead**
  (H10 measured +10.5).

con-ron does not keep them: `parseNameEntryD` interns `.str p s` with `s` a heap `String`, freed
on a hit. So it is waste of ours, recorded as **D58** (Temporary). The fix: in `apply_str`, when
`apply_nstr` hit (the `nstr` count `CTL[36]` unchanged; the parse runs in tier 0), reset the pool
top `CTL[0]` to the slice's start `o`. Its refinement: on a hit `consInternM` returns the memory
unchanged and the twin's `internNNode` the state unchanged, so the line's memory is the one before
it except pool words above the top; the front's relations need a frame lemma for pool words
above the top, and `FrontPreOK1`'s pre-condition proof of `applyStrW` changes with the model. I
estimate about two hours with the regeneration and the frontend's rebuild: **not done here**
(not cheap; the brief's bar). It would save 8 MiB in every flat `Init` run as well, not only in
the compared one. Not measured: the time, which should not move (the same unescape, no new
pass).
