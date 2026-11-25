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

## 4. The sequential bank switch exchanges the index rows (D57; 17:31–18:05)

Mode `8` (`cq_bank_s`) no longer copies the challenge's index rows to `CEIX*`/`CTIX*` and the
solution's over them: `cq_swap_*` exchanges `EIX*` ↔ `SIX*`, `TIX*` ↔ `STX*` in place below
`2 · count` (`cqXchgLoop`, a `for` loop, three words moved per index), the memory header S's view
of the threaded run shows; mode `9` (`cq_bank_c`) exchanges them back (`cq_xchg_*`) at the extents
`CCTL[0‥5]`. The six stash arrays are gone from the layout (`CFIRSTS`, `CDLP`, `CCTL` are now
`228‥230`). Proofs: `xchgM` (the loop's memory, `Checker/CmpSeqSpec.lean`: `xchgM_get`,
`xchgM_back`, the loop spec by `Triple.forUp_pre`), the switch's rows (`cqRowStep_rows`, both
arrays), its frame (`csAS` now holds the solution's rows, `csAX = csAS`), the restore (`CqX`,
`CqX.back`, `Checker/CmpSeqViewC.lean`: both row sets back exactly, so `CsViewC.rows` comes from the
exchange instead of from the solution's rows being untouched); `CsKeep.sol` already excluded the
exchanged rows. No statement of `Final/*` changed. About 35 minutes, well inside compare2's
2–3 h estimate (the threaded mode's `csAX`/`CsViewC` were already shaped for a swap).

Checks: `diff-e2e --parallel 16` 766/766 agree (UNSOUND/INCOMPLETE/CRASH/TIMEOUT 0). Init,
`_tmp/compare/init{C,S}.ndjson`, interleaved with master's binary, 2 rounds, load about 5:

| run | instructions:u master → new | wall | peak RSS |
|---|---|---|---|
| flat, 1 thread | 202 631.85 M → 202 631.85 M | 14.8–14.9 s both | 627 MB both |
| flat, 16 threads | 204.02–204.12 G → 204.08–204.14 G (noise) | 2.55–2.6 s both | 764 MB both |
| compare, 1 thread | 407 588.6 M → 407 609.9 M (+0.005 %, the loop) | 29.7–30.0 s both | 1 017 → 1 006 MB |
| compare, 16 threads | 409 806 M → 409 808 M | 5.1–5.3 s both | 1 177 MB both |

The sequential compared run's peak drops by 11 MB (H10 estimated 12); the threaded run never used
the stash.
`diff-e2e --refs --parallel 16`: 766/766 agree, REFDIFF 0.

## 6. D58 fixed: `apply_str` drops a hit's string (user's request via the coordinator; 18:08–18:40)

L (`Front/Line.lean`): `apply_str` reads the `nstr` counts `CTL[36]`, `CTL[37]` before
`apply_nstr` and, when both are unchanged after it (the node existed), sets the pool top back to
the slice's start `o` (`str_put_esc` put the slice at the old top). The model gains `strDropW`.
Proofs: `nsinternW_hit` (an intern that leaves both counts alone returned the memory unchanged:
`consInternM_out`, `pushRec_cnt`), `nstr_twin_hit` (then the twin's `internNNode` hit too: both
states' `NStrR` at one memory give equal node counts, and `protoRun_casesG`'s append would add
one), `applyNStrW_hit` (`Front/StateDR.lean`: the arena state unchanged, the memory moved only by
the name table's put), and in `lineRecW_refines`'s `str` arm the hit case: `grows_drop` (the
dropped memory is a `Grows` of the one before the line), `MemFrame.set0`, `ArenaR.frame_ext`/
`DerR.frameT` across the put, `StateDR.frame` across the top's store. `set64_rdW_self` moved from
`Arena/Jobs.lean` to `Arena/StoreRel.lean` (needed this early in the frontend).

**Correction to §3:** a single file never hits: lean4export lists each name once and a `str` node's
key is its prefix and its string, so the "8 MiB dead in flat `Init`" there was wrong (it counted
equal components under different prefixes, which are different nodes). The waste was the compared
run's second file only.

Measured (Init, interleaved with master = item 4's binary, 2 rounds, load about 6; `POOL` by a
debug copy of `main.c` that counts the tier-0 pool slot's resident pages with `mincore` after the
driver returns):

| run | instructions:u master → new | wall | peak RSS | `POOL` resident |
|---|---|---|---|---|
| flat, 1 thread | 202 631.9 M → 202 633.1 M (+0.0006 %) | 15.0–16.6 s → 15.0 s | 627 MB both | 14.0 MiB both |
| flat, 16 threads | 204.13–204.15 G → 204.09–204.10 G (noise) | 2.7 s both | 764 MB both | – |
| compare, 1 thread | 407 610.0 M → 407 613.4 M | 30.7–31.3 s → 30.4–30.6 s | 1 005 → 994–996 MB | 24.0 → 14.0 MiB |
| compare, 16 threads | 409 856–409 878 M → 409 817–409 857 M | 5.1–5.6 s both | 1 177 → 1 155 MB | – |

`diff-e2e --parallel 16`: 766/766 agree.
`diff-e2e --refs --parallel 16`: 766/766 agree, REFDIFF 0.
