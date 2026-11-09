# Lane ronsync2: con-ron 97eead2d → 01ecb31c, con-leche 0d2f467b → 210a580e

The protocol of PLAN.md, "Bumping the twin". Toolchain unchanged (upstream v4.35.0, ours
nightly-2026-10-20).

## 1. The report (step 1, run by the coordinator)

`_tmp/bump-01ecb31c/report.{txt,md,json}`: con-ron 414 commits, con-leche 211. Definitions:
con-ron 156 changed, 333 new, 90 removed; con-leche 176 changed, 455 new, 111 removed. Types:
con-ron 12 changed, 26 new, 7 removed. L items to re-check: **431** (306 citations changed, 135
gone, 110 through a changed helper below a cited declaration). Declarations of ours that mention
a changed item: 2178 (1483 theorems) in 548 files. Patches: con-leche 0001–0003 and con-ron 0002
CONFLICT, con-ron 0001 applies.

## 2. What changed upstream, and what L takes

| upstream | what | L |
|---|---|---|
| #139 (con-leche #386/#410/#411/#430/#431) | stored recursors checked against the generated ones up to defeq; `RecShape.rhss` → `rules`; `classRecTyCheck`, `classRuleCheck` | mirror |
| #139 (con-leche #452) | `CheckMode` is `verified \| trusted`, `eager : Bool` beside it | mirror |
| #139 (con-leche #450) | observable command line (`--`, `--help`, non-regular input exit 3, `u8` exit codes) | harness (`main.c`) where it applies |
| #140 | proof-only (Theorem 1 loses `μ`/`hμ`) | statements follow where they mention it |
| #141 | stored install + block jobs, two-tier environment | superseded by #143 (only its final state is mirrored) |
| #142, #145, #146 | the `.olean` reader and its memory | **excluded** (deviation, §6) |
| #143 (con-leche #480/#481/#484) | **the install phase goes**: parse, prepare, pins, the stream index (`buildIndex`, records read off once, no inference), then every record's check is a job at the index's view of its position; derived data at use (`formerSortLoop`, `iotaCase3At`, `etaRescueOk`, `projGuardRows`, `litShapeOk`, …); `BlockParts` → `BlockShape`, `StoredRecs` → `StreamRecs`; promotion and the persistent-intern family deleted; the environment a layer over the frozen index | mirror (non-olean path) |
| #144 (con-leche #488/#490/#491/#489) | the `meta` header exactly as line 0; a failed final flush is exit 3; reads through a handle (olean side); flat `uses` (olean, skipped upstream too) | #488 in L's frontend, #490 in the harness |
| #148 | key-free cons tables: 8-byte slot (16-bit stamp, 16-bit hash fragment, handle) | mirror in the generic cons library (helper ronsync2-kf, §7) |

## 3. Plan (stages)

1. **Vendor** (step 2): re-vendor, re-make the conflicting patches (helper ronsync2-vendor for the
   Theorem-1 toolchain fixes).
2. **L code, no proofs**: the data layout first (environment records: `RecRule` without
   `ctorParams`/`k`/`eta`, `IndCaps` without `ruleK`/`sortZ` with `nIdx`, `ProjTable` without
   `structSort`/`guards`, `recInfo`'s `isK`, no `basisDecl`; the environment as an own layer over
   the frozen stream index), then the functions by area (core, inductives, declarations and
   the pipeline, frontend and ROM), then the program, `checker.s`, and verdicts (`diff-e2e`).
3. **Proofs**: the `@[refines]` theorems, then the relations, then the end-to-end chain and the
   Final statements; by file across helpers.
4. **Gates, perf, landing.**

## 4. The L design (stage 2)

* **`EREC` is tiered** (`Layout.lean`): tier 0 the stream index's and the pins' records, tier 1 a
  job's own (a block's pushes, a gate's temporary record), dropped with the scratch tier
  (`record_job` empties the tier-1 top `CTL[130]`). A record address is tier-tagged (bit 40, as the
  pool's slices); reads are `EREC⦃a⦄`, writes `erec_put(a, v)`, `erec_alloc(n)` picks the tier by
  the scratch flag. Why: a block job pushes constants, and in the threaded mode tier 0 is the frozen
  buffer (read-only, shared); a per-worker copy of the base records would be ~42 MB per worker on
  `Init`. The decoders read a **reader** `Nat → Option Word` (`erecP m` joins both tiers as one
  address space, `aread a` for an array), so a decoding below both tops survives both growths.
* **Record layouts** (`EnvRec.lean`): offsets kept stable; `recInfo` gains `isK` at `p + 9` (10
  words); a rule's `ctorParams`/`k`/`eta` words and the caps' `sortZ`, the tables' `structSort`/
  `guards` words are no longer read (a compaction is left for later: it would move every reader's
  offsets in this sync); the caps' `nIdx` takes the old `ruleK` word. `decCI`/`decCaps` lost `dn`
  (no `PropWhen` names any more), and with them `StageR`, `KeepPost`, `CheckR`, `EnvR`.
* **The environment** (`Env.lean`): a job's own layer over the frozen stream index, the twin's
  `IFEnv = ⟨own idx, own tbls, base⟩`. The stream index (`EIX*`, `TIX*`, untiered: the stream's names
  are persistent) is written by `build_index` only; its view is two control words, `CTL[134]`
  (`below`) and `CTL[135]` (`belowRec`), set by the job. The own layer (`OIX*`, `OTX*`, tiered by the
  name's tier, worker-owned) carries the job's stamp `CTL[133]` in each row, so a job starts empty
  without clearing; its view is `vis` (the push count), as before, so the API (`env_find(w, vis)`,
  `env_push`, `env_row_get` = the own raw row, `env_pop_temp`, `find_table`) kept its shape. The
  twin's "an empty own index is not hashed into" is `vis = 0`. `IEnv`'s lists are not represented
  (nothing reads them). Control words rather than globals so that `MemFrame`'s `CTL` clause covers
  them (a process-rule deviation: the frame machinery has no globals).
* **The pins**: slot 51 (`quotMkName`, new upstream) is `PINS[71]`, past the reserved names, so no
  other slot moves; `PINS` is 72 words.
* **The ROM's structured constants** (`Rom/CIEnc.lean`, `Rom/CIRead.lean`): no annotated basis
  blocks (`declsA`) and no `eqA` (both gone upstream); caps with `nIdx`, rules with the `levels`
  fire, recursors with `isK`; 25 slots.
* **The frontend**: `front_line(i, first)` applies `lineRecPlaced` (#488: the header only first, no
  record first, no blank line); the parse no longer checks a recursor's `k` (the block's check
  does: `streamKCheck`), and the recursor record carries it.
* **The check phase** (`CheckerL.lean`, `Entry.lean`, `Freeze.lean`): entry 1 runs the stages and
  `build_index`, entry 2 runs the jobs `PLO‥PHI-1` (`check_jobs`, `record_job`); the frozen buffer
  holds the stream index, `FIRSTS` and the front's `DECL`/`DLP` (a job reads its record), and no
  `PEND`; the harness's job count is the number of records.
* **The harness**: a failed final flush of the verdict is status 3 (#490). #450's command line is
  con-ron's own CLI; `main.c` is a different, minimal harness (`checker [--jobs=N] FILE`), so
  nothing of it applies.

## 5. Progress log

* 2026-11-08 15:27 start. Bump run (`_tmp/ronsync2/bump.log`); con-leche 0001 re-applied without
  its `ParInstall.lean` hunk (file gone); 0002/0003 re-made at the new signatures (`eager`);
  con-ron 0002 re-applied without `Split.lean` (gone), conflicts taken from upstream, the
  toolchain fixes re-done where the build fails (helper ronsync2-vendor).
* 15:40–16:20: foundation (EREC tiering, layouts, environment, pins, ROM, frontend #488, the check
  phase, `Final/Twin.lean`'s statements). Helpers: ronsync2-vendor (done: Theorem 1 builds on our
  toolchain, `con-ron/0002` re-made), ronsync2-kf (#148), ronsync2-core (the core tier),
  ronsync2-ind (the inductive stage, `Install.lean`), ronsync2-decl (the declaration arms, Basis).
* 16:20–19:45: helpers ronsync2-core, -ind, -decl finished the L code of their areas (merged);
  ronsync2-kf (#148) landed on its own (master 09a78343, #232); ronsync2-fix made the whole library
  build with stage-2 sorries (a big share of the old proofs is commented out under
  `/- ronsync2 stage 2: … -/` markers, to restate in stage 3; an early `--delete` pass of the
  sorry-out tool removed declarations in commit 3df264b01, restore candidates are its diff).
  Program regenerated (1770 functions, no stubs). Two fixes found by running it: the jobs read the
  ROM's structured constants, but entry 2 has no pin-data buffer, so they are read once at
  startup into `ROMC` (`rom_fill`, frozen); `lv_lookup` over `EREC` keys reads them at tagged
  addresses (`lvLookupTG`).
* First verdicts (`diff-e2e --tests` at con-leche 210a580e, sequential): 687 of 689 agree, `Init`
  accepts; the two left were the `lv_lookup` tier bug.
* Environment (resolved, not a lane change): the toolchain's `ld.lld` wrapper pointed at a
  garbage-collected nix store path, so no Lean executable linked; a temporary `LEAN_CC` wrapper
  was used until the coordinator reinstalled the toolchain (23:30), after which the executables
  were rebuilt normally.
* 19:56–20:15, performance of the stage-2 binary (L code final, proofs pending) against master
  09a78343 (which already has #148, ronsync2-kf: its own numbers are in
  `docs/design/ronsync2-kf.md`, `Init` peak RSS −12 %, −17 % at 16 threads, +0.9 % instructions):

  | | master 09a78343 | ronsync2 | Δ |
  |---|---:|---:|---:|
  | `Init`, `instructions:u`, one thread | 223.85 G | 223.53 G | −0.14 % |
  | `Init`, `cycles:u`, one thread | 75.78 G | 75.31 G | −0.6 % |
  | `Init`, peak RSS, one thread | 645 MB | 638 MB | −1.0 % |
  | `Init`, peak RSS, `--jobs=16` | 808 MB | 782 MB | −3.3 % |
  | `Init` wall, one thread (CPU 44, 16 paired rounds, load 0.7–6.2) | 17.33 s | −0.4 % (Wilcoxon p = 0.30; mean [−1.0, +0.2]) | |
  | `Init` wall, `--jobs=16` (CPUs 24–39, 20 paired rounds, load 4–12) | 3.49 s | **−7.7 %** (p = 0.007; mean [−11.8, −2.1]) | |
  | `complete_c04a_restart_70` (largest e2e fixture), instructions | 16.51 G | 17.09 G | +3.5 % |
  | `complete_c04a_restart_70`, peak RSS | 261 MB | 261 MB | 0 |

  The install phase is gone, so the jobs carry the blocks' checks and the pool parallelises them
  (the 16-thread gain); one thread breaks even (`_tmp/ronsync2/perf/`).
* 20:15– stage 3 (proofs), three areas on helper branches (`ronsync2-p3a` infrastructure/pipeline/
  Final/Front/Rom, `ronsync2-p3b` the inductive stage, `ronsync2-p3c` the core tier and the
  declarations), helpers handing over through area files as their context runs out. By 21:35:
  the shared relations restated and proved (`EnvR` as the own layer over the frozen index, the
  two-tier record pool in `IWOK`/`IWGrow`, `CheckR.erGrow`), every `Env.lean` function refined,
  the stream index's relation `IndexR` and the `idx_consts`/`idx_tables` loops proved,
  `check_decl` ⊑ `checkDecl` proved from the arms' contracts; master's proofs restored wherever
  they still check. Left: ~860 sorries over the three areas.
* Decision (21:55), the fold invariant at a job's view. A job's check needs con-ron's `FoldOK` at
  `I.view k`, whose `envWF` upstream obtains only from the model (`view_foldOK`, `job_spec`,
  `pooled_fold_records`, `Arena.pooledAccepts_bridge` all take `(V) [ConLeche.SetTheory V]`;
  upstream proves no V-free accept and no rejection theorem for the pool). Mirroring that: the
  Final accept theorems (`checkerFile_accepts(_regs)`, `threadsRun_twinAcceptsPooled(_regs)`, their
  Audit copies) and the sequential verdict gain `(V : Type w) [ConLeche.SetTheory V]` (the
  sequential verdict keeps `TwinVerdict [b] c`); the threaded verdict `TwinVerdictPooled` keeps
  job `k`'s failure with class `c` or, weakened, some job below `k` rejected (a failure in another
  thread below `k` leaves no `PrefixOK` at `k`). Before/after texts: §6 (statement changes).

## 6. Statement changes of the final theorems

Approved by the user (via the coordinator, 2026-11-09). Reason: a job is checked at the stream
index's view of its position, and con-ron's fold invariant there (`FoldOK`, its `envWF`) comes
only from the model of the accepted prefix (`view_foldOK V`); upstream's own bridge
(`Arena.pooledAccepts_bridge V`) takes the set theory, and it proves no rejection theorem for the
pool.

1. **The accept theorems** (`checkerFile_accepts`, `checkerFile_accepts_regs`,
   `threadsRun_twinAcceptsPooled`, `threadsRun_twinAcceptsPooled_regs`, their copies in
   `Audit/Final`). Before: `theorem checkerFile_accepts [Host] (k0 : Nat) (hcode : Code
   checkerFile k0) (b pb : ByteArray) … : Ev (fun st => … (rdx = 0 → rax = ACCEPT → TwinAccepts
   [b]) ∧ (rdx = 2 → rax &&& 3 ≠ 0 → TwinVerdict [b] (rax &&& 3))) dm (label abiStartL)`. After:
   the same with `(V : Type w) [ConLeche.SetTheory V]` added before `[Host]` (the conclusion
   unchanged).
2. **The sequential verdict** (`checkerFile_verdict_of`): gains `(V : Type w)
   [ConLeche.SetTheory V]`; its conclusion `TwinVerdict [b] c` is unchanged.
3. **The threaded verdict** (`TwinVerdictPooled`, used by `checkerFile_threads_verdict_of`).
   Before: `TwinVerdict chunks c ∨` (the stages and phase A ok, and some worker's list of pending
   records `w ⊆ pend` fails from the phase-A state's worker with class `c`). After:
   `TwinVerdict chunks c ∨` (the stages and the stream index ok, and either job `k` fails at the
   view of `k` with class `c`, or some job `j < k` fails at the view of `j`). Weaker: a failure
   reported by one thread at `k` says only "rejected" when another record below `k` is rejected.
   It also gains the set theory.

The final texts are given in the report when the theorems are proved.
