# Lane ronsync8: the con-ron sync de06320f → 8021ddac

Lane of 2026-11-23 (Opus), con-ron `de06320f → 8021ddac` (Tasks #161–#173), con-leche `600d3b58 → bc667610`.
Followed by lane `compare` (verified `--compare` on two lean4export files, upstream #165/#612).

## 0. Stage 0: footprint and stage plan

`_tmp/bump-8021ddac/report.{txt,md,json}` (the coordinator's step 1), then ronsync6's classifier
(`_tmp/ronsync8/fp.py`, outside the repository).

**Upstream.** con-ron definitions: 58 changed, 447 new, 5 removed (most new ones are `--compare`
#165 and modular checking #166); con-leche 51 changed, 148 new. Types: only `ConLeche.Literal`
(the hash, #547/#598) reaches us. `pins/`: one variant file renamed (label only).
Patches: con-leche/0001 and con-ron/0002 conflict.

**Toolchain.** Upstream moved to v4.36.0; ours is nightly-2026-10-20 (4.37.0-nightly, after
v4.36's branch point), and upstream had already adapted to the per-conjunct `vcgen`. The new
trees build on our toolchain with the patch series (§2): no toolchain bump.

**L items** to re-check: 26 (39 markers in 10 files; one gone, `natOpStoredOkAll`).

**Proof declarations**: the report counts 612 mentioning declarations; about 400 of them are
textual hits of short twin names (`NeedsSt.rules`, `Args.closed`, `MixedStep.scoped`,
`ImpsD.isEmpty`, …). Without those: **213 in 97 files**.

| form | count | lines |
|---|---:|---:|
| call-by-call walks (`callW`) | 14 | 1 886 |
| model-arm walks | 4 | 235 |
| declarative, ≤ 12 lines | 1 | 12 |
| declarative, longer | 14 | 557 |
| manual, > 12 lines | 44 | 2 989 |
| manual, ≤ 12 lines | 65 | 652 |

Hand specs: 1 (`check_a`). Theorems with a positional `⟨…⟩` of ≥ 5 parts: 56.

**New twin code to port** (uncited): `Arena/Inductives/IotaRead.lean` (#622, the ι reading rule,
~30 functions); every building block it calls has an L function already.

**Final statements likely to change**: `Final/Twin.lean`'s `SeqAccepts` and three lemmas of
`Final/TwinVerdict.lean` (`checkJobList … I` → `checkJobList … none I`, the twin's new `J`).

**The ROM**: not touched (the ι rule's names are interned from bytes in code, as `name_rec`).

**Kind of sync**: an L-code sync (≈ 30 ported, ≈ 10 changed functions) plus one mechanical
statement change (`J = none`). Ladder estimate: 10–20 % of the failing theorems (the `none`
rule), the rest the port's re-proofs.

## 1. Stage 3a: the interface

* **Reasons**: `scripts/reasons.py --add` appended 33 twin messages (most of them are the
  modular and `--compare` readers' messages, which L never raises). Three apply to L:
  `R_A_COMPILER_TRUST`, `R_THE_TOLERATED_AXIOM`, `R_THE_RECURSOR_S_MINOR`.
* **`check_constant_val(vis, q, allowOp, allowReduce, allowSorry)`** (#501): `reduceOpNames` is
  pin slots `43`/`44`, `sorryAx` is pin `13`. The flags at the 8 call sites are the twin's:
  defn `T,F,F`, thm `F,F,F`, opaque `F,T,F`, axiom `F,F,T`, and `F,F,F` at the four inductive
  sites.
* **`J = none`** (#165/#619): a regex rule (`scripts/sync-rules/ronsync8.txt`) inserts `none`
  after `pins` in every `checkJobList`/`runJob`/`recordJob`/`recordCheck`; it was applied to the
  whole tree once.
* **The ι rule's records** (`Arena/IotaReadDec.lean`): `IotaRec` and `IIotaParts` are each seven
  result words (`IW` slices for the lists), with decoders `decOIR`/`decOIP`/`decOIPD` and their
  grow lemmas, plus the table of L names and signatures.

## 2. Progress log

* 14:32 start; 14:35 bump (`468feaed1`); the conflicts in the toolchain patches were resolved
  to upstream's text. con-leche/0001 (the `withPtrEq` shim) is kept and extended to
  `Kernel/Name.lean`. The ∧-split lemma patches (DiscC4, KnotC) went: upstream has those lemmas
  since v4.36.0. `checkConstantVal_bridge`'s `try replace` is now its own patch (0003).
  `ConRon.Bridge.Modular.*` (#166) is not built: its run-style proofs meet our `do` elaborator
  at every `pure () >>=`, nothing imports it, and L has no modular modes (D50).
* 14:40–15:00 stage 3a, the first two full builds; the stage 0 message was sent.
* 14:50 helpers `ronsync8-iota` (the ι reading rule) and `ronsync8-decl` (#501, #462, #443,
  `J = none`) started; the briefs are `_tmp/ronsync8/brief-{common,iota,decl}.md`.
* 15:00–15:40 helpers' first milestones. `ronsync8-decl` (#501, #462, #443, `J = none`) finished
  with zero `sorry`. `ronsync8-iota` wrote the L code of all 35 ι functions, their generated
  models and the arm, proved four refinements, and handed over when its context ran out. Its
  successor `ronsync8-iota2` took phase 1. A third helper, `ronsync8-iotarel`, took phase 2 (the
  comparisons, `block_reads_at`, `cid_ref`).
* Integration fallout, fixed by the lead:
  * a name clash (`iota_rec_major` was taken: now `iota_read_major`);
  * con-leche #598's `natBigHash` is C (`native/nat_hash.c`), which our `lakefile.toml` does not
    compile and our runtime does not export, so every executable failed to link. Patch
    con-leche/0004 makes it `@[implemented_by]` a Lean fold;
  * the whole-program kernel checks need `import all` of the two ι modules;
  * the closure lists (`loopFns`, `JobsClosed`, `PhaseBReads`) needed the 35 names;
  * `nvFns` and `PreLoopWS` were regenerated.
* `diff-e2e --tests` at con-leche bc667610 with the regenerated binary: **748/748 agree**
  (441 accepted, 307 not), UNSOUND/INCOMPLETE/CRASH/TIMEOUT 0. 18 NOT PORTED: con-leche's new
  argument rows `--compare -- C S`, for lane compare; `diff-e2e.py` now names them instead of
  failing on them. 7 SKIPPED (`--max-nat-size`, D49).

## 5. Statement changes (Final/*)

All are mechanical and follow the twin. No headline statement changed (`TwinAccepts`,
`TwinVerdict`, `TwinAcceptsPooled`, `TwinVerdictPooled`, the `Final/Checker*` theorems).

| declaration | before | after |
|---|---|---|
| `Final/Twin.lean` `SeqAccepts` (def) | `checkJobList mode pins I ds (List.range ds.size) s'.worker = …` | `checkJobList mode pins none I ds …` |
| `Final/Twin.lean` `twinAccepts_pure` | `… = .ok (ConLeche.Cached.streamEnv …)` | `… = .ok (ConLeche.streamEnv …)` (upstream moved the definition, unchanged) |
| `Final/TwinPooled.lean` `twinAcceptsPooled_pure` | `ConLeche.Cached.streamEnv` | `ConLeche.streamEnv` |
| `Final/TwinVerdict.lean` `TwinFailsV.checkStream_jobs` | `TwinFailsV (checkJobList mode pins I ds …)` | `… pins none I ds …` |
| `Final/TwinVerdict.lean` `TwinVerdict.jobs` | `checkJobList .verified ipins I ds (List.range ds.size)` | `… ipins none I …` |
| `Final/TwinVerdict.lean` (pooled jobs lemma) | `checkJobList .verified ipins I ds w` | `… ipins none I ds w` |

`Audit/*`, `E2E/*`: unchanged.

**`natBigHash` (patch con-leche/0004).** The `@[implemented_by]` fold is compiled only into
Lean executables that link con-leche's `Kernel/Expr` (e.g. `romgen`, `romtest`, `census`, `e2e-l`,
`e2e-diff`, `con-ron-lean`, `con-ron-lean-twin`, the benches) and into elaboration-time evaluation.
It is not part of `checker`: `checker.s` is the L compiler's output for `checkerProg`, which has no
Lean runtime code. `main.c` and `pins.bin` (unchanged by this sync) do not involve it either. So it
is outside the final theorems' trusted base. To the proofs, `natBigHash` stays an opaque function.
* 15:40–16:30 the ι refinements: `ronsync8-iota2` proved phase 1 except `iotaPartsAt_rel`
  (handed over), `ronsync8-iota3` proved that one (`IotaFrameTwin.lean`: `TwinOK.of_pstep`, the
  twin's `PStep` lemmas), and `ronsync8-iotarel` proved phase 2 up to the driver.
  More integration fixes: a lemma-name clash (`decW0B_true`); `block_reads_at`'s closure
  (`block_constants`, …) added to the step lists (found with a per-function `#eval` of `wsChk`);
  `import all` of the ι modules in every whole-program check; the loop/leaf/phaseB lists
  regenerated by their scripts; the OVERVIEW anchors moved (citation line numbers, `none`, the
  upstream revisions).
* 16:30–17:10 `ronsync8-cid` (the successor of `ronsync8-iotarel`) proved `cid_ref` at the new
  arm. `block_reads_at` could not join `cidFrameCallees`: its closure writes the walk memos and the
  `mentions_any` memo. Instead, a frame `BrMem` (`IotaRelRefK.lean`) and one `prog_all` over four
  write sets (`Checker/IotaArmClosed.lean`, 9 s, 1.4 GB). The tree builds with zero `sorry`; the
  axiom guards are unchanged.
* `con-ron-lean-twin` hung on `nat_size_ok`: the first `natBigHash` fold (`>>> 64` per word) is
  quadratic, and the twin hashes `2^16777216` thousands of times; a fold in halves still copied the
  number per level. It now mixes three words read in constant time (the lowest, the highest, the
  bit length): weaker than upstream's C, but only our Lean tools run it.
  con-ron #171 removed `--pins` (every run decodes the embedded pins, all four variants), so
  `e2e.py`, `diff-e2e.py --refs` and `bench.py` call it without the flag.

## 3. What was mirrored (by upstream item)

| upstream | L |
|---|---|
| #622 the ι reading rule (con-ron #164 lane I) | 35 new L functions (`Arena/IotaFrame.lean`: the frame and the two readings; `Arena/IotaRel.lean`: the comparisons and `block_reads_at`), each with a generated model and a refinement (`IotaFrame*.lean`, `IotaRelRef*.lean`); `check_ind_decl` runs `block_reads_at` before `check_block` and rejects after it (`R_THE_RECURSOR_S_MINOR`). The twin's own deviations are mirrored: a `Bool` answer, the input index with the block's constants pushed in place, the frame read once per recursor, interned annotation names. |
| #501 reserved names | `check_constant_val(…, allowOp, allowReduce, allowSorry)`, the twin's flags at all 8 sites |
| #462 a dependency only stored | `nat_op_deps_stored` (any kind), the two gates on `nat_op_stored_ok`; `nat_op_stored_ok_all` removed |
| #443 every group mate typed at the key | `family_key_checks` (a loop), `nest_frame` calls it |
| #165/#619 `J` | `none` on the flat path: statements only |
| #547/#598/#564 literal hash | citation only: L hashes every limb (FNV-1a, as con-ron) and stores the hash in the record (#163's cache was L's layout from the start) |
| #163 `pred` in place | not mirrored: L's `nat_pred_lit` is `nat_sub(a, 1)`, linear as con-ron's (bignum parity holds) |
| #168/#169 loops | `build_index` and `check_jobs` were already `for` loops; `str_cons_spine` stays a recursion as the twin (`docs/ROADMAP.md`, Ideas) |
| #166/#170 modular modes | omitted, D50 |
| #165 `--compare` | ported by lane compare |
| #171 the driver over `CheckerIo` | twin-side: con-ron's main theorems now quantify over a run of the extracted driver (`CanGive`, `AnswersAs`, `PoolSound`); ours are about `checker.s` and `main.c` and already have that shape (the harness statements `Final/Drv*`). Nothing to mirror; the `--pins` flag it removed only affects our reference runs. |
| #173 Windows/macOS | twin-side |

**Deviation rows added**: D50 (the modular modes). New aborts: capacity guards on count and
handle words (`iota_rec_of`, `iota_parts_of_at`, `iota_parts_at`, `lift_field_doms`,
`lift_idx_args`), all fixed capacities, so no row.

## 4. The ladder against the estimate

Estimate: 10–20 % of the failing theorems (the `J = none` rule). Measured: the `none` rule ran
over the whole tree before the first build, so no theorem failed for it; the remaining failures
were the ported functions' proofs, which no rung can produce. Yield 0, as in ronsync3, ronsync4
and ronsync6. The ladder was not needed as a compile-pass tool either: the helpers' first
milestones restated by hand, and the build failures were few (11 modules at the first full build).

## 6. Checks

* `gates.sh`: all 16 OK. `provenance.py check --strict`: every citation exact at con-ron
  8021ddac, con-leche bc667610; 0 markers left (39 at the bump). `bump-con-ron.sh --check` ok.
  `asm_file.py --check`: `checker.s` and `pins.bin` up to date (`pins/` moved only by a file
  rename, so `pins.bin` did not change).
* `diff-e2e --refs --no-cache --tests` at con-leche bc667610 (con-ron 8021ddac built in
  `_tmp/ref/con-ron-8021`; con-ron-lean-twin at this branch): **748/748 agree** (441 accepted,
  307 not), UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF 0; 18 NOT PORTED (`--compare`), 7 SKIPPED
  (D49). con-leche's expectations grew from 740 to 748 file rows, plus the 18 argument rows.
* `e2e.py --latest ''` (that con-ron): 827 fixtures, all agree with con-ron-lean-twin (482
  accept, 57 decline, 286 reject, 2 time out in both).
* Census: 100 %, zero `sorry` sources (the 2 bad links of `topLitS` were there before).

## 7. Performance

Against master `6896d49c1`, both binaries `make` from the committed files, `Init`
(`_tmp/fixtures/init/init435.ndjson`). The wall rounds ran while the helpers built (load up to
3.8).

| | master | ronsync8 | Δ |
|---|---:|---:|---:|
| `Init`, `instructions:u`, one thread (`perf stat`, 2 runs each, identical to ±0.00 %) | 202 593 M | 202 631 M | **+0.019 %** |
| `Init`, peak RSS, one thread | 628 MB | 628 MB | 0 % |
| `Init`, peak RSS, `--jobs=16` | 765 MB | 765 MB | 0 % |
| `Init` wall, one thread (12 interleaved paired rounds, Wilcoxon) | 14.78 s | 14.90 s | mean +0.85 % [+0.26, +1.44], p = 0.012 |
| `Init` wall, `--jobs=16` (same rounds) | 2.57 s | 2.56 s | mean −0.14 % [−2.13, +1.85], p = 0.155 |

The ι reading rule is the only new work on `Init`'s path: it runs once per inductive block (each
recursor's rules read off its type and through its constructor). Upstream measured +0.23–0.26 %
`instructions:u` on its three inductive-heaviest fixtures and ≈ 0 on `Init` (#164, +0.025 %),
which matches L's +0.019 %. The one-thread wall difference (+0.85 %) is larger than the
instruction count, and those rounds ran under load. No regression in memory.

## 8. What went wrong

* **Helper context.** The ι port took five helpers in sequence (iota → iota2 → iota3 for phase 1,
  iotarel → cid for phase 2 and the arm). Each ran out of context after 4–15 proofs; the
  hand-overs worked, but a helper cannot write to `_tmp/ronsync8/` (the sandbox guard), so the
  hand-overs sat in their worktrees until the lead copied them.
* **`natBigHash`.** con-leche's new C hash broke every executable's link. The first Lean
  replacement (a word fold) hung `con-ron-lean-twin` on `nat_size_ok`, and a halving fold was no
  better. A constant-time mix fixed it. Two full rebuilds of the tree went into this.
* **Integration lists by hand.** The new functions had to go into the closure lists, and their
  modules needed `import all` in every whole-program check. Each was found by one failing build
  round and fixed by hand. The per-function `#eval` of `wsChk` (which function fails) was the
  quickest diagnosis; `loop_fns.py`/`leaf_fns.py`/`phaseb_fns.py` regenerate the lists and
  should be run right after the program is regenerated.
* **The `--pins` reference flag.** con-ron #171 removed `--pins`, and the first `--refs` run
  cached "error" verdicts for all 748 fixtures. `--no-cache` replaced them.
