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
