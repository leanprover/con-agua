# Lane ronsync4: the con-ron sync 4ca283d1 → c78714ac

Lane of 2026-11-13 (Opus), from master `dfe9fbdd7`. con-ron `4ca283d1 → c78714ac`, con-leche
`eb2c5939 → ca6af099`, upstream task #152 (con-ron DESIGN.md "### Task #152"; 38 con-ron and 33
con-leche commits). Standing decisions: no new driver/CLI option; every new or rewritten
function gets a generated model and a declarative refinement (exception: limb arithmetic);
`EREC` offsets kept stable, new fields appended.

## 0. Stage 0: footprint and stage plan

`scripts/bump-con-ron.sh --report c78714ac` (`_tmp/bump-c78714ac/report.{txt,md,json}`), then
presync3's classifier (`_tmp/ronsync4/fp.py`, `fp1.py`, outside the repository).

**Upstream** (con-ron's own triage): #573 the constructor record gains its family
(`ctorInfo cv nP nF induct`) and `IIndCaps.neverZero` is stored at install; #556 P-A the stuck
spine (`isStuckHead`, `iotaTarget`, `whnfStuck`: ι once, at the recursor's prefix); #572 the
official `whnfCore` memo policy (the memo moves from the knot's slot into the loop: pending keys
`pend`/`pendC`, the chain stored at its end, the cheap mode stores nothing); #556 P-W (a literal
reduct of `reduceNat` is the answer at once) and P-N (`NatBinOp`, `natBinOpOfName?` once,
`natBinOpResult` replaces `natOpResult`); #557 (`natOpWfNames` deleted); #558/#574/#576/#577
citations only. con-ron definitions: 60 changed, 21 new, 3 removed; types `IConstantInfo`
(ctor arity), `IIndCaps` (`neverZero`), `NatBinOp` (new). con-leche: 157 changed, 46 new, 10
removed. `pins/` did not move. Patches: con-leche/0003 and con-ron/0002 conflict (`KnotC.lean`,
`WhnfCore.lean`, `IotaMajor.lean`, `Lines.lean`).

**L items** to re-check: **159** in 32 files (130 changed citations, 28 gone, 50 through a changed
callee). Groups: `Front/IndApply` 30 (`installIndD`/`validateIndD`: the family), `IndInstall` 14
(caps, ctors), `WhnfDelta` 13 (`reduceNat`, `whnfStep`, the wf names), `WhnfM2C` 12
(`majorToCtor`), the Nat ops 24 (all cite the removed `natOpResult`), `DefEq` 9 (η readers),
`WhnfIotaRec` 9 + `WhnfIota` 6 (`iotaRecAt`, `ctorFamily`, `iotaCase3At`), `WhnfCore` 5 + `Knot` 4
(the memo policy, the stuck spine), `IndDeclConsts` 5, `DeclArms*` 9, `StrLit` 4, `Rom/CIRead` 3.

**Proof declarations** that mention a changed twin function or an affected L item, or carry its
`@[refines]`, plus the `IIndCaps` mentioners: **525 in 155 files, 314 theorems** (with every
`IConstantInfo` mentioner: 806 in 224 files). The `ctorInfo` arity alone: 119 positional
`ctorInfo _ _ _` sites in 47 files (one codemod rule).

| form (theorems) | count | lines |
|---|---:|---:|
| call-by-call walks (`callW`) | 43 | 3 454 |
| model-arm walks | 12 | 1 241 |
| declarative, ≤ 12 lines | 16 | 197 |
| declarative, longer | 39 | 1 418 |
| manual, > 12 lines | 67 | 3 232 |
| manual, ≤ 12 lines | 137 | 1 224 |

Hand specs in the footprint: 35, of which 24 are the Nat primitives (limb arithmetic, kept).

**Final statements**: none of `Final/*`, `Audit/*` mentions a changed twin type or function;
upstream's capstone statements are unchanged. Expected: no final statement change.

**The ROM**: the raw-`EREC` relations (`PinSetR`, `SliceR`, `DivModTypePins`, `BlockRecLpsOk`,
`CIReadRefBase`) mention no constructor record and no caps; `pins/` and `INatOpPinSet` did not
move. The sync reaches the ROM through the CI encoding only (`CIEnc`: the constructor's family
name, the caps' `neverZero` byte), whose refinement (`CIReadRefCI`, `CIReadRefCaps`) already
states its result through `decCI` over the record reader. So the move behind the record reader
is not done (the coordinator's rule: only the encoding bytes are touched).

## 1. Stage plan

**Kind of sync.** Mixed: one type change that breaks many proofs mechanically (the `ctorInfo`
arity: a codemod rule, where the ladder pays) and L-code rewrites (the `whnfCore` loop and slot,
the install's family and `neverZero`, the readers, the Nat dispatch), where it does not
(ronsync3: 0 of 54). Expectation: the rule rung closes most theorems that fail only by the arity
(tens), the rest are re-proofs of the ported functions.

**Stage 3a (lead)**: the constructor record's family at `p + 7` (appended; `decCI`'s ctor arm),
the caps' `neverZero` in the caps record's unread word `q + 7` (the old `sortZ` slot; the record
stays 15 words), the ROM's `encCI`/`encCaps` and the readers' layout lemmas; the pending keys'
storage (a stack slice at `CTL[136]`, `pendC` a suffix of `pend` by an offset: `pushCheapKey` only
ever keeps a suffix) with its relation; `NatBinOp` as a word code with `natBinOpOfName?`'s
vocabulary.

**Fan-out** (after 3a, three helpers, disjoint files):
* **ind** (#573, install and front): `IndInstall`, `IndDeclConsts*`, `IndSum`, `IndParts`,
  `IndPos`, `BasisL`, `DeclArms*`, `Front/IndApply`, `Rom/CIRead*`, and their spec files.
* **core** (#556 P-A, #572): `WhnfCore`, `WhnfCoreSlot`, `WhnfCoreLoop`, `Knot*`, the new stuck
  spine and memo functions, and the #573 readers in `WhnfIota*`, `WhnfM2C*`, `DefEq*`.
* **nat** (#556 P-W/P-N, #557): `WhnfDelta*`, `NatArms`, `Nat*.lean`, `Refine`, `StrLit*`, the
  `reduce_nat_wf` deletion.

## 2. Progress log

* 2026-11-13 07:07 start; 07:10 report; stage 0 sent to the coordinator.
* 07:11–07:17 bump (`79c91c281`). `bump-con-ron.sh c78714ac` stopped at two conflicting patches.
  con-leche/0003 (the `CSOK.*_hit_ws` companions of the `vcgen` ∧-split): upstream moved the two
  `whnfCore` memo lemmas from `KnotC` to `DiscC4` (#572), so their companions moved with them:
  the new patch con-leche/0004, and `DiscC4`'s new `whnfCoreLoopC_spec` finds them through
  `conleche_grind`. con-ron/0002: upstream's new `Arms/WhnfCore` loop proofs (lane B, explicit
  triples) needed the same ∧-split pattern (`all_goals subst_vars`, one closer per conjunct, eight
  sites), `Frontend/Lines`' four `MProd` states became `Prod` (the field order of our toolchain's
  `Prod` state is not `MProd`'s: `(Option …) × (Array … × Nat)`), `Walks/IotaMajor`'s old hunk
  dropped (upstream rewrote the arm, and the new text builds). ConLeche, ConRonArena,
  ConRonBridge build. 208 `CHANGED` markers.
* 07:17–07:22 stage 3a: `decCI`'s constructor reads the family at `p + 7` (`hd?`), `decCaps`
  `neverZero` at `q + 7` (the old `sortZ` word), `ArrExt.decCI`/`decCaps`, the layout table;
  `Rom/CIEnc`: the constructor's family name after `nF`, `bw neverZero` after `ctors`;
  `RomCI`'s item model (the family name is one more name item), `ErecRd.decCI_split`,
  `InitLink`. The arity codemod over the whole tree (`_tmp/ronsync4/arity.py`, `arity2.py`: 35
  files: binders, match arms, hypotheses with `{fam : NIdx}`), the same as rules in
  `scripts/sync-rules/ronsync4.txt` (plus generic `obtain`/`exact`/`fun` rules for base proofs).
* 07:22–07:28 compile passes (build, ladder `--write` on the failing files, build): ladder round
  1 (5 files, 12 failing theorems, 0 closed), round 2 (10 files, 24 failing, 3 closed at the
  codemod rung). By hand: `KnotMono1`'s store-monotonicity list at the new twin (the new
  `whnfCore` memo and stuck-spine functions, `natBinOpOfName?`/`natBinOpResult`; `ctorFamily`
  is pure now), `DeclCanonEq.ciD` and `installIndD_pre` at the new arity, and a TEMPORARY shim
  `Arena/NatOpShim.lean` (con-ron 4ca283d1's `natOpResult`, verbatim) so that the 754 modules
  behind `PinsNatOp` elaborate until the `Nat` port deletes it (upstream's lead did the same
  for #573's fields).
* 07:28–07:33 compile passes 3–4 (`KnotMono2`: `etaCtorPartialFam` is pure now; the shim's
  `natBinOpName`; `WhnfIotaRefine.decCI_ctorR`, `WhnfDeltaRefine`'s `natZeroOk`/`natSuccOk`
  statements at the family; ladder rounds 3–4: 23 more failing theorems, 4 closed at the codemod
  rung). Left blocked: `WhnfCoreLoop` (the slot and the loop changed: core's), `IndKindEnvProof`
  (`blockCapsAt`/`blockFormers` monadic: ind's), `AsmStubEq`/`AsmFileEq` (the ROM bytes changed:
  `checker.s` regenerated at integration). Tickets so far: 47 (`_tmp/ronsync4/tickets-r1.tsv`).
* 07:33 fan-out: helpers `ronsync4-core` (#556 P-A, #572), `ronsync4-ind` (#573 write side: the
  install, the front, the ROM reader, the declaration arms), `ronsync4-rn` (#573 read side and
  the `Nat` dispatch #556 P-W/P-N, #557), briefs `_tmp/ronsync4/brief-{common,core,ind,rn}.md`,
  3 build threads each (lead 3).
* 07:38–08:12 helpers' unblock commits merged (ind: `TwinStep`, `EntryW`, `IndKindEnvProof` at
  the monadic install, proved; rn: the `Nat` dispatch ported, `NatOpShim` deleted, the readers by
  the family; core: `whnf_core` is the loop now, the pending keys a stack slice, the memo and
  stuck-spine functions with generated models). One conflict (`IndArmFns`' write-set lists).
  Interface for core: `Arena/ErecRdCV.lean` (`decCV_rd1`, `decCI_rec_rd`, moved verbatim from
  `WhnfIotaRecRefine`). `R_NATIVE_NAT_COMPUTATION` (only user: the deleted `reduce_nat_wf`) goes at
  integration (a renumbering rebuilds every module).
* 08:21 core finished (0 sorry in its area): `whnf_core` is the loop (the knot's slot keeps no memo
  of its own, mirroring the twin), the pending keys a stack slice from the entry top (the cheap
  keys a suffix of it), the tag tests (`isStuckHead`, `whnfCoreKey`, `whnfCoreCheapSafe`,
  `whnfCoreStoresDone`) branch-free bit masks (the first version with `if` chains made the
  generated loop model time out at 10× the heartbeats); new `whnf_core_lookup_at`,
  `whnf_core_store_{chain,keys,cheap_keys}`, `iota_target` (`(1, mI)` for `some (mI + 1)`),
  `whnf_stuck`; `whnf_core_step` takes the spine head. Two capacity aborts (stack full at a key
  push, stack top past `SPN` at entry): fixed capacities, no row. Refinements `coreLoop_ref`
  (`PendR`, `LoopInv` over the stack slice), `core_ref`, `step_ref`, the memo functions'
  (`WhnfCoreMemo.lean`), the stuck spine's (`WhnfStuck.lean`, with the twin lemma
  `iotaRecAt_prefix`).
* 08:46 rn finished (0 sorry in its area): `NatBinOp` as a word code (`natBinOpW`, 1‥14, 0 for
  none; `decNatBinOp`), `nat_bin_op_of_name`/`nat_bin_op_result` (one `vcgen` per operation,
  `PinsNatOp`), `reduce_nat_wf`/`nat_op_is_wf`/`nat_op_result`/`nat_bin_op_name`/`const_name_of`
  removed, the shim deleted; `whnf_step` answers a literal reduct at once; the readers by the
  family (`ctor_family`, `iota_case3_at`, `m2c_ctor`, `eta_ctor_partial_fam` read `EREC[q + 7]`;
  no type walk), `iota_no_cert`, `rec_fire_level_count`, `family_never_zero_at` with generated
  models and refinements; `iota_rec_fam` checks the stored facts before case 3. No deviation row.
* 09:26 ind finished (0 sorry in its area): `ctor_info_rec(cv, nP, nF, T)` (8 words, the family at
  `p + 7`), `cons_sum_ctors` with the family, `cons_block_ctors`/`check_block_tail` over the
  constructor groups (new `block_shape_ctor_groups`, `block_ctors_groups`), new
  `member_never_zero` (`former_z` on the declared former; refinement `MemberNZ.lean` under
  `StageR`/`ReadLCOK`/`SortsDen`), `block_caps_fin` writes `neverZero`; the front pairs each
  constructor with its type's name (`vi_order`'s parallel `IFL` slice, `ind_ctor(c, T)`); the ROM
  reader at the new encoding; `ci_eq`/`caps_eq`/`ci_canon_eq` compare the family and `neverZero`.
  No deviation row. `R_NATIVE_NAT_COMPUTATION` dropped (reasons renumbered).
* 09:26–09:52 integration: the helpers' last milestones merged (no conflict), `R_NATIVE_NAT_COMPUTATION`
  dropped, a full build, then the program regenerated (`checker_prog.py`, the generated function
  lists, `preloop_ws.py`, `asm_file.py`: `checker.s`, `pins.bin`): **09:52 the whole library builds
  (4 416 jobs), zero `sorry`, the axiom guards unchanged; `provenance.py check --strict` clean
  (no marker left; 159 L items re-checked); `bump-con-ron.sh --check` ok.**
* 09:55–10:04 verdicts (§5) and performance (§4).

## 2. The ladder's yield against the estimate

Estimate (stage 0): a mixed sync; the codemod rung should pay for the theorems that fail only by
the `ctorInfo` arity, not for the ported functions' refinements. Measured: the arity codemod went
over the whole tree before the first build (stage 3a; 35 files changed by the script, so those
theorems never failed), and the ladder then saw **76 failing theorems in five rounds and closed 7**
(all at the codemod rung, by the generic `obtain`/`exact`/`fun` arity rules); the other 69 were
tickets, closed by the helpers in their areas along with the ports. As in ronsync3 the ladder was
mostly the compile-pass tool (turning failing theorems into `sorry` tickets so the modules behind
them elaborate); the codemod rules paid where the base proof differed from the new one only by the
family's binder. What the ladder cannot do — definitions and statements that fail (the TEMPORARY
`natOpResult` shim, `KnotMono1`'s list, `ciD`, the `decCI_ctorR` statements) — the lead fixed by
hand in three compile passes before the fan-out, so that each helper started with its area
elaborating as far as its own changes allowed.

## 3. Statement changes of the final theorems

None. No file under `ConAgua/Final`, `ConAgua/Audit`, `ConAgua/E2E` changed; upstream's capstone
statements did not change either.

## 4. Performance

Against master `dfe9fbdd7`, both binaries `make` from the committed `checker.s`, `Init` (Lean
4.35's export, `_tmp/fixtures/init/init435.ndjson`), CPU 44 (one thread) or 24–39 (`--jobs=16`):

| | master | ronsync4 | Δ |
|---|---:|---:|---:|
| `Init`, `instructions:u`, one thread (`perf stat`; `bench.py` agrees: 223 412 M / 217 202 M) | 223 407 M | 217 200 M | **−2.78 %** |
| `Init`, peak RSS, one thread | 631 MB | 620 MB | −1.7 % |
| `Init`, peak RSS, `--jobs=16` | 768 MB | 768 MB | 0 % |
| `Init` wall, `--jobs=16` (16 paired rounds, load 31–35) | 7.69 s | 8.20 s | mean −1.8 % [−11.9, +8.4], p = 0.61 |
| `Init` wall, one thread (`bench.py`, 12 interleaved rounds, load 134) | 37.2 s | 38.9 s | spread 142–161 %: not a measurement |

The wall times could not be measured: the machine's load stayed between 30 and 134 the whole
time (another job's, not ours; the coordinator also reported the disk filling), so the
interleaved rounds' spread is larger than any effect (ronsync3 measured 17.2 s and 3.16 s at load
≈ 1). The instruction count is load-independent: −2.78 %, against upstream's −5.61 % for the whole
task #152 on its own binary (#572 alone +2.7 % there; the stuck spine −5.5 %). No regression in
instructions or memory; the wall comparison should be repeated on a quiet machine (or by
`perf-overview.py` after the landing).

## 5. Results

* **Proofs.** Zero `sorry`; the axiom guards unchanged; the whole library builds; every gate
  green (`gates.sh`: 15 OK).
* **Provenance.** `provenance.py check --strict`: every citation exact at con-ron c78714ac,
  con-leche ca6af099; no marker left (159 L items re-checked).
* **Verdicts.** `diff-e2e --tests` at con-leche ca6af099 with `--refs` (con-ron c78714ac,
  e2e-ref): 726/726 agree, UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF 0; 7 skipped (con-leche's
  `E2E_FLAGS` fixtures, D49). `e2e.py --latest ''`: 780 fixtures, all agree (2 time out in all
  three).
* **Deviations.** None added (no aborts beyond fixed capacities: the pending-key stack).
* **Statements.** No final statement changed.

### What went wrong

* The first full build after the bump stopped at only 8 failing modules, but they blocked 760 of
  1421 modules; three lead compile passes (the ladder for theorems, hand fixes for definitions and
  statements, a TEMPORARY shim for the removed `natOpResult`) before the fan-out kept the helpers
  from blocking each other for long, but the helpers still needed one round of "make your
  failing modules elaborate first" before their real work (ronsync3's lesson, applied earlier).
* A merge into the worktree during a running build (lead): the wrapper caught it (nothing
  published), a rebuild fixed it.
* The core helper's first loop with `if`-chain tag tests made the generated model time out even at
  10× the heartbeats; branch-free bit masks fixed it.
* The wall-time comparison could not be done (load, above).
