# Lane `tierswitch`: the store library on tiered arrays (journal)

Branch `tierswitch`, worktree `_tmp/wt/tierswitch`. Goal: fix D35. Every node store keeps one
word array per tier (tier `t` of array `a` is array `a + 256`, lane tierarr's `ld64t`/`st64t`),
as con-ron keeps one `Tbl` per constructor per tier (handle bit 27). Background:
docs/design/tierarr.md (the compiler feature, KSTP on tiered arrays), docs/design/tieracc.md (the
accessors that confine the layout to the store library).

## Phase 1: the L side, unproved

### Layout

* **Records** (`TRec.ld`/`st`, `ConsLib.cpMid`/`cpWr`): node `i` of tier `t` at
  `ra⟨t⟩[i * w + f]` (was `ra[i * 2w + t * w + f]`). `TRec.ad R j f = j * w + f` (no tier).
* **Counts**: unchanged, `CTL[ca + t]`.
* **Slot tables** (KSTP, `ConsLib`): one table per tier array `sa⟨t⟩`, one formula for both
  tiers: words `0`, `1` hold `n − SN0` and the offset `o`; the table starts at word `2 + o`;
  growth ping-pongs `o = 0 ↔ 4 n'` upward and aborts if `2 + o' + 2 n' > len`. Gone: tier 1's
  mirrored `len − o − 2n`, the half bound `H`. `consMinWords` = `2 + 2 SN0` = 18 per tier array.
* **Columns** (DER 42–46, HP/LP 55–61): `col⟨t⟩[i]` (was `col[2 i + t]`); the `mk_*` writes take
  the tier in a local (`tr`, a store's tier must be simple).
* **Matchers** (`lit_match`, `ls_match`, `nstr_match`, the `mc` conditions): `REC⟨t⟩[i * w + f]`.
* **Room tests**: per tier, `len(R⟨t⟩) >> log w <= c` (was `len(R) >> log 2w`).
* **Entry** (`Checker/Entry.lean`): `wordArrays` = 318 (tier-1 ids up to `61 + 256`),
  `slotArrs` also lists the tier-1 slot arrays.

### Building the prototype

The L changes break the library's proofs (the record/slot/column addresses, the `_raw` iffs, the
write-set lists). For the prototype every failing theorem got `sorry` (statement unchanged) by
`_tmp/tierswitch/sorryfy.py` over the build log, in rounds (`_tmp/tierswitch/round.sh`,
`loop.sh`), until `ConAgua.Checker.Prog` built: 14 rounds, 90 `sorry`s in 54 files (the
library: ConsLibSpec 12, ExprMk 6, StoreFields 3, the store and `*Refine` files 1–3 each,
ConsLibRel, ArenaRel, DerRelBase; outside it: hand-written write-set lists `closedA … [AREC, …]`
(WriteSets, IndRealNames, IndRealAbs/Opf/Spine, StageInst1, WhnfDeltaRefine/2: each must list the
tier-1 ids too, a `st64t` writes `a` and `a + 256`), and the three known layout leaks
(WhnfSpineArgs, InferBodySpine, WhnfIotaRefine3)). Then `AsmEmit` → `_tmp/tierswitch/tier.s`
(nw 318, region 10.0 TB of `MAP_NORESERVE` address space, was 7.4 TB; 128 TB available).
Commit `tierswitch` at the end of phase 1.

### Verdicts

`bench.py --set all --reps 0 --no-conron --no-ref`, master's `asm/checker.s` (165a58ab) against
`tier.s`: **675 fixtures, 0 disagreements** (408 accept, 261 error, 3 reject-front, 2 timeout, 1
exhausted: `stack_fuel_offset`, as on master).

### Speed and memory

`bench.py --set full --reps 3` (18 fixtures, load ~27, `_tmp/tierswitch/bench_full.{log,json}`):

| system | instructions | cycles (median) | wall |
|---|---:|---:|---:|
| base | 1.000 | 1.000 | 1.000 |
| tier | 1.014 | 1.050 | 1.025 |

Cycles and wall were very noisy (per-run spreads 40–140 %); a second run on the five large
fixtures pinned to two cores, 5 reps (`bench_big.{log,json}`) gave cycles 0.882, wall 0.877.
Minimum over the runs (the least disturbed run), cycles in G:

| fixture | instr base → tier | min cycles base → tier | RSS base → tier |
|---|---|---|---|
| app-lam | 64.8 → 68.2 G (+5.3 %) | 48.2 → 40.3 (−16 %) | 4110 → 3204 MB (−22 %) |
| beta-ladder | 17.4 → 18.4 G (+5.6 %) | 9.9 → 9.7 | 1212 → 943 MB (−22 %) |
| let-ladder | 9.27 → 9.77 G (+5.3 %) | | 628 → 478 MB (−24 %) |
| eager_open_nat_control | 25.8 → 27.0 G (+4.6 %) | 11.8 → 12.2 (+3 %) | 1446 → 1194 MB (−17 %) |
| c04a_restart_70 | 26.0 → 26.6 G (+2.2 %) | 10.9 → 11.1 (+2 %) | 702 → 579 MB (−18 %) |
| c03d_pi_depth_1030 | 4.32 → 4.61 G (+6.8 %) | | 345 → 303 MB (−12 %) |
| c05b | 20.1 → 20.3 G (+0.8 %) | | 866 → 819 MB (−5 %) |
| Init (init435) | 372.9 → 367.0 G (−1.6 %) | 128.2 → 124.7 (−3 %) | 1517 → 1384 MB (−9 %) |
| small fixtures | ±3 % | | 27 MB = |

Where the instructions come from: a tiered access costs four instructions for the descriptor
block (`mov t, rdx; and 1; shl 12; add r15`) and, with a computed tier (`R⟦h⟧.f`: `(h >> 27) & 1`),
a spill of the tier to a temporary; the index arithmetic it saves is about two instructions, and
in the probe loops the extra register (`rdx`) pushes a local out of its register (`app_find`: the
slot base `b` moves to the stack). Init's instructions go down: KSTP's tier-1 mirror arithmetic
(`len − o − 2n`) and the `if t == 0` branches are gone. Possible follow-ups, not in this
prototype: a cheaper descriptor sequence in the compiler (lane blkcopy owns `Compiler/*`), and
`R⟦h⟧.f` passing `h >> 27` (the access masks the tier itself; one `and` less per handle read).

## Phase 2: proofs

Coordinator (2026-10-24): approved; the per-access tier cost goes to a compiler lane; the `R⟦h⟧.f`
→ `h >> 27` trick in the library is fine. Split with lane tierpool (its message, agreed): this lane
owns `wordArrays`, `slotArrs`, `consMinWords`, `capCheckBody`'s loop and `CapsOK`'s first
conjunct; tierpool owns `capTail`, the pool conjuncts at the end of `CapsOK`/`CapsW`, `CapsOK.pool`
and the pool part of `arenaR_loadMem`; neither restructures the other's parts of the store files.

### The library, bottom up

* `SlotGrow.lean`: the tier-array facts (`tierA_of_le`, `tierA_inj`, `tierA_ne`, `tierA_ne_tier`,
  `ne_tierA`, `tierA_cases'`). `omega` does not see facts whose type is the `abbrev ArrId`
  (it reads them as atoms of a non-`Nat` type), so the statements take `Nat` and the proofs go
  through `show … : Nat`.
* `TRec.lean`: `TRec.ld` passes `tierX t` (a handle's `tierE h` as `h >> 27`, the access masks it);
  `evalE_tierX_bind`, `pval_tierX` (`StoreFields`), `mapE_tierX` (`ConsLib`).
* `StoreFields`: `evalE_tld` now evaluates the tier first (the semantics of `ld64t`);
  `tfld_arr_eq`/`tfld_set64_ne` take both tiers' arrays.
* `SlotGrowSpec`: `knW`/`koW`/`krW` read tier `t`'s own array (`krW = koW + 2`); `kgrowM` grows in
  `tierA sa t` only.
* `ConsLibSpec`: the loop, find, growth and push specs over `tierA C.sa (loc 0)`; `ConsOK` gets
  `lt` (the arrays are tier-0 ids); `cpMid`'s `k := c * w` (`k := c` when `w = 1`) splits on
  `C.w = 1`.
* `StoreLib`: `Schema` loses `st`; `Schema.ad i f = i * w + f`; `TierLay` per tier array (size
  below `2^61`: with offset `8 n` and `n < 2^60` the growth's `nb + 4 n` does not wrap — with
  `2^62` it could, the old half-array layout had `n ≤ 2^60` for free); `GrowR` = both tiers'
  `TierLay`; the push and slot lemmas separate tiers by array (`tierA_ne_tier`) instead of by the
  half bound.
* `StoreGrow`: the growth writes only `tierA sa t`; the other tier is `tierR_mono` (no
  `tierR_keep` any more).
* `Frame`: `RLocal` and `Apart` cover both tiers; `apart_hi` excludes the tier-1 twins of arrays
  below `ka`; `MemFrame.tier`.
* `ConsLibRel`: `ConsR.mono`/`setFlag`/`consR_init` over both tiers; `ConsSch.wset` (the interning's
  write set, both tiers); `colLt`; columns written at `tierA A t`.
* Store instances: models read `m.arr64 (tierA X t)` at `i * w + f`; room tests `len(X⟨t⟩)`;
  `_raw` iffs still `Iff.rfl` (`tfld` unfolds to the tiered read).
* `LpColRel`/`DerRelBase`/`DerRel`: `ColT`/`cP` read `A⟨t⟩[i]`; frames take both tiers.
* `ArenaRel`: `storeArrs` lists the tier-1 arrays; `frame_ext` for arrays in `[64, 256)`,
  `frame_above` for the range columns in both tiers; `arenaR_init` needs the tier-1 slot arrays.
* Entry/CapCheck: slot arrays (both tiers) at least `consMinWords` = 18 and below `2^61` words.

### Consumers

Three helpers (whnf/defeq/infer, front/rom/checker/final, promote/decl/ind) and this lane fixed
the consumers; the changes are mechanical and of five kinds:

* Explicit frame lists and write sets name the tier-1 twin (`X + 256`) of every store array they
  name (memo arrays and `POOL` unchanged); `closedA … = true` lemmas are decided over the longer
  lists. `simp` membership over the long lists can hit `maxRecDepth`: `eFrame_cons`
  (`PromoteCIRef1`), `simp only [X]; decide`, or case splits over the ids instead. A
  `decide +kernel` over a membership in such a list ran past memwatch's 16 GB.
* Range hypotheses: low writers `b < 64 ∨ (256 ≤ b ∧ b < 320)` (`lowTierArrs`), high writers
  `64 ≤ b ∧ b < 256` (`not_low_tier`, `ApplyExprRefine`), `DerR.frameM`'s
  `(b < 42 ∨ 46 < b) ∧ (b < 298 ∨ 302 < b)`; `ArenaD.memo` needs `S.arr < 256`.
* The checker's write-set lists (`leafA`, `coreErecA`, `stepA`, `imA`, `coreStageA`, `loopA` and
  the arm sets) are `List.range 320` with the same filters, and the Checker-side tests `a < 320`;
  `scripts/preloop_ws.py` records `st64t` and tier copies as writing `a` and `a + 256`
  (`PreLoopWS*.lean` regenerated); `HighFr`/`PFr` keep every array outside `lowTierArrs`.
* Raw-layout bridges (`WhnfIotaRefine3`'s `lmW`, `HoistWalkRef`, `WhnfSpineArgs`,
  `InferBodySpine`) read `tierA X (tierW h)` at `idxW h * w + f`.
* `ConsSch.wset` unfolded in side conditions (`simp [ConsSch.wset]`).

### Landing numbers

* Diff against master 4bae455b: 187 files, +15957 / −14544 lines (library: 11 files ±750).
* `scripts/lake build ConAgua` from the merged state: 10 m 49 s wall, 66 m user; zero sorry;
  `checkerFile_accepts_remaining`'s statement files unchanged, its `#guard_msgs` axiom checks pass;
  census unchanged (1352 targets, 1328 proven, 11791 / 30421 weighted, sorry sources 0).
* Verdicts, `bench.py --set all --reps 0`, master's `asm/checker.s` against this branch's: 675
  fixtures, 0 disagreements.
* `bench.py --set full --reps 3` (load ~25, `_tmp/tierswitch/bench_final.{log,json}`):
  instructions 1.034, cycles 1.033, wall 1.025 (geomean over 18). The small fixtures pay about
  +4 M instructions each (the start-up over 318 arrays, cap checks of the tier-1 slot arrays);
  the large ones +3…+7 % (app-lam 64.8 → 68.2 G); Init 366.9 → 366.9 G. RSS: app-lam 4110 →
  3203 MB (−22 %), beta-ladder 1212 → 943 MB (−22 %), let-ladder 629 → 481 MB (−24 %),
  eager_open_nat_control 1445 → 1194 MB (−17 %), c04a 702 → 578 MB (−18 %), Init 1516 → 1383 MB
  (−9 %).
