# Lane presync3: preparing the con-ron sync 01ecb31c → 4ca283d1

Lane of 2026-11-11 (Opus), from master `4f5c4a14c`. The task (user): "there is a new sync coming
up. Decide what you want to do now (e.g. lockstep tactic, or more generated models) before it to
make it less painful, then sync again." A separate lane does the sync after this one. The sync:
con-ron `01ecb31c → 4ca283d1`, con-leche `210a580e → eb2c5939`, upstream tasks #149 (projection
guard field loop, basis blocks installed like any other, the reader's reasons), #150 (cached twins,
binder congruence, wider unit-like η, maximum `Nat` size) and #151 (no computation moved). The
`--olean` changes stay out (D44). Constraints: no L program change, no final statement change, no
new axiom; only proofs and the generator are reshaped.

## 1. Footprint

`scripts/bump-con-ron.sh --report 4ca283d1` (`_tmp/bump-4ca283d1/report.{md,json}`), then a
classifier over the declarations it lists (`_tmp/presync3/fp.py`, outside the repository).

**Upstream.** con-ron: 51 definitions changed, 50 new, 27 removed; types `IIndCaps` (five fields
gone: `etaCtor`, `etaParams`, `etaFields`, `unitlike`, `unitParams`; 48 mentioning declarations of
ours) and `Pins` (`maxNatSize` added; 1). con-leche: 77 changed, 247 new, 117 removed. Its
`Expr`/`Name`/`Level`/`Literal` changes are the dropped `deriving DecidableEq` (#554/#551; 1 741
declarations of ours "mention" them, none depends on the derived instance by name; see §5 for the
two patches this hits). `pins/` did not move.

**L items** to re-check: 173 in 39 files (124 changed citations, 52 gone, 81 through a changed
callee). The large groups: `DefEq` 36 (`defeq_peel`/`defeq_lams` → `defeq_binders`; the η and
unit-like certificates), `IndParts` 29 (`block_shape*` → `read_block`, mostly gone), `WhnfM2C` 24
and `WhnfIota` 4 (η rescue through the projection table), `Infer` 22 (projection guard rows; the
inference arms only by citation), the Nat ops 30 (every one cites `natOpResult`; only
`nat_op_result`, `nat_pow_lit`, `top_lit` change, `pow_nat` is new), `WhnfDelta` 16
(`reduce_nat`'s `succ`), `IndInstall` 12 (caps, tables), `RecCheck` 8, `WalkLift` 7 (gone:
`instantiate1Lift` → `instantiateLift`).

**Proof declarations** that mention a changed twin function or an affected L item, or carry its
`@[refines]` (plus the mentioners of `IIndCaps` and `Pins`): **697 in 226 files, 396 theorems**.

| form (theorems) | count | lines |
|---|---:|---:|
| call-by-call walks (`rcases h : callW` / `triple_of_callW`, reproof.md §2's measure) | 50 | 4 646 |
| model-arm walks (`fooW.armN`, `ipK_inv`, `of_K`, no `vcgen`/`grind`) | 22 | 1 722 |
| declarative, ≤ 12 lines (`vcgen`/`grind`/`finish`/`sym`) | 15 | 190 |
| declarative, longer | 39 | 1 309 |
| manual, > 12 lines | 95 | 4 777 |
| manual, ≤ 12 lines | 175 | 1 703 |

Hand specs (a triple over an L function with no `l_model`, not `@[refines]`): 37. Twenty are
the Nat-op primitives (`nat_add`, `nat_mul`, …, `pv` posts, kept by mgen5 §4), whose L code does
not change; the rest (`close_telescope`, `abstract_prefix`, `block_caps_*`, `er_sl_eq`,
`m2c_const_view`, `rom_items`, `intern_all_pins_rom`, `pi_binders`, `rec7`, …) belong to functions
whose code the sync rewrites or does not touch at all. Theorems with a positional `⟨…⟩` of five or
more parts: 134 (406 sites), nearly all tuples of a callee's results, not invariants. Positional
invariant constructions in the footprint: `PinsFull.congr`, the `IIndCaps` constructions of
`CIReadRefCaps` and `RomCI` (fixed in batch 2).

**What the mention count overstates.** Linking each declaration to the twin functions it names:
of the 72 walks, 14 belong to removed functions (`atBlockGo`, `checkBasisBlock`, `defeqPeel`,
`lamPair?`, `blockCounts?`, `blockMemberCounts?`, the `instantiate1Lift` arms: deleted, not
re-proved), 7 are about functions whose change is a citation or one arm (`quickDefEq`,
`targetRecPins`, `natOpResult`), and 36–50 sit in functions whose algorithm changes: the closers
(one pass), the tables (#495), the projection guard rows, the caps, `check_decl`'s split. Their
callers are insulated already: they use the callee's `…W_ok`/`_refines` statement, which the sync
keeps (con-ron's own closers keep `closeTelescope`'s meaning). So the re-proving concentrates in
the rewritten functions and in the ~50 new twin functions, not in the existing walks.

**The ROM.** The raw-`EREC` relations the user named (`Rom/PinSets`' `PinSetR`/`SliceR`,
`DivModTypePins`, `CIReadRefBase`, `BlockRecLpsOk`) are not touched: `INatOpPinSet` and `pins/` did
not change, and `CIReadRefBase`/`BlockRecLpsOk` use `arr64 EREC` only for frame and size facts of
code that stays. The sync reaches the ROM only through the CI capability encoding (`CIEnc`,
`CIReadRefCaps`: byte offsets of the five dropped fields), `PinsFull` (the new maximum) and
`intern_reserved_pins`/`intern_all_pins`. By the user's rule ("in the sync that touches them") the
move behind the record reader is **not** done now (coordinator agreed).

**The ladder** (`scripts/reproof-ladder.py`) has no dry estimate: it needs the restated tree. My
estimate is in §4.

## 2. Is the generator enough for the new code?

The coordinator's rule for the sync: the new and the rewritten functions get generated models
(`l_model`) and declarative refinements from the start, never new hand `…W` models or `callW`
walks. Checked by writing the new shapes as `l_model` tests (batch 1, `L/ModelGenTest.lean`, last
section):

* `t_pgr` is `proj_guard_rows_go`: a `unified` fuel loop over a telescope, with a read-only callee
  (the loose-bvar test), a total store callee (the push), a `unified` callee that aborts (the
  opening), a self call and an `if`/`else` that pushes or steps over;
* `t_lns` is `lit_nat_sized` / `pow_guard`: two refusals, one against a size read from a global
  (the run's maximum), then an intern;
* `t_setmax` is `intern_all_pins`' prelude: the maximum written into a global.

All three generate and prove their specs with no generator change (3.1 s, 0.96 GB alone). Recipe:
a `unified` model with a load takes `extra [ld64_rdW_specE]` (`Arena/Verdict.lean`);
`ld64_rd_spec` leaves the error post unproved. The other new kinds have generated precedents: the
memo walks `instantiate_lift_go` and `has_loose_bvar_in_go` are `i1l_go`'s and `bvar_b`'s kind
(`WalkLift`, `BvarB`), `defeq_binders` and the η/unit-like certificates `defeq_lams`' and
`struct_eta_cert`'s (`unified` models), and the knot-level refinements (`reduce_nat`,
`major_to_ctor`, `check_block`, …) are already `…E` models with `RefE` theorems walked by the
`RefWalk` kit (docs/design/refgen.md §6). **The exceptions** are limb arithmetic: `pow_nat`'s
square-and-multiply and the size in bytes (`size_bytes`, `8·max(len, 1)`) stay hand specs with
`pv` posts, like `nat_mul` (mgen5 §4). The generator's known limits (`g += e`, record stores, store
bounds) are not needed by any new function.

## 3. What was done

### Batch 1 (#284): the regression tests of §2

`L/ModelGenTest.lean` +115 lines (and `import ConAgua.Arena.Verdict` for `ld64_rdW_specE`):
95.9 → 109.4 G instructions (`LEAN_NUM_THREADS=1`, `perf stat`), 10.0 → 11.2 s, 1.15 → 1.26 GB.
A scratch module first (`ModelGenR3`); folded into the test file at the coordinator's request.

### Batch 2 (#285): invariants built by field name where the sync changes them

* `IIndCaps` built by field name in `Rom/CIReadRefCaps` (two sites) and `Arena/RomCI`
  (`sim_caps`), so the five dropped fields are one codemod rule (deleting `f := v,`), checked on
  both files with the rules file of §4;
* `PinsFull.congr` (`Arena/Tiers`) by field name, so the new maximum is one field more; every other
  construction of `PinsFull` (`RomPins`) was already by name.

Instructions unchanged (Tiers 10.70 → 10.71 G, CIReadRefCaps 25.12 → 25.07 G, RomCI 15.24 →
15.23 G); memory unchanged (0.94–1.08 GB).

### Not done, and why

* **More generated models in the footprint.** Each remaining hand model there is either of a
  function the sync rewrites (`close_telescope`, `abstract_prefix`, `close_lams`: the one-pass
  closers; `er_sl_eq`, `block_caps_*`: the caps), where a conversion now converts code that is about
  to go, or of a function whose code does not change (`rom_items`: the caps change the ROM data,
  not the item interpreter; the Nat primitives). Neither saves sync work. The new code is
  generated from the start (§2).
* **mgen5's follow-ups** (the store-bound guard option: `lh_push`, `lh_mk`, `name_put`,
  `level_put`, `expr_put`; the `LevelSubstL` batch): none of these functions is in the footprint.
* **The ROM move**: §1.
* **A walk tactic**: §3.1.

### 3.1 The walk tactic (helper `presync3-walk`)

**Not built.** The footprint has 72 walks, so the brief's threshold (> 40) asked for a measured
prototype. The coordinator's yardstick: generated model plus the existing kit, not today's hand
walks. The project already has a lockstep kit: `Arena/RefWalk.lean` (25 rules over `RefE`, rolled
out by refwalk1–11) for `unified` models, and `SimLib`/`RecSim` (`Sim`/`RSim`) for ok models. A
generator/registry on top of it was measured and rejected in refgen §3–5.

The helper `presync3-walk` built `Arena/ModelWalk.lean` (225 code lines: 41 of lemmas, 184 of meta
code; `walk_arm`, `walk_split`, `walk_call`/`walk_sim`/`walk_only`). It works over the `Sim` and
`RSim` kits, has no registry, and when it is stuck it names the guards no hypothesis closes. It
rewrote five footprint walks over generated models:

| walk | before | after | |
|---|---:|---:|---:|
| `btsW_ok` (`IndDeclConstsTable`) | 41 | 31 | −24 % |
| `pbW_ok` (`IndSumSpec/StructProjBodies`, already the `Sim` kit) | 63 | 55 | −13 % |
| `spbW_ok` (same file) | 63 | 42 | −33 % |
| `closeLamsW_ok` (`RecClassSpec/CloseLams`) | 51 | 36 | −29 % |
| `cW_sim` (`RecClassSpec/MnW`, already the `RSim` kit) | 50 | 40 | −20 % |
| **total** (proof lines) | **268** | **204** | **−24 %** |

The same lemmas used by hand, without the tactic, would give about 222 (−17 %): the tactic adds
about 7 points. Instructions (`LEAN_NUM_THREADS=1`, whole module, interleaved runs) are flat:
IndDeclConstsTable 24.0 → 24.2 G, StructProjBodies 11.6 → 11.8 G, CloseLams 38.2 → 38.1 G, MnW
41.2 → 41.9 G; RSS 1.0–1.2 GB; ModelWalk itself 6.3 G once. What stays manual is most of the
remaining 204 lines: decoded facts and their transports, guard arithmetic, the twin's own
`if`/`match`, the twin unfolded, fuel cases, the final post. That is the share refgen found for
`RefE`. The go bar (≥ 40 % fewer lines, no module 2× slower) is not met, and the sync's new code
gets generated models and `RefE`/`RefWalk` proofs anyway (§2). The prototype stays on branch
`presync3-walk` (not landed; its five samples belong to functions the sync rewrites).

## 4. The starting kit

### Rules file

`scripts/sync-rules/ronsync3.txt` (`vocab_hook vocab_attr.py`), the renames upstream made that a
regex can carry: `blockCounts?`/`blockMemberCounts?` lose the `?` (and
`blockMemberCounts?_spec`), `blockShape?_installS` → `readBlock_installS`, `lamPair?` →
`binderPair?`, `inst1LiftArm*` → `instLiftArm*`, `instantiate1Lift{Go,Fast}` →
`instantiateLift{Go,Fast}` (with `_succ`/`_zero`), `openPisAtFvarsFGo` → `openPisRawGo`,
`etaRescueOk` → `etaRescueTable?`, `internAllPins pins` → `internAllPins pins maxNatSizeDefault`
(our statements at the default maximum; see stage 1), and the five `IIndCaps` field deletions.
Deliberately no rule for `checkDecl` → `checkDeclKind` (one regex cannot tell the arms'
`@[refines]` from the headline's). Shape changes (`Option` → `Except` of the reader,
`blockTables`' `Option (List IProjTable)`, `checkStructProjTable` over a table, `defeqBinders`' new
arguments) are restated by hand in stage 3b; add a rule for every mechanical argument change found
then.

### Stage plan

PLAN.md "Bumping the twin", with these specifics.

**Stage 1–2 (bump).** `scripts/bump-con-ron.sh 4ca283d1`. Two patches conflict
(`con-leche/0001-withptreq-shim`, `con-ron/0002-bridge-toolchain`, both in con-leche's
`Kernel/Expr.lean` and `Kernel/Name.lean`): #551/#554 dropped `deriving DecidableEq` for
pointer-first `decEqPtr`/`decEq`; check whether the shim is still needed at all before rebasing it.
Decide here: **`--max-nat-size`.** con-leche's `E2E_FLAGS` pass it to some fixtures; without it in
`main.c` those fixtures' verdicts can differ. Either `main.c` parses it and hands it to the checker
(a pin word written at startup; the final theorems then hold at every maximum, like upstream's), or
the maximum is fixed at 134 217 728 and those fixtures get a `## Deliberate` row in
docs/deviations.md. The rules file assumes the default in our twin statements; change that one rule
if the flag is ported.

**Stage 3a (interface, the lead alone)**, one file per encoding, `grind` sets registered with
`vocab_attr.py`:

* `Arena/Tiers.lean`: `PinsFull` gains the maximum (a word of `PINS`, the table grows by one; the
  relation is upstream's `Pins.maxNatSize`), `PinsR` unchanged; `intern_reserved_pins` writes the
  default, `intern_all_pins` the run's value.
* `Arena/EnvRec.lean`, `Rom/CIEnc.lean`, `Rom/CIReadRefCaps.lean`: the caps. Recommended: keep the
  15-word `IIndCaps` record's offsets in `EREC` (the five words become unwritten and unread, as the
  three unread words already are), so no offset in `DefEqStuck*`, `WhnfIota`, `IcaW`, `EnvRec`
  moves; drop the five fields from the ROM's `encCaps` (the bytes do change; `CIReadRefCaps` loses the
  five fields' `u64_at`/`hword` lines).
* A small vocabulary for the reader's `Except` as our `Option` (`Except.toOption`, upstream's
  `readBlock_spec` style) and for the projection table read by the η readers (`fe.findTable? T`:
  `ctor`, `numParams`, `numFields`).
* `natSizeBytes` over a limb slice (`8 · max(len, 1)` for a normalised slice; upstream proves the
  equation with `log2` once), beside the Nat vocabulary.

**Stage 3b (statements).** The changed ones: `checkDecl`'s refinement (now `checkDeclKind`, the
flush, `basisNamesOk`; `DeclCheckT`'s `ArmsE`/`cd_arm`/`cd_ref` and the five `*_loopT`), the arms
(`checkDeclKind`), `read_block` and its stretches (`IndParts`, `IndPartsSpec/*`, `IndT/CheckIndDecl`),
`block_counts`/`block_member_counts` (an `Except`), `block_tables`/`decl_tables`/`decl_constants`
(`IndDeclConsts*`), `check_struct_proj_table` (over a table), `check_block_tables`/`check_block_tail`
(`IndT/Tail*`), `struct_proj_bodies(_go)` (gains the values), `quick_defeq`'s two binder arms, the η
certificates and `major_to_ctor`'s rescue, `nat_op_result` (the refusals), `reduce_nat`'s `succ`,
`lit_shape_ok`'s `Nat` arms, `reduce_elem_ok`, `intern_all_pins` (and the `Final/Twin*`,
`Checker/Pipeline`, `PipeRest`, `RomProg`, `Rom/Stage`, `E2E/*` statements that name it). Delete
the theorems of the removed functions: the basis install (`BasisL`, `DeclBasisRef`, `DeclBasisSpec`,
`BasisBlockT/C`, `Checker/BasisBlockProg`), `IndT/Shapeless`, `DefEqMidPeel`/`DefEqMidLams`' peel
and lams, `WalkLift`/`WalkLiftRefine`/`TeleLift` (replaced by the `instantiate_lift` walk), the
`tower_slots_all` loop, `opf_go`.

**Rule for every new or rewritten function** (coordinator, 2026-11-11): a generated model
(`l_model`, `unified` where it can fail) and a declarative refinement, `RefE` with the `RefWalk` kit
(docs/design/refgen.md §6) or a short `vcgen`/`grind` triple; no new hand `…W` model, no new
`callW` walk. Exceptions: `pow_nat` and `size_bytes` (limb arithmetic, hand specs with `pv` posts,
as `nat_mul`). Recipe: a `unified` model with loads takes `extra [ld64_rdW_specE]`. Write these
three lines into every helper brief.

**Stage 3c (ladder)**: `scripts/reproof-ladder.py --rules scripts/sync-rules/ronsync3.txt --write`.
Expected yield: of the 396 footprint theorems, about 70 are deleted with their functions; of the
other ~325, the citation-only and callee-insulated ones (roughly 200–240: the Nat primitives, the
inference arms, the closers' and tables' callers, the IIndCaps mentioners that read only `eta`,
`all`, `nparams`, `nIdx`, `ctors`) should close at rungs (i)–(ii); about 80–120 stay tickets,
nearly all in the rewritten functions, plus the new proofs of ~50 new twin functions.

**Stage 3d (fan-out)**, three helpers on disjoint files, the lead keeping the interface files and
the final statements:

* **decl** (#493, #494): `Arena/DeclArms`, `DeclStep`, `DeclCheckT`, `DeclCheckLoop`, `DeclAxQuotT`,
  `DeclCrpT`, `DeclDefnT`, `DeclValSpec`, `DeclReduceSpec2`; the basis files to delete; `IndParts`,
  `IndPartsSpec/*`, `IndT/CheckIndDecl`, `IndT/Shapeless`; `IndDeclConsts*`, `IndexBuild`;
  `StubNames`, `StubNamesRefine`, `RecCheck` (`target_rec_pins`' message), `RecGen` and
  `Verdict/IndBHdr` (`class_const_ok`), `StrLit*` (`lit_shape_ok`); `Verdict/IndBRecPins`.
* **ind** (#495, the closers, the opener, #492 and L7): `WalkLift*`, `TeleLift`, `IndRealIlpP` →
  the `instantiate_lift` walk; `IndSum`, `IndSumSpec/StructProjBodies`, `IndRealSctC`; `IndInstall`,
  `IndInstallSpec/{IcaW,BlockCapsAt}`, `IndT/{Tail,TailRef,TailStream,Block*}`; `IndPos`
  (`close_telescope`), `RecClass` (`close_lams`), `RecCheck` (`abstract_prefix`) with their spec
  files; `StubInd` (`open_pis_at_fvars_f`), `IndRealOpf3`; `Infer`'s `proj_guard_rows*`,
  `ProjGuardRows*`, `ProjGuardRef`, and the new window walk.
* **core** (#515, #519, #520): `DefEq` and `DefEqMid*`/`DefEqStuck*` (`defeq_binders`, the η and
  unit-like certificates), `KnotMono2`; `WhnfIota*`, `WhnfM2C*`, `EtaRescueRef`, `IotaCase3Ref`,
  `FormerNZRef`, `Verdict/PosFt`; the Nat files (`NatArms`, `WhnfDelta*`, `Refine`, the new
  `pow_nat`), `RomPins`, `RomCI`, `RomItems`, `Rom/CIEnc`, `Rom/CIReadRefCaps`, `InitLink`.

## 5. Recommendation for the sync

1. Do the `--max-nat-size` decision and the caps layout decision (keep the `EREC` offsets) before
   stage 3a: both decide which files move at all.
2. Stage 3a is small (four vocabulary pieces above); do it before any helper starts.
3. Restate, run the ladder with `ronsync3.txt`, then fan out by the three file sets above, each
   brief carrying the "generated + declarative" rule and its two exceptions.
4. Expect most of the hand work in the new code (≈50 twin functions) and in the rewritten
   functions; the existing walks' callers should come back at the ladder's first rungs.
