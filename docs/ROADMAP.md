# Roadmap: from here to "x64 accepts ⇒ consistency"

Written 2026-10-21, after lanes `lang`, `scan`, `compiler`, `lext`, `arena`, `store`, `store2`,
`storelib`, `tables`, `tables2`, `walk`, `imul`, `stageb`, `capstone` (see `DESIGN.md`). Rust is
con-ron's `crates/con-ron-core/src` (`_tmp/ref/con-ron`); "twin" is the vendored arena model
`vendor/con-ron/ConRon/Arena/**` (`AM := StateT AState (Except CheckError)`); Theorem 1 is
`vendor/con-ron/ConRon/Bridge/**`. Line counts are `wc -l`.

## 1. Inventory

Status: **done** = L code + refinement against the twin, no `sorry`; **partial**; **–** = not
started; **n/a** = not ported (types, data, threads, or replaced by a design choice here).

### Phase 0: stores, handles, the monad's primitives (partial)

| Rust module | lines | twin (main functions) | status here |
|---|---:|---|---|
| `ron/hashmap2.rs` | 1213 | `Std.HashMap` in `Store.lean`'s `Tbl` and in `Memos` | done for cons tables (`StoreLib`, open addressing, no resize) and one memo (`Memo`, epoch stamps) |
| `ron/hashmap.rs` | 740 | `Std.HashMap` in `Caches` (`CoreState.lean`) | – (memo library generalising `Memo.lean` planned) |
| `ron/ptr.rs` | 118 | – | n/a (handles replace pointers) |
| `arena/store.rs` | 5041 | `Store.lean`: `Tbl`, the 21 node tables, `derOfView`, `EStore.find?/push`, `enterScratch`/`dropScratch`, binder data | partial: all 21 cons tables (`*Store`/`*Refine`, `ArenaR`), `arenaR_init`; **missing** derived columns, scratch lifecycle, binder datum store |
| `arena/handle.rs` | 548 | `Handle.lean`: `mk`, `tag`, `tier`, `index`, `isPersistent` | done (`decI`/`decE`, `StoreRel.lean`) |
| `arena/monad.rs` | 1564 | `Monad.lean`: `view`, `internE`, `internNodeE`, `internLamE`, `readName/Level/Levels`, `internPersistent*` | partial: `intern*` for every table; **missing** `read*` (readback), `internPersistent*` |
| `arena/intern.rs` | 574 | `Intern.lean`: `internExpr`, `internCV`, `internCI` (con-leche terms → handles) | – (needed for basis blocks and pins: ROM trees, §2) |

### Phase 1: frontend, bytes → stores (validator done, apply not started)

| Rust module | lines | twin | status |
|---|---:|---|---|
| `frontend/scan_fast.rs` | 4513 | none: the twin calls con-leche's `scanLineFwd` | validation done (Stage B, `scanLine_run`, linked to `scanLineFwd`); **record values not produced** |
| `frontend/export_c.rs` | 2808 | `Frontend/ExportC.lean` 631: `parseChunks`, `feedChunk`, `applyFinalLine`, `parseNameEntryD`, `parseLevelEntryD`, expr/decl entries, `StateD` id tables | – |
| `frontend/prepare.rs` | 452 | `Frontend/Prepare.lean`: `prepareD`, `preparePrelude` | – |
| `frontend/prelude.rs` (+ `prelude_text.rs` 1440 data) | 159 | `Frontend/Prelude.lean`: `builtinPreludeE` | – (prelude bytes become ROM, parsed by the same L frontend) |
| `frontend/nat_op_ground.rs` | 646 | `Frontend/NatOpGround.lean`: `usedConsts`, `hoistClosure` | – |
| `frontend/nat_decimal.rs` | 181 | (decimal `Nat` read inside the scanner) | – (limb-pool decimal parse) |
| `frontend/text.rs`, `types.rs`, `scan_types.rs`, `mod.rs` | 185+55+679+116 | `Frontend/Types.lean` | mostly types; n/a |

### Phase 2: environment, pins, declaration checking (not started)

| Rust module | lines | twin (main functions) |
|---|---:|---|
| `arena/env.rs` | 1128 | `Env.lean`: `IFEnv` (`Std.HashMap NIdx (Nat × IConstantInfo)`), `mkIFEnv`, `IFEnv.find?`, `restrictTo` |
| `arena/core_state.rs` | 539 | `CoreState.lean`: `Caches` (14 maps), `ModeMemos`, `Pins` |
| `arena/pins.rs`, `nat_op_pin_set.rs` | 978+183 | `Pins.lean` (`pin*`, `internReservedPins`), `NatOpPinSet.lean` (`internPinSets`) |
| `arena/basis.rs`, `std_axioms.rs`, `trust_axioms.rs` | 258+172+277 | `Basis.lean`, `StdAxioms.lean`, `TrustAxioms.lean`: pinned blocks, matched against records |
| `arena/prop_read.rs` | 580 | `PropRead.lean`: `typeSortPW`, `headProofPW` |
| `arena/canon.rs` | 791 | `Canon.lean`: `canonExprEq`, `IConstantInfo.canonEq` |
| `arena/promote.rs` | 1239 | `Promote.lean` + `PromoteExt.lean`: `promoteE/N/L/Ls`, `promoteCV` |
| `arena/checker.rs`, `checker_base.rs`, `checker_split.rs` | 1138+1202+349 | `Checker.lean` (`installFold`, `checkPendingList`, `installThenCheck`, `internAllPins`), `CheckerBase.lean` (`orElseAttempt`, `attemptSnapshot/Restore`), `CheckerSplit.lean` (`installHeader`, `checkValueGroup`), `Phased.lean` (`AState.worker`) |
| `arena/check_decl.rs`, `decl_check.rs` | 732+3024 | `CheckDecl.lean` (`checkDecl`, `checkDeclStep`), `DeclCheck.lean` (axiom/pin guards, `divModCertProofs`) |

### Phases 3–7: the core (only `bvarBoundMemo` done)

| Rust module | lines | twin | status |
|---|---:|---|---|
| `kernel/level.rs` (+ level parts of `expr_ops.rs`, `core.rs`) | 748 + ~250 | con-leche's pure `Level.isEquiv`/`leq` (fuel `defaultFuel = 10000`) on read-back levels, called from `Core.lean`'s `lvlEq?`/`lvlsEq?`; `ExprOps.lean`'s `substLevelList`, `substLMemoAt`, `instLPGo` | – |
| `arena/expr_ops.rs` | 3893 | `ExprOps.lean` 2270 (112 defs): `instantiate1Go`, `instantiateListGo`, `liftLooseBVarsGo`, `abstract1Go`, `abstractRangeGo`, `instantiate1LiftGo`, `instLPGo`, `bvarBoundGo/Memo`, `fvarRangeGo/Memo`, `fvarLeaves*`, `wscopedB*`, spines (`getAppFn`, `mkAppN`, `instSpine`) | `bvarBoundMemo` done (`Walk`/`WalkRefine`, all node kinds) |
| `arena/core.rs`, whnf part (~6000) | 10381 total | `Core.lean` 1–2440: `whnfCoreStep/Loop/Body`, `whnfStep/Loop`, `whnfApp`, `betaPeel`, `reduceProjCore`, `iotaRecAt`, `majorToCtor`, `reduceNat`, `natOpResult`, `strLitToConstructor`, `unfoldDefinition`, eta certificates | – |
| core.rs, infer part (~1300) | | `Core.lean` 2440–2880: `inferBody`, `inferBodyIO`, `inferLams`, `inferPis`, `inferApp`, `inferProj`, `ensureSort` | – |
| core.rs, defeq part (~2100) | | `Core.lean` 2880–3540: `defeqBody`, `quickDefEq`, `defeqPeel`, `lazyDeltaReduction`, `defeqStuck`, `proofIrrel`, `defeqOffset` | – |
| core.rs knot (~400) + `core_io.rs` 36 | | `coreKnot` (memo wrappers, `takeModeMemos`/`putModeMemos`), `pureFnsA`, `checkFuel` | – |

### Phase 8: inductive types and recursors (not started)

`arena/inductives/*.rs`, 12494 lines: `positivity.rs` 3529, `gen_rec.rs` 2447, `rec_check.rs` 1649,
`block_parts.rs` 1154, `block_install.rs` 924, `sum_install.rs` 817, `struct_parts.rs` 737,
`class_read.rs` 531, `struct_install.rs` 279, `block_tail.rs` 276, the rest 151. Twins:
`Arena/Inductives/*.lean` (≈ 4000 lines): `checkBlock`, `checkBlockTail`, `classGenRecTy`,
`nestOcc`/positivity walks, `targetMajorAt`, `checkSumCtors`, `checkStructProjTable`.

### Phase 9: `Nat`/`String` literal operations (the GMP paths; partial)

| Rust | lines | twin | status |
|---|---:|---|---|
| `ron/nat.rs` | 1080 | Lean `Nat` inside `natOpResult` (`+ - * ^ / % gcd land lor xor shiftLeft shiftRight beq ble`), `natLitToConstructor`, `natPred?`, `isNatZero`, `strLitConsSpine` | `add`, `mul` done (`NatAdd`, `NatMul`, `natAddLit_refinesA`); sub, compare, bit ops, shifts, pow, div/mod, gcd, decimal – |

### Phase 10: driver (not started)

`crates/con-ron/src/driver.rs` 1113 (the chunk loop, `check_decls_driver`), `bin/con-ron.rs` 602
(CLI), `pool.rs` 601 (threads: **n/a**, x64 runs one worker), `keys.rs`, `render.rs`. Twin:
`Arena/Main.lean` (`runPipelineHead`, `runPipelineTail`), `Phased.lean`. Here: one L entry
`check()` plus the C harness (`harness/run.c` style).

### `kernel/*` (n/a or ROM)

`kernel/expr.rs` 1658, `name.rs` 265, `core_k.rs`, `core_types.rs`, `env.rs` 645, `expr_ops.rs` 178,
`prop_when.rs` 316 are con-ron's boxed-term types; the store replaces them (`PropWhen` survives
as data in `IIndCaps`). `pins_text.rs` 26761, `basis_raw.rs` 852, `basis_tables.rs` 593,
`basis_builder.rs`, `basis_names.rs`, `std_axioms.rs`, `trust_axioms.rs` are data, and
`pins_decode.rs` 1334 is a text decoder: they become ROM (constant data, `D.c8[i]`, lane `lext`)
in a tree encoding that one generic L interner reads (§2, "constant terms").

## 2. Cost

### Rates measured so far (DESIGN.md)

| quantity | measured | planning value |
|---|---|---|
| L lines per Rust line | scanner 0.48 (Stage B), `nat_add` 0.62, `nat_mul` 0.53, walk 0.56; stores 0.29, memo 0.3 | 0.5 logic, 0.3 data structures |
| L-side proof (models, arm lemmas, `vcgen` specs) per L line | Stage B 3.3, `nat_add` 2.9, `nat_mul` 3.7, walk 7.5 | 4 |
| refinement against the twin per L line | stores 3–4 (with `StoreLib`), walk 10 (by hand) | 5 (after a view/memo library) |
| link to con-leche per L line (only where the twin calls con-leche directly) | Stage B 2.5 | frontend only |
| CPU per Rust line | Stage B ~0.1 s, walk ~0.15 s, a store table 5–20 s | 0.1–0.15 s |
| automation | every L spec `vcgen` + `finish` so far; refinement half by hand (`WalkRefine`, `MemoRel`, pool uniqueness) | – |
| throughput per lane-day (opus) | Stage B: 1641 L + 9.4k proof; `tables2`: ~400 L + relations; `walk`: 49 L + 2.5k infrastructure | 1500 L scanner-like, 400 L twin-refining |

For calibration: con-ron's own Theorem 2 (Aeneas Rust ⇄ twin, lockstep, `proof/ConRon/Refine2`)
is 100k lines for the same 50k Rust lines; Theorem 1 (twin ⇒ pure) is 118k.

### Estimate per phase

Assumptions: the rates above; proof = 9 × L (4 L-side + 5 refinement) except where noted; L
fuel and errors handled as in §3; no resize, fixed capacities from the harness. Lane-days are
single-lane agent days, before integration (add 50 %).

| # | phase | Rust left | L | proof | lane-days | notes |
|---|---|---:|---:|---:|---:|---|
| 0 | stores rest (derived, scratch, readback, promote-persistent, ROM interner) | ~3.0k | 1.0k | 9k | 3 | library exists |
| 1 | frontend apply (records, id tables, prepare, prelude, ground) | ~5.9k | 2.8k | 22k | 6 | scanner side reuses Stage B and `scanLineFwd` links |
| 2 | env, pins, declarations, promote, canon | 12.6k | 6.0k | 54k | 15 | needs the env record pool |
| 3 | level ops | 1.0k | 0.5k | 5k | 2–3 | new idea: scratch tree heap |
| 4 | expr ops (memoized walks) | 3.8k | 2.0k | 18k | 5 | memo library first |
| 5 | whnf, iota, proj, eta, literal reductions | 6.0k | 3.0k | 27k | 8 | |
| 6 | defeq | 2.1k | 1.1k | 10k | 3 | |
| 7 | infer, the knot, caches | 2.2k | 1.1k | 10k | 3 | mode-memo banks |
| 8 | inductives | 12.5k | 6.0k | 54k | 15 | positivity: deep walks |
| 9 | `Nat`/`String` literal ops | 0.95k | 0.55k | 3k | 3 | div/mod (Knuth D) is most of it |
| 10 | driver, harness, final theorem | 0.3k | 0.15k | 3k | 2 | |
| | **total** | **~50k** | **~24k** | **~215k** | **~65** | ≈ 100 lane-days with integration; 5–6 weeks at 4 lanes |

Build: ~1.5–2 CPU-hours for the whole proof at 0.1–0.15 s per Rust line; keep every file
under ~2 minutes (`Line.lean`, 136 s, is the current worst).

### Parts that need new ideas (each is a design spike, opus)

1. **Memo library with two-word keys and epochs.** Six `Memos` tables keyed `(EIdx × Nat)`, two
   `Nat`-valued, two level ones; 14 `Caches`. `Memo.lean`/`MemoRel.lean` (one table, by hand,
   695 lines) must become a library like `StoreLib` (schema: key width, value width, epoch word).
2. **Selective drop.** `Caches.dropScratchEntries` deletes the entries that name a scratch handle.
   Open addressing cannot delete cheaply. Proposal: two tables per cache, "all persistent" and
   "mentions scratch" (decided from the tier bit at insert), the second cleared by epoch at the
   drop; the relation is "the arena map is the union".
3. **Mode-memo banks.** `takeModeMemos`/`putModeMemos` move six tables out for an eager
   comparison and back. **Audited (lane `final`): eager comparisons nest without a structural
   bound in `.verified` mode** (re-entry through full-grade `r.infer` in `defeqLamsInner`,
   `etaCert`, `iotaCertsFullAux`; at most depth 1 in the trusted modes). Decision: a **bank stack**:
   the six mode tables exist in `D` banks, an eager-depth word selects the bank, entering `defeqE`
   increments it and clears the new bank by epoch, leaving decrements it (the outer bank is
   untouched, which is exactly `putModeMemos saved`). `D` is a capacity (checked at entry, abort
   beyond it). The other eight caches and the store are shared across depths.
4. **Values that are not handles.** `IFEnv`, `IConstantInfo` (lists of names, `IRecRule`s,
   projection tables, `IIndCaps`), `PendingCheck`, `Array EIdx` spines (`getAppSpine`,
   `instSpine`), `List NIdx`: a record pool (bump-allocated words, slices as in `PoolSlice`)
   with decoders as value relations (`decE`'s analogue), and per-call scratch stacks for arrays.
5. **Level comparison without interning.** `lvlEq?` reads levels back and runs con-leche's pure
   `Level.isEquiv`, which builds new levels (`simplify`, `byCases` substitutes params). Interning
   them into the store would break the store relation (the twin does not intern). Needs a scratch
   tree heap reset per call, related to `Level` values by a decoder.
6. **Closures and the knot.** `CoreFnsA` is a record of closures tied by `coreKnot` with a `wrap`
   and `ioView`. L has no function values: one mutually recursive group of L functions with a
   mode word; the refinement is by induction on L fuel against every twin fuel `F ≥ n` (the
   `GoOK n` shape of `WalkRefine`).
7. **Deep recursion.** The walk costs 184 stack bytes per level and runs 3·10^6 deep with a 1 GiB
   stack. whnf/defeq/infer frames are larger and interleave; measure on con-leche's
   `stack_fuel_offset` before deciding on explicit work stacks for the worst walks (positivity,
   `instantiate*` on long spines). Stack exhaustion is already a defined outcome (`rdx = 1`).
8. **Counted twin fuels.** Audited, decisions in §3 (b).
9. **Errors.** Audited, decisions in §3 (c): no recovery in L at all.
10. **Derived columns.** `derOfView` packs `hash32 … * 2^32 + bvar * 65536 + fvar * 2 + lp`
    (con-leche's `packData`). **Audited (lane `final`): no verdict reads the hash bits.** Every read
    of a hash feeds only a parent's hash; every other consumer (`bvarOfData`, `fvarOfData`,
    `lpOfData`, ExprOps) reads `w % 2^32`; no `Hashable` instance uses derived data (handles hash by
    their word); no `Std.HashMap` iteration order reaches a result; Theorem 1 uses
    `derived_exact` only through those three accessors. con-leche's hash-based `beqMemo` is a
    `@[csimp]` of `decide (a = b)`. Decision: **no twin patch**; L computes any transparent hash
    (or none) in the high word, and the derived-column relation relates `w % 2^32` only.
11. **Constant terms.** The basis blocks, std/trust axiom shapes and the pin sets are con-leche
    terms the twin interns (`internExpr`). In L: ROM trees and one generic interner, proved once
    against `internExpr`; the ROM's denotation is fixed by `decide` for the basis, and is free for
    the pins (the theorem holds at every pin list).

## 3. The final theorem

### Shape (landed, lane `final`: `ConAgua/Final/{Twin,Statement}.lean`)

```lean
theorem checker_x64_accepts [Host] (p : Prog) (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0) (hnargs : G.nargs = 0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL)

def PipelineRefines (p : Prog) : Prop :=        -- the one named hypothesis
  ∀ (b : ByteArray) (s8 s64 : List Nat) (N : Nat) (rs : List Word) (m' : Mem),
    System.Platform.numBits = 64 → b.size < 2 ^ 63 → N < 2 ^ 62 →
    L.run p N "check" [] (loadMem b s8 s64) = .ok (rs, m') →
    rs.headD 0 = ACCEPT → TwinAccepts [b]

def TwinAccepts (chunks : List ByteArray) : Prop :=   -- the twin's pipeline, one worker
  ∃ pins sA sB sC sD sE sF pre r ds ipins fe,
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧ internAllPins pins sD = .ok (ipins, sE) ∧
    SeqAccepts .verified ipins ds sE fe sF    -- installFold, then one checkPendingList from sF.worker
```

`loadMem b s8 s64`: byte array 0 is `b`, the other byte arrays (sizes `s8`) and the word arrays
(sizes `s64`) are zero. `ACCEPT = 0x414343455054` (not 0/1/2, so no status word reads as accept).
`HarnessCall` bundles `compile_correct`'s premises on the call (`rdi`, `rsi`, stack room, stack top,
return address, the 32 bytes of machine stack).

Corollaries, both with con-leche's three axioms only (`#guard_msgs` in `Statement.lean`):

* `x64_model_exists V`: on accept, `∃ pins preC rc F env, ConLeche.Frontend.parseChunks [b] = .ok rc ∧
  checkDeclsPure .verified (fueledOps .verified F) pins (preparePrelude preC rc.decls).toList = .ok env
  ∧ Nonempty (Model V env)`: con-leche's own parser on the bytes, con-leche's pure fold, at some pin
  list and some prelude (both free, see below).
* `x64_no_False V (hfalse : jsonWithTheoremFalse [b])`: the machine returns and does not report
  `rdx = 0 ∧ rax = ACCEPT`.

`pipelineRefines_reject` proves `PipelineRefines` for a `check` that always rejects: the hypothesis is
satisfiable, so the theorems are not vacuous in `p`.

**`PipelineRefines`, the contract for the per-function lanes.** Its proof, for the real
`checkerProg`, is the composition of: `ArenaR (loadMem b s8 s64) (AState.init EStore.empty)` (today
`arenaR_init` over `initMem`; it must grow to every twin field, and to the input buffer at byte
array 0); then one refinement per stage of `check`, in the `natAddLit_refinesA` shape
`⦃s = s₀⦄ invoke … ⦃r s' ↦ AM.ok f a₀ ∧ R s'.mem (AM.st f a₀) ∧ AM.res f a₀ = dec r; ⊤⦄`, for
`internReservedPins`, `builtinPreludeE` (prelude bytes in ROM), `parseChunks [b]`, `preparePrelude`,
`internAllPins` (pins in ROM), `installFold`, `AState.worker`, `checkPendingList`; each knot fuel
taken as any `F ≥ n` (`GoOK` shape), each counted fuel as an L counter (§3 (b)); the final
`ACCEPT` returned only after `checkPendingList` answered `.ok ()`. Decisions it fixes:

* **Capacities are not trusted.** `PipelineRefines` holds at every `s8`, `s64`, so `check` must
  read `len8`/`len64` of every array at entry and `abort` unless each meets its minimum (`CTL ≥ 42`,
  `POOL < 2^63`, …: `arenaR_init`'s premises); a full table aborts. The harness may pick any sizes.
* **L fuel `N < 2^62`.** The twin's `2^62` fuels are covered by induction against every `F ≥ n`.
* **The ROM is not trusted.** The pin list is existential in `TwinAccepts` and con-leche's theorems
  hold at every list; the prelude bytes give some `preC` (`builtinPreludeE_run`) whose records are
  checked as part of the stream.
* **One worker.** Phase B is one `checkPendingList` over `pend.toList` from `s'.worker`
  (`SeqAccepts`, `pooledAccepts_of_seq`).
* **The entry.** `check` has no parameters; the input length is `len8(IN)`.

### Trusted base

Kraken's x64 semantics (`Ev`, fuzzed against hardware); the assembler, the printer and the loader
(the printed `compileProg G.tab p "check"` is at `k0`: `hcode`; `harness/check-asm.sh` audits the
printing); the layout (`hG`, `hmem`: the loader put the file's bytes at byte array 0 and zeroed the
other arrays, the table and descriptors as `G` says); the harness (`HarnessCall`: how `ca_enter` is
called; and it prints "accept" exactly on `rdx = 0 ∧ rax = ACCEPT`, `rdx = 1` as "resources
exhausted", anything else as "reject"); buffer to stream (the buffer holds the whole file, read
once: con-ron's `hreads`); `numBits = 64`. Requirement on the harness (not yet written): the
checker's `run.c` must compare `rax` with `ACCEPT` itself, not print `rax` (today's generic
`ConAgua/Compiler/harness/run.c` prints `ok <rax>`).

### How it composes

1. `compile_correct` (`Compiler/Main.lean`): `rdx = 0 ∧ rax = r` ⇒
   `L.run checkerProg N "check" [] m₀ = .ok (r :: _, m')`.
2. **Pipeline refinement** (`PipelineRefines`, a hypothesis until built): from `ArenaR m₀ (AState.init EStore.empty)`
   (`arenaR_init`, extended with every new field) and an L run returning `ACCEPT`, the twin's
   stage runs `hA … hF` exist. It is the sequence of the per-stage refinements, each the
   composition of per-function refinements of the `natAddLit_refinesA`/`bbMemo_refines` shape:
   `⦃s = s₀⦄ invoke … ⦃r s' ↦ AM.ok f a₀ ∧ R s'.mem (AM.st f a₀) ∧ AM.res f a₀ = dec r; ⊤⦄`.
3. **Theorem 1.** `Arena.pooledAccepts_bridge` (`Bridge/Checker/Phased.lean:86`): from
   `FoldOK` at the start, `PinsDenote`, `PersDecl`, `denoteDecls s.store ds = some dsP` and
   `PooledAccepts`, it gives `∃ env' F', denoteFEnv s'.store fe' = some env' ∧
   checkDeclsPure μ (fueledOps μ F') pinsP dsP = .ok env'`, under `hk : CoreSpec .verified
   checkFuel` (`CoreSpec.of_core rfl`) and `hind : IndSpec .verified`
   (`indSpec_of_bridge rfl hk`), both closed. The start facts come from `stages_frame`, which
   chains `internReservedPins_run`, `builtinPreludeE_run`, `parseChunks_run`,
   `preparePrelude_run`, `internAllPins_run`.
4. **con-leche.** `Model.checkDeclsPure_sound_of` gives the model;
   `no_False_theorem_accepted_pure` (`Bridge/Frontend/Capstone.lean`) refutes a `False` theorem.
   The stream's `False` record comes from con-leche's `parseChunks_jsonWithTheoremFalse` and
   `mem_preparePrelude`. Steps 3–4 are `ConAgua/Final/Twin.lean` (`stages_frame`,
   `twinAccepts_pure`, `twinAccepts_model`, `twinAccepts_no_False`), steps 1, 2 and the assembly
   `ConAgua/Final/Statement.lean`.

### Mismatches to resolve

* **(a) Theorem 1's glue** (resolved, lane `final`). con-ron's `stages_*` (in `ConRon/Capstone.lean`,
  which imports Aeneas) are restated in `ConAgua/Final/Twin.lean` on `ConRonBridge` alone, 160
  lines. `stages_frame` now names the stream (`preparePrelude preC rc.decls` with
  `ConLeche.Frontend.parseChunks chunks = .ok rc`) instead of `∃ dsP`, which lets the corollaries
  be stated in con-leche's terms; `stages_false_mem`/`stages_no_False`/`stages_model` collapse
  into `twinAccepts_pure` plus one con-leche lemma each.
* **(b) Fuel** (audited, lane `final`; file:line in DESIGN.md, "The final theorem"). `compile_correct`
  runs L with the machine's `N` (`r14` counts every back-edge and call, so `N` is large, ~10^11),
  and L's fuel bounds nesting only. Decisions:
  * **The `2^62` fuels are not counted in L**: `checkFuel` (one per knot level), `whnfCoreLoopFuel`,
    `whnfLoopFuel`, `defeqLoopFuel` (one per loop step), `lamsFuel` (one per λ pair; exhaustion
    falls back to `defeqLamsInner`, not an error, but each step costs L a loop iteration or call,
    so it is out of reach). Every twin knot level or loop step costs L at least one unit of
    nesting, so with `N < 2^62` the refinements are stated for every twin fuel `F ≥ n`.
  * **Every counted fuel below `2^62` is an explicit L counter**, decremented exactly where the
    twin decrements it, and at zero L does what the twin does: `coreWalkFuel = 4·10^9` (per
    recursive walk call, reset per walk; throws), `storeFuel = nodeCount + 1` (per Π node;
    throws), `hoistClosure`'s `ds.size` (throws), `whnfWalkFuel e = depth e + fuelSlack (1024)`
    in nested positivity (throws a decline; reachable), con-leche's `Level.defaultFuel = 10^4` per
    `leq` (answers **`none`**, read as "no" at nine sites, see below), `peelFuel = 2^24` (per binder;
    at zero **hands the rest to the knot**, same answer but a different path), `unwrapIdDefs`' `4`
    (at zero **returns the term unwrapped so far**; feeds proof irrelevance), and the store
    capacity `idxCap = 2^27` per constructor per tier (`.native` throw). One word each; this
    avoids the rank argument the unreachable ones would otherwise need.
  * **Exhaustion that is an answer, not an error** (L must reproduce the value): `Level.isEquiv`'s
    `none` (`fireOk`, projection typing, `BlockInstall`/`BlockParts`/`SumInstall`'s `isProp`, the
    K-target test: all against `zero`; `defeqSpine`'s same-head shortcut and `targetClassMatch`
    against arbitrary levels), `unwrapIdDefs`, `peelFuel`. Lane E (`levels`) must return the
    three-way `Option Bool`.
* **(c) Errors** (audited, lane `final`). The twin recovers from a thrown error in exactly one
  place: `orElseAttempt` (`CheckerBase.lean:102`), used only by `checkDivModPinLoop`
  (`DeclCheck.lean:613`), the `Nat.div`/`Nat.mod` pin variants. A throw inside one variant's
  attempt (anything but `.native`, so **fuel exhaustion included**) resumes from the pre-attempt
  state with the next variant; `.ok false` continues from the post-attempt state; when no variant
  matches the declaration is **declined** (`.notImplemented`, exit 2: the fold ends, never
  accepts). Every other `.error` match (`installDeclStep`, `checkPendingList`, the frontend's
  `atLine`, `runPipelineTail`) only carries the error to a non-accept verdict. `feedChunk`'s
  "scanner `.err` without a later newline is an incomplete tail" is an ordinary branch on a pure
  result. Decision: **option (i), L recovers nowhere.** Every twin throw, including one inside a
  pin attempt, is an L `abort`; `.ok false` continues from the post-attempt state as in the twin.
  Sound for the accept direction: an accepting L run had no throw inside any attempt, so the twin
  (whose fuels are at least L's) took the same path at the same pin list. Cost: completeness only,
  when a variant the twin would skip by recovery throws in L; the harness then reruns with a ROM
  holding the remaining variants (a different `p`, so `PipelineRefines` must be proved
  parametric in the pin ROM, which it is anyway). The error kinds (reject/decline/error) are not
  distinguished; only `ACCEPT` is interpreted.
* **(d) Pool.** The x64 checker runs phase A (`installFold`) and then phase B on one worker
  (`checkPendingList` from `s'.worker`, as the Rust's sequential `check_decls_phased`), which is
  `PooledAccepts` with `parts = [pend.toList]` (`Arena/Pooled.lean`; the vendored twin has no
  `installThenCheckPhased` any more). L must implement `AState.worker` (drop scratch, clear memos
  and caches: epochs).
* **(e) Relation shape.** Theorem 1 has no relation to L: it is about twin runs. What we need is
  that L's run *produces* twin runs from `AState.init EStore.empty`; `ArenaR` (a relation, not an
  abstraction function, since `Std.HashMap` layouts are history-dependent) must grow to every
  field the twin reads: the store with derived columns, binder data and the scratch flag; the 10
  memos; the 14 caches and mode memos; the pins. Twin *values* in L memory (`StateD`, `IFEnv`,
  `PendingCheck` arrays, `PreludeIx`) get value relations. Exact per-table relations (counts equal
  to `nodes.size`) rule out evicting memo entries (a recomputation would intern extra nodes and
  shift every later handle): tables are sized by the harness and abort when full.
* **(f) Partial vs total.** Fine as is: `Ev` gives termination of the machine; L specs are partial
  (`⊤` error posts); only the accept direction is claimed. Three-outcome theorems
  (`natAddLit_x64`, `bbMemo_x64`) are the expected shape; nothing needs "no abort".
* **(g) Input.** The twin parses `List ByteArray`; L has one buffer, so `chunks = [b]`. Stage B's
  `DriverLink` already relates the whole-buffer driver to `feedChunk` + `applyFinalLine` for
  con-leche; the twin's `parseChunksGo` needs the same lemma (`Bridge/Frontend/Chunks.lean`'s
  `chunkStep_run`, `chunkFinish_run` are the twin-side handles).
* **(h) Verdict.** `check()` returns `(status, records)`; only `ACCEPT` is interpreted. The
  harness prints `rdx = 1` as "resources exhausted" (retry with more fuel, stack or capacity),
  never as accept.

## 4. Next week: lanes

Rules as in `PLAN.md`. This week only lane B edits `ArenaRel.lean`; the others keep their new
relations in their own files as separate conjuncts, merged into `ArenaR` afterwards.

| lane | model | files (owned) | runs in parallel with |
|---|---|---|---|
| A `final` | opus | `ConAgua/Final/*.lean`, `docs/` audit notes | all |
| B `exprops` | opus | `ConAgua/Arena/{MemoLib,View,Lift*,Inst1*}.lean`, `ArenaRel.lean` | all |
| C `nat` | sonnet | `ConAgua/Arena/Nat{Sub,Cmp,Bits,Shift,Pow}.lean`, `NatOpRefine.lean` | all |
| D `front` | opus | `ConAgua/Front/*.lean` | all (reads `Scan/*`, does not edit them) |
| E `levels` (second half of the week) | opus | `ConAgua/Level/*.lean` | after B's memo library lands |

**A `final`: the statement first.** Write `ConAgua/Final/Twin.lean`: restate `stages_frame`,
`stages_model`, `stages_false_mem`, `stages_no_False` from `vendor/con-ron/ConRon/Capstone.lean`
using only `ConRonBridge`; derive `PooledAccepts` from an `installFold` run followed by one
`checkPendingList` run from `s'.worker`. Write `ConAgua/Final/Statement.lean`: `TwinAccepts`,
`checker_x64_accepts` and the two corollaries, proved from `compile_correct` and one named
hypothesis `PipelineRefines checkerProg` (a `Prop`: an accepting L run from `initMem` yields
`TwinAccepts`), not a `sorry`. Then audit and record in DESIGN.md: every twin fuel and where it
decrements (§3 b), every recovery point (§3 c; what happens when no pin variant matches), every
read of the derived hash bits (§2 item 10), whether eager comparisons nest (item 3). Done when
the corollaries check with the standard axioms plus the named hypothesis.

*Status (lane `final` landed):* done as briefed; the statement and decisions are in §3. Requirements
it puts on the other lanes:

* **every lane:** each counted twin fuel below `2^62` in a function you port becomes an L counter
  (§3 (b)); every twin throw is an `abort`, including inside a pin attempt (§3 (c));
* **B `exprops` / derived columns:** the derived-word relation relates `w % 2^32` only (§2 item 10);
  the walk counter for `coreWalkFuel`;
* **E `levels`:** the three-way `Option Bool` of `Level.isEquiv` with the `10^4` counter per `leq`;
* **the knot / whnf lanes:** the mode-memo bank stack (§2 item 3), `peelFuel` and `unwrapIdDefs`'
  `4` reproduced exactly;
* **the driver lane:** `check` reads `len8`/`len64` of every array at entry and aborts unless the
  capacities meet `ArenaR`'s minimums; phase B is one `checkPendingList` from `AState.worker`
  (`SeqAccepts`); the input is byte array 0, read whole; `ArenaR` is established from `loadMem`
  (generalise `arenaR_init` from `initMem` to `loadMem`'s word arrays);
* **the harness:** prints "accept" exactly on `rdx = 0 ∧ rax = ACCEPT`.

**B `exprops`: memo library, then `liftLooseBVars`.** Generalise `Memo.lean`/`MemoRel.lean` to a
schema (key words 1–2, value word, epoch word, `CTL` slots) as `StoreLib` did for the cons
tables; port `bvarBC` onto it. Factor `WalkRefine.lean`'s arena side (handle decoding, `view`
under `ArenaR`, memo set/clear) into `View.lean` so the next walk does not repeat it. Then
`liftLooseBVarsGo` and its arms (`ExprOps.lean`, Rust `expr_ops.rs`): the first walk that interns
its results, memo keyed `(EIdx, Nat)`. Measure refinement lines per L line against the walk's 10;
the target is ≤ 5. If time remains: `instantiate1Go`.

**C `nat`: the remaining limb operations.** Following `NatAdd`/`NatMul` exactly (pool append,
`Grows`, word-level loops with straight-line bodies): `nat_sub` (truncating), `nat_cmp`
(`beq`/`ble`), `land`/`lor`/`xor`, `shiftLeft`/`shiftRight` by a word, `pow` by repeated `nat_mul`
under the twin's `2^24` bound. Then refine the corresponding `natOpResult` arms as
`natAddLit_refinesA` does, with the pin read stated as a hypothesis for now. Leave
div/mod/gcd and decimal parsing for an opus lane; write down what Knuth D needs (normalisation,
`mulhi`, the quotient-digit correction) as the brief for it.

**D `front`: the first records into the store.** Make the Stage B scanner produce the fields
of name and level records (the validator's models already compute their positions). Write the
L version of `parseNameEntryD`/`parseLevelEntryD` (`Arena/Frontend/ExportC.lean`): export id →
handle arrays (`StateD`'s id tables as dense word arrays with an "unset" word), interning through
`intern_nstr`/`intern_nnum` and the level tables, the twin's errors (rebound id, dangling
reference) as `abort`. Relation `StateDR` (id tables ↔ the twin's maps) in its own file; refine
one line of each kind against the twin's per-line step, with `scanLineFwd`'s record as the
interface (Stage B's links to `scanLineFwd` stay valid). Note what an expression record will need
(binder data, `lit` strings, the derived columns).

**E `levels`: comparison on a scratch heap.** Design and build the scratch tree heap (§2 item
5): readback of a level handle into heap nodes, con-leche's `simplify`/`leqCore`/`isEquiv` over the
heap with the `defaultFuel` counter, reset per call; refine `lvlEq?` (including its cache, on B's
memo library) against the twin.

After this week, in order: derived columns and the scratch lifecycle (sonnet, templates), the
env record pool (opus), `instantiate*`/`abstract*` (sonnet once B's pattern exists), whnf (opus),
then the declaration fold end to end on a prelude-only file, which closes `PipelineRefines` for
the smallest input and makes `checker_x64_accepts` unconditional for it.
