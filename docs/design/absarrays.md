# Lane absarrays: abstract arrays, layout in the compiler only

**Goal** (the user's decision, 2026-10-27): only the compiler knows how arrays map to memory. In
L's syntax and semantics an array is abstract: no `+ 256`, no `tierA` arithmetic and no slot
numbers above the compiler (hand-written assembly stubs excepted). Source names stay `Nat`s, each
aliased by a Lean constant (`ConAgua/Layout.lean`). The source number is not the layout: the
compiler chooses descriptor positions, addresses and order. Tiers are abstract: memory is indexed
by (array, tier), so "different arrays" is a structural fact. The layout is proved once, in the
compiler, and never in per-function proofs.

This file is the scoping result (master 0f2558d7): the design, the inventory of layout-dependent
places, the batch plan, the risks and the decision points. No proof changed. A prototype
(`_tmp/absarrays/Proto.lean`, outside the repository; it imports `ConAgua.Compiler.SimStore`) checked the core of the design. Its results
are quoted below.

## 1. The new L semantics

### 1.1 Types

```lean
abbrev ArrId := Nat                       -- unchanged: the source name of an array

/-- Tier `hi` of source array `arr` (`hi = false`: tier 0, which is every untiered array). -/
structure TArr where
  arr : Nat                               -- an `ArrId`, typed `Nat` so that `omega` reads `s.arr < 64`
  hi  : Bool

@[coe, reducible] def TArr.t0 (a : ArrId) : TArr := ⟨a, false⟩
instance : Coe ArrId TArr := ⟨TArr.t0⟩     -- `m.arr64 POOL` elaborates as before

/-- Equality through a number, as for `GVar`, so the kernel compares one `Nat` (§6.1). -/
def TArr.code (s : TArr) : Nat := 2 * s.arr + (if s.hi then 1 else 0)
instance : DecidableEq TArr := fun a b => decidable_of_iff (a.code = b.code) …
```

`TArr` is a working name. "Slot" is taken twice already (cons-table slots, region slots), so the
type should not be called that. There is deliberately **no** `OfNat TArr` instance: otherwise
`(258 : TArr)` would silently mean array 258's tier 0 where old code meant tier 1 of array 2.

### 1.2 Memory

```lean
structure Mem where
  bytes : ArrId → Array UInt8 := fun _ => #[]
  words : TArr  → Array Word  := fun _ => #[]
  glob  : GVar  → Word        := fun _ => 0

def Mem.arr64 (m : Mem) (s : TArr) : Array Word := m.words s
def Mem.set64 (m : Mem) (s : TArr) (i v : Word) : Mem :=
  let a := (m.words s).set! i.toNat v
  { m with words := fun s' => if s' = s then a else m.words s' }
```

* **Every array exists.** The memory is a total map, possibly empty at any key. "A missing array
  reads as empty" and `m.words.size` both go away: the size of the array of arrays no longer
  exists. An access out of bounds of `m.arr64 s` is `oob`, as before. Which arrays a program may
  name is the compiler's business (`Prog.wf` against the layout, §2). The compiler relates only
  those arrays, and the others are never read.
* **Bounds** are unchanged: `ld64`/`st64` check `i < (m.arr64 s).size`. Block operations check
  once, before writing. Lengths are fixed for a run.
* **Byte arrays** stay indexed by `ArrId`. They have no tiers, and the ABI fixes the input as byte
  array `0` and the pin data as `1` (the stub fills positions `0` and `1`). A layout map for them is
  possible but worth nothing today.

### 1.3 Operations

| form | today | new |
|---|---|---|
| `ld64 a i`, `st64 a i e`, `len64 a` | array `a` | `↑a` (tier 0 of `a`) |
| `ld64t a t i`, `st64t a t i e`, `len64t a t` | array `tierA a u = a + 256 (u &&& 1)` | `tierA a u : TArr := ⟨a, u &&& 1 != 0⟩` |
| `WArr.plain a` / `WArr.tier a t` (`warr`) | `a` / `tierA a u` | `↑a` / `tierA a u` |
| `copy64`, `copy8w` | on `ArrId`s | on `TArr`s; unchanged otherwise |
| `ld8`, `st8`, `len8`, `ld8x8`, `scan8`, `BSrc` | byte array `a` | unchanged |
| `Mem.copy64 d di s si n` | `d s : ArrId` | `d s : TArr` |

The syntax (`Expr`, `Stmt`, `WArr`, `BSrc`, `Record`, `TRec`) is unchanged: operands are
`ArrId`s, and a plain access means tier 0. So `fz_i`'s plain reads of a tiered array's tier 0
keep their meaning. Plain access to a tier-1 *number* (only `cap_check`, `len64 300`) can no longer
be written; §3.1 covers what replaces it.

### 1.4 What happens to the vocabulary

| name | new meaning | note |
|---|---|---|
| `ArrId` | unchanged (`Nat`) | |
| `tierA a u` | `⟨a, u &&& 1 != 0⟩ : TArr` | `tierA_zero : tierA a 0 = ↑a`, `tierA_one : tierA a 1 = tier1 a`, both `rfl` |
| `tier1 a` | `⟨a, true⟩` (reducible) | the simp normal form of `tierA a 1` |
| `tiers a` | `[↑a, tier1 a] : List TArr` | |
| `tierA_mem_tiers`, `tierA_ne`, `ne_tierA`, `not_mem_tiers`, `tierA_eq_or` | same statements over `TArr` | proofs by `cases` on the `Bool` |
| `tier1_ne`, `ne_tier1`, `tierA_ne_tierA`, `not_mem_tiers_of_lt` | now unconditional | keep the old signature (with a `_ : b < tierOff` argument that goes unused) while the migration runs, so call sites compile, then drop it |
| `tier1_inj`, `t0_inj` | `@[simp]` iff lemmas | |
| new | `@[simp] t0_ne_tier1`, `tier1_ne_t0` | decide every tier-0 vs tier-1 question with no hypothesis |
| `tierOff`, `tierA_lt`, `tierA_cases'` (`= a + 256`), `SlotGrow.tierA_one` (`= a + 256`), `withTiers` | leave L | `tierOff` stays private to the compiler while the old layout is kept (§2.3) |
| `POOL1` | `abbrev POOL1 : TArr := tier1 POOL` | no longer a numeral |
| `WArr.arr` | unchanged (tier 0's `ArrId`) | |
| `ArrTable.wordSlots` | `List TArr` | `extent` and the `cap_check` exemption go away (§3.8) |

**Prototype results (`Proto.lean`, all checked):** with the names listed as today (simp compares
numerals, not names), `simp` decides `↑ADER ∉ [↑AREC, tier1 AREC, ↑ASLOT, tier1 ASLOT]` and
`tier1 ADER ∉ …` with no unfolding of a tier encoding. `decide` decides the same goals. `grind`
decides `tier1 POOL ≠ ↑CTL` (the goal for which namedarrays had to keep `POOL1` a numeral), and
`grind [Mem.arr64_set64]` and `simp [Mem.arr64_set64]` close
`(m.set64 (tier1 POOL) i v).arr64 CTL = m.arr64 CTL` without naming `POOL` or `CTL`. A region
predicate on `.arr` (`b.arr < 64`) is read by `omega` and `decide`. A field typed `ArrId`
is not: `omega` does not read a comparison at type `ArrId`, as namedarrays found. Hence
`arr : Nat`, and lemma binders that need `omega` stay `Nat`.

## 2. The compiler side

### 2.1 The layout map

The compiler owns a layout of the word arrays with `nw` descriptor positions:

```lean
structure WLay (nw : Nat) where
  dom     : TArr → Bool                       -- the arrays the program may name
  pos     : TArr → Nat                        -- the descriptor position
  pos_lt  : ∀ s, dom s → pos s < nw
  pos_inj : ∀ s s', dom s → dom s' → pos s = pos s' → s = s'
  adj     : ∀ a, dom (tier1 a) → dom a ∧ pos (tier1 a) = pos a + 1   -- the one indexed load
```

plus an inverse `at : Nat → TArr` on `[0, nw)`, which the stub walks. That inverse already exists
today as `Tab.wposInv`. `Tab` carries the layout as data, so that the kernel can evaluate it.
`Prog.wf` checks every operand against `dom`: `ld64 a` needs `dom ↑a`, and a tiered access needs
`dom (tier1 a)`. This replaces `a < tab.nw` and `a + tierOff < tab.nw`. From `adj`:
`pos (tierA a u) = pos ↑a + (u &&& 1).toNat` (`WLay.pos_tierA`, prototype), which is
`Tab.wpos_tier` with no encoding.

**Today's layout is one instance** (prototype, `curLay`, checked): `dom ⟨a, false⟩ ↔ a < 256 ∧ a < nw`,
`dom ⟨a, true⟩ ↔ a < wK`, `pos ⟨a, t⟩ = wpos (a + 256 t)`, with injectivity and adjacency proved
from the existing `wposInv_wpos`/`wpos_tier`. So the semantics can change while the generated
code stays the same, byte for byte (§5, the switch).

**The compiler's own layout** (a later batch): `Prog.layout p` reads the program's text. The arrays
it names, in source order, get one position each, and an array named by a tiered operation gets
two adjacent positions. Holes go away: 115 word arrays and 54 tiered ones give 169 positions,
where today there are 388. The region slot of position `p` is `2 + (nb - 2) + p`, so `abiSlot64`
and `wposInv` leave the stub (it fills positions in order).

**Registration hints (not designed here)** would plug in at three places. An array's order in
`Prog.layout` (a hot array first, giving short displacements, or its base in a reserved register:
a codegen change in `Ctx` plus one `Inv` field). Its tiered flag (never tiered: no tier-1
position, and `Prog.wf` rejects tiered access). Its capacity (`abiVals`' length word, the sizes in
`loadMem`, and `cap_check`'s test for that array, which a static capacity discharges). All three
are fields of the layout entries, which the table's rows could supply.

### 2.2 The simulation relation

`Layout` (the machine) stays indexed by descriptor positions: `b64 s64 : Nat → Nat`. `Layout.Ok`
keeps its position-wise disjointness unchanged. `MemRel` relates L's arrays through the map:

```lean
structure MemRel (G : Layout) (m : Mem) (d : DataMem) : Prop where
  size64 : ∀ s, G.tab.dom s → (m.arr64 s).size = G.s64 (G.tab.pos s)
  get64  : ∀ s, G.tab.dom s → ∀ i (h : i < (m.arr64 s).size),
             rdW d (A (G.b64 (G.tab.pos s) + 8 * i)) = some (m.arr64 s)[i]
  base64 : ∀ p < G.tab.nw, rdW d (A (G.T + 16 + 16 * G.tab.nb + 8 * p)) = some (UInt64.ofNat (G.b64 p))
  len64  : ∀ p < G.tab.nw, …                         -- positional: no L array in them
  -- `nb`, `nw` (`m.bytes.size`, `m.words.size`) go; the byte, table, stack, result and global fields stay
```

`compile_correct` keeps its statement: `MemRel G m d.dmem` in, `OutcomeRel G (run p N entry args m)`
out. Only `MemRel`'s body and `Prog.wf`'s array conditions change. The one new proof step is
injectivity: after a store to `s`, any other `c` in `dom` has `pos c ≠ pos s`, so its region is
disjoint (`ArrRel.store64`, prototype: today's `MemRel.store64` proof plus that one line).

### 2.3 Which compiler proof files change

| file | what changes | size |
|---|---|---|
| `L/Semantics.lean`, `L/Syntax.lean` | `TArr`, `Mem`, `tierA`; `tierOff` moves to the compiler | ~60 lines |
| `Compiler/Compile.lean` | `Tab` gets the layout (switch: `curLay`, a function of `nw`; later: a literal map); `base64`/`len64` by `pos`; `tierDesc`/`warrDesc` unchanged | ~60 lines |
| `Compiler/WF.lean`, `WFFast.lean`, `WFSplit.lean` | array conditions by `dom`; `Prog.arrs` → `Prog.layout` (later batch) | ~60 lines |
| `Compiler/Rel.lean` | `MemRel` (above), lemmas over positions | ~60 lines |
| `Compiler/SimStore.lean` | `MemRel.store64`/`Inv.store64`/`Pres.store64` over `TArr` + injectivity; `descW_tier` by `pos_tierA` | ~120 of 1198 |
| `Compiler/SimExpr.lean` | `ld64t`/`len64t` (`tier_desc`, `tierA_le`, `tier_T` become `pos_tierA`) | ~130 of 1398 |
| `Compiler/SimBlock.lean`, `SimGen.lean`, `StepGen.lean`, `SimStmt.lean`, `SimFun.lean`, `SimCall.lean`, `Step.lean` | `a < nw` → `dom s`, `arr64 a` at `TArr` | ~250 lines in all, mechanical |
| `Compiler/RunEq.lean`, `Run.lean` | `tierA` at `TArr` | ~10 |
| `Compiler/Abi.lean`, `AbiSim.lean` | switch: none or nearly none. Dense layout: `abiVals`, `seqVals`, `parDescB` by position | ~80 |
| `Final/Abi.lean`, `SeqLayout.lean`, `BufLayout.lean`, `BufAbi.lean`, `DrvAbi.lean`, `ParAbi.lean`, `BufChain.lean`, `ThreadsFinal.lean`, `ThreadsVerdict.lean` | the stub's L memories (`loadMem`, `seqMem0`, `bufMem0`) as maps; `abiSlot64` by position; `fz`/`own : List TArr` | ~300 of 3 400 |
| `Checker/AsmStubEq.lean`, `AsmFileEq.lean`, `AsmPart*` | regenerated, not edited | |

In total about 1 000–1 300 lines touched in the compiler, the stubs and `Final`. The net delta is
small (−100 to +200): the `wpos` arithmetic and the `nb`/`nw` fields go, the layout lemmas come
in. `checkerFile_eq` is unchanged as a statement. It is re-established by regeneration whenever
the code changes (§4).

## 3. Layout-dependent places above the compiler

Inventory by grep (master 0f2558d7, `ConAgua/`, counts are lines). The brief's list was
complete, apart from the items marked *new*.

### 3.1 `cap_check` (`Checker/Entry.lean`, `CapCheck.lean`)
It reads `len64 b` for every slot `b < 388` by number (`wordArrays`), holes and tier-1 numbers
included, then `len64 256` for `POOL1`. **Moves to the table, not below L.** The body becomes a
fold over the table's word arrays: `len64 a` for every word array and `len64t a (const 1)` for the
tier 1 of a tiered one. `CapsOK`/`CapsW`/`WordsFit` quantify over `checkerArrays.wordSlots`
(a `List TArr`), and `slotArrs` becomes a `List TArr` written with names. `capFold_run` is already
generic in the list. 169 tests instead of 388. The surface check loses its exemption. This
changes `cap_check`'s code in `checker.s` and nothing else. A compiler-provided "capacity facts"
alternative would move the dynamic check into `compile_correct`'s premises. It does not fit entry
2, where most arrays have length 0 by design, so it is not proposed.

### 3.2 The freeze step `par_compact` (`Arena/Freeze.lean`)
It reads tiered arrays' tier 0 with plain operands (`.plain src`, `fzSlotExt`'s `ld64 sa 0`). Under
the new semantics a plain operand *is* tier 0, so the text and its meaning are unchanged. Its
descriptors are rewritten not by `par_compact` but by the `ca_check_b` stub (`parDescB`), which
already goes position by position: position `p` gets buffer entry `i` if `at p = fz[i]`, slot `k`
of the worker region if `at p = own[k]`, otherwise `(0, 0)`. Only the lists' type changes (§3.3).
The frozen buffer's header order is L's (entry `i` of `frozenIds`), independent of the layout.

### 3.3 The lists read by the stub, the harness and the kernel checks
`storeArrs`, `slotArrs`, `parOwnedL`, `frozenIdsL`, `storeArrs`'s tier-1 numerals `258…317`, the
`*_A` write sets in `Arena/WriteSets.lean` (`liftA`, `mkA`, …), the generated `stageA_*`
(`Checker/PreLoopWSStages.lean`): about 70 `List ArrId` definitions, many containing tier-1
numerals. **They become `List TArr` written with names** (`[LMEMO, …, tier1 REC]`). The literal
ones the kernel reads (`frozenIdsL`, `parOwnedL`) stay literals, with names, and the existing
`#guard`s against the computed lists stay. The generators (`scripts/preloop_ws.py` emits
`a + 256`; `core_fns.py`, `loop_fns.py`, `leaf_fns.py`, `phaseb_fns.py`) emit names and `tier1`.
The harness reads only symbols (`ca_region_size`, `ca_slot`, `ca_w0`, `ca_nw`, `ca_out_off`,
`ca_worker_size`), which the stub generator computes from the layout, so **`main.c` does not
change**.

### 3.4 `tblArr`, `rowArr`, IdTable's `b + 8` (`Arena/Tiers.lean`, `Arena/Env.lean`, `Front/IdTable.lean`)
`rowArr w = 132 + tag + 8 tier`, `tblArr w = 129 + tag + 256 tier` and `spS b = ⟨b + 8, …⟩` compute
array numbers. They are proof models or generator parameters, not code. **They become
name-based.** `rowArr` is `selArr (rowSelW w)`, which already exists, with an equation for it.
`tblArr w = tierA (tixArr (rowTag w)) (rowTier w)` with `tixArr 0 = TIXA`, …. The IdTable
generators take the sparse array as a schema field instead of `b + 8`. These are not memory
layout after the decoupling (source numbers are only names), but they tie proofs to the
numbering, which the table should be free to manage.

### 3.5 `TRec` rows in `StoreFields.lean`
`⟨2, 4, 2, 0⟩`: the `arr` field is a source number. That is not layout. It is left a numeral
because store proofs unfold it, and it becomes `⟨REC, 4, 2, 0⟩` once the unfolding goes through
`simp` lemmas on names (§1.4). `TRec.ld`/`st` already use `ld64t`/`st64t`, so they are
unchanged. `TRec.ctl := 1` (`CTL`) likewise.

### 3.6 Write sets and read sets (`L/WriteSet.lean`, `L/Agree.lean`, `Compiler/WriteSetSplit.lean`, `Checker/ParOwned.lean`)
`okW`: `a + tierOff ≠ ctl && a + tierOff ∈ A` becomes `tier1 a ∈ A`, with `A : List TArr`. The
`≠ ctl` test becomes unnecessary for tier 1, because `tier1 a ≠ ↑CTL` structurally. Agree's
`tierOk S a := S ↑a && S (tier1 a)`, `S : TArr → Bool`. `ParOwned`'s `parArrsE` gives
`List TArr`. `MemFrame A C` (`Arena/Frame.lean`) takes `A : List TArr`, and `MemFrame.tier`
loses its `tier1_ne (by decide)` step. The `words.size` conjunct of `MemFrame`, `OutFrame` (`FreezeSpec`)
and the store frames goes away (*new*: 159 lines in 59 files mention `words.size`; most are
these conjuncts and `POOL < s.mem.words.size` hypotheses, which become vacuous).
The checks run under `decide +kernel`, so equality on `TArr` goes through `TArr.code` (§6.1).

### 3.7 Regions by number (*new*)
`lowTierArrs := range 64 ++ map tier1 (range 64)` and `b < 64 ∨ (256 ≤ b ∧ b < 320)` (46 lines),
`pinA_not (64 ≤ x ∧ x < 256)`, `CIReadRefBase`'s `y + 256 = b`. These become `b.arr < 64`
(prototype: `low_tier_mem`). That ties a group to a numbering convention (arrays below 64 are the
store tier), not to the layout. A `group` column in the table would remove even that, and is
optional.

### 3.8 `RomProg*`, `ArrCheck`, `Layout.lean`, `L/Arrays.lean`
`RomProgInit`: `loadMem_arr` by `s64[a]?` (sizes by number) becomes `loadMem b pb (sz : TArr → Nat)`.
`slotArrs` with tier-1 numerals becomes names. `ArrCheck`: `progOK` loses `["cap_check"]`.
`Prog.arrs == extent` and `extent.2 == wordArrays` become "the table's tiered flags are the
program's tiered uses" (`Prog.layout checkerProg` agrees with `checkerArrays`). The list checks
compare `TArr`s. `L/Arrays.lean`: `wf` drops "below `tierOff`" (numbers need only be distinct per
kind), `wordSlots : List TArr`, the tier lemmas move to `L/Syntax` or `L/Semantics` with the type.
`Layout.lean`'s module doc stops describing slots: "array `a` gets slot `2 + a`" becomes "the
compiler lays out the arrays (`Prog.layout`)".

### 3.9 Test memories (*new*)
106 `{ words := #[…] }` literals in 66 files, `withTiers` (which pads to 256 and appends the tier-1
copies: the encoding again, 26 files), `initMem sizes`, `testMem`, and `#guard`s that compare
`m.words`. They become a builder, `Mem.ofWords : List (TArr × Array Word) → Mem` (`withTiers`
becomes `(a, xs) ↦ [(↑a, xs), (tier1 a, xs)]`), and the `#guard`s compare named arrays.

### 3.10 The memory map in `OVERVIEW.md`
§5.2 ("an array of word arrays"), §5.3 ("L names tier 1 of `a` as `a + 256`"), §6.4 ("its number,
which is its slot"; 390 slots, 12 TiB), §8.1 (`wpos`). They are rewritten as: L's memory is a map
from (array, tier) to arrays. The compiler's layout gives each a descriptor position and a region
slot, tier 1 next to tier 0. The table is the list of arrays, not the map. `Layout.lean`'s doc
and `docs/deviations.md` D10 ("array 0, array 256") and D35 ("`a + 256`") change in wording only.

## 4. Trusted base and final theorems

* **Statements.** `checkerFile_accepts`, `_regs`, `_model_exists`, `_no_False`, and the threaded
  `_threads_accept`, `_threads_regs`, `_threads_verdict` do not mention L's memory, so they keep their
  statements. `AbiCall` is unchanged. `ThreadsRun`/`ThreadsFail` keep their wording. Their
  `outAddr base = base + abiSlot * abiSlot64 checkerTab OUT` keeps its name and meaning ("`OUT`'s
  slot"), and with the dense layout its body reads the layout (`checkerTab.regionSlot ↑OUT`). The
  harness takes the same number from `ca_out_off`, which the same function prints.
* **`main.c`, `pins.bin`: unchanged.** `main.c` reads the layout only through the stub's symbols.
  `pins.bin` is data, independent of the layout.
* **`checker.s` changes**, and that is allowed because `checkerFile_eq` re-establishes the theorem
  for the new file: it is kernel-checked against the compiler's output, function by function. The
  `cap_check` batch changes `cap_check`'s code only. The semantics switch changes nothing (the
  compiler maps through `curLay`, today's positions). The dense layout changes every function's
  displacements, the stub, the descriptor table and `ca_region_size` (390 → 171 slots,
  12.2 → 5.3 TiB of address space): a full regeneration, all `AsmPart`s re-checked.
* **Trusted base: unchanged.** The layout was already not trusted (OVERVIEW §2.3, "the layout of
  memory, the capacities"). Kraken, the parser, the harness and the OS are as before.

## 5. Migration plan

Each batch lands green on its own. The pre-batches work under today's numeric semantics, so they
can land, and conflict with other lanes, in small pieces. They shrink the switch, which has to be
one wide landing (a core type changes).

| # | batch | what | agent-h | proof lines | `checker.s` |
|---|---|---|---|---|---|
| P | **prototype** (not landed) | In a worktree: `TArr`/`Mem`/`tierA` in `L/Semantics`, `MemRel` through `curLay`, `Prog.wf` by `dom`, `SimStore`/`SimExpr`'s tiered cases; build up to `compile_correct`. Measure the `Compiler/*` build time and that `checkerAsm` is unchanged (`compileProg` evaluated before and after). Go/no-go for the design of §1–2 | 6–10 | (throwaway; ~600 touched) | unchanged |
| 1 | `Mem.Has`, `Mem.SameShape` | Name the uses of `words.size` (`a < m.words.size` → `m.HasW a`, size-equality conjuncts → `SameShape m m'`), defined numerically now; the switch redefines them as `True` and the lemmas that build them keep their names | 3–4 | ~160 changed, ±0 | – |
| 2 | test memories | `Mem.ofWords`, `withTiers` as pairs, `#guard`s on named arrays (§3.9) | 3–5 | ~130 changed | – |
| 3 | lists by name | §3.3 and §3.7: every `List ArrId` with tier-1 numerals written as `tier1 X` (still evaluates to the numeral today); range facts via named predicates (`InStoreTier b`); generators emit names | 4–6 | ~200 changed + scripts | – |
| 4 | computed numbers | §3.4: `rowArr` by `selArr`, `tblArr` by `tixArr`, IdTable's sparse array as a schema field | 3–5 | ~80 changed, +20 | – |
| 5 | `cap_check` from the table | §3.1; the surface check without exemption | 3–4 | ~150 changed, −20 | `cap_check` |
| 6 | **the switch** (`--wide`) | §1 and §2 with `curLay`: `L/Semantics`, `Syntax`, `Arrays`, `Logic`, `WriteSet`, `Agree`, `PureEval`, `ModelGen`, `TRec`; the compiler and `Final`; above L: `List ArrId` → `List TArr` where lists hold tiers, frames over `TArr`, `simp [tier1, tierOff, …]` → `simp […]` (219 sites, the `tierOff` argument would be unused, a warning), `tier1_ne (by decide)` → `tier1_ne`, `POOL1 : TArr`, `HasW`/`SameShape` → `True`. Generated closures regenerated | compiler 12–18, L core 4–6, above L 15–30 | ~200 files, 1 500–2 500 lines changed line for line; net −200 to −400 (size conjuncts, encoding arguments) | unchanged (byte for byte) |
| 7 | dense layout | `Prog.layout` from the program text (§2.1), `Tab` carries it (literal in `checkerTab`), the stubs by position, `Final/*Layout` by position, `tierOff` and `wpos` deleted. Benchmark (wall time interleaved, instruction counts), `diff-e2e.py --refs` | 8–12 | ~500 changed, −100 | all (displacements, table, region size) |
| 8 | cleanup and docs | `ArrCheck` (§3.8), `Layout.lean` doc, OVERVIEW §5.2/§5.3/§6.4/§8.1, deviations wording, `TRec` rows and the store lists with names (§3.5) | 3–4 | ~100 | – |

About 65–115 agent-hours in all. The switch is about half of it, and most of that is fallout above
L. Batches 1–5 can run in parallel with each other. The switch needs them all. Batch 7 is
optional: after the switch the layout is already known only to the compiler (through `curLay`),
and batch 7 only lets it choose a better one. The constant-tier fold (`.tier a (.const k)` compiled
as a plain access to `pos ⟨a, k &&& 1⟩`) is an independent compiler optimization. It fits between
7 and 8 and helps `POOL⟨0⟩[…]` in `pool_copy0`'s loop.

## 6. Risks

1. **Kernel cost.** (a) *Equality on `TArr`* in the `decide +kernel` checks (write sets, read sets,
   closures). Measured on 3 000 membership queries against a 128-element list: `Nat` 9.3 s, `TArr`
   with derived `DecidableEq` 17.3 s, with equality through `TArr.code` 10.8–11.2 s. So the
   instance goes through `code`, as `GVar`'s does. (b) *`checkerFile_eq`*: the code generator
   evaluates `tab.pos s` at every array access in every `AsmPart` (10 parts, 15–21 s each). With
   `curLay` (the switch) this is today's `wpos` plus one addition. With the dense layout it is a
   lookup in a literal map (a `Nat`-keyed search tree like the name trees, about 7 comparisons). To be
   measured in batch 7. The fallback is the closed form `pos ⟨a, t⟩ = if a < K then 2a + t else a + K`,
   which needs the table to number tiered arrays first (decision point 2). (c) The stub's
   `list_eq` (10 383 directives, about 10 s) walks positions with `idxOf?` on `TArr` lists, at the same
   cost as (a).
2. **Generated code.** The switch is byte for byte identical. Batch 5 drops 219 hole checks and
   gives the 54 tier-1 checks a tiered load (once per run). Batch 7 keeps every instruction shape
   (`[r15 + d]`, `[r15 + 8 t + d]`), changes displacements, and shrinks the descriptor table from
   6.2 KB to 2.7 KB. No regression is expected and it has to be measured: `scripts/bench.py`, wall
   time interleaved, plus instruction counts.
3. **Parallel mode, frozen descriptors.** The frozen arrays are tier-0 slots (`↑REC`), and the
   worker owns their tier 1 (`tier1 REC`). The `TArr` lists say this directly, where today it is
   numbers like `258`. Adjacency (`adj`) is a property of each worker's own descriptor table, so
   pointing tier 0 into the read-only buffer and tier 1 into the worker region is unchanged.
   `bufMem`/`seqMem` become map definitions (`fun s => match fz.idxOf? s …`). The risk is in the
   `Final/Buf*` proofs (about 1 300 lines), which today reason by `mapIdx` over `words` and by
   `idxOf?` on numbers. Budgeted in the switch.
4. **Executable semantics.** With `words` as a function, each `set64` adds one closure, and a read
   walks the writes since the start. The 76 `#guard`/`#eval` runs of L (`WalkBench`, the Nat
   ops, `NatPow`, the scanners) are small, but a long one becomes quadratic. To be measured in the
   prototype. The fallback keeps the proof API (`arr64`, `set64`, `arr64_set64`, `Mem.ext`) and
   stores the map as a `Std.TreeMap TArr (Array Word)`. Proofs above L see only the API either way
   (decision point 1).
5. **Twin data-layout fidelity.** Nothing the L code computes changes: same arrays, same records,
   same tiers. The relations name arrays, not addresses. Abstract tiers bring L closer to con-ron's
   per-tier tables (`tiers[t]`), which D35 describes. No new row in `docs/deviations.md`; D10 and
   D35 change wording only. The env index's tier-1 rows stay separate untiered arrays
   (`EIXA1`…, chosen by `selArr`). Making them a tiered array is possible, but it changes L code
   and is out of scope.
6. **Merge pressure.** The switch touches about 200 files while other lanes keep proving. The
   pre-batches move most of the line-level churn into small landings. The switch itself is a
   `--wide` entry, announced so that the coordinator can hold dependent entries.
7. **`simp` behaviour.** Today's 219 `simp [tier1, tierOff, …]` calls must lose `tierOff` (or
   produce an unused-argument warning, which the gates reject). Some goals that `simp` closed by
   evaluating `a + 256` may now need `t0_ne_tier1`/`tier1_inj`. They are `@[simp]`, so the
   expected fallout is small. namedarrays' failures (`1 = tier1 42` evaluated to a numeral) do not
   arise: `tier1 42` is a constructor application.

## 7. Decision points for the user

1. **The representation of `Mem.words`**: a function (cleanest proofs, quadratic in long
   interpreter runs) or a tree map behind the same API. Recommendation: a function, unless the
   prototype's `#guard` timings say otherwise.
2. **Who orders the layout**: the compiler from the program text, with a literal map in
   `checkerTab` (fully decoupled, a kernel lookup per access), or a closed form over a dense,
   tiered-first numbering that the table assigns (cheaper kernel, but the numbering implies the
   layout again). Recommendation: the compiler's map; the closed form if batch 7 measures the
   lookup as too slow.
3. **Is batch 7 worth a full `checker.s` regeneration?** After the switch the layout is
   compiler-only either way. Batch 7 buys a smaller table and region, no holes, and the place
   where registration hints go. It can wait.
4. **Pre-batches or one big switch.** Recommendation: the pre-batches (1–5), since each is small
   and can land today.
5. **Byte arrays** stay positional (the ABI fixes `IN = 0`, `PB = 1`). Is that fine?
6. **The type's name** (`TArr` here).
