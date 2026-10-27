# Lane namedarrays: one table of the checker's arrays

Goal: every array of the checker has a name, a kind (byte or word) and a tiered flag in one
declaration table, which assigns its number; programs and proofs use the names; the tier-1
encoding (`tierA a t = a + 256 * (t &&& 1)`) stays inside a handful of lemmas. Constraints:
`checker.s`, `pins.bin` and `main.c` unchanged (so no array number changes), the final theorems'
statements unchanged, no change to the twin data layout.

## Inventory (master 8a4d29c7, 2026-10-27)

**The arrays.** Measured over `checkerProg`'s text (every `ld8`/`ld64`/`ld64t`/`len*`/`st*`/`copy*`/
`scan8` operand, `_tmp/namedarrays/scan.lean`), leaving out `cap_check` (it reads the length of
every slot `0‥387` by number):

* byte arrays: `0` (the input, `IN`), `1` (the pin data, `PB`);
* word arrays: 115 numbers, all below `256`: `0‥62`, `64‥68`, `70‥76`, `96‥106`, `128‥155`, `192`,
  `200‥207`, `240‥242`;
* tiered (accessed by `ld64t`/`st64t`/`len64t`/`WArr.tier`): 54 of them, `0`, `2‥23`, `25‥40`,
  `42‥46`, `55‥61`, `129‥131`; their tier-1 arrays are `256 +` those, up to `387`, so the program
  has `388` word slots (`Prog.arrs checkerProg = (2, 388)`, `wordArrays`);
* plain accesses to a tiered array: only tier 0, only in the freeze images `fz_i` (`.plain src`,
  `fzSlotExt`'s `ld64 sa 0`); a plain access to a tier-1 number: only in `cap_check`.

**Where the numbers are assigned.**

* 141 `abbrev X : ArrId := n` in 61 modules (two of them test programs) (`Arena/*Store.lean` two each, `Arena/Tiers.lean` 15,
  `Arena/LpCol.lean` 12, `Arena/IndIface.lean` 9, `Front/*`, `Scan/*`, `Rom/*`, `Checker/Hoist.lean`),
  in the namespaces `L.Arena`, `L.Ind`, `L.Front`, `L.Front.Ind`, `L.Rom`, `L.Stubs`, `L.Checker` and
  one per scanner module (`L.Scan.Key.IN`, …: 13 declarations of byte array `0`).
  Aliases (one array, two names): `SPN`/`ILSPN` 144, `WSM`/`APDM` 151, `IW`/`LPIW` 200,
  `DLP`/`DIND` 68, `IN`/`IN0` 0. `POOL1 := 256` names a tier-1 array.
* Arrays with no name, only a number in a schema or a list: `72‥74` (the id tables' sparse
  overflow, computed as `b + 8` in `Front/IdTable.lean`), `99‥102`, `104` (`CoreCaches.lean`'s
  `MemoSch` literals `⟨99, 102⟩`, …; `96‥98`, `103`, `105`, `106` have names elsewhere).
* Records and schemas with literal numbers: 32 `TRec` literals (`StoreFields.lean`, `⟨2, 4, 2, 0⟩`),
  24 `MemoSch` literals (`CoreCaches.lean`, `IndStubs.lean`, …).
* Lists of numbers: `storeArrs`, `memoArrs` (`ArenaRel.lean`), `lowTierArrs` (`Frame.lean`),
  `slotArrs`, `wordArrays` (`Checker/Entry.lean`), `parOwned`, `parOwnedL`, `frozenIdsL`, `fzCols`
  (`Freeze.lean`), `idArrs` (`IdTable.lean`), `CapsOK`'s `67`, `68`, `0`, `256` (`CapCheck.lean`).
* Computed array numbers: `rowArr w = 132 + tag + 8 tier` (the env index: tier 1 is a plain array
  `8` above tier 0, chosen by `selArr`, not `tierA`), `tblArr w = 129 + tag + 256 tier`
  (`Arena/Tiers.lean`), `b + 8` (`IdTable.lean`).

**The tier encoding outside the core.**

* `+ 256`: 639 occurrences on 310 lines in 79 files (all `ConAgua/`, generated files excluded).
  Largest: `Arena/DerRel.lean` 26 lines, `ArenaRel.lean` 23, `PromotePiE.lean` 19,
  `PromotePi.lean` 11, `FreezeTruncArena.lean` 10, `SlotGrow.lean` 9, `Front/StateDR.lean` 8; the
  three named in the brief: `Checker/ParOwned.lean` 4, `Checker/HoistWalkRef.lean` 4,
  `Checker/RomProgInit.lean` 1. Shapes: frame lists `[REC, REC + 256, SLOT, SLOT + 256]`, ownership
  conjunctions `S.ra ∈ own ∧ S.ra + 256 ∈ own`, single arrays `m.arr64 (PJREC + 256)`.
* `256 *` (the encoding unfolded): 18 in 6 files. `tierOff`: in the core (`L/`, `Compiler/`: stays)
  and in `SlotGrow.lean`, `Pool.lean`, `Env.lean`, `FreezeTruncStore.lean`.
* Region bounds `b < 64 ∨ (256 ≤ b ∧ b < 320)` and similar: 62 lines.
* `POOL1`: 231 occurrences. `tierA 0` (the pool by number): 410 occurrences in 31 files.
* Simp normal form: `SlotGrow.lean`'s `@[simp] tierA_one : tierA a 1 = a + 256` turns every
  tier-1 access into `a + 256`.

## Design

1. **The core keeps numbers.** `ArrId := Nat`, `Mem`, the semantics, the compiler, the write-set
   and read-set checks are unchanged; distinctness stays `decide`.
2. **`ConAgua/L/Arrays.lean` (generic, above `L.Syntax`).** `ArrKind` (`byte`, `word`), `ArrDecl`
   (name, id, kind, tiered), `ArrTable := List ArrDecl` with its well-formedness check (every id
   below `tierOff`, ids distinct within a kind, tiered only for word arrays), the slots a table
   occupies (`ids` and the tier-1 ids of its tiered arrays), and the surface check over a
   program's text: byte accesses name a byte array of the table, plain word accesses a word array
   of the table (so never a tier-1 number), tiered accesses a tiered array; functions on an
   exemption list (`cap_check`, which checks every slot by number) may name any slot. The
   vocabulary for proofs: `tier1 a` (tier 1 of `a`), `tiers a = [a, tier1 a]`, and lemmas
   `tierA_zero`, `tierA_one`, `tierA_mem_tiers`, `tierA_ne` (`b ∉ tiers a → tierA a t ≠ b`),
   `tierA_inj`, `tier1_ne` (two ids below `tierOff`), `set64_tierA` frames.
3. **`ConAgua/Layout.lean`: the checker's table.** Declares every array as a Lean constant in the
   namespace its users already open (`L.Arena.POOL`, `L.Front.DECL`, `L.IN`, …), each with its
   doc comment, kind and tier flag, and builds `checkerArrays : ArrTable` from the same rows, so
   the number appears once. Aliases are declared next to the array they share. It imports only
   `L.Arrays`, so every module that names an array can import it.
4. **Checks against the program** (`Checker/ArrCheck.lean`, `#guard`s like `ParOwned`):
   `checkerArrays.wf`, the surface check on `checkerProg` (exempt: `cap_check`),
   `Prog.arrs checkerProg = checkerArrays.extent`, and `parOwned`, `frozenIds`, `storeArrs`,
   `slotArrs` inside the table's slots.
5. **Proofs** write `tier1 X`/`tiers X` instead of `X + 256` and get tier facts from the lemmas.
   `tier1` is reducible (`a + tierOff`), so a proof still stated with `+ 256` and one with `tier1`
   check against each other during the migration.

**Where it is referenced.** The harness (`main.c`) and the entry stub (`Compiler/Abi.lean`) lay
out slots by number (`abiSlot64`, the descriptor table `Tab`, `ca_nw`); they do not change, and
the table's module doc says which slot each array gets. `Compiler/Compile.lean`'s `Tab` doc points
to the table for the checker's arrays. OVERVIEW §5.3 and §6.4 describe it and link it. The
memory map in `DESIGN.md` is history; the table replaces it as the current map.

## Plan (batches)

1. `L/Arrays.lean` + tests. Changes nothing else.
2. `Layout.lean`: the table, with the names moved out of their modules (each module imports
   `ConAgua.Layout`); names for `72‥74`, `99‥102`, `104`; `Checker/ArrCheck.lean`; OVERVIEW.
   Wide (every module downstream of a store rebuilds); announced to the coordinator.
3. Proofs: `+ 256` → `tier1`/`tiers`, file by file (helpers by file group), plus `POOL1` →
   `tier1 POOL` and `tierA 0` → `tierA POOL` where mechanical.
4. The lists of numbers (`storeArrs`, `slotArrs`, `fzCols`, …) as names, or checked against the
   table where they must stay literals (`frozenIdsL`, `parOwnedL`: the stub is built from them).

## Journal
