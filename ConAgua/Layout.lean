module

public import ConAgua.L.Arrays

@[expose] public section

/-!
# The checker's arrays

Every array the checker's program (`checkerProg`) names is declared here, once: its name (a Lean
constant in the namespace its users open), its kind and whether it is tiered (`L/Arrays.lean`),
and its number. `checkerArrays` is the table; `Checker/ArrCheck.lean` checks it against the
program (the surface check: plain word accesses only name tier-0 numbers, tiered accesses only
tiered arrays) and against the lists the entries and the parallel mode use.

**Numbers are names.** A row's number names the array in L's syntax; it is not an address. A word
array of L's memory is a `TieredArray`: tier 0 of every word array (`↑a`) and tier 1 of every
tiered one (`tier1 a`). Where each array lives is the compiler's choice: its layout map
(`L.Compiler.WLay`, `L.Compiler.BLay`) gives every array the program names a descriptor
position, tier 1 right after tier 0, and the entry stub (`Compiler/Abi.lean`) gives each position
a region. The harness (`main.c`) reads the layout only through the symbols the stub exports.

Kept apart from the rows: the aliases (one array under a second name, for a second, time-disjoint
use) and the stand-alone example programs' arrays (`L.Examples.HIST`, `L.Scan.Utf8.OUT`,
`L.Compiler.Tests`), which are not part of the checker.

**Minimum lengths.** A row's `min k` (`ArrDecl.min`) promises at least `k` words of both tiers
of the array in every layout the checker runs in; the compiler then drops the bounds check of a
constant index below `k`. The entry stubs establish it and their proofs prove it: `ca_setup` and
`ca_check_seq` give every array a whole slot (except `OUT`, `CTLF`, which have no minimum, and
`HDRF`'s 132 words), and `ca_check_b` gives the owned arrays a slot and tests every frozen array's
length in the buffer, declining below the minimum; an array that is neither frozen nor owned gets no
memory there, so it has no minimum. The minima are the largest constant index the program uses,
plus one (`CTL`: 256, `L.Checker.ctlMin`).

**The table-relative array.** `CTL`'s row is marked `at table` (`ArrDecl.atTable`): the stubs place
its `min` words inside the table's slot, past the table, at an offset the compiler knows
(`L.Compiler.Tab.tbl`), and the code addresses it from the table's register without loading its
base.
-/

namespace L

/-- **The checker's arrays.** Tiered rows are the persistent (tier 0) and scratch (tier 1) tiers
of con-ron's per-tier tables. -/
declare_arrays checkerArrays
  -- byte arrays
  | /-- The input buffer. -/ IN : byte := 243
  | /-- The pin data (`pins.bin`). -/ Rom.PB : byte := 244
  -- the stores (`Arena/StoreFields.lean`): the pool, then per table its records and cons slots
  | /-- The limb pool: limbs, level lists' handles, names' bytes (`Arena/Pool.lean`). -/
    Arena.POOL : word tiered := 0
  | /-- The control words; word 0 is the pool top. -/ Arena.CTL : word min 256 at table := 1
  | /-- The `lit` records (four words per node). -/ Arena.REC : word tiered := 2
  | /-- The `lit` cons-table slots. -/ Arena.SLOT : word tiered min 2 := 3
  | /-- The `app` records (one packed word per node). -/ Arena.AREC : word tiered := 4
  | /-- The `app` cons-table slots. -/ Arena.ASLOT : word tiered min 2 := 5
  | /-- The `succ` records (one word per node). -/ Arena.SREC : word tiered := 6
  | /-- The `succ` cons-table slots. -/ Arena.SSLOT : word tiered min 2 := 7
  | /-- The `zero` records (one dummy word per node). -/ Arena.ZREC : word tiered := 8
  | /-- The `zero` cons-table slots. -/ Arena.ZSLOT : word tiered min 2 := 9
  | /-- The `max` records (one packed word per node). -/ Arena.MREC : word tiered := 10
  | /-- The `max` cons-table slots. -/ Arena.MSLOT : word tiered min 2 := 11
  | /-- The `imax` records (one packed word per node). -/ Arena.IREC : word tiered := 12
  | /-- The `imax` cons-table slots. -/ Arena.ISLOT : word tiered min 2 := 13
  | /-- The `param` records (one word per node). -/ Arena.PREC : word tiered := 14
  | /-- The `param` cons-table slots. -/ Arena.PSLOT : word tiered min 2 := 15
  | /-- The `sort` records (one word per node). -/ Arena.SOREC : word tiered := 16
  | /-- The `sort` cons-table slots. -/ Arena.SOSLOT : word tiered min 2 := 17
  | /-- The `const` records (one packed word per node). -/ Arena.CREC : word tiered := 18
  | /-- The `const` cons-table slots. -/ Arena.CSLOT : word tiered min 2 := 19
  | /-- The `letE` records (two words per node). -/ Arena.LEREC : word tiered := 20
  | /-- The `letE` cons-table slots. -/ Arena.LESLOT : word tiered min 2 := 21
  | /-- The `bvar` records (one word per node). -/ Arena.BREC : word tiered := 22
  | /-- The `bvar` cons-table slots. -/ Arena.BSLOT : word tiered min 2 := 23
  | /-- The slots of `bvarBound`'s memo (`bvarBC`, one-word keys). -/ Arena.BMEMO : word min 3 := 24
  | /-- The `fvar` records (two words per node). -/ Arena.FVREC : word tiered := 25
  | /-- The `fvar` cons-table slots. -/ Arena.FVSLOT : word tiered min 2 := 26
  | /-- The `lam` records (one packed word per node). -/ Arena.LAREC : word tiered := 27
  | /-- The `lam` cons-table slots. -/ Arena.LASLOT : word tiered min 2 := 28
  | /-- The `forallE` records (one packed word per node). -/ Arena.FAREC : word tiered := 29
  | /-- The `forallE` cons-table slots. -/ Arena.FASLOT : word tiered min 2 := 30
  | /-- The `proj` records (two words per node). -/ Arena.PJREC : word tiered := 31
  | /-- The `proj` cons-table slots. -/ Arena.PJSLOT : word tiered min 2 := 32
  | /-- The name `anonymous` records (one dummy word per node). -/ Arena.NAREC : word tiered := 33
  | /-- The name `anonymous` cons-table slots. -/ Arena.NASLOT : word tiered min 2 := 34
  | /-- The name `str` records (four words per node). -/ Arena.NSREC : word tiered := 35
  | /-- The name `str` cons-table slots. -/ Arena.NSSLOT : word tiered min 2 := 36
  | /-- The name `num` records (two words per node). -/ Arena.NNREC : word tiered := 37
  | /-- The name `num` cons-table slots. -/ Arena.NNSLOT : word tiered min 2 := 38
  | /-- The level-list records (three words per node). -/ Arena.LSREC : word tiered := 39
  | /-- The level-list cons-table slots. -/ Arena.LSSLOT : word tiered min 2 := 40
  | /-- The slots of `liftLooseBVars`' memo (`liftC`, keys `(handle, cutoff)`). -/
    Arena.LMEMO : word := 41
  -- the derived columns (`Arena/LpCol.lean`, `Arena/DerRel.lean`): one word per node
  | /-- The derived word of the `app` nodes (loose bvar range, `lp` bit). -/ Arena.ADER : word tiered := 42
  | /-- The derived word of the `lam` nodes. -/ Arena.LADER : word tiered := 43
  | /-- The derived word of the `forallE` nodes. -/ Arena.FADER : word tiered := 44
  | /-- The derived word of the `letE` nodes. -/ Arena.LEDER : word tiered := 45
  | /-- The derived word of the `proj` nodes. -/ Arena.PJDER : word tiered := 46
  | /-- The slots of `instantiate1`'s memo (`inst1C`, keys `(handle, depth)`). -/
    Arena.IMEMO : word min 3 := 47
  | /-- The slots of `fvarRange`'s memo (`fvarBC`, one-word keys). -/ Arena.FRMEMO : word min 3 := 48
  | /-- The slots of `abstract1`'s memo (`abs1C`, keys `(handle, k)`). -/ Arena.ABMEMO : word min 3 := 49
  | /-- The slots of `instantiateList`'s memo (`instLC`, keys `(handle, depth)`). -/
    Arena.ILMEMO : word min 3 := 50
  | /-- `instantiate1LiftGo`'s memo (`inst1LC`). -/ Arena.ILFM : word := 51
  | /-- `instLPC`'s memo (level-parameter instantiation of an expression). -/ Arena.LPMEMO : word min 3 := 52
  | /-- `instLPLC`'s memo (of a level). -/ Arena.LPLMEMO : word min 3 := 53
  | /-- `instLPLsC`'s memo (of a level list). -/ Arena.LPLSMEMO : word min 3 := 54
  | /-- The `hasParam` column of the `succ` nodes. -/ Arena.SHP : word tiered := 55
  | /-- The `hasParam` column of the `max` nodes. -/ Arena.MHP : word tiered := 56
  | /-- The `hasParam` column of the `imax` nodes. -/ Arena.IHP : word tiered := 57
  | /-- The `hasParam` column of the level lists. -/ Arena.LSHP : word tiered := 58
  | /-- The `hasParam` column of the `sort` nodes. -/ Arena.SOLP : word tiered := 59
  | /-- The `hasParam` column of the `const` nodes. -/ Arena.CLP : word tiered := 60
  | /-- The `lp` column of the `fvar` nodes (of the type). -/ Arena.FVLP : word tiered := 61
  | /-- Word 0 is the tier-0 pool top while the scratch tier is open (`CTL[0]` then holds the
    tier-1 top): saved by `scratch_reset` when it leaves tier 0, restored when it drops the scratch
    tier. An array, not a global: every memory frame (`MemFrame`, the stores' `OutEq`) keeps it. -/
    Arena.PT0 : word min 1 := 62
  -- the front end (`Front/`)
  | /-- Export name id ↦ name handle word `+ 1` (dense part). -/ Front.NID : word := 64
  | /-- Export level id ↦ level handle word `+ 1` (dense part). -/ Front.LID : word := 65
  | /-- Export expression id ↦ expression handle word `+ 1` (dense part). -/ Front.EID : word := 66
  | /-- The declaration records. -/ Front.DECL : word := 67
  | /-- The universe parameter names of the declaration records, and the installed inductive
    blocks' constant records (`DIND`). -/ Front.DLP : word := 68
  | /-- The fixed-size field records of the current inductive line. -/ Front.Ind.IFR : word := 70
  | /-- The word lists and rule records of the current inductive line. -/ Front.Ind.IFL : word := 71
  | /-- `NID`'s sparse overflow (a memo-library table, `Front/IdTable.lean`: `spArr NID`). -/
    Front.NIDS : word := 72
  | /-- `LID`'s sparse overflow. -/ Front.LIDS : word := 73
  | /-- `EID`'s sparse overflow. -/ Front.EIDS : word := 74
  | /-- The ground hoist's expression visited set. -/ Checker.HSEEN : word := 75
  | /-- The ground hoist's name index: name handle ↦ the first position declaring it. -/
    Checker.HNIX : word := 76
  -- the per-declaration caches (`Arena/CoreCaches.lean`)
  | /-- The `whnfCore` memo (`wcSch`). -/ Arena.WCM : word min 3 := 96
  | /-- The cheap-mode `whnfCore` memo (`wkSch`). -/ Arena.WKM : word min 3 := 97
  | /-- The `whnf` memo (`whSch`). -/ Arena.WH : word min 3 := 98
  | /-- The `infer` memo (`inSch`). -/ Arena.INM : word min 3 := 99
  | /-- The `inferOnly` memo (`ioSch`). -/ Arena.IOM : word min 3 := 100
  | /-- The `isDefEq` memo (`deSch`). -/ Arena.DEM : word min 3 := 101
  | /-- The `constType` memo (`ctSch`). -/ Arena.CTM : word min 3 := 102
  | /-- The `constValue` memo (`cvSch`). -/ Arena.CV : word min 3 := 103
  | /-- The `ruleRhs` memo (`rrSch`). -/ Arena.RRM : word min 3 := 104
  | /-- The level-equality memo (`lqSch`). -/ Arena.LQ : word min 3 := 105
  | /-- The level-list-equality memo (`lsqSch`). -/ Arena.LSQ : word min 3 := 106
  -- the environment (`Arena/Tiers.lean`)
  | /-- The pin table. -/ Arena.PINS : word min 55 := 128
  | /-- The projection-table rows of `anonymous` names (`tblArr`). -/ Arena.TIXA : word tiered := 129
  | /-- The projection-table rows of `str` names. -/ Arena.TIXS : word tiered := 130
  | /-- The projection-table rows of `num` names. -/ Arena.TIXN : word tiered := 131
  | /-- The environment index rows of tier-0 `anonymous` names (`rowArr`). -/
    Arena.EIXA : word := 132
  | /-- The environment index rows of tier-0 `str` names. -/ Arena.EIXS : word := 133
  | /-- The environment index rows of tier-0 `num` names. -/ Arena.EIXN : word := 134
  | /-- The record pointer of every constant, oldest first. -/ Arena.ECON : word := 135
  | /-- The environment's record pool (`EnvRec.lean`). -/ Arena.EREC : word := 136
  | /-- The pending checks. -/ Arena.PEND : word := 137
  | /-- The ROM interner's handle stack. -/ Rom.RSTK : word := 138
  | /-- The memo of the ROM expression interner. -/ Rom.RMEMO : word := 139
  | /-- The environment index rows of tier-1 `anonymous` names (`EIXA`'s scratch tier, chosen by
    `selArr`, not `tierA`). -/ Arena.EIXA1 : word := 140
  | /-- The environment index rows of tier-1 `str` names. -/ Arena.EIXS1 : word := 141
  | /-- The environment index rows of tier-1 `num` names. -/ Arena.EIXN1 : word := 142
  | /-- The projection tables, by slot, oldest first. -/ Arena.ETAB : word := 143
  -- walk stacks and walk-local memos
  | /-- The spine stack (also the substitution slice of `instantiateList`, `ILSPN`). -/
    Arena.SPN : word := 144
  | /-- The binder stack. -/ Arena.BSTK : word := 145
  | /-- The promotion's name memo. -/ Arena.PNM : word := 146
  | /-- The promotion's level memo. -/ Arena.PLM : word := 147
  | /-- The promotion's level-list memo. -/ Arena.PLSM : word := 148
  | /-- The promotion's expression memo. -/ Arena.PEM : word := 149
  | /-- The handles of the ROM interner memo's entries, as a set. -/ Rom.RSET : word := 150
  | /-- The scope walk's memo (`wscopedBGo`), also the `apd` walk's (`APDM`). -/
    Arena.WSM : word min 3 := 151
  | /-- `fvarLeavesGo`'s `seen` set. -/ Arena.FLM : word min 3 := 152
  | /-- `leavesSubGo`'s memo. -/ Arena.LSM : word min 3 := 153
  | /-- The leaf list (`fvarLeavesGo`'s accumulator). -/ Arena.LVS : word := 154
  | /-- The constants-resolution walk's memo. -/ Stubs.CRM : word min 3 := 155
  | /-- The level scratch heap: three words per node. -/ Arena.LH : word := 192
  -- the inductive checks (`Arena/IndIface.lean`)
  | /-- The work pool (handle slices). -/ Ind.IW : word := 200
  | /-- Per-call walk memo (`maSch`). -/ Ind.MAM : word := 201
  | /-- Per-call walk memo (`noSch`). -/ Ind.NOM : word := 202
  | /-- Per-call walk memo (`dpSch`). -/ Ind.DPM : word := 203
  | /-- Per-call walk memo (`rfSch`). -/ Ind.RFM : word := 204
  | /-- Per-call walk memo (`raSch`). -/ Ind.RAM : word := 205
  | /-- Per-call walk memo (`taSch`). -/ Ind.TAM : word := 206
  | /-- Per-call walk memo (`hbSch`). -/ Ind.HBM : word := 207
  | /-- Per-call walk memo (`mcSch`). -/ Ind.MCM : word := 208
  -- the phase boundary (`Arena/Freeze.lean`)
  | /-- The frozen buffer (written by entry 1; the harness and entry 2 read it). -/
    Arena.OUT : word := 240
  | /-- The frozen buffer's header, as entry 2 sees it. -/ Arena.HDRF : word min 4 := 241
  | /-- The seed of `CTL`, as entry 2 sees it. -/ Arena.CTLF : word := 242

/-- **The checker's word arrays**: tier 0 of every word array of the table and tier 1 of every
tiered one. Write sets "every array but …" are filters of this list. -/
abbrev checkerWordArrays : List TieredArray := checkerArrays.wordSlots

/-! ## Aliases: one array, a second name -/

/-- The input buffer (the driver's name). -/
abbrev Front.IN0 : ArrId := IN
/-- The pool's tier-1 array. -/
abbrev Arena.POOL1 : TieredArray := tier1 Arena.POOL

theorem Arena.POOL1_eq : Arena.POOL1 = tier1 Arena.POOL := rfl
/-- The spine stack, as `instantiateList`'s substitution slice. -/
abbrev Arena.ILSPN : ArrId := Arena.SPN
/-- The work pool, as the level-parameter walks' handle slices. -/
abbrev Arena.LPIW : ArrId := Ind.IW
/-- The `apd` walk's memo (the scope walk's array). -/
abbrev Ind.APDM : ArrId := Arena.WSM
/-- The constant records of the installed inductive blocks: they share `DLP`'s pool (word `0` its
top), so that the declarations relation reads one pool (`DeclAtF`, `StateDR.lean`). -/
abbrev Front.Ind.DIND : ArrId := Front.DLP

/-! ## Groups of arrays by number

Frame lemmas quantify over two groups of word arrays, named here by the source numbers of their
arrays (a numbering convention of the table above, not a layout). -/

/-- **The store tier**: both tiers of the arrays below `64` (the pool, the stores' record and slot
arrays, their derived columns, the walk memos, `PT0`). A walk writes only these
(`WriteSets.lean`), and `ArenaR` reads only these (`arenaArrs`). -/
@[simp] abbrev InStoreTier (b : TieredArray) : Prop := b.arr < 64

/-- **The high arrays**: the tier-0 arrays from `64` on (the front end, the per-declaration caches,
the environment, the walk stacks, the inductive checks, the phase boundary). None is in the store
tier (`InHigh.not_storeTier`), and none is a tier-1 array (`InHigh.ne_tier1`). -/
@[simp] abbrev InHigh (b : TieredArray) : Prop := b.hi = false ∧ 64 ≤ b.arr

theorem InStoreTier.of_lt {b : Nat} (h : b < 64) : InStoreTier ↑b := h

theorem InStoreTier.of_tier1 {a : Nat} (h : a < 64) : InStoreTier (tier1 a) := h

theorem InHigh.not_storeTier {b : TieredArray} (h : InHigh b) : ¬ InStoreTier b := by
  simp only [InHigh, InStoreTier] at *; omega

theorem InHigh.ne_tier1 {b : TieredArray} (h : InHigh b) (a : Nat) : b ≠ tier1 a := by
  rintro rfl; simp at h

end L
