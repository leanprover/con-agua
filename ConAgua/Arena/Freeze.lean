import ConAgua.Arena.Store
import ConAgua.Arena.AppStore
import ConAgua.Arena.LevelStore
import ConAgua.Arena.ZeroStore
import ConAgua.Arena.MaxStore
import ConAgua.Arena.ImaxStore
import ConAgua.Arena.ParamStore
import ConAgua.Arena.SortStore
import ConAgua.Arena.ConstStore
import ConAgua.Arena.LetStore
import ConAgua.Arena.BVarStore
import ConAgua.Arena.FVarStore
import ConAgua.Arena.LamStore
import ConAgua.Arena.ForallStore
import ConAgua.Arena.ProjStore
import ConAgua.Arena.NAnonStore
import ConAgua.Arena.NStrStore
import ConAgua.Arena.NNumStore
import ConAgua.Arena.LsStore
import ConAgua.Arena.DeclBase
import ConAgua.Arena.Globals

/-!
# The frozen buffer: compaction of the persistent tier (lane parmode, docs/design/parmode.md)

Entry 1 of the parallel mode (`check_a`, `Checker/Entry.lean`) ends with `par_compact(vis)`, which
writes the **frozen buffer** into the word array `OUT`: a header (`HDRF`), then, per frozen array,
the image of what phase B reads of it. Entry 2 (`ca_check_b`, `Compiler/Abi.lean`) points each
frozen array's descriptor into the buffer (at the image's offset, with the image's length), so
phase B reads the images where entry 1 wrote them.

**Header** (`HDRF`, `hdrW` words): word `0` the magic, `1` the buffer's length in words, `2` the
number of pending groups, `3` phase A's final view, `4` the number of frozen arrays; then
`(off, len)` of `HDRF` itself at words `8`, `9` and of frozen entry `i` at `10 + 2 i`, `11 + 2 i`.

**Images** (`frozen`): the store library's tier-0 extents. A store's records `R[0‥count₀ · w)`, its
slot table in canonical form (`[n - SN0, 0]` and the `2 n` table words, wherever the table sits in
the array: with growth in place it is at offset `0` already, an older one may sit higher), its
derived or hash column `C[0‥count₀)`; the env index `EIX*[0‥2 count₀)` (tier 0 only: tier 1 is the
worker's own); `PINS[0‥71)`, `EREC[0‥CTL[129])`, `PEND[0‥3 CTL[130])`; and two **seeds**, which
entry 2 copies into its own arrays before the first group: `CTLF` (`CTL[0‥256)`) and `POOLF`
(`POOL[0‥CTL[0])`; with lane tierpool's tiered pool `POOL⟨0⟩` becomes a frozen image instead).

Each image is written by one function, an instance of a generator: `fzPreG src a e` (a prefix of
`src` of length `e`, into entry `a`'s slot of the header), `fzSlotG sa` (a slot table). The
compaction is their sequence.
-/

namespace L.Arena

open L

/-- The buffer array (written by entry 1; the harness and entry 2 read it). -/
abbrev OUT : ArrId := 240
/-- The header, as entry 2 sees it. -/
abbrev HDRF : ArrId := 241
/-- The seed of `CTL`, as entry 2 sees it. -/
abbrev CTLF : ArrId := 242
/-- The seed of `POOL`, as entry 2 sees it. -/
abbrev POOLF : ArrId := 243

/-- The magic word of a frozen buffer (`"PARMODE1"`). -/
def fzMagic : Word := 0x5041524d4f444531

/-- The cons tables whose tier 0 is frozen: (record array, slot array, words per record, count
slot). -/
def fzStores : List (ArrId × ArrId × Nat × Nat) :=
  ([litCS, appCS, succCS, zeroCS, maxCS, imaxCS, paramCS, sortCS, constCS, letCS, bvarCS, fvarCS,
    lamCS, forallCS, projCS, nanonCS, nstrCS, nnumCS, lsCS] : List ConsSch).map
    fun C => (C.ra, C.sa, C.w.toNat, C.ca.toNat)

/-- The one-word columns (derived columns `ADER`‥`PJDER`, hash/level columns `SHP`‥`FVLP`) and the
count slot of their store. -/
def fzCols : List (ArrId × Nat) :=
  [(42, 4), (43, 28), (44, 30), (45, 20), (46, 32),
   (55, 6), (56, 10), (57, 12), (58, 40), (59, 16), (60, 18), (61, 26)]

/-- How a frozen array's image is made: a prefix of `src` with extent `e`, or a slot table. -/
inductive Fz where
  | pre (src : ArrId) (e : Expr)
  | slot (sa : ArrId)

/-- `CTL[k]`. -/
def fzCtl (k : Nat) : Expr := .ld64 CTL (.const k.toUInt64)
def fzC (k : Nat) : Expr := .const k.toUInt64

/-- **The frozen arrays**, in header order: (the id entry 2 reads it as, how entry 1 makes it). -/
def frozen : List (ArrId × Fz) :=
  [(CTLF, .pre CTL (fzC 256)), (POOLF, .pre POOL (fzCtl 0))] ++
  fzStores.flatMap (fun (ra, sa, w, ca) =>
    [(ra, .pre ra (.bin .mul (fzCtl ca) (fzC w))), (sa, .slot sa)]) ++
  fzCols.map (fun (c, ca) => (c, .pre c (fzCtl ca))) ++
  [(PINS, .pre PINS (fzC 71)),
   (EIXA, .pre EIXA (.bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat))),
   (EIXS, .pre EIXS (.bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat))),
   (EIXN, .pre EIXN (.bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat))),
   (EREC, .pre EREC (fzCtl 129)),
   (PEND, .pre PEND (.bin .mul (fzC 3) (fzCtl 130)))]

/-- The ids entry 2 maps into the buffer: the header, then the frozen arrays. -/
def frozenIds : List ArrId := HDRF :: frozen.map (·.1)

/-- **The worker's own arrays**: every word array phase B (`check_b`'s call closure) touches that
is not frozen: `POOL`, `CTL`, the memos and caches, the env index's tier 1, the walk stacks and
scratch heaps, the stores' tier-1 arrays. Entry 2 gives them slots in the worker region; any
other array gets no memory (an access is out of bounds, an error). `Checker/ParOwned.lean` checks
the list against the program. -/
def parOwned : List ArrId :=
  [0, 1, 24, 47, 48, 49, 50, 52, 53, 54, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
   140, 141, 142, 144, 145, 151, 152, 153, 154, 155, 192, 200] ++
  ((fzStores.flatMap (fun (x : ArrId × ArrId × Nat × Nat) => [x.1 + 256, x.2.1 + 256]) ++
    fzCols.map (fun (x : ArrId × Nat) => x.1 + 256)).mergeSort : List ArrId)

/-- The header's length. -/
def hdrW : Nat := 10 + 2 * frozen.length

/-- con-ron: none — the phase boundary's copy of a prefix (con-ron moves its tables, `freeze_tier`)

`fz_pre(o)` for the prefix image of `src` with extent `e` in header entry `i`: writes the image
at `OUT[o‥o+e)` and its `(o, e)` into the header; returns `o + e`. Locals `o e`. -/
def fzPreG (src : ArrId) (e : Expr) (i : Nat) : FunDecl :=
  let body : Stmt :=
    .seq (.set 1 e) <|
    .seq (.copy64 (.plain OUT) (.var 0) (.plain src) (.const 0) (.var 1)) <|
    .seq (.st64 OUT (fzC (10 + 2 * i)) (.var 0)) <|
    .seq (.st64 OUT (fzC (11 + 2 * i)) (.var 1)) <|
    .ret [.bin .add (.var 0) (.var 1)]
  { nparams := 1, nlocals := 2, body }

/-- con-ron: none — the phase boundary's copy of a slot table (con-ron moves its tables, `freeze_tier`)

`fz_slot(o)` for the slot table `sa` in header entry `i`: the canonical table
`[n - SN0, 0, table…]` (`2 + 2 n` words) at `OUT[o‥)`; returns its end. Locals `o n q r`. -/
def fzSlotG (sa : ArrId) (i : Nat) : FunDecl :=
  let body : Stmt :=
    .seq (.set 1 (.bin .mul (fzC 2) (.bin .add (.ld64 sa (fzC 0)) (.const SN0)))) <|
    .seq (.st64 OUT (.var 0) (.ld64 sa (fzC 0))) <|
    .seq (.st64 OUT (.bin .add (.var 0) (fzC 1)) (fzC 0)) <|
    .seq (.set 2 (.bin .add (.var 0) (fzC 2))) <|
    .seq (.set 3 (.bin .add (.ld64 sa (fzC 1)) (fzC 2))) <|
    .seq (.copy64 (.plain OUT) (.var 2) (.plain sa) (.var 3) (.var 1)) <|
    .seq (.st64 OUT (fzC (10 + 2 * i)) (.var 0)) <|
    .seq (.st64 OUT (fzC (11 + 2 * i)) (.bin .add (.var 1) (fzC 2))) <|
    .ret [.bin .add (.var 2) (.var 1)]
  { nparams := 1, nlocals := 4, body }

/-- The name of frozen entry `i`'s function. -/
def fzName (i : Nat) : FnName := "fz_" ++ toString i

/-- The image function of frozen entry `i` (`entryProg` binds `fz_i` to it). -/
def fzF (i : Nat) : FunDecl :=
  match frozen[i]? with
  | some (_, .pre src e) => fzPreG src e i
  | some (_, .slot sa) => fzSlotG sa i
  | none => { nparams := 1, nlocals := 1, body := .abort }

/-- The calls of the image functions, in order: `o := fz_i(o)`. -/
def fzCalls : List Stmt := (List.range frozen.length).map fun i => .call [1] (fzName i) [.var 1]

/-- con-ron: none — the phase boundary's copy (con-ron moves its persistent tables, `freeze_tier`)

`par_compact(vis)`: the frozen buffer (all images, then the header); returns its length.
Locals `vis o`. -/
def parCompactL : FunDecl :=
  let tail : Stmt :=
    .seq (.st64 OUT (fzC 0) (.const fzMagic)) <|
    .seq (.st64 OUT (fzC 1) (.var 1)) <|
    .seq (.st64 OUT (fzC 2) (fzCtl 130)) <|
    .seq (.st64 OUT (fzC 3) (.var 0)) <|
    .seq (.st64 OUT (fzC 4) (fzC frozen.length)) <|
    .seq (.st64 OUT (fzC 8) (fzC 0)) <|
    .seq (.st64 OUT (fzC 9) (fzC hdrW)) <|
    .ret [.var 1]
  { nparams := 1, nlocals := 2, body := .seq (.set 1 (fzC hdrW)) (fzCalls.foldr .seq tail) }

/-- `frozenIds` as a literal (what the entry stub is built from: the kernel checks the committed
file's stub against it, and a computed list would be re-evaluated in every piece). -/
def frozenIdsL : List ArrId :=
  [241, 242, 243, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 55, 56, 57,
   58, 59, 60, 61, 128, 132, 133, 134, 136, 137]

/-- `parOwned` as a literal (as `frozenIdsL`). -/
def parOwnedL : List ArrId :=
  [0, 1, 24, 47, 48, 49, 50, 52, 53, 54, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 140,
   141, 142, 144, 145, 151, 152, 153, 154, 155, 192, 200, 258, 259, 260, 261, 262, 263, 264, 265,
   266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 281, 282, 283, 284, 285,
   286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 298, 299, 300, 301, 302, 311, 312, 313,
   314, 315, 316, 317]

#guard frozenIdsL == frozenIds
#guard parOwnedL == parOwned
#guard frozen.length = 58
#guard hdrW = 126

end L.Arena
