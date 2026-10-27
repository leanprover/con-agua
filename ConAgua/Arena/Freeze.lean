import ConAgua.Arena.DeclBase

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

**Images** (`frozen`): the store library's tier-0 extents; every image is a **prefix** of its
array. A store's records `R[0‥count₀ · w)`, its slot table `S[0‥2 + 2 n)` (`n = S[0] + SN0`; the
offset word `S[1]` is never written, so the table sits at word `2`, and growth in place keeps it
there), its derived or hash column `C[0‥count₀)`; the env index `EIX*[0‥2 count₀)` and the
table rows `TIX*[0‥count₀)` (tier 0 only: tier 1 is the worker's own); the pool's tier 0 `POOL[0‥CTL[0])` (lane tierpool: after phase A the scratch flag
is off and `CTL[0]` is tier 0's top; phase B allocates in `POOL⟨1⟩`, the worker's own, and saves
the tier-0 top in `PT0`, also the worker's); `PINS[0‥71)`, `EREC[0‥CTL[129])`,
`PEND[0‥3 CTL[130])`; and one **seed**, which entry 2 copies into its own array before the first
group: `CTLF` (`CTL[0‥256)`).

Each image is written by one function, an instance of one generator, `fzPreG src e i` (a prefix of
`src` of length `e`, header entry `i`). `par_compact(vis, c)` runs them in sequence; with `c = 0`
(the sequential driver) only the header is written: the driver's entry 2 reads every image in place,
as a prefix of its own array (`ca_check_seq`), so nothing is copied.
-/

namespace L.Arena

open L

/-- The buffer array (written by entry 1; the harness and entry 2 read it). -/
abbrev OUT : ArrId := 240
/-- The header, as entry 2 sees it. -/
abbrev HDRF : ArrId := 241
/-- The seed of `CTL`, as entry 2 sees it. -/
abbrev CTLF : ArrId := 242

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

/-- A frozen array's image: the prefix of `src` with extent `e`. -/
structure Fz where
  src : ArrId
  e : Expr

/-- `CTL[k]`. -/
def fzCtl (k : Nat) : Expr := .ld64 CTL (.const k.toUInt64)
def fzC (k : Nat) : Expr := .const k.toUInt64

/-- The tier-0 extent of the slot array `sa`: `2 + 2 (sa[0] + SN0)`. -/
def fzSlotExt (sa : ArrId) : Expr :=
  .bin .add (fzC 2) (.bin .mul (fzC 2) (.bin .add (.ld64 sa (fzC 0)) (.const SN0)))

/-- **The frozen arrays**, in header order: (the id entry 2 reads it as, how entry 1 makes it). -/
def frozen : List (ArrId × Fz) :=
  [(CTLF, ⟨CTL, fzC 256⟩), (POOL, ⟨POOL, fzCtl 0⟩)] ++
  fzStores.flatMap (fun (ra, sa, w, ca) =>
    [(ra, ⟨ra, .bin .mul (fzCtl ca) (fzC w)⟩), (sa, ⟨sa, fzSlotExt sa⟩)]) ++
  fzCols.map (fun (c, ca) => (c, ⟨c, fzCtl ca⟩)) ++
  [(PINS, ⟨PINS, fzC 71⟩),
   (EIXA, ⟨EIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩),
   (EIXS, ⟨EIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩),
   (EIXN, ⟨EIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩),
   (TIXA, ⟨TIXA, fzCtl nanonCS.ca.toNat⟩),
   (TIXS, ⟨TIXS, fzCtl nstrCS.ca.toNat⟩),
   (TIXN, ⟨TIXN, fzCtl nnumCS.ca.toNat⟩),
   (EREC, ⟨EREC, fzCtl 129⟩),
   (PEND, ⟨PEND, .bin .mul (fzC 3) (fzCtl 130)⟩)]

/-- The ids entry 2 maps into the buffer: the header, then the frozen arrays. -/
def frozenIds : List ArrId := HDRF :: frozen.map (·.1)

/-- **The worker's own arrays**: every word array phase B (`check_b`'s call closure) touches that
is not frozen: `CTL`, the pool's tier 1 and `PT0`, the memos and caches, the env index's tier 1, the walk stacks and
scratch heaps, the stores' tier-1 arrays. Entry 2 gives them slots in the worker region; any
other array gets no memory (an access is out of bounds, an error). `Checker/ParOwned.lean` checks
the list against the program. -/
def parOwned : List ArrId :=
  [1, 24, 47, 48, 49, 50, 52, 53, 54, 62, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
   140, 141, 142, 144, 145, 151, 152, 153, 154, 155, 192, 200, 256, 385, 386, 387] ++
  ((fzStores.flatMap (fun (x : ArrId × ArrId × Nat × Nat) => [x.1 + 256, x.2.1 + 256]) ++
    fzCols.map (fun (x : ArrId × Nat) => x.1 + 256)).mergeSort : List ArrId)

/-- The header's length. -/
def hdrW : Nat := 10 + 2 * frozen.length

/-- con-ron: none — the phase boundary's copy of a prefix (con-ron moves its tables, `freeze_tier`)

`fz_i(o, c)` for the prefix image of `src` with extent `e` in header entry `i`: writes `(o, e)` into
the header and, if `c ≠ 0`, the image at `OUT[o‥o+e)`; returns `o + e`. Locals `o c e`. -/
def fzPreG (src : ArrId) (e : Expr) (i : Nat) : FunDecl :=
  let body : Stmt :=
    .seq (.set 2 e) <|
    .seq (.ite (.cmp .ne (.var 1) (fzC 0))
      (.copy64 (.plain OUT) (.var 0) (.plain src) (.const 0) (.var 2)) .skip) <|
    .seq (.st64 OUT (fzC (10 + 2 * i)) (.var 0)) <|
    .seq (.st64 OUT (fzC (11 + 2 * i)) (.var 2)) <|
    .ret [.bin .add (.var 0) (.var 2)]
  { nparams := 2, nlocals := 3, body }

/-- The name of frozen entry `i`'s function. -/
def fzName (i : Nat) : FnName := "fz_" ++ toString i

/-- con-ron: none — the phase boundary's copy (con-ron moves its tables, `freeze_tier`)

The image function of frozen entry `i` (`entryProg` binds `fz_i` to it). -/
def fzF (i : Nat) : FunDecl :=
  match frozen[i]? with
  | some (_, z) => fzPreG z.src z.e i
  | none => { nparams := 2, nlocals := 2, body := .abort (.const 0) }

/-- The calls of the image functions, in order: `o := fz_i(o, c)`. -/
def fzCalls : List Stmt := (List.range frozen.length).map fun i => .call [2] (fzName i) [.var 2, .var 1]

/-- con-ron: none — the phase boundary's copy (con-ron moves its persistent tables, `freeze_tier`)

`par_compact(vis, c)`: the frozen buffer (the images if `c ≠ 0`, then the header); returns its
length. Locals `vis c o`. -/
def parCompactL : FunDecl :=
  let tail : Stmt :=
    .seq (.st64 OUT (fzC 0) (.const fzMagic)) <|
    .seq (.st64 OUT (fzC 1) (.var 2)) <|
    .seq (.st64 OUT (fzC 2) (fzCtl 130)) <|
    .seq (.st64 OUT (fzC 3) (.var 0)) <|
    .seq (.st64 OUT (fzC 4) (fzC frozen.length)) <|
    .seq (.st64 OUT (fzC 8) (fzC 0)) <|
    .seq (.st64 OUT (fzC 9) (fzC hdrW)) <|
    .ret [.var 2]
  { nparams := 2, nlocals := 3, body := .seq (.set 2 (fzC hdrW)) (fzCalls.foldr .seq tail) }

/-- `frozenIds` as a literal (what the entry stub is built from: the kernel checks the committed
file's stub against it, and a computed list would be re-evaluated in every piece). -/
def frozenIdsL : List ArrId :=
  [241, 242, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 55, 56,
   57, 58, 59, 60, 61, 128, 132, 133, 134, 129, 130, 131, 136, 137]

/-- `parOwned` as a literal (as `frozenIdsL`). -/
def parOwnedL : List ArrId :=
  [1, 24, 47, 48, 49, 50, 52, 53, 54, 62, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 140,
   141, 142, 144, 145, 151, 152, 153, 154, 155, 192, 200, 256, 385, 386, 387, 258, 259, 260, 261, 262, 263, 264,
   265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 281, 282, 283, 284,
   285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 298, 299, 300, 301, 302, 311, 312,
   313, 314, 315, 316, 317]

#guard frozenIdsL == frozenIds
#guard parOwnedL == parOwned
#guard frozen.length = 61
#guard hdrW = 132

end L.Arena
