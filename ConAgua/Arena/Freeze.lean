module

public import ConAgua.Arena.DeclBase
meta import ConAgua.Arena.DeclBase
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.BVarStore
public import ConAgua.Arena.ConstStore
public import ConAgua.Arena.FVarStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.ImaxStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.LevelStore
public import ConAgua.Arena.LsStore
public import ConAgua.Arena.MaxStore
public import ConAgua.Arena.NAnonStore
public import ConAgua.Arena.NNumStore
public import ConAgua.Arena.NStrStore
public import ConAgua.Arena.ParamStore
public import ConAgua.Arena.ProjStore
public import ConAgua.Arena.SortStore
public import ConAgua.Arena.ZeroStore

@[expose] public section

/-!
# The frozen buffer: compaction of the persistent tier (lane parmode, docs/design/parmode.md)

Entry 1 of the parallel mode (`check_a`, `Checker/Entry.lean`) ends with `par_compact(vis)`, which
writes the **frozen buffer** into the word array `OUT`: a header (`HDRF`), then, per frozen array,
the image of what phase B reads of it. Entry 2 (`ca_check_b`, `Compiler/Abi.lean`) points each
frozen array's descriptor into the buffer (at the image's offset, with the image's length), so
phase B reads the images where entry 1 wrote them.

**Header** (`HDRF`, `hdrW` words): word `0` the magic, `1` the buffer's length in words, `2` the
number of records (the jobs), `3` the stream index's next counter, `4` the number of frozen
arrays; then `(off, len)` of `HDRF` itself at words `8`, `9` and of frozen entry `i` at `10 + 2 i`,
`11 + 2 i`.

**Images** (`frozen`): the store library's tier-0 extents; every image is a **prefix** of its
array. A store's records `R[0‥count₀ · w)`, its slot table `S[0‥2 + n)` (`n = S[0] + SN0`; the
offset word `S[1]` is never written, so the table sits at word `2`, and growth in place keeps it
there), its derived or hash column `C[0‥count₀)`; the stream index's rows `EIX*[0‥2 count₀)` and
table rows `TIX*[0‥2 count₀)` (`Env.lean`; a job's own layer is the worker's own); the pool's
tier 0 `POOL[0‥CTL[0])` (lane tierpool: after the index build the scratch flag is off and `CTL[0]`
is tier 0's top; a job allocates in `POOL⟨1⟩`, the worker's own, and saves the tier-0 top in
`PT0`, also the worker's); `PINS[0‥73)`, `EREC[0‥CTL[129])` (tier 0; a job's records are tier 1,
the worker's), `FIRSTS[0‥DECL[0])`, the front's records `DECL[0‥1 + 8 DECL[0])` and their pool
`DLP[0‥1 + DLP[0])` (every job reads its record); and one **seed**, which entry 2 copies into its
own array before the first job: `CTLF` (`CTL[0‥256)`).

Each image is written by one function, an instance of one generator, `fzPreG src e i` (a prefix of
`src` of length `e`, header entry `i`). `par_compact(c)` runs them in sequence; with `c = 0`
(the sequential driver) only the header is written: the driver's entry 2 reads every image in place,
as a prefix of its own array (`ca_check_seq`), so nothing is copied.
-/

namespace L.Arena

open L

/-- The magic word of a frozen buffer (`"PARMODE1"`). -/
def fzMagic : Word := 0x5041524d4f444531

/-- The cons tables whose tier 0 is frozen: (record array, slot array, words per record, count
slot). -/
def fzStores : List (ArrId × ArrId × Nat × Nat) :=
  ([litCS, appCS, succCS, zeroCS, maxCS, imaxCS, paramCS, sortCS, constCS, letCS, bvarCS, fvarCS,
    lamCS, forallCS, projCS, nanonCS, nstrCS, nnumCS, lsCS] : List ConsSch).map
    fun C => (C.ra, C.sa, C.w.toNat, C.ca.toNat)

/-- The packed 32-bit columns (the derived columns `ADER`‥`PJDER`, `Arena/P32.lean`) and the count
slot of their store. -/
def fzPCols : List (ArrId × Nat) :=
  [(ADER, 4), (LADER, 28), (FADER, 30), (LEDER, 20), (PJDER, 32)]

/-- The one-word columns (hash/level columns `SHP`‥`FVLP`) and the count slot of their store. -/
def fzCols : List (ArrId × Nat) :=
  [(SHP, 6), (MHP, 10), (IHP, 12), (LSHP, 40), (SOLP, 16), (CLP, 18), (FVLP, 26)]

/-- A frozen array's image: the prefix of `src` with extent `e`. -/
structure Fz where
  src : ArrId
  e : Expr

/-- `CTL[k]`. -/
def fzCtl (k : Nat) : Expr := .ld64 CTL (.const k.toUInt64)
def fzC (k : Nat) : Expr := .const k.toUInt64

/-- The number of the front's records, `DECL[0]` (the jobs). -/
def fzDecl : Expr := .ld64 L.Front.DECL (fzC 0)

/-- The tier-0 extent of a packed column of `CTL[k]` elements, in words: `(CTL[k] + 1) >> 1`. -/
def fzPExt (k : Nat) : Expr := .bin .shr (.bin .add (fzCtl k) (fzC 1)) (fzC 1)

/-- The tier-0 extent of the slot array `sa`: `2 + (sa[0] + SN0)`. -/
def fzSlotExt (sa : ArrId) : Expr :=
  .bin .add (fzC 2) (.bin .add (.ld64 sa (fzC 0)) (.const SN0))

/-- The extent of a solution row (`SIX*`, `STX*`, `MAT*`, by the name handle's index): `2 · count`
of its name store while the challenge's jobs run (`CTL[224] = 1`), else `0`. -/
def fzSolExt (ca : Nat) : Expr := .bin .mul (fzCtl 224) (.bin .mul (fzC 2) (fzCtl ca))

/-- **The frozen arrays**, in header order: (the id entry 2 reads it as, how entry 1 makes it). -/
def frozen : List (ArrId × Fz) :=
  [(CTLF, ⟨CTL, fzC 256⟩), (POOL, ⟨POOL, fzCtl 0⟩)] ++
  fzStores.flatMap (fun (ra, sa, w, ca) =>
    [(ra, ⟨ra, .bin .mul (fzCtl ca) (fzC w)⟩), (sa, ⟨sa, fzSlotExt sa⟩)]) ++
  fzPCols.map (fun (c, ca) => (c, ⟨c, fzPExt ca⟩)) ++
  fzCols.map (fun (c, ca) => (c, ⟨c, fzCtl ca⟩)) ++
  [(PINS, ⟨PINS, fzC 73⟩),
   (EIXA, ⟨EIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩),
   (EIXS, ⟨EIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩),
   (EIXN, ⟨EIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩),
   (TIXA, ⟨TIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩),
   (TIXS, ⟨TIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩),
   (TIXN, ⟨TIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩),
   (EREC, ⟨EREC, fzCtl 129⟩),
   (FIRSTS, ⟨FIRSTS, fzDecl⟩),
   (L.Front.DECL, ⟨L.Front.DECL, .bin .add (fzC 1) (.bin .mul (fzC 8) fzDecl)⟩),
   (L.Front.DLP, ⟨L.Front.DLP, .bin .add (fzC 1) (.ld64 L.Front.DLP (fzC 0))⟩)] ++
  [(SIXA, ⟨SIXA, fzSolExt nanonCS.ca.toNat⟩), (SIXS, ⟨SIXS, fzSolExt nstrCS.ca.toNat⟩),
   (SIXN, ⟨SIXN, fzSolExt nnumCS.ca.toNat⟩), (STXA, ⟨STXA, fzSolExt nanonCS.ca.toNat⟩),
   (STXS, ⟨STXS, fzSolExt nstrCS.ca.toNat⟩), (STXN, ⟨STXN, fzSolExt nnumCS.ca.toNat⟩),
   (MATA, ⟨MATA, fzSolExt nanonCS.ca.toNat⟩), (MATS, ⟨MATS, fzSolExt nstrCS.ca.toNat⟩),
   (MATN, ⟨MATN, fzSolExt nnumCS.ca.toNat⟩)]

/-- The ids entry 2 maps into the buffer: the header, then the frozen arrays. -/
def frozenIds : List TieredArray := ↑HDRF :: frozen.map (fun x => ↑x.1)

/-- **The worker's own arrays**: every word array phase B (`check_b`'s call closure) touches that
is not frozen: `CTL`, the pool's tier 1 and `PT0`, the memos and caches, the env index's tier 1, the walk stacks and
scratch heaps, the stores' tier-1 arrays, and the comparison's walks' memos and stacks (`NDM`‥`CWK`,
the job's own; the solution's rows `SIX*`/`STX*`/`MAT*` are frozen). Entry 2 gives them slots in the worker region; any
other array gets no memory (an access is out of bounds, an error). `Checker/ParOwned.lean` checks
the list against the program. -/
def parOwned : List TieredArray :=
  tier0s [CTL, BMEMO, IMEMO, FRMEMO, ABMEMO, ILMEMO, LPMEMO, LPLMEMO, LPLSMEMO, PT0, WCM, WKM, WH,
    INM, IOM, DEM, CTM, CV, RRM, LQ, LSQ, OIXA, OIXS, OIXN, OTXA, OTXS, OTXN, SPN, BSTK, WSM,
    FLM, LSM, LVS, Stubs.CRM, LH, Ind.IW, LMEMO, ILFM, Ind.MAM, Ind.NOM, Ind.DPM, Ind.RFM,
    Ind.RAM, Ind.TAM, Ind.HBM, Ind.MCM, L.Rom.RSTK, L.Rom.RMEMO, L.Rom.RSET, NDM, CSM, NACC, CWK] ++
  tier1s [POOL, EREC, OIXA, OIXS, OIXN, OTXA, OTXS, OTXN] ++
  ((fzStores.flatMap (fun (x : ArrId × ArrId × Nat × Nat) => [tier1 x.1, tier1 x.2.1]) ++
    fzPCols.map (fun (x : ArrId × Nat) => tier1 x.1) ++
    fzCols.map (fun (x : ArrId × Nat) => tier1 x.1)).mergeSort (fun a b => a.code ≤ b.code))

/-- The header's length. -/
def hdrW : Nat := 10 + 2 * frozen.length

/-- con-ron: none — the phase boundary's copy of a prefix (con-ron moves its tables, `freeze_tier`)

`fz_i(o, c)` for the prefix image of `src` with extent `e` in header entry `i`: writes `(o, e)` into
the header and, if `c ≠ 0`, the image at `OUT[o‥o+e)`; returns `o + e`. Locals `o c e`. -/
@[no_expose] def fzPreG (src : ArrId) (e : Expr) (i : Nat) : FunDecl :=
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
@[no_expose] def fzF (i : Nat) : FunDecl :=
  match frozen[i]? with
  | some (_, z) => fzPreG z.src z.e i
  | none => { nparams := 2, nlocals := 2, body := .abort (.const 0) }

/-- The calls of the image functions, in order: `o := fz_i(o, c)`. -/
def fzCalls : List Stmt := (List.range frozen.length).map fun i => .call [1] (fzName i) [.var 1, .var 0]

/-- con-ron: none — the phase boundary's copy (con-ron moves its persistent tables, `freeze_tier`)

`par_compact(c)`: the frozen buffer (the images if `c ≠ 0`, then the header); returns its
length. Locals `c o`. -/
@[no_expose] def parCompactL : FunDecl :=
  let tail : Stmt :=
    .seq (.st64 OUT (fzC 0) (.const fzMagic)) <|
    .seq (.st64 OUT (fzC 1) (.var 1)) <|
    .seq (.st64 OUT (fzC 2) fzDecl) <|
    .seq (.st64 OUT (fzC 3) (fzCtl 128)) <|
    .seq (.st64 OUT (fzC 4) (fzC frozen.length)) <|
    .seq (.st64 OUT (fzC 8) (fzC 0)) <|
    .seq (.st64 OUT (fzC 9) (fzC hdrW)) <|
    .ret [.var 1]
  { nparams := 1, nlocals := 2, body := .seq (.set 1 (fzC hdrW)) (fzCalls.foldr .seq tail) }

/-- `frozenIds` as a literal (what the entry stub is built from: the kernel checks the committed
file's stub against it, and a computed list would be re-evaluated in every piece). -/
def frozenIdsL : List TieredArray :=
  tier0s [HDRF, CTLF, POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT,
   PREC, PSLOT, SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC, FVSLOT, LAREC,
   LASLOT, FAREC, FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC,
   LSSLOT, ADER, LADER, FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, PINS, EIXA,
   EIXS, EIXN, TIXA, TIXS, TIXN, EREC, FIRSTS, L.Front.DECL, L.Front.DLP, SIXA, SIXS, SIXN,
   STXA, STXS, STXN, MATA, MATS, MATN]

/-- `parOwned` as a literal (as `frozenIdsL`). -/
def parOwnedL : List TieredArray :=
  tier0s [CTL, BMEMO, IMEMO, FRMEMO, ABMEMO, ILMEMO, LPMEMO, LPLMEMO, LPLSMEMO, PT0, WCM, WKM, WH,
    INM, IOM, DEM, CTM, CV, RRM, LQ, LSQ, OIXA, OIXS, OIXN, OTXA, OTXS, OTXN, SPN, BSTK, WSM,
    FLM, LSM, LVS, Stubs.CRM, LH, Ind.IW, LMEMO, ILFM, Ind.MAM, Ind.NOM, Ind.DPM, Ind.RFM,
    Ind.RAM, Ind.TAM, Ind.HBM, Ind.MCM, L.Rom.RSTK, L.Rom.RMEMO, L.Rom.RSET, NDM, CSM, NACC, CWK] ++
  tier1s [POOL, EREC, OIXA, OIXS, OIXN, OTXA, OTXS, OTXN, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT,
    IREC, ISLOT, PREC, PSLOT, SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC,
    FVSLOT, LAREC, LASLOT, FAREC, FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC,
    NNSLOT, LSREC, LSSLOT, ADER, LADER, FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP,
    FVLP]

#guard frozenIdsL == frozenIds
#guard parOwnedL == parOwned
/-- The header's view in `ca_check_seq` (`HDRF`'s words in place): room for an entry per id of
`frozenIdsL` past word `10`. -/
def hdrHw : Nat := 156

#guard frozen.length = 72
#guard hdrW = 154
#guard hdrHw = 10 + 2 * frozenIdsL.length

/-! The sizes, stated once (proofs use these, not the numbers). -/

theorem frozen_length : frozen.length = 72 := by decide
theorem frozenIdsL_length : frozenIdsL.length = 73 := rfl
theorem hdrW_eq : hdrW = 154 := by decide
theorem hdrHw_eq : hdrHw = 10 + 2 * frozenIdsL.length := rfl

end L.Arena
