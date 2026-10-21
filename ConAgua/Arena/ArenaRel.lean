import ConAgua.Arena.LitRefine
import ConAgua.Arena.AppRefine
import ConAgua.Arena.SortRefine
import ConAgua.Arena.ConstRefine
import ConAgua.Arena.LetRefine
import ConAgua.Arena.BVarRefine
import ConAgua.Arena.FVarRefine
import ConAgua.Arena.LamRefine
import ConAgua.Arena.ForallRefine
import ConAgua.Arena.ProjRefine
import ConAgua.Arena.ZeroRefine
import ConAgua.Arena.LevelRefine
import ConAgua.Arena.MaxRefine
import ConAgua.Arena.ImaxRefine
import ConAgua.Arena.ParamRefine
import ConAgua.Arena.LsRefine
import ConAgua.Arena.NAnonRefine
import ConAgua.Arena.NStrRefine
import ConAgua.Arena.NNumRefine
import ConAgua.Arena.MemoLibRel

/-!
# The arena relation: one relation for the whole L memory

`ArenaR m a` assembles every table relation of the arena tier on one memory layout, with the limb
pool and the walk memo:

| array | contents | `CTL` words |
|---|---|---|
| 0 `POOL` | limbs, level lists' handle words, names' bytes | 0: pool top |
| 1 `CTL` | control words | 1: scratch flag |
| 2, 3 `REC`, `SLOT` | expression `lit` | 2, 3 |
| 4, 5 `AREC`, `ASLOT` | expression `app` | 4, 5 |
| 6, 7 `SREC`, `SSLOT` | level `succ` | 6, 7 |
| 8, 9 `ZREC`, `ZSLOT` | level `zero` | 8, 9 |
| 10, 11 `MREC`, `MSLOT` | level `max` | 10, 11 |
| 12, 13 `IREC`, `ISLOT` | level `imax` | 12, 13 |
| 14, 15 `PREC`, `PSLOT` | level `param` | 14, 15 |
| 16, 17 `SOREC`, `SOSLOT` | expression `sort` | 16, 17 |
| 18, 19 `CREC`, `CSLOT` | expression `const` | 18, 19 |
| 20, 21 `LEREC`, `LESLOT` | expression `letE` | 20, 21 |
| 22, 23 `BREC`, `BSLOT` | expression `bvar` | 22, 23 |
| 24 `BMEMO` | the `bvarBound` memo | 24: stamp − 1, 25: live count |
| 25, 26 `FVREC`, `FVSLOT` | expression `fvar` | 26, 27 |
| 27, 28 `LAREC`, `LASLOT` | expression `lam` | 28, 29 |
| 29, 30 `FAREC`, `FASLOT` | expression `forallE` | 30, 31 |
| 31, 32 `PJREC`, `PJSLOT` | expression `proj` | 32, 33 |
| 33, 34 `NAREC`, `NASLOT` | name `anonymous` | 34, 35 |
| 35, 36 `NSREC`, `NSSLOT` | name `str` (bytes in the pool) | 36, 37 |
| 37, 38 `NNREC`, `NNSLOT` | name `num` | 38, 39 |
| 39, 40 `LSREC`, `LSSLOT` | level lists (slices of the pool) | 40, 41 |

| 41‥63 | reserved for lane `exprops` (memos, derived columns) | 42‥63 |
| ≥ 64 | **free for other lanes** (`ArenaR.frame_ext`) | ≥ 64 |

(Tables 2‥23: `CTL[r + t]` is tier `t`'s node count of the table with record array `r`; tables from
25 on: `CTL[s + t]`, `s` the slot array.) **Extension point:** a writer of arrays `≥ 64` and `CTL`
words `≥ 64` only keeps `ArenaR` (`ArenaR.frame_ext`, stable); `arenaR_init` takes at least 64
arrays and a `CTL` of at least 64 words, so a lane may add its own arrays above 63 without touching
this file. A new relation over such arrays is a separate conjunct (`ArenaR m a ∧ MyR m a`), merged
into `ArenaR` later. This file is maintained by hand (it was once generated; `arena_build` removed
the text that grew quadratically). Each table relation reads only its own arrays and counts,
the scratch flag, and (for `lit`, the level lists and the name `str` table) the pool and its top,
so a writer of other arrays leaves it alone (`Frame.lean`, `storeR_frame`). Every `intern_*`
refinement lifts to `ArenaR` (`intern*_refinesA`): the table's own relation from the table's
theorem, the others by the frame, on both sides (the L memory: `internM_frame`; the arena state:
the interning replaces one table behind its lens, `AM.st_proto`). The tactic `arena_build` builds
an `ArenaR` field by field: the given tactic where it applies, the frame elsewhere. `arenaR_init`:
the all-zero memory is related to the arena's initial state `AState.init EStore.empty`.

Not represented: the derived columns, the other memos, the per-declaration caches and the pins,
and the contents of `lit`'s `strVal` nodes. They are not in `ArenaR`, so nothing is claimed about
them.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- Decide that a table is apart from a writer (`Apart`, `BMEMO ∉ A`, `24 ∉ C`) for concrete
schemas: `decide` times out on the `UInt64` list memberships, `simp` with the array ids is
immediate. -/
macro "apart" : tactic => `(tactic| simp [Apart, POOL, CTL, BMEMO, bmSch, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT])

/-- The side condition of `apart_hi` for a concrete schema. -/
macro "lo_apart" : tactic => `(tactic| simp [POOL, CTL, BMEMO, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT])

/-! ## Locality of each table's records -/

theorem litLocal : RLocal litSch RecRel litH [POOL] [0] := by
  intro m m' hra hb hc
  have h0 := hc 0 (by simp)
  have hp := hb POOL (by simp)
  simp only [litSch] at hra
  refine ⟨fun t i k h => ?_, fun t i => by simp only [litH, hra]⟩
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec, hra, hp, top_rdW, h0] at h ⊢; exact h
  · simpa only [RecRel, hra] using h

theorem appLocal : RLocal appSch ARecRel ahash [] [] := by
  intro m m' hra _ _; simp only [appSch] at hra
  exact ⟨fun t i k h => by simpa only [ARecRel, hra] using h, fun t i => by simp only [ahash, hra]⟩
theorem sortLocal : RLocal sortSch SoRecRel sohash [] [] := by
  intro m m' hra _ _; simp only [sortSch] at hra
  exact ⟨fun t i k h => by simpa only [SoRecRel, hra] using h, fun t i => by simp only [sohash, hra]⟩
theorem constLocal : RLocal constSch CeRecRel cehash [] [] := by
  intro m m' hra _ _; simp only [constSch] at hra
  exact ⟨fun t i k h => by simpa only [CeRecRel, hra] using h, fun t i => by simp only [cehash, hra]⟩
theorem letELocal : RLocal letSch LeRecRel lehash [] [] := by
  intro m m' hra _ _; simp only [letSch] at hra
  exact ⟨fun t i k h => by simpa only [LeRecRel, hra] using h, fun t i => by simp only [lehash, hra]⟩
theorem bvarLocal : RLocal bvarSch BRecRel bhash [] [] := by
  intro m m' hra _ _; simp only [bvarSch] at hra
  exact ⟨fun t i k h => by simpa only [BRecRel, hra] using h, fun t i => by simp only [bhash, hra]⟩
theorem fvarLocal : RLocal fvarSch FVRecRel fvhash [] [] := by
  intro m m' hra _ _; simp only [fvarSch] at hra
  exact ⟨fun t i k h => by simpa only [FVRecRel, hra] using h, fun t i => by simp only [fvhash, hra]⟩
theorem lamLocal : RLocal lamSch LaRecRel lahash [] [] := by
  intro m m' hra _ _; simp only [lamSch] at hra
  exact ⟨fun t i k h => by simpa only [LaRecRel, hra] using h, fun t i => by simp only [lahash, hra]⟩
theorem forallELocal : RLocal forallSch FaRecRel fahash [] [] := by
  intro m m' hra _ _; simp only [forallSch] at hra
  exact ⟨fun t i k h => by simpa only [FaRecRel, hra] using h, fun t i => by simp only [fahash, hra]⟩
theorem projLocal : RLocal projSch PJRecRel pjhash [] [] := by
  intro m m' hra _ _; simp only [projSch] at hra
  exact ⟨fun t i k h => by simpa only [PJRecRel, hra] using h, fun t i => by simp only [pjhash, hra]⟩
theorem zeroLocal : RLocal zeroSch ZRecRel zhash [] [] :=
  fun _ _ _ _ _ => ⟨fun _ _ _ h => h, fun _ _ => rfl⟩
theorem succLocal : RLocal succSch SRecRel shash [] [] := by
  intro m m' hra _ _; simp only [succSch] at hra
  exact ⟨fun t i k h => by simpa only [SRecRel, hra] using h, fun t i => by simp only [shash, hra]⟩
theorem maxLocal : RLocal maxSch MRecRel mhash [] [] := by
  intro m m' hra _ _; simp only [maxSch] at hra
  exact ⟨fun t i k h => by simpa only [MRecRel, hra] using h, fun t i => by simp only [mhash, hra]⟩
theorem imaxLocal : RLocal imaxSch IRecRel imhash [] [] := by
  intro m m' hra _ _; simp only [imaxSch] at hra
  exact ⟨fun t i k h => by simpa only [IRecRel, hra] using h, fun t i => by simp only [imhash, hra]⟩
theorem paramLocal : RLocal paramSch PRecRel phash [] [] := by
  intro m m' hra _ _; simp only [paramSch] at hra
  exact ⟨fun t i k h => by simpa only [PRecRel, hra] using h, fun t i => by simp only [phash, hra]⟩
theorem lsLocal : RLocal lsSch LsRecRel lshash [POOL] [0] := by
  intro m m' hra hb hc
  have h0 := hc 0 (by simp)
  have hp := hb POOL (by simp)
  simp only [lsSch] at hra
  refine ⟨fun t i k h => ?_, fun t i => by simp only [lshash, hra]⟩
  simpa only [LsRecRel, lsO, lsL, hra, hp, top_rdW, h0] using h

theorem nanonLocal : RLocal nanonSch NaRecRel nahash [] [] :=
  fun _ _ _ _ _ => ⟨fun _ _ _ h => h, fun _ _ => rfl⟩
theorem nstrLocal : RLocal nstrSch NsRecRel nshash [POOL] [0] := by
  intro m m' hra hb hc
  have h0 := hc 0 (by simp)
  have hp := hb POOL (by simp)
  simp only [nstrSch] at hra
  refine ⟨fun t i k h => ?_, fun t i => by simp only [nshash, hra]⟩
  simpa only [NsRecRel, nsQ, nsO, nsL, hra, hp, top_rdW, h0] using h

theorem nnumLocal : RLocal nnumSch NnRecRel nnhash [] [] := by
  intro m m' hra _ _; simp only [nnumSch] at hra
  exact ⟨fun t i k h => by simpa only [NnRecRel, hra] using h, fun t i => by simp only [nnhash, hra]⟩

/-! ## Each table relation across a writer it is apart from -/

section frames
variable (A : List ArrId) (C : List Word) (m m' : Mem) (hf : MemFrame A C m m') (a : AState)

include hf

theorem LitR.frame (hap : Apart litSch [POOL] [0] A C) (h : LitR m a) : LitR m' a := by
  obtain ⟨hp, hs⟩ := h
  refine ⟨?_, storeR_frame litSch RecRel litH litS_wf [POOL] [0] litLocal A C hap m m' hf _ _ _ hs⟩
  obtain ⟨-, -, hA₀, -, -, -, hC₀⟩ := hap
  have h0 := hC₀ 0 (by simp)
  have hpool := hf.1 POOL (hA₀ POOL (by simp)).1 (by decide)
  have hc := hf.2.2.1 CTL
  have ht := hf.2.1 0 h0
  simp only [PoolOK, top_rdW, hf.2.2.2, hc, hpool, ht] at hp ⊢
  exact hp
theorem AppR.frame (hap : Apart appSch [] [] A C) (h : AppR m a) : AppR m' a :=
  storeR_frame appSch ARecRel ahash appSch_wf [] [] appLocal A C hap m m' hf _ _ _ h
theorem SortR.frame (hap : Apart sortSch [] [] A C) (h : SortR m a) : SortR m' a :=
  storeR_frame sortSch SoRecRel sohash sortSch_wf [] [] sortLocal A C hap m m' hf _ _ _ h
theorem ConstR.frame (hap : Apart constSch [] [] A C) (h : ConstR m a) : ConstR m' a :=
  storeR_frame constSch CeRecRel cehash constSch_wf [] [] constLocal A C hap m m' hf _ _ _ h
theorem LetR.frame (hap : Apart letSch [] [] A C) (h : LetR m a) : LetR m' a :=
  storeR_frame letSch LeRecRel lehash letSch_wf [] [] letELocal A C hap m m' hf _ _ _ h
theorem BVarR.frame (hap : Apart bvarSch [] [] A C) (h : BVarR m a) : BVarR m' a :=
  storeR_frame bvarSch BRecRel bhash bvarSch_wf [] [] bvarLocal A C hap m m' hf _ _ _ h
theorem FVarR.frame (hap : Apart fvarSch [] [] A C) (h : FVarR m a) : FVarR m' a :=
  storeR_frame fvarSch FVRecRel fvhash fvarSch_wf [] [] fvarLocal A C hap m m' hf _ _ _ h
theorem LamR.frame (hap : Apart lamSch [] [] A C) (h : LamR m a) : LamR m' a :=
  storeR_frame lamSch LaRecRel lahash lamSch_wf [] [] lamLocal A C hap m m' hf _ _ _ h
theorem ForallR.frame (hap : Apart forallSch [] [] A C) (h : ForallR m a) : ForallR m' a :=
  storeR_frame forallSch FaRecRel fahash forallSch_wf [] [] forallELocal A C hap m m' hf _ _ _ h
theorem ProjR.frame (hap : Apart projSch [] [] A C) (h : ProjR m a) : ProjR m' a :=
  storeR_frame projSch PJRecRel pjhash projSch_wf [] [] projLocal A C hap m m' hf _ _ _ h
theorem ZeroR.frame (hap : Apart zeroSch [] [] A C) (h : ZeroR m a) : ZeroR m' a :=
  storeR_frame zeroSch ZRecRel zhash zeroSch_wf [] [] zeroLocal A C hap m m' hf _ _ _ h
theorem SuccR.frame (hap : Apart succSch [] [] A C) (h : SuccR m a) : SuccR m' a :=
  storeR_frame succSch SRecRel shash succSch_wf [] [] succLocal A C hap m m' hf _ _ _ h
theorem MaxR.frame (hap : Apart maxSch [] [] A C) (h : MaxR m a) : MaxR m' a :=
  storeR_frame maxSch MRecRel mhash maxSch_wf [] [] maxLocal A C hap m m' hf _ _ _ h
theorem ImaxR.frame (hap : Apart imaxSch [] [] A C) (h : ImaxR m a) : ImaxR m' a :=
  storeR_frame imaxSch IRecRel imhash iimaxSch_wf [] [] imaxLocal A C hap m m' hf _ _ _ h
theorem ParamR.frame (hap : Apart paramSch [] [] A C) (h : ParamR m a) : ParamR m' a :=
  storeR_frame paramSch PRecRel phash paramSch_wf [] [] paramLocal A C hap m m' hf _ _ _ h
theorem LsR.frame (hap : Apart lsSch [POOL] [0] A C) (h : LsR m a) : LsR m' a :=
  storeR_frame lsSch LsRecRel lshash lsSch_wf [POOL] [0] lsLocal A C hap m m' hf _ _ _ h
theorem NAnonR.frame (hap : Apart nanonSch [] [] A C) (h : NAnonR m a) : NAnonR m' a :=
  storeR_frame nanonSch NaRecRel nahash nanonSch_wf [] [] nanonLocal A C hap m m' hf _ _ _ h
theorem NStrR.frame (hap : Apart nstrSch [POOL] [0] A C) (h : NStrR m a) : NStrR m' a :=
  storeR_frame nstrSch NsRecRel nshash nstrSch_wf [POOL] [0] nstrLocal A C hap m m' hf _ _ _ h
theorem NNumR.frame (hap : Apart nnumSch [] [] A C) (h : NNumR m a) : NNumR m' a :=
  storeR_frame nnumSch NnRecRel nnhash nnumSch_wf [] [] nnumLocal A C hap m m' hf _ _ _ h

end frames

/-! ## The relation -/

/-- **The arena relation**: every represented table, the pool and the `bvarBound` memo, on the
one layout above. -/
structure ArenaR (m : Mem) (a : AState) : Prop where
  lit : LitR m a
  app : AppR m a
  sort : SortR m a
  const : ConstR m a
  letE : LetR m a
  bvar : BVarR m a
  fvar : FVarR m a
  lam : LamR m a
  forallE : ForallR m a
  proj : ProjR m a
  zero : ZeroR m a
  succ : SuccR m a
  max : MaxR m a
  imax : ImaxR m a
  param : ParamR m a
  ls : LsR m a
  nanon : NAnonR m a
  nstr : NStrR m a
  nnum : NNumR m a
  memo : MemoRG bmSch bmKey (·.toNat) m a.memos.bvarBC

/-- **Build an `ArenaR m' a'` from `hR : ArenaR m a` and a writer `hf : MemFrame A C m m'`**: each
field by the tactic `t` if it closes it (the written table, the memo, the pool's tables), else by
the field's frame across `hf` (which needs the table apart from the writer). -/
macro "arena_build " hR:term ", " hf:term " with " t:tacticSeq " using " ap:tacticSeq : tactic => `(tactic| exact ⟨
    by first | $t | exact ($hR).lit.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).app.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).sort.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).const.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).letE.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).bvar.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).fvar.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).lam.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).forallE.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).proj.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).zero.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).succ.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).max.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).imax.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).param.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).ls.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).nanon.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).nstr.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact ($hR).nnum.frame _ _ _ _ $hf _ (by $ap),
    by first | $t | exact memoRG_frame bmSch bmSch_wf bmKey _ _ _ (by $ap) (by $ap) _ _ $hf _ ($hR).memo⟩)

/-- `arena_build hR, hf with t` for a writer of concrete arrays and words (`Apart` by `apart`). -/
macro "arena_build " hR:term ", " hf:term " with " t:tacticSeq : tactic =>
  `(tactic| arena_build $hR, $hf with $t using apart)

/-- **The extension point for other lanes**: arrays `≥ 64` and `CTL` words `≥ 64` are outside
every relation of `ArenaR` (lane `exprops` reserves arrays `41‥63` and `CTL` words `42‥63` for its
memos and derived columns). A writer of only such arrays and words keeps `ArenaR`. -/
theorem ArenaR.frame_ext (A : List ArrId) (C : List Word) (hA : ∀ b ∈ A, 64 ≤ b)
    (hC : ∀ x ∈ C, 64 ≤ x.toNat) (m m' : Mem) (hf : MemFrame A C m m') (a : AState)
    (hR : ArenaR m a) : ArenaR m' a := by
  arena_build hR, hf with
    exact memoRG_frame bmSch bmSch_wf bmKey _ _ _ (fun h => absurd (hA _ h) (by simp [BMEMO]))
      (fun h => absurd (hC _ h) (by simp)) _ _ hf _ hR.memo
  using exact apart_hi _ _ _ _ _ (by lo_apart) hA hC

/-! ## The initial state -/

/-- **The empty L memory**: word arrays of the given sizes, all zero (`CTL` must have room for
its words, the pool must stay below `2^63` words). -/
def initMem (sizes : List Nat) : Mem := { words := (sizes.map (Array.replicate · 0)).toArray }

theorem initMem_arr (sizes : List Nat) (b : ArrId) :
    (initMem sizes).arr64 b = Array.replicate (sizes[b]?.getD 0) 0 := by
  simp only [Mem.arr64, initMem, Array.getD_eq_getD_getElem?]
  cases h : sizes[b]? <;> simp [h]

theorem initMem_rd (sizes : List Nat) (b : ArrId) (x : Word) : rdW ((initMem sizes).arr64 b) x = 0 := by
  rw [initMem_arr]; simp only [rdW, Array.getElem?_replicate]; split <;> rfl

theorem storeR_init {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (m : Mem)
    (hz : ∀ b x, rdW (m.arr64 b) x = 0) (hctl : S.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    StoreR S R hs m false (Tbl.empty : Tbl α (Idx k) δ) Tbl.empty := by
  have hT : ∀ t, TierR S R hs m t (Tbl.empty : Tbl α (Idx k) δ) := by
    intro t
    refine ⟨by simp [cntW, hz, Tbl.empty], by simp [Tbl.empty], by simp [Tbl.empty],
      fun i a h => by simp [Tbl.empty] at h, fun i a h => by simp [Tbl.empty] at h,
      fun a x h => by simp [Tbl.empty] at h, fun j _ => by simp [slotW, hz],
      fun i hi => by simp [Tbl.empty] at hi⟩
  exact ⟨hctl, by simp [hz], hT 0, hT 1⟩

/-- **The relation holds initially**: the all-zero memory and the arena's initial state. -/
theorem arenaR_init (sizes : List Nat) (hlen : 64 ≤ sizes.length) (hctl : 64 ≤ sizes[1]?.getD 0)
    (hpool : sizes[0]?.getD 0 < 2 ^ 63) : ArenaR (initMem sizes) (AState.init EStore.empty) := by
  have hz := initMem_rd sizes
  have hc : ((initMem sizes).arr64 CTL).size = sizes[1]?.getD 0 := by
    rw [initMem_arr]; simp [CTL]
  have hp : ((initMem sizes).arr64 POOL).size = sizes[0]?.getD 0 := by
    rw [initMem_arr]; simp [POOL]
  have hw : CTL < (initMem sizes).words.size := by
    show 1 < (sizes.map _).toArray.size; simp only [List.size_toArray, List.length_map]; omega
  refine ⟨⟨?_, storeR_init _ _ _ _ hz (by rw [hc]; simp [litSch]; omega)⟩,
    storeR_init _ _ _ _ hz (by rw [hc]; simp [appSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [sortSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [constSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [letSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [bvarSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [fvarSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [lamSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [forallSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [projSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [zeroSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [succSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [maxSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [imaxSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [paramSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [lsSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [nanonSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [nstrSch]; omega),
    storeR_init _ _ _ _ hz (by rw [hc]; simp [nnumSch]; omega), ?_⟩
  · refine ⟨hw, by rw [hc]; omega, by rw [hp]; exact hpool, ?_⟩
    simp only [top_rdW, hz, UInt64.toNat_zero]; exact Nat.zero_le _
  · exact memoRG_zero bmSch bmKey _ _ hz (by rw [hc]; simp; omega)

/-! ## Interning lifts to `ArenaR`

Per table: the table's own relation after the interning (its `*intern_correct`), the frame of the
other tables in memory (`internM_frame`), and in the arena state (the interning replaced at most
one table behind its lens, so the other relations read the same fields). -/

section lift
variable (m m' : Mem) (a a' : AState) (hR : ArenaR m a)
include hR

/-- Interning into `lit` keeps `ArenaR`. -/
theorem ArenaR.lift_lit (hX : LitR m' a')
    (hf : MemFrame [litSch.ra, litSch.sa] [litSch.ca, litSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = litLens.setP a t) ∨ (∃ t, a' = litLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `app` keeps `ArenaR`. -/
theorem ArenaR.lift_app (hX : AppR m' a')
    (hf : MemFrame [appSch.ra, appSch.sa] [appSch.ca, appSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = appLens.setP a t) ∨ (∃ t, a' = appLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `sort` keeps `ArenaR`. -/
theorem ArenaR.lift_sort (hX : SortR m' a')
    (hf : MemFrame [sortSch.ra, sortSch.sa] [sortSch.ca, sortSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = sortLens.setP a t) ∨ (∃ t, a' = sortLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `const` keeps `ArenaR`. -/
theorem ArenaR.lift_const (hX : ConstR m' a')
    (hf : MemFrame [constSch.ra, constSch.sa] [constSch.ca, constSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = constLens.setP a t) ∨ (∃ t, a' = constLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `letE` keeps `ArenaR`. -/
theorem ArenaR.lift_letE (hX : LetR m' a')
    (hf : MemFrame [letSch.ra, letSch.sa] [letSch.ca, letSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = letLens.setP a t) ∨ (∃ t, a' = letLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `bvar` keeps `ArenaR`. -/
theorem ArenaR.lift_bvar (hX : BVarR m' a')
    (hf : MemFrame [bvarSch.ra, bvarSch.sa] [bvarSch.ca, bvarSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = bvarLens.setP a t) ∨ (∃ t, a' = bvarLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `fvar` keeps `ArenaR`. -/
theorem ArenaR.lift_fvar (hX : FVarR m' a')
    (hf : MemFrame [fvarSch.ra, fvarSch.sa] [fvarSch.ca, fvarSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = fvarLens.setP a t) ∨ (∃ t, a' = fvarLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `lam` keeps `ArenaR`. -/
theorem ArenaR.lift_lam (hX : LamR m' a')
    (hf : MemFrame [lamSch.ra, lamSch.sa] [lamSch.ca, lamSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = lamLens.setP a t) ∨ (∃ t, a' = lamLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `forallE` keeps `ArenaR`. -/
theorem ArenaR.lift_forallE (hX : ForallR m' a')
    (hf : MemFrame [forallSch.ra, forallSch.sa] [forallSch.ca, forallSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = forallLens.setP a t) ∨ (∃ t, a' = forallLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `proj` keeps `ArenaR`. -/
theorem ArenaR.lift_proj (hX : ProjR m' a')
    (hf : MemFrame [projSch.ra, projSch.sa] [projSch.ca, projSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = projLens.setP a t) ∨ (∃ t, a' = projLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `zero` keeps `ArenaR`. -/
theorem ArenaR.lift_zero (hX : ZeroR m' a')
    (hf : MemFrame [zeroSch.ra, zeroSch.sa] [zeroSch.ca, zeroSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = zeroLens.setP a t) ∨ (∃ t, a' = zeroLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `succ` keeps `ArenaR`. -/
theorem ArenaR.lift_succ (hX : SuccR m' a')
    (hf : MemFrame [succSch.ra, succSch.sa] [succSch.ca, succSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = succLens.setP a t) ∨ (∃ t, a' = succLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `max` keeps `ArenaR`. -/
theorem ArenaR.lift_max (hX : MaxR m' a')
    (hf : MemFrame [maxSch.ra, maxSch.sa] [maxSch.ca, maxSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = maxLens.setP a t) ∨ (∃ t, a' = maxLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `imax` keeps `ArenaR`. -/
theorem ArenaR.lift_imax (hX : ImaxR m' a')
    (hf : MemFrame [imaxSch.ra, imaxSch.sa] [imaxSch.ca, imaxSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = imaxLens.setP a t) ∨ (∃ t, a' = imaxLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `param` keeps `ArenaR`. -/
theorem ArenaR.lift_param (hX : ParamR m' a')
    (hf : MemFrame [paramSch.ra, paramSch.sa] [paramSch.ca, paramSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = paramLens.setP a t) ∨ (∃ t, a' = paramLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `ls` keeps `ArenaR`. -/
theorem ArenaR.lift_ls (hX : LsR m' a')
    (hf : MemFrame [lsSch.ra, lsSch.sa] [lsSch.ca, lsSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = lsLens.setP a t) ∨ (∃ t, a' = lsLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `nanon` keeps `ArenaR`. -/
theorem ArenaR.lift_nanon (hX : NAnonR m' a')
    (hf : MemFrame [nanonSch.ra, nanonSch.sa] [nanonSch.ca, nanonSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = nanonLens.setP a t) ∨ (∃ t, a' = nanonLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `nstr` keeps `ArenaR`. -/
theorem ArenaR.lift_nstr (hX : NStrR m' a')
    (hf : MemFrame [nstrSch.ra, nstrSch.sa] [nstrSch.ca, nstrSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = nstrLens.setP a t) ∨ (∃ t, a' = nstrLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `nnum` keeps `ArenaR`. -/
theorem ArenaR.lift_nnum (hX : NNumR m' a')
    (hf : MemFrame [nnumSch.ra, nnumSch.sa] [nnumSch.ca, nnumSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = nnumLens.setP a t) ∨ (∃ t, a' = nnumLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

end lift

/-! ## The `intern_*` refinements under `ArenaR` -/

/-- `intern_*` for `app` refines its arena interning under `ArenaR`. -/
theorem internApp_refinesA (p : Prog) (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hp : p.lookup "intern_app" = some internApp)
    (a₀ : AState) (n : Nat) (s₀ : St) (f x : Word) (hR : ArenaR s₀.mem a₀) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_app" [f, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.app (decE f) (decE x))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.app (decE f) (decE x))) a₀) ∧
      AM.res (internE (.app (decE f) (decE x))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internApp_spec p hpf hpp hp n s₀ f x)
  subst hs
  obtain ⟨hok, hX, hres⟩ := aintern_correct s.mem a₀ hR.app f x hf hx _ _ hI
  rw [ainternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_app _ _ _ _ hX (internM_frame _ appSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto appLens _ _ _ _ _ _ a₀ (internE_app_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `sort` refines its arena interning under `ArenaR`. -/
theorem internSort_refinesA (p : Prog) (hpf : p.lookup "sort_find" = some sortFind)
    (hpp : p.lookup "sort_push" = some sortPush) (hp : p.lookup "intern_sort" = some internSort)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : ArenaR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_sort" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.sort (decI u))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.sort (decI u))) a₀) ∧
      AM.res (internE (.sort (decI u))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internSort_spec p hpf hpp hp n s₀ u)
  subst hs
  obtain ⟨hok, hX, hres⟩ := sointern_correct s.mem a₀ hR.sort u hu _ _ hI
  rw [sointernW_eq] at hI
  exact ⟨hloc, hok, hR.lift_sort _ _ _ _ hX (internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto sortLens _ _ _ _ _ _ a₀ (internE_sort_run _ a₀) hok), hres⟩

/-- `intern_*` for `const` refines its arena interning under `ArenaR`. -/
theorem internConst_refinesA (p : Prog) (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (a₀ : AState) (n : Nat) (s₀ : St) (f x : Word) (hR : ArenaR s₀.mem a₀) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_const" [f, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a₀) ∧
      AM.res (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internConst_spec p hpf hpp hp n s₀ f x)
  subst hs
  obtain ⟨hok, hX, hres⟩ := ceintern_correct s.mem a₀ hR.const f x hf hx _ _ hI
  rw [ceinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_const _ _ _ _ hX (internM_frame _ constSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto constLens _ _ _ _ _ _ a₀ (internE_const_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `letE` refines its arena interning under `ArenaR`. -/
theorem internLet_refinesA (p : Prog) (hpf : p.lookup "letE_find" = some letFind)
    (hpp : p.lookup "letE_push" = some letPush) (hp : p.lookup "intern_letE" = some internLet)
    (a₀ : AState) (n : Nat) (s₀ : St) (ty val body : Word) (hR : ArenaR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hval : val.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_letE" [ty, val, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.letE (decE ty) (decE val) (decE body))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.letE (decE ty) (decE val) (decE body))) a₀) ∧
      AM.res (internE (.letE (decE ty) (decE val) (decE body))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internLet_spec p hpf hpp hp n s₀ ty val body)
  subst hs
  obtain ⟨hok, hX, hres⟩ := leintern_correct s.mem a₀ hR.letE ty val body hty hval hbody _ _ hI
  rw [leinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_letE _ _ _ _ hX (internM_frame _ letSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto letLens _ _ _ _ _ _ a₀ (internE_let_run _ _ _ a₀) hok), hres⟩

/-- `intern_*` for `bvar` refines its arena interning under `ArenaR`. -/
theorem internBVar_refinesA (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hp : p.lookup "intern_bvar" = some internBVar)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : ArenaR s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_bvar" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.bvar u.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.bvar u.toNat)) a₀) ∧
      AM.res (internE (.bvar u.toNat)) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internBVar_spec p hpf hpp hp n s₀ u)
  subst hs
  obtain ⟨hok, hX, hres⟩ := bintern_correct s.mem a₀ hR.bvar u _ _ hI
  rw [binternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_bvar _ _ _ _ hX (internM_frame _ bvarSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto bvarLens _ _ _ _ _ _ a₀ (internE_bvar_run _ a₀) hok), hres⟩

/-- `intern_*` for `zero` refines its arena interning under `ArenaR`. -/
theorem internZero_refinesA (p : Prog) (hpf : p.lookup "zero_find" = some zeroFind)
    (hpp : p.lookup "zero_push" = some zeroPush) (hp : p.lookup "intern_zero" = some internZero)
    (a₀ : AState) (n : Nat) (s₀ : St) (hR : ArenaR s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_zero" []
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode .zero) a₀ ∧
      ArenaR s'.mem (AM.st (internLNode .zero) a₀) ∧
      AM.res (internLNode .zero) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internZero_spec p hpf hpp hp n s₀)
  subst hs
  obtain ⟨hok, hX, hres⟩ := zintern_correct s.mem a₀ hR.zero _ _ hI
  rw [zinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_zero _ _ _ _ hX (internM_frame _ zeroSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto zeroLens _ _ _ _ _ _ a₀ (internLNode_zero_run a₀) hok), hres⟩

/-- `intern_*` for `succ` refines its arena interning under `ArenaR`. -/
theorem internSucc_refinesA (p : Prog) (hpf : p.lookup "succ_find" = some succFind)
    (hpp : p.lookup "succ_push" = some succPush) (hp : p.lookup "intern_succ" = some internSucc)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : ArenaR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_succ" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.succ (decI u))) a₀ ∧
      ArenaR s'.mem (AM.st (internLNode (.succ (decI u))) a₀) ∧
      AM.res (internLNode (.succ (decI u))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internSucc_spec p hpf hpp hp n s₀ u)
  subst hs
  obtain ⟨hok, hX, hres⟩ := sintern_correct s.mem a₀ hR.succ u hu _ _ hI
  rw [sinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_succ _ _ _ _ hX (internM_frame _ succSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto succLens _ _ _ _ _ _ a₀ (internLNode_succ_run _ a₀) hok), hres⟩

/-- `intern_*` for `max` refines its arena interning under `ArenaR`. -/
theorem internMax_refinesA (p : Prog) (hpf : p.lookup "max_find" = some maxFind)
    (hpp : p.lookup "max_push" = some maxPush) (hp : p.lookup "intern_max" = some internMax)
    (a₀ : AState) (n : Nat) (s₀ : St) (u v : Word) (hR : ArenaR s₀.mem a₀) (hu : u.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_max" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.max (decI u) (decI v))) a₀ ∧
      ArenaR s'.mem (AM.st (internLNode (.max (decI u) (decI v))) a₀) ∧
      AM.res (internLNode (.max (decI u) (decI v))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internMax_spec p hpf hpp hp n s₀ u v)
  subst hs
  obtain ⟨hok, hX, hres⟩ := mintern_correct s.mem a₀ hR.max u v hu hv _ _ hI
  rw [minternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_max _ _ _ _ hX (internM_frame _ maxSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto maxLens _ _ _ _ _ _ a₀ (internLNode_max_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `imax` refines its arena interning under `ArenaR`. -/
theorem internImax_refinesA (p : Prog) (hpf : p.lookup "imax_find" = some imaxFind)
    (hpp : p.lookup "imax_push" = some imaxPush) (hp : p.lookup "intern_imax" = some internImax)
    (a₀ : AState) (n : Nat) (s₀ : St) (u v : Word) (hR : ArenaR s₀.mem a₀) (hu : u.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_imax" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.imax (decI u) (decI v))) a₀ ∧
      ArenaR s'.mem (AM.st (internLNode (.imax (decI u) (decI v))) a₀) ∧
      AM.res (internLNode (.imax (decI u) (decI v))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internImax_spec p hpf hpp hp n s₀ u v)
  subst hs
  obtain ⟨hok, hX, hres⟩ := imintern_correct s.mem a₀ hR.imax u v hu hv _ _ hI
  rw [iiminternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_imax _ _ _ _ hX (internM_frame _ iimaxSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto imaxLens _ _ _ _ _ _ a₀ (internLNode_imax_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `param` refines its arena interning under `ArenaR`. -/
theorem internParam_refinesA (p : Prog) (hpf : p.lookup "param_find" = some paramFind)
    (hpp : p.lookup "param_push" = some paramPush) (hp : p.lookup "intern_param" = some internParam)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : ArenaR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_param" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.param (decI u))) a₀ ∧
      ArenaR s'.mem (AM.st (internLNode (.param (decI u))) a₀) ∧
      AM.res (internLNode (.param (decI u))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internParam_spec p hpf hpp hp n s₀ u)
  subst hs
  obtain ⟨hok, hX, hres⟩ := pintern_correct s.mem a₀ hR.param u hu _ _ hI
  rw [pinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_param _ _ _ _ hX (internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto paramLens _ _ _ _ _ _ a₀ (internLNode_param_run _ a₀) hok), hres⟩

/-- `intern_ls` refines `internLsNode` under `ArenaR`. -/
theorem internLs_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "ls_match" = some lsMatch)
    (hpf : p.lookup "ls_find" = some lsFind) (hpp : p.lookup "ls_push" = some lsPush)
    (hp : p.lookup "intern_ls" = some internLs)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : ArenaR s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (us : List LIdx)
    (hk : sliceL (s₀.mem.arr64 POOL) o.toNat l.toNat = lsWords us) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_ls" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLsNode us) a₀ ∧
      ArenaR s'.mem (AM.st (internLsNode us) a₀) ∧
      AM.res (internLsNode us) a₀ = decI (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hR.lit.1
  have hspec := internLs_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := lsintern_correct s.mem a₀ hR.lit.1 hR.ls o l hq us hk _ _ hI
  rw [lsinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_ls _ _ _ _ hX (internM_frame _ lsSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto lsLens _ _ _ _ _ _ a₀ (internLsNode_run _ a₀) hok), hres⟩

/-- `intern_nstr` refines `internNNode (.str _ _)` under `ArenaR`. -/
theorem internNStr_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "nstr_match" = some nsMatch)
    (hpf : p.lookup "nstr_find" = some nsFind) (hpp : p.lookup "nstr_push" = some nsPush)
    (hp : p.lookup "intern_nstr" = some internNStr)
    (a₀ : AState) (n : Nat) (s₀ : St) (q o l : Word) (hR : ArenaR s₀.mem a₀)
    (hqw : q.toNat < 2 ^ 32) (hq : SliceOK s₀.mem o l) (s : String)
    (hk : sliceL (s₀.mem.arr64 POOL) o.toNat l.toNat = strWords s) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nstr" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internNNode (.str (decI q) s)) a₀ ∧
      ArenaR s'.mem (AM.st (internNNode (.str (decI q) s)) a₀) ∧
      AM.res (internNNode (.str (decI q) s)) a₀ = decI (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hR.lit.1
  have hspec := internNStr_spec p hph hpe hpm hpf hpp hp n s₀ q o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := nsintern_correct s'.mem a₀ hR.lit.1 hR.nstr q o l hqw hq s hk _ _ hI
  rw [nsinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_nstr _ _ _ _ hX (internM_frame _ nstrSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto nstrLens _ _ _ _ _ _ a₀ (internNNode_str_run _ _ a₀) hok), hres⟩

/-- `intern_*` for name `anonymous` refines its arena interning under `ArenaR`. -/
theorem internNAnon_refinesA (p : Prog) (hpf : p.lookup "nanon_find" = some nanonFind)
    (hpp : p.lookup "nanon_push" = some nanonPush) (hp : p.lookup "intern_nanon" = some internNAnon)
    (a₀ : AState) (n : Nat) (s₀ : St) (hR : ArenaR s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nanon" []
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internNNode .anonymous) a₀ ∧
      ArenaR s'.mem (AM.st (internNNode .anonymous) a₀) ∧
      AM.res (internNNode .anonymous) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internNAnon_spec p hpf hpp hp n s₀)
  subst hs
  obtain ⟨hok, hX, hres⟩ := naintern_correct s.mem a₀ hR.nanon _ _ hI
  rw [nainternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_nanon _ _ _ _ hX (internM_frame _ nanonSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto nanonLens _ _ _ _ _ _ a₀ (internNNode_anon_run a₀) hok), hres⟩

/-- `intern_*` for name `num` refines its arena interning under `ArenaR`. -/
theorem internNNum_refinesA (p : Prog) (hpf : p.lookup "nnum_find" = some nnumFind)
    (hpp : p.lookup "nnum_push" = some nnumPush) (hp : p.lookup "intern_nnum" = some internNNum)
    (a₀ : AState) (n : Nat) (s₀ : St) (pre u : Word) (hR : ArenaR s₀.mem a₀)
    (hpre : pre.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nnum" [pre, u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internNNode (.num (decI pre) u.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (internNNode (.num (decI pre) u.toNat)) a₀) ∧
      AM.res (internNNode (.num (decI pre) u.toNat)) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internNNum_spec p hpf hpp hp n s₀ pre u)
  subst hs
  obtain ⟨hok, hX, hres⟩ := nnintern_correct s.mem a₀ hR.nnum pre u hpre _ _ hI
  rw [nninternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_nnum _ _ _ _ hX (internM_frame _ nnumSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto nnumLens _ _ _ _ _ _ a₀ (internNNode_num_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `forallE` refines its arena interning under `ArenaR`. -/
theorem internForall_refinesA (p : Prog) (hpf : p.lookup "forall_find" = some forallFind)
    (hpp : p.lookup "forall_push" = some forallPush) (hp : p.lookup "intern_forall" = some internForallL)
    (a₀ : AState) (n : Nat) (s₀ : St) (ty body : Word) (hR : ArenaR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_forall" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.forallE (decE ty) (decE body))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.forallE (decE ty) (decE body))) a₀) ∧
      AM.res (internE (.forallE (decE ty) (decE body))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internForallL_spec p hpf hpp hp n s₀ ty body)
  subst hs
  obtain ⟨hok, hX, hres⟩ := faintern_correct s.mem a₀ hR.forallE ty body hty hbody _ _ hI
  rw [fainternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_forallE _ _ _ _ hX (internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto forallLens _ _ _ _ _ _ a₀ (internE_forall_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `fvar` refines its arena interning under `ArenaR`. -/
theorem internFVar_refinesA (p : Prog) (hpf : p.lookup "fvar_find" = some fvarFind)
    (hpp : p.lookup "fvar_push" = some fvarPush) (hp : p.lookup "intern_fvar" = some internFVar)
    (a₀ : AState) (n : Nat) (s₀ : St) (u ty : Word) (hR : ArenaR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_fvar" [u, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.fvar u.toNat (decE ty))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.fvar u.toNat (decE ty))) a₀) ∧
      AM.res (internE (.fvar u.toNat (decE ty))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internFVar_spec p hpf hpp hp n s₀ u ty)
  subst hs
  obtain ⟨hok, hX, hres⟩ := fvintern_correct s.mem a₀ hR.fvar u ty hty _ _ hI
  rw [fvinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_fvar _ _ _ _ hX (internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto fvarLens _ _ _ _ _ _ a₀ (internE_fvar_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `lam` refines its arena interning under `ArenaR`. -/
theorem internLam_refinesA (p : Prog) (hpf : p.lookup "lam_find" = some lamFind)
    (hpp : p.lookup "lam_push" = some lamPush) (hp : p.lookup "intern_lam" = some internLamL)
    (a₀ : AState) (n : Nat) (s₀ : St) (ty body : Word) (hR : ArenaR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lam" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.lam (decE ty) (decE body))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.lam (decE ty) (decE body))) a₀) ∧
      AM.res (internE (.lam (decE ty) (decE body))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internLamL_spec p hpf hpp hp n s₀ ty body)
  subst hs
  obtain ⟨hok, hX, hres⟩ := laintern_correct s.mem a₀ hR.lam ty body hty hbody _ _ hI
  rw [lainternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_lam _ _ _ _ hX (internM_frame _ lamSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto lamLens _ _ _ _ _ _ a₀ (internE_lam_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `proj` refines its arena interning under `ArenaR`. -/
theorem internProj_refinesA (p : Prog) (hpf : p.lookup "proj_find" = some projFind)
    (hpp : p.lookup "proj_push" = some projPush) (hp : p.lookup "intern_proj" = some internProj)
    (a₀ : AState) (nn : Nat) (s₀ : St) (n u e : Word) (hR : ArenaR s₀.mem a₀)
    (hn : n.toNat < 2 ^ 32) (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p nn) "intern_proj" [n, u, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.proj (decI (k := .name) n) u.toNat (decE e))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.proj (decI (k := .name) n) u.toNat (decE e))) a₀) ∧
      AM.res (internE (.proj (decI (k := .name) n) u.toNat (decE e))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internProj_spec p hpf hpp hp nn s₀ n u e)
  subst hs
  obtain ⟨hok, hX, hres⟩ := pjintern_correct s.mem a₀ hR.proj n u e hn he _ _ hI
  rw [pjinternW_eq] at hI
  exact ⟨hloc, hok, hR.lift_proj _ _ _ _ hX (internM_frame _ projSch_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto projLens _ _ _ _ _ _ a₀ (internE_proj_run _ _ _ a₀) hok), hres⟩

end L.Arena

/-! ## The pool and `nat_add_lit` under `ArenaR` -/

namespace L.Arena

/-- Appending to the pool is a frame of the pool and its top. -/
theorem grows_frame (m m' : Mem) (hg : Grows m m') : MemFrame [POOL] [0] m m' := by
  obtain ⟨⟨-, hw, hb⟩, -, -, -, hps⟩ := hg
  refine ⟨fun b hb' hc => ?_, fun x hx => ?_, fun b => ?_, ?_⟩
  · rw [hb b (by simpa using hb'), Mem.arr64_set64_ne _ _ _ _ _ hc]
  · rw [hb CTL (by apart), rdW_set64]
    have : (0 : Word) ≠ x := fun h => hx (by simp [h])
    simp [this]
  · by_cases h : b = POOL
    · subst h; exact hps
    · rw [hb b h, size_set64]
  · rw [hw, Mem.words_size_set64]

/-- **Appending to the pool keeps `ArenaR`**: the tables whose records point into the pool by
their own `grow` lemmas, the others by the frame. -/
theorem ArenaR.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hR : ArenaR m a) : ArenaR m' a := by
  have hf := grows_frame m m' hg
  arena_build hR, hf with
    first | exact LitR.grow m m' hg a hR.lit | exact LsR.grow m m' hg a hR.ls |
      exact NStrR.grow m m' hg a hR.nstr

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `ArenaR`. -/
theorem internLit_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : ArenaR s₀.mem a₀) (hq : SliceOK s₀.mem o l)
    (hn : Norm (s₀.mem.arr64 POOL) o.toNat l.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hR.lit.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := intern_correct s.mem a₀ hR.lit o l hq hn _ _ hI
  rw [internW_eq] at hI
  exact ⟨hloc, hok, hR.lift_lit _ _ _ _ hX (internM_frame _ litS_wf _ _ _ _ _ _ _ _ hI)
    (AM.st_proto litLens _ _ _ _ _ _ a₀ (internE_lit_run _ a₀) hok), hres⟩

/-- **`nat_add_lit` refines `natOpResult`'s `Nat.add` arm under `ArenaR`**: the store's
`natAddLit_refines_store` with the whole arena relation in place of `LitR`. -/
theorem natAddLit_refinesA (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke storeProg (exec storeProg n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ :=
  natAddLit_refines storeProg rfl rfl rfl rfl rfl ArenaR (fun _ _ h => h.lit.1)
    (fun m m' a hR hg => ArenaR.grow m m' hg a hR)
    (internLit_refinesA storeProg rfl rfl rfl rfl rfl rfl) n s₀ a₀ hR oa la ob lb ha hb

end L.Arena
