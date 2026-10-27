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
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The arena relation: one relation for the whole L memory

`ArenaR m a` assembles every table relation of the store tier on one memory layout, with the limb
pool, and the walk memos as one nested group (`MemosR m a.memos`). The array and `CTL` map of the
whole L memory is one table in DESIGN.md ("The memory map"); `storeArrs`/`storeCtl`,
`memoArrs`/`memoCtl` below are its rows for this file, and `Tiers.lean` reserves the ranges of
the tiers still to come.

(Tables 2‥23: `CTL[r + t]` is tier `t`'s node count of the table with record array `r`; tables from
25 on: `CTL[s + t]`, `s` the slot array.) **Extension point:** a writer that avoids `arenaArrs` and `arenaCtl` keeps
`ArenaR` (`ArenaR.frame`, the group frame; `frame_ext` for arrays and words `≥ 64`); `arenaR_init` takes at least 64
arrays and a `CTL` of at least 64 words, so a lane may add its own arrays above 63 without touching
this file. A new relation over such arrays is a separate group over the projection it reads,
with its own group frame (`Tiers.lean`), not a new field here. This file is maintained by hand (it was once generated; `arena_build` removed
the text that grew quadratically). Each table relation reads only its own arrays and counts,
the scratch flag, and (for `lit`, the level lists and the name `str` table) the pool and its top,
so a writer of other arrays leaves it alone (`Frame.lean`, `ConsR.frame`). Every `intern_*`
refinement lifts to `ArenaR` (`intern*_refinesA`): the table's own relation from the table's
theorem, the others by the frame, on both sides (the L memory: `consInternM_frame`; the arena state:
the interning replaces one table behind its lens, `AM.st_proto`). The tactic `arena_build` builds
an `ArenaR` field by field: the given tactic where it applies, the frame elsewhere. `arenaR_init`:
the all-zero memory is related to the arena's initial state `AState.init EStore.empty`.

Not represented here: the derived columns (`DerR`), the other six memos, and the per-declaration
caches and the pins (`Tiers.lean`). They are not in `ArenaR`, so nothing is claimed about them.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## Ownership lists (see "Ownership" below) -/

/-- The store tier's arrays: the pool, the 19 tables' record and slot arrays, and the seven
level-parameter columns 55‥61 (`LpCol.lean`, helper `whnf4-d23`), each table array and column in
both tiers (tier 1 of array `a` is `a + 256`, lane tierswitch). -/
def storeArrs : List ArrId :=
  [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 55, 56, 57, 58, 59, 60, 61,
   258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 311, 312, 313, 314, 315, 316, 317, 62, 256]
/-- The store tier's `CTL` words: the pool top, the scratch flag, the tables' counts. -/
def storeCtl : List Word :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 62]
/-- The memo tier's arrays: `BMEMO`, `LMEMO`, `IMEMO`, `FRMEMO`. -/
def memoArrs : List ArrId := [24, 41, 47, 48]
/-- The memo tier's `CTL` words: each memo's stamp and live count. -/
def memoCtl : List Word := [24, 25, 42, 43, 44, 45, 46, 47]
/-- What `ArenaR` reads. -/
def arenaArrs : List ArrId := storeArrs ++ memoArrs
def arenaCtl : List Word := storeCtl ++ memoCtl

/-- Decide that a table is apart from a writer (`Apart`, `BMEMO ∉ A`, `24 ∉ C`) for concrete
schemas: `decide` times out on the `UInt64` list memberships, `simp` with the array ids is
immediate. -/
macro "apart" : tactic => `(tactic| simp [Apart, ConsSch.wset, memoArrs, memoCtl, storeArrs, storeCtl, POOL, POOL1, PT0, CTL, SCB, BMEMO, bmSch, LMEMO, lfSch, IMEMO, imSch, FRMEMO, frSch, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP])

/-- The side condition of `apart_hi` for a concrete schema. -/
macro "lo_apart" : tactic => `(tactic| simp [POOL, POOL1, PT0, CTL, SCB, BMEMO, FRMEMO, frSch, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP])

/-- The ownership side condition of `apart_own` for a concrete schema of the store tier. -/
macro "own" : tactic => `(tactic| (simp [storeArrs, storeCtl, POOL, POOL1, PT0, CTL, SCB, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, List.mem_cons, List.not_mem_nil, List.forall_mem_cons]))

/-! ## Locality of each table's records -/

theorem litLocal : RLocal litSch RecRel litH [POOL, POOL1, PT0] [0] := by
  intro m m' hra hb hc
  have h0 := hc 0 (by simp)
  have hp := hb POOL (by simp)
  have hp₁ := hb POOL1 (by simp)
  have hpₜ := hb PT0 (by simp)
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m') t o l (by simp only [top_rdW]; exact h0)
    (ptop0_congr hpₜ)
  simp only [litSch] at hra
  refine ⟨fun t i k h => ?_, fun t i => by simp only [litH, hra]⟩
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec, tfld_arr_eq (R := LIT) (hra 0) (hra 1), hpv, hpq, hrs] at h ⊢; exact h
  · simp only [RecRel, StrRec, tfld_arr_eq (R := LIT) (hra 0) (hra 1), hpv, hpq, hrs] at h ⊢; exact h

theorem appLocal : RLocal appSch ARecRel ahash [] [] := by
  intro m m' hra _ _; simp only [appSch] at hra
  exact ⟨fun t i k h => by simpa only [ARecRel, tfld_arr_eq (R := APP) (hra 0) (hra 1)] using h, fun t i => by simp only [ahash, hra]⟩
theorem letELocal : RLocal letSch LeRecRel lehash [] [] := by
  intro m m' hra _ _; simp only [letSch] at hra
  exact ⟨fun t i k h => by simpa only [LeRecRel, tfld_arr_eq (R := LET) (hra 0) (hra 1)] using h, fun t i => by simp only [lehash, hra]⟩
theorem bvarLocal : RLocal bvarSch BRecRel bhash [] [] := by
  intro m m' hra _ _; simp only [bvarSch] at hra
  exact ⟨fun t i k h => by simpa only [BRecRel, tfld_arr_eq (R := BVAR) (hra 0) (hra 1)] using h, fun t i => by simp only [bhash, hra]⟩
theorem lamLocal : RLocal lamSch LaRecRel lahash [] [] := by
  intro m m' hra _ _; simp only [lamSch] at hra
  exact ⟨fun t i k h => by simpa only [LaRecRel, tfld_arr_eq (R := LAM) (hra 0) (hra 1)] using h, fun t i => by simp only [lahash, hra]⟩
theorem forallELocal : RLocal forallSch FaRecRel fahash [] [] := by
  intro m m' hra _ _; simp only [forallSch] at hra
  exact ⟨fun t i k h => by simpa only [FaRecRel, tfld_arr_eq (R := FORALL) (hra 0) (hra 1)] using h, fun t i => by simp only [fahash, hra]⟩
theorem projLocal : RLocal projSch PJRecRel pjhash [] [] := by
  intro m m' hra _ _; simp only [projSch] at hra
  exact ⟨fun t i k h => by simpa only [PJRecRel, tfld_arr_eq (R := PROJ) (hra 0) (hra 1)] using h, fun t i => by simp only [pjhash, hra]⟩
theorem zeroLocal : RLocal zeroSch ZRecRel zhash [] [] :=
  fun _ _ _ _ _ => ⟨fun _ _ _ h => h, fun _ _ => rfl⟩
theorem paramLocal : RLocal paramSch PRecRel phash [] [] := by
  intro m m' hra _ _; simp only [paramSch] at hra
  exact ⟨fun t i k h => by simpa only [PRecRel, tfld_arr_eq (R := PARAM) (hra 0) (hra 1)] using h, fun t i => by simp only [phash, hra]⟩

theorem nanonLocal : RLocal nanonSch NaRecRel nahash [] [] :=
  fun _ _ _ _ _ => ⟨fun _ _ _ h => h, fun _ _ => rfl⟩
theorem nstrLocal : RLocal nstrSch NsRecRel nshash [POOL, POOL1, PT0] [0] := by
  intro m m' hra hb hc
  have h0 := hc 0 (by simp)
  have hp := hb POOL (by simp)
  have hp₁ := hb POOL1 (by simp)
  have hpₜ := hb PT0 (by simp)
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m') t o l (by simp only [top_rdW]; exact h0)
    (ptop0_congr hpₜ)
  simp only [nstrSch] at hra
  refine ⟨fun t i k h => ?_, fun t i => by simp only [nshash, hra]⟩
  simpa only [NsRecRel, nsQ, nsO, nsL, tfld_arr_eq (R := NSTR) (hra 0) (hra 1), hra, hpv, hpq, hrs] using h

theorem nnumLocal : RLocal nnumSch NnRecRel nnhash [] [] := by
  intro m m' hra _ _; simp only [nnumSch] at hra
  exact ⟨fun t i k h => by simpa only [NnRecRel, tfld_arr_eq (R := NNUM) (hra 0) (hra 1)] using h, fun t i => by simp only [nnhash, hra]⟩

/-! ## Each table relation across a writer it is apart from -/

section frames
variable (A : List ArrId) (C : List Word) (m m' : Mem) (hf : MemFrame A C m m') (a : AState)

include hf

theorem LitR.frame (hap : Apart litSch [POOL, POOL1, PT0] [0] A C) (h : LitR m a) : LitR m' a := by
  obtain ⟨hp, hs⟩ := h
  refine ⟨?_, ConsR.frame litCS_wf litLocal hap hf hs⟩
  obtain ⟨-, -, -, -, hA₀, -, -, -, -, hC₀⟩ := hap
  have h0 := hC₀ 0 (by simp)
  exact hp.frame (hf.1 POOL (hA₀ POOL (by simp)).1 (by decide))
    (hf.1 POOL1 (hA₀ POOL1 (by simp)).1 (by decide)) (hf.1 PT0 (hA₀ PT0 (by simp)).1 (by decide))
    (hf.2.2.1 CTL) (by simp only [top_rdW]; exact hf.2.1 0 h0) hf.2.2.2
theorem AppR.frame (hap : Apart appSch [] [] A C) (h : AppR m a) : AppR m' a :=
  ConsR.frame appCS_wf appLocal hap hf h
theorem SortR.frame (hap : Apart sortSch [] [] A C) (h : SortR m a) : SortR m' a :=
  ConsR.frame sortCS_wf sortLocal hap hf h
theorem ConstR.frame (hap : Apart constSch [] [] A C) (h : ConstR m a) : ConstR m' a :=
  ConsR.frame constCS_wf constLocal hap hf h
theorem LetR.frame (hap : Apart letSch [] [] A C) (h : LetR m a) : LetR m' a :=
  ConsR.frame letCS_wf letELocal hap hf h
theorem BVarR.frame (hap : Apart bvarSch [] [] A C) (h : BVarR m a) : BVarR m' a :=
  ConsR.frame bvarCS_wf bvarLocal hap hf h
theorem FVarR.frame (hap : Apart fvarSch [] [] A C) (h : FVarR m a) : FVarR m' a :=
  ConsR.frame fvarCS_wf fvarLocal hap hf h
theorem LamR.frame (hap : Apart lamSch [] [] A C) (h : LamR m a) : LamR m' a :=
  ConsR.frame lamCS_wf lamLocal hap hf h
theorem ForallR.frame (hap : Apart forallSch [] [] A C) (h : ForallR m a) : ForallR m' a :=
  ConsR.frame forallCS_wf forallELocal hap hf h
theorem ProjR.frame (hap : Apart projSch [] [] A C) (h : ProjR m a) : ProjR m' a :=
  ConsR.frame projCS_wf projLocal hap hf h
theorem ZeroR.frame (hap : Apart zeroSch [] [] A C) (h : ZeroR m a) : ZeroR m' a :=
  ConsR.frame zeroCS_wf zeroLocal hap hf h
theorem SuccR.frame (hap : Apart succSch [] [] A C) (h : SuccR m a) : SuccR m' a :=
  ConsR.frame succCS_wf succLocal hap hf h
theorem MaxR.frame (hap : Apart maxSch [] [] A C) (h : MaxR m a) : MaxR m' a :=
  ConsR.frame maxCS_wf maxLocal hap hf h
theorem ImaxR.frame (hap : Apart imaxSch [] [] A C) (h : ImaxR m a) : ImaxR m' a :=
  ConsR.frame imaxCS_wf imaxLocal hap hf h
theorem ParamR.frame (hap : Apart paramSch [] [] A C) (h : ParamR m a) : ParamR m' a :=
  ConsR.frame paramCS_wf paramLocal hap hf h
theorem LsR.frame (hap : Apart lsSch [POOL, POOL1, PT0] [0] A C) (h : LsR m a) : LsR m' a :=
  ConsR.frame lsCS_wf lsLocal hap hf h
theorem NAnonR.frame (hap : Apart nanonSch [] [] A C) (h : NAnonR m a) : NAnonR m' a :=
  ConsR.frame nanonCS_wf nanonLocal hap hf h
theorem NStrR.frame (hap : Apart nstrSch [POOL, POOL1, PT0] [0] A C) (h : NStrR m a) : NStrR m' a :=
  ConsR.frame nstrCS_wf nstrLocal hap hf h
theorem NNumR.frame (hap : Apart nnumSch [] [] A C) (h : NNumR m a) : NNumR m' a :=
  ConsR.frame nnumCS_wf nnumLocal hap hf h

end frames

section lpframes
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]
  (A : List ArrId) (C : List Word) (m m' : Mem) (hf : MemFrame A C m m') (a : AState)

include hf in
/-- **A level-parameter column across a writer apart from its table and column** (the column
is the table's extra array `B` in `Apart`). -/
theorem ColT2.frameAp (S : Schema) {L : Lens α δ k} {B : ArrId} {f : δ → Word}
    (hap : Apart S [B, B + 256] [] A C) (h : ColT2 L B f m a) : ColT2 L B f m' a :=
  h.frameM hf (hap.2.2.2.2.1 B (by simp)).1 (hap.2.2.2.2.1 (B + 256) (by simp)).1
    (hap.2.2.2.2.1 B (by simp)).2

end lpframes

/-! ## Ownership: the arrays and `CTL` words each group reads

A group relation reads only the arrays and `CTL` words it owns, so a writer that avoids them
keeps it (`MemosR.frame`, `ArenaR.frame`): one lemma per group, from the ownership lists, instead
of one per writer. The lists are concrete, so a writer's side conditions are `by decide`. -/

/-- A table is apart from a writer that avoids what the table's group owns. -/
theorem apart_own (S : Schema) (A₀ : List ArrId)
    (C₀ : List Word) (own : List ArrId) (ownC : List Word)
    (hown : S.ra ∈ own ∧ S.ra + 256 ∈ own ∧ S.sa ∈ own ∧ S.sa + 256 ∈ own ∧
      (∀ b ∈ A₀, b ∈ own ∧ b ≠ CTL) ∧ S.ca ∈ ownC ∧
      S.ca + 1 ∈ ownC ∧ (1 : Word) ∈ ownC ∧ SCB ∈ ownC ∧ ∀ x ∈ C₀, x ∈ ownC)
    (A : List ArrId) (C : List Word) (hA : ∀ b ∈ A, b ∉ own) (hC : ∀ x ∈ C, x ∉ ownC) :
    Apart S A₀ C₀ A C := by
  obtain ⟨h1, h1', h2, h2', h3, h4, h5, h6, h8, h7⟩ := hown
  exact ⟨fun h => hA _ h h1, fun h => hA _ h h1', fun h => hA _ h h2, fun h => hA _ h h2',
    fun b hb => ⟨fun h => hA _ h (h3 b hb).1, (h3 b hb).2⟩, fun h => hC _ h h4, fun h => hC _ h h5,
    fun h => hC _ h h6, fun h => hC _ h h8, fun x hx h => hC _ h (h7 x hx)⟩

/-! ## The memo tier -/

/-- **The walk memos** (tier C: cleared at each top-level call), over the projection `a.memos`.
A separate group, so that a table writer frames it with one lemma (`MemosR.frame`), a memo writer
leaves the tables definitionally alone on the arena side, and a new memo changes this structure
only. -/
structure MemosR (m : Mem) (ms : Memos) : Prop where
  bvar : MemoRG bmSch bmKey (·.toNat) m ms.bvarBC
  lift : MemoRG lfSch lfKey decE m ms.liftC
  inst1 : MemoRG imSch lfKey decE m ms.inst1C
  fvar : MemoRG frSch bmKey (·.toNat) m ms.fvarBC

/-- **The memo tier's group frame.** -/
theorem MemosR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {ms : Memos}
    (hA : ∀ b ∈ A, b ∉ memoArrs) (hC : ∀ x ∈ C, x ∉ memoCtl) (hf : MemFrame A C m m')
    (h : MemosR m ms) : MemosR m' ms :=
  ⟨memoRG_frame bmSch bmSch_wf bmKey _ A C (fun h => hA _ h (by simp [memoArrs]))
      (fun h => hC _ h (by simp [memoCtl])) m m' hf _ h.bvar,
    memoRG_frame lfSch lfSch_wf lfKey _ A C (fun h => hA _ h (by simp [memoArrs]))
      (fun h => hC _ h (by simp [memoCtl])) m m' hf _ h.lift,
    memoRG_frame imSch imSch_wf lfKey _ A C (fun h => hA _ h (by simp [memoArrs]))
      (fun h => hC _ h (by simp [memoCtl])) m m' hf _ h.inst1,
    memoRG_frame frSch frSch_wf bmKey _ A C (fun h => hA _ h (by simp [memoArrs]))
      (fun h => hC _ h (by simp [memoCtl])) m m' hf _ h.fvar⟩

/-- **Build a `MemosR m' ms'`** across a memo writer `hf`: the written memo by `t`, the others
by their frame. -/
macro "memos_build " hM:term ", " hf:term " with " t:tacticSeq : tactic => `(tactic| exact ⟨
    by first | $t | exact memoRG_frame bmSch bmSch_wf bmKey _ _ _ (by apart) (by apart) _ _ $hf _ ($hM).bvar,
    by first | $t | exact memoRG_frame lfSch lfSch_wf lfKey _ _ _ (by apart) (by apart) _ _ $hf _ ($hM).lift,
    by first | $t | exact memoRG_frame imSch imSch_wf lfKey _ _ _ (by apart) (by apart) _ _ $hf _ ($hM).inst1,
    by first | $t | exact memoRG_frame frSch frSch_wf bmKey _ _ _ (by apart) (by apart) _ _ $hf _ ($hM).fvar⟩)

/-! ## The relation -/

/-- **The arena relation**: every represented table and the pool (the store tier, over
`a.store`), and the memo tier as one nested group over `a.memos`, on the one layout above. Kept
opaque to `grind` (DESIGN.md, "Does the relation scale?"): proofs name its fields. -/
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
  memos : MemosR m a.memos
  /-- The level-parameter bits (helper `whnf4-d23`, `LpCol.lean`): the constant ones of `zero`
  and `param`, the columns of `succ`, `max`, `imax`, the level lists, `sort`, `const`, `fvar`. -/
  zeroHp : ConstT2 zeroLens (fun d : LDer => hpW d = 0) a
  paramHp : ConstT2 paramLens (fun d : LDer => hpW d = 1) a
  succHp : ColT2 succLens SHP hpW m a
  maxHp : ColT2 maxLens MHP hpW m a
  imaxHp : ColT2 imaxLens IHP hpW m a
  lsHp : ColT2 lsLens LSHP hpW m a
  sortLp : ColT2 sortLens SOLP lpW m a
  constLp : ColT2 constLens CLP lpW m a
  fvarLp : ColT2 fvarLens FVLP lpW m a

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
    by first | $t | exact ($hR).memos.frame (by $ap) (by $ap) $hf,
    by first | $t | exact ($hR).zeroHp,
    by first | $t | exact ($hR).paramHp,
    by first | $t | exact ($hR).succHp.frameAp _ _ _ _ $hf _ succSch (by $ap),
    by first | $t | exact ($hR).maxHp.frameAp _ _ _ _ $hf _ maxSch (by $ap),
    by first | $t | exact ($hR).imaxHp.frameAp _ _ _ _ $hf _ imaxSch (by $ap),
    by first | $t | exact ($hR).lsHp.frameAp _ _ _ _ $hf _ lsSch (by $ap),
    by first | $t | exact ($hR).sortLp.frameAp _ _ _ _ $hf _ sortSch (by $ap),
    by first | $t | exact ($hR).constLp.frameAp _ _ _ _ $hf _ constSch (by $ap),
    by first | $t | exact ($hR).fvarLp.frameAp _ _ _ _ $hf _ fvarSch (by $ap)⟩)

/-- `arena_build hR, hf with t` for a writer of concrete arrays and words (`Apart` by `apart`). -/
macro "arena_build " hR:term ", " hf:term " with " t:tacticSeq : tactic =>
  `(tactic| arena_build $hR, $hf with $t using apart)

/-- **A memo writer keeps `ArenaR`**: the tables by the frame (the writer avoids the store
tier), the memo tier as given; the arena state changed only in `memos`, so the tables' relations
read the same fields. -/
theorem ArenaR.with_memos {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState} {ms : Memos}
    (hR : ArenaR m a) (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b ∉ storeArrs)
    (hC : ∀ x ∈ C, x ∉ storeCtl) (hM : MemosR m' ms) : ArenaR m' { a with memos := ms } := by
  arena_build hR, hf with exact hM using exact apart_own _ _ _ storeArrs storeCtl (by own) _ _ hA hC

/-- **The store and memo tiers' group frame**: a writer that avoids `arenaArrs` and `arenaCtl`
keeps `ArenaR`. -/
theorem ArenaR.frame {A : List ArrId} {C : List Word} (hA : ∀ b ∈ A, b ∉ arenaArrs)
    (hC : ∀ x ∈ C, x ∉ arenaCtl) {m m' : Mem} (hf : MemFrame A C m m') {a : AState}
    (hR : ArenaR m a) : ArenaR m' a :=
  hR.with_memos hf (fun b hb h => hA b hb (List.mem_append_left _ h))
    (fun x hx h => hC x hx (List.mem_append_left _ h))
    (hR.memos.frame (fun b hb h => hA b hb (List.mem_append_right _ h))
      (fun x hx h => hC x hx (List.mem_append_right _ h)) hf)

theorem not_mem_arenaCtl (x : Word) (hx : 64 ≤ x.toNat) : x ∉ arenaCtl := by
  intro h
  simp only [arenaCtl, storeCtl, memoCtl, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at h
  have : ∀ y : Word, y.toNat < 64 → x ≠ y := fun y hy h => by subst h; omega
  simp_all

/-- **A writer of the derived-range arrays 42‥46 (and `CTL` words `≥ 64`) keeps `ArenaR`**: nothing
in it reads them (they are `DerR`'s, `ExprMk.lean`). -/
theorem ArenaR.frame_above (A : List ArrId) (C : List Word)
    (hA : ∀ b ∈ A, (42 ≤ b ∧ b < 47) ∨ (298 ≤ b ∧ b < 303))
    (hC : ∀ x ∈ C, 64 ≤ x.toNat) (m m' : Mem) (hf : MemFrame A C m m') (a : AState)
    (hR : ArenaR m a) : ArenaR m' a :=
  have hlt : ∀ y ∈ arenaArrs, ¬ ((42 ≤ y ∧ y < 47) ∨ (298 ≤ y ∧ y < 303)) := by decide
  hR.frame (fun b hb h => hlt b h (hA b hb))
    (fun x hx => not_mem_arenaCtl x (hC x hx)) hf

/-- **The extension point for other lanes**: arrays in `[64, 256)` and `CTL` words `≥ 64` are
outside every relation of `ArenaR` (ids from `256` on are tier-1 arrays). A writer of only such
arrays and words keeps `ArenaR`. -/
theorem ArenaR.frame_ext (A : List ArrId) (C : List Word) (hA : ∀ b ∈ A, 64 ≤ b ∧ b < 256)
    (hC : ∀ x ∈ C, 64 ≤ x.toNat) (m m' : Mem) (hf : MemFrame A C m m') (a : AState)
    (hR : ArenaR m a) : ArenaR m' a :=
  have hlt : ∀ y ∈ arenaArrs, ¬ (64 ≤ y ∧ y < 256) := by decide
  hR.frame (fun b hb h => hlt b h (hA b hb))
    (fun x hx => not_mem_arenaCtl x (hC x hx)) hf

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

/-- The walk memos in the all-zero memory are empty. -/
theorem memosR_init (sizes : List Nat) (hctl : 64 ≤ sizes[1]?.getD 0) :
    MemosR (initMem sizes) (AState.init EStore.empty).memos := by
  have hz := initMem_rd sizes
  have hc : ((initMem sizes).arr64 CTL).size = sizes[1]?.getD 0 := by
    rw [initMem_arr]; simp [CTL]
  exact ⟨memoRG_zero bmSch bmKey _ _ hz (by rw [hc]; simp; omega),
    memoRG_zero lfSch lfKey _ _ hz (by rw [hc]; simp; omega),
    memoRG_zero imSch lfKey _ _ hz (by rw [hc]; simp; omega),
    memoRG_zero frSch bmKey _ _ hz (by rw [hc]; simp; omega)⟩

/-- **The relation holds initially**: the all-zero memory and the arena's initial state. -/
theorem arenaR_init (sizes : List Nat) (hlen : 64 ≤ sizes.length) (hctl : 64 ≤ sizes[1]?.getD 0)
    (hpool : sizes[0]?.getD 0 < 2 ^ 40) (hpool1 : sizes[256]?.getD 0 < 2 ^ 40)
    (hsz : ∀ b, b < 64 ∨ (256 ≤ b ∧ b < 320) →
      consMinWords ≤ sizes[b]?.getD 0 ∧ sizes[b]?.getD 0 < 2 ^ 61) :
    ArenaR (initMem sizes) (AState.init EStore.empty) := by
  have hz := initMem_rd sizes
  have hs : ∀ (a : Nat), a < 64 → ∀ t, consMinWords ≤ ((initMem sizes).arr64 (tierA a t)).size ∧
      ((initMem sizes).arr64 (tierA a t)).size < 2 ^ 61 := fun a ha t => by
    rw [initMem_arr]
    rcases tierA_cases' a t with e | e <;> rw [e] <;> simpa using hsz _ (by omega)
  have hc : ((initMem sizes).arr64 CTL).size = sizes[1]?.getD 0 := by
    rw [initMem_arr]; simp [CTL]
  have hp : ((initMem sizes).arr64 POOL).size = sizes[0]?.getD 0 := by
    rw [initMem_arr]; simp [POOL]
  have hw : CTL < (initMem sizes).words.size := by
    show 1 < (sizes.map _).toArray.size; simp only [List.size_toArray, List.length_map]; omega
  refine ⟨⟨?_, consR_init hz (by rw [hc]; simp [litCS, litCSk]; omega) (hs _ (by decide))⟩,
    consR_init hz (by rw [hc]; simp [appCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [sortCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [constCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [letCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [bvarCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [fvarCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [lamCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [forallCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [projCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [zeroCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [succCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [maxCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [imaxCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [paramCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [lsCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [nanonCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [nstrCS]; omega) (hs _ (by decide)),
    consR_init hz (by rw [hc]; simp [nnumCS]; omega) (hs _ (by decide)), ?_,
    ⟨constT_empty _, constT_empty _⟩, ⟨constT_empty _, constT_empty _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩, ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩, ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩, ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩⟩
  · have hp1 : ((initMem sizes).arr64 POOL1).size = sizes[256]?.getD 0 := by
      rw [initMem_arr]; simp [POOL1]
    have hpc : pcap (initMem sizes) = 2 ^ 41 - 1 := pcap_of_small _ ⟨by rw [hp]; exact hpool, by rw [hp1]; exact hpool1⟩
    have ht : (initMem sizes).top = 0 := by simp only [top_rdW, hz]
    have hq : (initMem sizes).ptop0 = 0 := by simp only [Mem.ptop0]; exact hz PT0 0
    refine ⟨hw, by rw [hc]; omega, by rw [hpc]; omega, by rw [hpc, ht]; simp, by rw [hq]; simp, ?_⟩
    rw [ht]; simp
  · exact memosR_init sizes hctl

/-! ## Interning lifts to `ArenaR`

Per table: the table's own relation after the interning (its `*intern_correct`), the frame of the
other tables in memory (`consInternM_frame`), and in the arena state (the interning replaced at most
one table behind its lens, so the other relations read the same fields). -/

section lift
variable (m m' : Mem) (a a' : AState) (hR : ArenaR m a)
include hR

/-- Interning into `lit` keeps `ArenaR`. -/
theorem ArenaR.lift_lit (hX : LitR m' a')
    (hf : MemFrame [litSch.ra, litSch.ra + 256, litSch.sa, litSch.sa + 256] [litSch.ca, litSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = litLens.setP a t) ∨ (∃ t, a' = litLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `app` keeps `ArenaR`. -/
theorem ArenaR.lift_app (hX : AppR m' a')
    (hf : MemFrame [appSch.ra, appSch.ra + 256, appSch.sa, appSch.sa + 256] [appSch.ca, appSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = appLens.setP a t) ∨ (∃ t, a' = appLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `sort` keeps `ArenaR`. -/
theorem ArenaR.lift_sort (hX : SortR m' a' ∧ ColT2 sortLens SOLP lpW m' a')
    (hf : MemFrame [sortSch.ra, sortSch.ra + 256, sortSch.sa, sortSch.sa + 256, SOLP, SOLP + 256] [sortSch.ca, sortSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = sortLens.setP a t) ∨ (∃ t, a' = sortLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `const` keeps `ArenaR`. -/
theorem ArenaR.lift_const (hX : ConstR m' a' ∧ ColT2 constLens CLP lpW m' a')
    (hf : MemFrame [constSch.ra, constSch.ra + 256, constSch.sa, constSch.sa + 256, CLP, CLP + 256] [constSch.ca, constSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = constLens.setP a t) ∨ (∃ t, a' = constLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `letE` keeps `ArenaR`. -/
theorem ArenaR.lift_letE (hX : LetR m' a')
    (hf : MemFrame [letSch.ra, letSch.ra + 256, letSch.sa, letSch.sa + 256] [letSch.ca, letSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = letLens.setP a t) ∨ (∃ t, a' = letLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `bvar` keeps `ArenaR`. -/
theorem ArenaR.lift_bvar (hX : BVarR m' a')
    (hf : MemFrame [bvarSch.ra, bvarSch.ra + 256, bvarSch.sa, bvarSch.sa + 256] [bvarSch.ca, bvarSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = bvarLens.setP a t) ∨ (∃ t, a' = bvarLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `fvar` keeps `ArenaR`. -/
theorem ArenaR.lift_fvar (hX : FVarR m' a' ∧ ColT2 fvarLens FVLP lpW m' a')
    (hf : MemFrame [fvarSch.ra, fvarSch.ra + 256, fvarSch.sa, fvarSch.sa + 256, FVLP, FVLP + 256] [fvarSch.ca, fvarSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = fvarLens.setP a t) ∨ (∃ t, a' = fvarLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `lam` keeps `ArenaR`. -/
theorem ArenaR.lift_lam (hX : LamR m' a')
    (hf : MemFrame [lamSch.ra, lamSch.ra + 256, lamSch.sa, lamSch.sa + 256] [lamSch.ca, lamSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = lamLens.setP a t) ∨ (∃ t, a' = lamLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `forallE` keeps `ArenaR`. -/
theorem ArenaR.lift_forallE (hX : ForallR m' a')
    (hf : MemFrame [forallSch.ra, forallSch.ra + 256, forallSch.sa, forallSch.sa + 256] [forallSch.ca, forallSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = forallLens.setP a t) ∨ (∃ t, a' = forallLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `proj` keeps `ArenaR`. -/
theorem ArenaR.lift_proj (hX : ProjR m' a')
    (hf : MemFrame [projSch.ra, projSch.ra + 256, projSch.sa, projSch.sa + 256] [projSch.ca, projSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = projLens.setP a t) ∨ (∃ t, a' = projLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `zero` keeps `ArenaR`. -/
theorem ArenaR.lift_zero (hX : ZeroR m' a' ∧ ConstT2 zeroLens (fun d : LDer => hpW d = 0) a')
    (hf : MemFrame [zeroSch.ra, zeroSch.ra + 256, zeroSch.sa, zeroSch.sa + 256] [zeroSch.ca, zeroSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = zeroLens.setP a t) ∨ (∃ t, a' = zeroLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `succ` keeps `ArenaR`. -/
theorem ArenaR.lift_succ (hX : SuccR m' a' ∧ ColT2 succLens SHP hpW m' a')
    (hf : MemFrame [succSch.ra, succSch.ra + 256, succSch.sa, succSch.sa + 256, SHP, SHP + 256] [succSch.ca, succSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = succLens.setP a t) ∨ (∃ t, a' = succLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `max` keeps `ArenaR`. -/
theorem ArenaR.lift_max (hX : MaxR m' a' ∧ ColT2 maxLens MHP hpW m' a')
    (hf : MemFrame [maxSch.ra, maxSch.ra + 256, maxSch.sa, maxSch.sa + 256, MHP, MHP + 256] [maxSch.ca, maxSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = maxLens.setP a t) ∨ (∃ t, a' = maxLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `imax` keeps `ArenaR`. -/
theorem ArenaR.lift_imax (hX : ImaxR m' a' ∧ ColT2 imaxLens IHP hpW m' a')
    (hf : MemFrame [imaxSch.ra, imaxSch.ra + 256, imaxSch.sa, imaxSch.sa + 256, IHP, IHP + 256] [imaxSch.ca, imaxSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = imaxLens.setP a t) ∨ (∃ t, a' = imaxLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `param` keeps `ArenaR`. -/
theorem ArenaR.lift_param (hX : ParamR m' a' ∧ ConstT2 paramLens (fun d : LDer => hpW d = 1) a')
    (hf : MemFrame [paramSch.ra, paramSch.ra + 256, paramSch.sa, paramSch.sa + 256] [paramSch.ca, paramSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = paramLens.setP a t) ∨ (∃ t, a' = paramLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `ls` keeps `ArenaR`. -/
theorem ArenaR.lift_ls (hX : LsR m' a' ∧ ColT2 lsLens LSHP hpW m' a')
    (hf : MemFrame [lsSch.ra, lsSch.ra + 256, lsSch.sa, lsSch.sa + 256, LSHP, LSHP + 256] [lsSch.ca, lsSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = lsLens.setP a t) ∨ (∃ t, a' = lsLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with first | exact hX.1 | exact hX.2

/-- Interning into `nanon` keeps `ArenaR`. -/
theorem ArenaR.lift_nanon (hX : NAnonR m' a')
    (hf : MemFrame [nanonSch.ra, nanonSch.ra + 256, nanonSch.sa, nanonSch.sa + 256] [nanonSch.ca, nanonSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = nanonLens.setP a t) ∨ (∃ t, a' = nanonLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `nstr` keeps `ArenaR`. -/
theorem ArenaR.lift_nstr (hX : NStrR m' a')
    (hf : MemFrame [nstrSch.ra, nstrSch.ra + 256, nstrSch.sa, nstrSch.sa + 256] [nstrSch.ca, nstrSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = nstrLens.setP a t) ∨ (∃ t, a' = nstrLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

/-- Interning into `nnum` keeps `ArenaR`. -/
theorem ArenaR.lift_nnum (hX : NNumR m' a')
    (hf : MemFrame [nnumSch.ra, nnumSch.ra + 256, nnumSch.sa, nnumSch.sa + 256] [nnumSch.ca, nnumSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = nnumLens.setP a t) ∨ (∃ t, a' = nnumLens.setS a t)) :
    ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

end lift

/-! ## The level-parameter bits are the twin's (helper `whnf4-d23`)

`lvlHPW m u` (the L read of a level handle's bit, `LpCol.lean`) is `hasParam` of the twin's
derived record of `decI u`, for every handle word below `2^32`: the tier check is the twin's
`derived`, the count check its `derAt` range, and the column or the constant is `ArenaR`'s. The
same for level lists (`lsHPW_ok`) and for the `or` over a slice of level handles (`lsOrW_ok`). -/

section lpok
variable (m : Mem) (a : AState) (hR : ArenaR m a)
include hR

theorem lvlHPW_ok (u : Word) (hu : u.toNat < 2 ^ 32) :
    lvlHPW m u = hpW (a.store.lss.ls.derived (decI u)) := by
  have ht := tierW_le u
  have hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.lss.ls.scratchOn := ConsR.flag hR.succ
  have hp : (decI u : LIdx).isPersistent = (tierW u == 0) := isPersistent_decI u hu
  unfold lvlHPW
  by_cases hs : tierW u ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ite_eq_left hs]
    have hon : a.store.lss.ls.scratchOn = false := by rw [← hfl]; simp [hs.2]
    simp [LStore.derived, hp, hs.1, hon]; rfl
  rw [ite_eq_right hs]
  have hder : a.store.lss.ls.derived (decI u) =
      (if tierW u = 0 then a.store.lss.ls.pers else a.store.lss.ls.scr).derAt (decI u) := by
    unfold LStore.derived; rw [hp]
    by_cases h0 : tierW u = 0
    · simp [h0]
    · have hon : a.store.lss.ls.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hs ⟨h0, h1⟩
      simp [h0, hon]
  rw [hder]
  have hz : (0 : Word) = hpW ((if tierW u = 0 then a.store.lss.ls.pers.zeros
      else a.store.lss.ls.scr.zeros).derAt (idxW u).toNat) := by
    rw [← const_read hpW 0 m _ _ _ hR.zero hR.zeroHp.1 hR.zeroHp.2 rfl
      (tierW u) (idxW u) ht]
    split <;> rfl
  have hpa := const_read hpW 1 m _ _ _ hR.param hR.paramHp.1 hR.paramHp.2
    rfl (tierW u) (idxW u) ht
  have hsu := col_read SHP hpW m _ _ _ hR.succ hR.succHp.1 hR.succHp.2 rfl
    (tierW u) (idxW u) ht
  have hma := col_read MHP hpW m _ _ _ hR.max hR.maxHp.1 hR.maxHp.2 rfl
    (tierW u) (idxW u) ht
  have him := col_read IHP hpW m _ _ _ hR.imax hR.imaxHp.1 hR.imaxHp.2 rfl
    (tierW u) (idxW u) ht
  simp only [paramCS, succCS, maxCS, imaxCS] at hz hpa hsu hma him
  have hidx := decI_idx (k := .level) u
  simp only [LTables.derAt, hidx, beq_iff_eq]
  have tg := fun g (hg : g < 16) => decI_tag_eq (k := .level) u hu g hg
  have hL : ∀ (g : Nat), g < 16 → u >>> 28 = UInt64.ofNat g →
      (decI u : LIdx).tag = UInt32.ofNat g := fun g hg h => (tg g hg).mpr h
  have hN : ∀ (g : Nat), g < 16 → u >>> 28 ≠ UInt64.ofNat g →
      (decI u : LIdx).tag ≠ UInt32.ofNat g := fun g hg h e => h ((tg g hg).mp e)
  by_cases g0 : u >>> 28 = UInt64.ofNat 0
  · simp (config := { decide := true }) only [g0, hL 0 (by decide) g0, LTag.zero, LTag.succ,
      LTag.max, LTag.imax, LTag.param, ite_true, ite_false]
    by_cases h0 : tierW u = 0 <;> simp only [h0, ite_true, ite_false] at hz ⊢ <;> exact hz
  by_cases g1 : u >>> 28 = UInt64.ofNat 1
  · simp (config := { decide := true }) only [g1, hL 1 (by decide) g1, LTag.zero, LTag.succ,
      LTag.max, LTag.imax, LTag.param, ite_true, ite_false]
    by_cases h0 : tierW u = 0 <;> simp only [h0, ite_true, ite_false] at hsu ⊢ <;> exact hsu
  by_cases g2 : u >>> 28 = UInt64.ofNat 2
  · simp (config := { decide := true }) only [g2, hL 2 (by decide) g2, LTag.zero, LTag.succ,
      LTag.max, LTag.imax, LTag.param, ite_true, ite_false]
    by_cases h0 : tierW u = 0 <;> simp only [h0, ite_true, ite_false] at hma ⊢ <;> exact hma
  by_cases g3 : u >>> 28 = UInt64.ofNat 3
  · simp (config := { decide := true }) only [g3, hL 3 (by decide) g3, LTag.zero, LTag.succ,
      LTag.max, LTag.imax, LTag.param, ite_true, ite_false]
    by_cases h0 : tierW u = 0 <;> simp only [h0, ite_true, ite_false] at him ⊢ <;> exact him
  by_cases g4 : u >>> 28 = UInt64.ofNat 4
  · simp (config := { decide := true }) only [g4, hL 4 (by decide) g4, LTag.zero, LTag.succ,
      LTag.max, LTag.imax, LTag.param, ite_true, ite_false]
    by_cases h0 : tierW u = 0 <;> simp only [h0, ite_true, ite_false] at hpa ⊢ <;> exact hpa
  have n0 : (decI u : LIdx).tag ≠ LTag.zero := hN 0 (by decide) g0
  have n1 : (decI u : LIdx).tag ≠ LTag.succ := hN 1 (by decide) g1
  have n2 : (decI u : LIdx).tag ≠ LTag.max := hN 2 (by decide) g2
  have n3 : (decI u : LIdx).tag ≠ LTag.imax := hN 3 (by decide) g3
  have n4 : (decI u : LIdx).tag ≠ LTag.param := hN 4 (by decide) g4
  have m1 : ¬ u >>> 28 = 1 := g1
  have m2 : ¬ u >>> 28 = 2 := g2
  have m3 : ¬ u >>> 28 = 3 := g3
  have m4 : ¬ u >>> 28 = 4 := g4
  simp only [n0, n1, n2, n3, n4, m1, m2, m3, m4, ite_false]
  rfl

theorem lvlHPW_or (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32) :
    lvlHPW m u ||| lvlHPW m v = b2w ((a.store.lss.ls.derived (decI u)).hasParam ||
      (a.store.lss.ls.derived (decI v)).hasParam) := by
  rw [lvlHPW_ok m a hR u hu, lvlHPW_ok m a hR v hv, hpW, hpW, b2w_or]

theorem lsHPW_ok (us : Word) (hus : us.toNat < 2 ^ 32) :
    lsHPW m us = hpW (a.store.lss.derived (decI us)) := by
  have ht := tierW_le us
  have hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.lss.scratchOn := ConsR.flag hR.ls
  have hp : (decI us : LsIdx).isPersistent = (tierW us == 0) := isPersistent_decI us hus
  unfold lsHPW
  by_cases hs : tierW us ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ite_eq_left hs]
    have hon : a.store.lss.scratchOn = false := by rw [← hfl]; simp [hs.2]
    simp [LsStore.derived, hp, hs.1, hon]; rfl
  rw [ite_eq_right hs]
  have hder : a.store.lss.derived (decI us) =
      (if tierW us = 0 then a.store.lss.pers else a.store.lss.scr).derAt (decI us) := by
    unfold LsStore.derived; rw [hp]
    by_cases h0 : tierW us = 0
    · simp [h0]
    · have hon : a.store.lss.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hs ⟨h0, h1⟩
      simp [h0, hon]
  rw [hder]
  have hl := col_read LSHP hpW m _ _ _ hR.ls hR.lsHp.1 hR.lsHp.2 rfl
    (tierW us) (idxW us) ht
  simp only [lsCS] at hl
  simp only [LsTables.derAt, decI_idx, beq_iff_eq]
  by_cases g0 : us >>> 28 = UInt64.ofNat 0
  · simp (config := { decide := true }) only [g0, (decI_tag_eq (k := .levels) us hus 0 (by decide)).mpr g0,
      LsTag.list, ite_true]
    by_cases h0 : tierW us = 0 <;> simp only [h0, ite_true, ite_false] at hl ⊢ <;> exact hl
  · have n0 : (decI us : LsIdx).tag ≠ LsTag.list :=
      fun e => g0 ((decI_tag_eq (k := .levels) us hus 0 (by decide)).mp e)
    have m0 : ¬ us >>> 28 = 0 := g0
    simp only [n0, m0, ite_false]
    rfl

theorem lsOrW_slice : ∀ (n : Nat) (o : Word) (us : List LIdx), o.toNat + n ≤ 2 ^ 41 →
    sliceL (vpool m) o.toNat n = lsWords us →
    lsOrW m o n = hpW (a.store.lss.derOfView us) := by
  intro n
  induction n with
  | zero =>
    intro o us _ hk
    cases us with
    | nil => rfl
    | cons u us => simp [sliceL, lsWords] at hk
  | succ n ih =>
    intro o us hlt hk
    cases us with
    | nil => simp [sliceL, lsWords] at hk
    | cons u us =>
      rw [sliceL_succ] at hk
      simp only [lsWords, List.map_cons, List.cons.injEq] at hk
      obtain ⟨h1, h2⟩ := hk
      have ho : (o + 1).toNat = o.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hrd : prd m o = u.word.toUInt64 := by rw [← vpool_getD m o (by omega)]; exact h1
      rw [lsOrW_cons, hrd, ih (o + 1) us (by omega) (by rw [ho]; exact h2),
        lvlHPW_ok m a hR _ (by simp; exact UInt32.toNat_lt _)]
      have hu : (decI u.word.toUInt64 : LIdx) = u := ((word_decI u _ (by simp; exact UInt32.toNat_lt _)).mp rfl).symm
      rw [hu]
      simp only [LsStore.derOfView, hpW, b2w_or]

theorem lsOrW_ok (o l : Word) (hq : SliceOK m o l) (us : List LIdx)
    (hk : sliceL (vpool m) o.toNat l.toNat = lsWords us) :
    lsOrW m o l.toNat = hpW (a.store.lss.derOfView us) := by
  have hle := hq.le
  have htop := hR.lit.1.2.2.2.1
  have hpc := pcap_eq m (by have := hR.lit.1.2.2.1; omega)
  exact lsOrW_slice m a hR l.toNat o us (by omega) hk

end lpok

/-! ## The `intern_*` refinements under `ArenaR` -/

/-- `intern_*` for `app` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "app"]
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
  exact ⟨hloc, hok, hR.lift_app _ _ _ _ hX (consInternM_frame appCS_wf hI)
    (AM.st_proto appLens _ _ _ _ _ _ a₀ (internE_app_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `sort` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "sort"]
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
  exact ⟨hloc, hok, hR.lift_sort _ _ _ _ ⟨hX, sointern_lp s.mem a₀ hR.sort u hu hR.sortLp
      (lvlHPW_ok s.mem a₀ hR u hu) _ _ hI⟩ (sointernW_frame _ _ _ _ hI)
    (AM.st_proto sortLens _ _ _ _ _ _ a₀ (internE_sort_run _ a₀) hok), hres⟩

/-- `intern_*` for `const` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "const"]
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
  exact ⟨hloc, hok, hR.lift_const _ _ _ _ ⟨hX, ceintern_lp s.mem a₀ hR.const f x hf hx hR.constLp
      (lsHPW_ok s.mem a₀ hR x hx) _ _ hI⟩ (ceinternW_frame _ _ _ _ _ hI)
    (AM.st_proto constLens _ _ _ _ _ _ a₀ (internE_const_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `letE` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "letE"]
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
  exact ⟨hloc, hok, hR.lift_letE _ _ _ _ hX (consInternM_frame letCS_wf hI)
    (AM.st_proto letLens _ _ _ _ _ _ a₀ (internE_let_run _ _ _ a₀) hok), hres⟩

/-- `intern_*` for `bvar` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "bvar"]
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
  exact ⟨hloc, hok, hR.lift_bvar _ _ _ _ hX (consInternM_frame bvarCS_wf hI)
    (AM.st_proto bvarLens _ _ _ _ _ _ a₀ (internE_bvar_run _ a₀) hok), hres⟩

/-- `intern_*` for `zero` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internLNode "zero"]
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
  have hL := zintern_hp s.mem a₀ hR.zero hR.zeroHp _ _ hI
  exact ⟨hloc, hok, hR.lift_zero _ _ _ _ ⟨hX, hL⟩ (consInternM_frame zeroCS_wf hI)
    (AM.st_proto zeroLens _ _ _ _ _ _ a₀ (internLNode_zero_run a₀) hok), hres⟩

/-- `intern_*` for `succ` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internLNode "succ"]
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
  exact ⟨hloc, hok, hR.lift_succ _ _ _ _ ⟨hX, sintern_hp s.mem a₀ hR.succ u hu hR.succHp
      (lvlHPW_ok s.mem a₀ hR u hu) _ _ hI⟩ (sinternW_frame _ _ _ _ hI)
    (AM.st_proto succLens _ _ _ _ _ _ a₀ (internLNode_succ_run _ a₀) hok), hres⟩

/-- `intern_*` for `max` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internLNode "max"]
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
  exact ⟨hloc, hok, hR.lift_max _ _ _ _ ⟨hX, mintern_hp s.mem a₀ hR.max u v hu hv hR.maxHp
      (lvlHPW_or s.mem a₀ hR u v hu hv) _ _ hI⟩ (minternW_frame _ _ _ _ _ hI)
    (AM.st_proto maxLens _ _ _ _ _ _ a₀ (internLNode_max_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `imax` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internLNode "imax"]
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
  exact ⟨hloc, hok, hR.lift_imax _ _ _ _ ⟨hX, imintern_hp s.mem a₀ hR.imax u v hu hv hR.imaxHp
      (lvlHPW_or s.mem a₀ hR u v hu hv) _ _ hI⟩ (iminternW_frame _ _ _ _ _ hI)
    (AM.st_proto imaxLens _ _ _ _ _ _ a₀ (internLNode_imax_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `param` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internLNode "param"]
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
  have hL := pintern_hp s.mem a₀ hR.param u hu hR.paramHp _ _ hI
  exact ⟨hloc, hok, hR.lift_param _ _ _ _ ⟨hX, hL⟩ (consInternM_frame paramCS_wf hI)
    (AM.st_proto paramLens _ _ _ _ _ _ a₀ (internLNode_param_run _ a₀) hok), hres⟩

/-- `intern_ls` refines `internLsNode` under `ArenaR`. -/
@[refines ConRon.Arena.internLsNode]
theorem internLs_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "ls_match" = some lsMatch)
    (hpf : p.lookup "ls_find" = some lsFind) (hpp : p.lookup "ls_push" = some lsPush)
    (hp : p.lookup "intern_ls" = some internLs)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : ArenaR s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (us : List LIdx)
    (hk : sliceL (vpool s₀.mem) o.toNat l.toNat = lsWords us) (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_ls" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLsNode us) a₀ ∧
      ArenaR s'.mem (AM.st (internLsNode us) a₀) ∧
      AM.res (internLsNode us) a₀ = decI (r.headD 0); ⊤⦄ := by
  have hps := hR.lit.1.2.2.1
  have htop := hR.lit.1.2.2.2.1
  have hq1 := hq.le
  have hspec := internLs_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := lsintern_correct s.mem a₀ hR.lit.1 hR.ls o l hq us hk hq0 _ _ hI
  exact ⟨hloc, hok, hR.lift_ls _ _ _ _ ⟨hX, lsintern_hp s.mem a₀ hR.lit.1 hR.ls o l hq us hk hq0 hR.lsHp
      (lsOrW_ok s.mem a₀ hR o l hq us hk) _ _ hI⟩ (lsinternW_frame _ _ _ _ _ hI)
    (AM.st_proto lsLens _ _ _ _ _ _ a₀ (internLsNode_run _ a₀) hok), hres⟩

/-- `intern_nstr` refines `internNNode (.str _ _)` under `ArenaR`. -/
@[refines_part ConRon.Arena.internNNode "str"]
theorem internNStr_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "nstr_match" = some nsMatch)
    (hpf : p.lookup "nstr_find" = some nsFind) (hpp : p.lookup "nstr_push" = some nsPush)
    (hp : p.lookup "intern_nstr" = some internNStr)
    (a₀ : AState) (n : Nat) (s₀ : St) (q o l : Word) (hR : ArenaR s₀.mem a₀)
    (hqw : q.toNat < 2 ^ 32) (hq : SliceOK s₀.mem o l) (s : String)
    (hk : sliceL (vpool s₀.mem) o.toNat l.toNat = strWords s) (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nstr" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internNNode (.str (decI q) s)) a₀ ∧
      ArenaR s'.mem (AM.st (internNNode (.str (decI q) s)) a₀) ∧
      AM.res (internNNode (.str (decI q) s)) a₀ = decI (r.headD 0); ⊤⦄ := by
  have hps := hR.lit.1.2.2.1
  have htop := hR.lit.1.2.2.2.1
  have hq1 := hq.le
  have hspec := internNStr_spec p hph hpe hpm hpf hpp hp n s₀ q o l (by omega)
    (by omega)
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := nsintern_correct s'.mem a₀ hR.lit.1 hR.nstr q o l hqw hq s hk hq0 _ _ hI
  exact ⟨hloc, hok, hR.lift_nstr _ _ _ _ hX (consInternM_frame nstrCS_wf hI)
    (AM.st_proto nstrLens _ _ _ _ _ _ a₀ (internNNode_str_run _ _ a₀) hok), hres⟩

/-- `intern_*` for name `anonymous` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internNNode "anon"]
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
  exact ⟨hloc, hok, hR.lift_nanon _ _ _ _ hX (consInternM_frame nanonCS_wf hI)
    (AM.st_proto nanonLens _ _ _ _ _ _ a₀ (internNNode_anon_run a₀) hok), hres⟩

/-- `intern_*` for name `num` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internNNode "num"]
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
  exact ⟨hloc, hok, hR.lift_nnum _ _ _ _ hX (consInternM_frame nnumCS_wf hI)
    (AM.st_proto nnumLens _ _ _ _ _ _ a₀ (internNNode_num_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `forallE` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "forallE"]
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
  exact ⟨hloc, hok, hR.lift_forallE _ _ _ _ hX (consInternM_frame forallCS_wf hI)
    (AM.st_proto forallLens _ _ _ _ _ _ a₀ (internE_forall_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `fvar` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "fvar"]
theorem internFVar_refinesA (p : Prog) (hpf : p.lookup "fvar_find" = some fvarFind)
    (hpp : p.lookup "fvar_push" = some fvarPush) (hp : p.lookup "intern_fvar" = some internFVar)
    (a₀ : AState) (n : Nat) (s₀ : St) (u ty : Word) (hR : ArenaR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hb : exprLPW s₀.mem ty = lpW (a₀.store.derived (decE ty))) :
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
  exact ⟨hloc, hok, hR.lift_fvar _ _ _ _ ⟨hX, fvintern_lp s.mem a₀ hR.fvar u ty hty hR.fvarLp hb _ _ hI⟩
      (fvinternW_frame _ _ _ _ _ hI)
    (AM.st_proto fvarLens _ _ _ _ _ _ a₀ (internE_fvar_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `lam` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "lam"]
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
  exact ⟨hloc, hok, hR.lift_lam _ _ _ _ hX (consInternM_frame lamCS_wf hI)
    (AM.st_proto lamLens _ _ _ _ _ _ a₀ (internE_lam_run _ _ a₀) hok), hres⟩

/-- `intern_*` for `proj` refines its arena interning under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "proj"]
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
  exact ⟨hloc, hok, hR.lift_proj _ _ _ _ hX (consInternM_frame projCS_wf hI)
    (AM.st_proto projLens _ _ _ _ _ _ a₀ (internE_proj_run _ _ _ a₀) hok), hres⟩

end L.Arena

/-! ## The pool and `nat_add_lit` under `ArenaR` -/

namespace L.Arena

/-- Appending to the pool is a frame of the pool and its top. -/
theorem grows_frame (m m' : Mem) (hg : Grows m m') : MemFrame [POOL, POOL1] [0] m m' := by
  have hf := hg.frame
  refine ⟨fun b hb' hc => ?_, fun x hx => ?_, fun b => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    rw [hf.arr b hb'.1 hb'.2, Mem.arr64_set64_ne _ _ _ _ _ hc]
  · rw [hf.ctl, rdW_set64]
    have : (0 : Word) ≠ x := fun h => hx (by simp [h])
    simp [this]
  · by_cases h : b = POOL
    · subst h; rw [hf.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · by_cases h1 : b = POOL1
      · subst h1; rw [hf.size1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      · rw [hf.arr b h h1, size_set64]
  · rw [hf.size, Mem.words_size_set64]

/-- **Appending to the pool keeps `ArenaR`**: the tables whose records point into the pool by
their own `grow` lemmas, the others by the frame. -/
theorem ArenaR.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hR : ArenaR m a) : ArenaR m' a := by
  have hf := grows_frame m m' hg
  arena_build hR, hf with
    first | exact LitR.grow m m' hg a hR.lit | exact LsR.grow m m' hg hR.lit.1 a hR.ls |
      exact NStrR.grow m m' hg hR.lit.1 a hR.nstr

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "lit"]
theorem internLit_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : ArenaR s₀.mem a₀) (hq : SliceOK s₀.mem o l)
    (hn : Norm (vpool s₀.mem) o.toNat l.toNat) (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄ := by
  have hps := hR.lit.1.2.2.1
  have htop := hR.lit.1.2.2.2.1
  have hq1 := hq.le
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := intern_correct s.mem a₀ hR.lit o l hq hn hq0 _ _ hI
  exact ⟨hloc, hok, hR.lift_lit _ _ _ _ hX (consInternM_frame litCS_wf hI)
    (AM.st_proto litLens _ _ _ _ _ _ a₀ (internE_lit_run _ a₀) hok), hres⟩

/-- `intern_lit_str` refines `internE (.lit (.strVal _))` under `ArenaR`. -/
@[refines_part ConRon.Arena.internE "lit"]
theorem internLitStr_refinesA (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match_str" = some litMatchStr)
    (hpf : p.lookup "lit_find_str" = some litFindStr) (hpp : p.lookup "lit_push_str" = some litPushStr)
    (hp : p.lookup "intern_lit_str" = some internLitStr)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : ArenaR s₀.mem a₀) (hq : SliceOK s₀.mem o l)
    (s : String) (hk : sliceL (vpool s₀.mem) o.toNat l.toNat = strWords s)
    (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit_str" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.strVal s))) a₀ ∧
      ArenaR s'.mem (AM.st (internE (.lit (.strVal s))) a₀) ∧
      AM.res (internE (.lit (.strVal s))) a₀ = decE (r.headD 0); ⊤⦄ := by
  have hps := hR.lit.1.2.2.1
  have htop := hR.lit.1.2.2.2.1
  have hq1 := hq.le
  have hspec := internLitStr_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hX, hres⟩ := internStr_correct s.mem a₀ hR.lit o l hq _ hk hq0 _ _ hI
  exact ⟨hloc, hok, hR.lift_lit _ _ _ _ hX (consInternM_frame litStrCS_wf hI)
    (AM.st_proto litLens _ _ _ _ _ _ a₀ (internE_lit_run _ a₀) hok), hres⟩

/-- **`nat_add_lit` refines `natOpResult`'s `Nat.add` arm under `ArenaR`**: the store's
`natAddLit_refines_store` with the whole arena relation in place of `LitR`. -/
@[refines_part ConRon.Arena.natOpResult "Nat.add"]
theorem natAddLit_refinesA (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke storeProg (exec storeProg n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ :=
  natAddLit_refines storeProg rfl rfl rfl rfl rfl ArenaR (fun _ _ h => h.lit.1)
    (fun m m' a hR hg => ArenaR.grow m m' hg a hR)
    (internLit_refinesA storeProg rfl rfl rfl rfl rfl rfl) n s₀ a₀ hR oa la ob lb ha hb hmode

end L.Arena
