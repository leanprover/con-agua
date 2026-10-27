import ConAgua.Front.ApplyDecl
import ConAgua.Arena.DerRel
import ConAgua.Arena.EnvRec
import ConAgua.Front.IndFields
import ConRon.Arena.Frontend.ExportC
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The parse state relation `StateDR`, and the refinement of the front functions

`StateDR m st`: the name, level and expression id tables of con-ron's `StateD`
(`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:99`) are the L tables `NID`, `LID`, `EID`
(`IdTable.lean`'s `TblR`: a dense array plus a sparse overflow, every handle word below `2^32`, as
the stores' refinements require); the declarations are `DECL`/`DLP` (`DeclsF`).

The theorems (`frontInit_refines`, `applyNStr_refines`, `applyNNum_refines`, `applyLevel_refines`)
are triples of the shape of `internNStr_refinesA` (`ArenaRel.lean`): from `ArenaR` and `StateDR`,
the twin's operation succeeds and both relations hold of the final memory and the twin's final
arena state / result. `strPut_spec`: the pool grows by the input bytes, both relations carried.

The L side is the model equation of each spec (`applyNStrW … = some m'`); the proofs here are by
hand: the model's cases, the store's `*intern_correct`, the frames.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend


namespace L.Front

instance : Inhabited StateD := ⟨{ names := {}, levels := {} }⟩

instance : Inhabited (StateD ⊕ RecordVerdict) := ⟨.inl default⟩

/-- The parse state before `StateD.init`: both tables empty. -/
def StateD.blank : StateD := { names := {}, levels := {} }

/-! ## The relation -/

/-! ### The declarations (`DECL`, `DLP`, `ApplyDecl.lean`) -/

/-- Word `k` of declaration record `i`. -/
def dw (D : Array Word) (i k : Nat) : Word := D[1 + 8 * i + k]?.getD 0

/-- The pool `P` up to its word `t`, with word `0` (the top) cleared: what an inductive block's
records may read (`IndDeclAt`), so that later appends above `t` and a moved top leave it alone. -/
def trunc (P : Array Word) (t : Nat) : Array Word := (P.extract 0 (t + 1)).set! 0 0

theorem trunc_congr (P P' : Array Word) (t : Nat) (hs : P'.size = P.size)
    (h : ∀ j, 0 < j → j ≤ t → P'[j]? = P[j]?) : trunc P' t = trunc P t := by
  apply Array.ext_getElem?
  intro j
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_extract,
    Array.size_extract, hs, Nat.sub_zero, Nat.zero_add]
  by_cases hj : j = 0
  · subst hj; simp
  · simp only [Ne.symm hj, ite_false]
    by_cases ht : j < min (t + 1) P.size
    · rw [ite_eq_left ht, ite_eq_left ht, h j (by omega) (by omega)]
    · rw [ite_eq_right ht, ite_eq_right ht]

/-- The constants of a slice of record pointers (lane `pinsenv`'s layout, `decCI`). -/
def decCIs (a : Array Word) (dn : NIdx → Option ConLeche.Name) (off cnt : Nat) :
    Option (List IConstantInfo) :=
  (List.range cnt).mapM fun j => do L.Arena.decCI a dn (← L.Arena.nat? a (off + j))

/-- **`DECL` record `i` is the inductive block `block` with `nP` parameters** (`IndApply.lean`):
kind `6`, its block a slice of the pool `P` (`DLP`) of pointers to `decCI` constant records in
`P`, all of it below some `t` at most `P`'s top. A block's constants carry no `PropWhen` names
(`sortZ := ifAllZero []`), so the name decoder is irrelevant (`fun _ => none`). -/
def IndDeclAt (D P : Array Word) (i : Nat) (block : List IConstantInfo) (nP : Nat) : Prop :=
  dw D i 0 = 6 ∧ (dw D i 4).toNat = nP ∧ ∃ t, t ≤ (P[0]?.getD 0).toNat ∧
    decCIs (trunc P t) (fun _ => none) (dw D i 2).toNat (dw D i 3).toNat = some block

/-- The hint of a definition record: kind `q` (`1` abbrev, `2` opaque, else regular), height `h`. -/
def hintW (q h : Word) : ConLeche.ReducibilityHint :=
  if q = 1 then .abbrev else if q = 2 then .opaque else .regular h.toNat

/-- The kind of a quotient record. -/
def quotW (q : Word) : ConLeche.QuotKind :=
  if q = 1 then .type else if q = 2 then .ctor else if q = 3 then .lift else .ind

/-- Record `i`'s common data: name, type, the universe parameters' slice of `P` (below its top). -/
def CVAt (D P : Array Word) (i : Nat) (cv : IConstantVal) : Prop :=
  decI (dw D i 1) = cv.name ∧ decI (dw D i 4) = cv.type ∧
    (dw D i 2).toNat + (dw D i 3).toNat ≤ (P[0]?.getD 0).toNat ∧
    (sliceL P (1 + (dw D i 2).toNat) (dw D i 3).toNat).map decI = cv.levelParams

/-- Record `i` represents the declaration. -/
def DeclAt (D P : Array Word) (i : Nat) : IDeclaration → Prop
  | .axiomDecl cv => dw D i 0 = 1 ∧ CVAt D P i cv
  | .defnDecl cv v h => dw D i 0 = 2 ∧ CVAt D P i cv ∧ decI (dw D i 5) = v ∧ hintW (dw D i 6) (dw D i 7) = h
  | .thmDecl cv v => dw D i 0 = 3 ∧ CVAt D P i cv ∧ decI (dw D i 5) = v
  | .opaqueDecl cv v => dw D i 0 = 4 ∧ CVAt D P i cv ∧ decI (dw D i 5) = v
  | .quotDecl k cv => dw D i 0 = 5 ∧ CVAt D P i cv ∧ quotW (dw D i 6) = k
  | _ => False

/-- Record `i` represents the declaration, inductive blocks included (`IndDeclAt`): the
front's records. (`DeclAt` is the one-constant kinds.) -/
def DeclAtF (D P : Array Word) (i : Nat) : IDeclaration → Prop
  | .indDecl b nP => IndDeclAt D P i b nP
  | d => DeclAt D P i d

/-- **The front's declarations** `ds` are the records of `D` (`DeclAtF`), the universe parameters
and inductive blocks' constants in `P`. -/
structure DeclsF (D P : Array Word) (ds : Array IDeclaration) : Prop where
  dsize : D.size < 2 ^ 63
  psize : P.size < 2 ^ 63
  count : (D[0]?.getD 0).toNat = ds.size
  room : 1 + 8 * ds.size ≤ D.size
  ptop : (P[0]?.getD 0).toNat + 1 ≤ P.size
  recs : ∀ i (h : i < ds.size), DeclAtF D P i ds[i]

/-- **The parse state relation**: `NID` represents the name table, `LID` the level table, `EID`
the expression table, `DECL`/`DLP` the declarations; the inductive lines' scratch arrays `IFR`,
`IFL` are below `2^63` words. -/
structure StateDR (m : Mem) (st : StateD) : Prop where
  names : TblR m NID st.names
  levels : TblR m LID st.levels
  exprs : TblR m EID st.exprs
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) st.decls
  ifs : (m.arr64 L.Front.Ind.IFR).size < 2 ^ 62 ∧ (m.arr64 L.Front.Ind.IFL).size < 2 ^ 62

theorem IdTable.get?_empty {α : Type} (i : Nat) : (({} : IdTable α)).get? i = none := by
  simp [IdTable.get?]

/-! ## Frames -/

/-- `NID`, `LID` are not among a store's arrays (concrete schemas, by their array ids). -/
macro "tapart" : tactic => `(tactic| simp [ConsSch.wset, nanonCS, nanonSch, NAREC, NASLOT, zeroCS, zeroSch, ZREC, ZSLOT, nstrCS, nstrSch,
  NSREC, NSSLOT, nnumCS, nnumSch, NNREC, NNSLOT, succCS, succSch, SREC, SSLOT, maxCS, maxSch, MREC, MSLOT, imaxCS, imaxSch, IREC,
  ISLOT, paramCS, paramSch, PREC, PSLOT, POOL, POOL1, NID, LID, EID, lsCS, lsSch, LSREC, LSSLOT, sortCS, sortSch, SOREC, SOSLOT,
  constCS, constSch, CREC, CSLOT, bvarCS, bvarSch, BREC, BSLOT, litCS, litStrCS, litCSk, litSch, REC, SLOT, appCS, appSch, AREC, ASLOT, lamCS, lamSch, LAREC,
  LASLOT, forallCS, forallSch, FAREC, FASLOT, letCS, letSch, LEREC, LESLOT, projCS, projSch, PJREC, PJSLOT, ADER, LADER, FADER,
  LEDER, PJDER, DECL, DLP, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP])

/-- A store's arrays are outside the id tables' (`idArrs`), its `CTL` words outside `idCtl`
(concrete schemas). -/
macro "tctl" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) [nanonSch, NAREC, NASLOT, zeroSch, ZREC, ZSLOT, nstrSch,
  NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC,
  ISLOT, paramSch, PREC, PSLOT, POOL, lsSch, LSREC, LSSLOT, sortSch, SOREC, SOSLOT,
  constSch, CREC, CSLOT, bvarSch, BREC, BSLOT, litSch, REC, SLOT, appSch, AREC, ASLOT, lamSch, LAREC,
  LASLOT, forallSch, FAREC, FASLOT, letSch, LEREC, LESLOT, projSch, PJREC, PJSLOT, idArrs, idCtl,
  DECL, DLP]) <;> decide)

/-- `0`, `1` (the pool top, the scratch flag) are not among a frame's `CTL` words. -/
macro "t01" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) [nanonSch, NAREC, NASLOT, zeroSch, ZREC, ZSLOT, nstrSch,
  NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC,
  ISLOT, paramSch, PREC, PSLOT, POOL, lsSch, LSREC, LSSLOT, sortSch, SOREC, SOSLOT,
  constSch, CREC, CSLOT, bvarSch, BREC, BSLOT, litSch, REC, SLOT, appSch, AREC, ASLOT, lamSch, LAREC,
  LASLOT, forallSch, FAREC, FASLOT, letSch, LEREC, LESLOT, projSch, PJREC, PJSLOT, idArrs, idCtl,
  DECL, DLP, szC, spS]) <;> decide)

/-- A frame that keeps `CTL[0]` (the top) and `CTL[1]` (the scratch flag) keeps the mode. -/
theorem MemFrame.modeOK {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (h0 : (0 : Word) ∉ C := by t01) (h1 : (1 : Word) ∉ C := by t01) (h : ModeOK m) : ModeOK m' := by
  have et : m'.top = m.top := hf.2.1 0 h0
  have ef : m'.flag = m.flag := hf.2.1 1 h1
  unfold ModeOK at h ⊢
  rw [et, ef]; exact h

/-- `StateDR` reads only the id tables (arrays `64‥66`, `72‥74`, `CTL` words `64‥72`) and
`DECL`, `DLP`. -/
theorem StateDR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {st : StateD}
    (hf : MemFrame A C m m') (_hn : NID ∉ A) (_hl : LID ∉ A) (_he : EID ∉ A := by tapart)
    (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart)
    (hs : ∀ x ∈ A, x ∉ idArrs := by tctl) (hc : ∀ x ∈ C, x ∉ idCtl := by tctl)
    (h : StateDR m st) : StateDR m' st :=
  ⟨h.names.frame hf (.inl rfl) hs hc, h.levels.frame hf (.inr (.inl rfl)) hs hc,
    h.exprs.frame hf (.inr (.inr rfl)) hs hc,
    by rw [hf.1 DECL hd (by decide), hf.1 DLP hq (by decide)]; exact h.decls,
    by rw [hf.2.2.1, hf.2.2.1]; exact h.ifs⟩

/-- `DerR` reads the arena state only through its two expression tiers. -/
theorem DerR.congrSt {m : Mem} {a a' : AState} (hp : a'.store.pers = a.store.pers)
    (hs : a'.store.scr = a.store.scr) (hD : DerR m a) : DerR m a' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hD
  constructor <;> simp only [DerT2, hp, hs] <;> assumption

/-- A memory frame that leaves the five derived arrays alone keeps `DerR`. -/
theorem DerR.frameT {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, (b < 42 ∨ 46 < b) ∧ (b < 298 ∨ 302 < b)) (hD : DerR m a) :
    DerR m' a :=
  DerR.frameM A C m m' hf hA a hD

/-- A table write keeps `ArenaD`. -/
theorem ArenaD.putT (m m' : Mem) (a : AState) (hA : ArenaD m a) (b : ArrId) (hb : TblIx b)
    (i w : Word) (h : tblPutW m b i w = some m') : ArenaD m' a := by
  have hf := tblPutW_frame hb h
  exact ⟨ArenaR.frame_ext _ _ (by rcases hb with rfl | rfl | rfl <;> simp)
      (by rcases hb with rfl | rfl | rfl <;> simp [szC, spS]) m m' hf a hA.1,
    DerR.frameT hf (by rcases hb with rfl | rfl | rfl <;> simp) hA.2⟩

/-- Appending to the pool keeps the mode (the flag stays, a tier-0 top stays in tier 0). -/
theorem ModeOK.growsF {m m' : Mem} (h : ModeOK m) (hg : Grows m m') : ModeOK m' := by
  have hf : m'.flag = m.flag := by rw [hg.frame.flag, Mem.flag_set64_top]
  have ht := hg.tier
  unfold ModeOK at h ⊢
  rw [hf]
  rcases h with h | h
  · exact .inl h
  · exact .inr (by omega)

/-- Appending to the pool keeps `ArenaD`. -/
theorem ArenaD.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hA : ArenaD m a) : ArenaD m' a :=
  ⟨ArenaR.grow m m' hg a hA.1, DerR.frameT (grows_frame m m' hg) (by simp [POOL, POOL1]) hA.2⟩

/-- Name id `i` bound to `w` after a frame: the name table with `i` bound to `w`. -/
theorem StateDR.putName {A : List ArrId} {C : List Word} {m m₁ m₂ : Mem} {st : StateD}
    (h : StateDR m st) (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (i w : Word)
    (hp : tblPutW m₁ NID i w = some m₂) (hw : w.toNat < 2 ^ 32) (st' : StateD)
    (hst : ∀ j, st'.names.get? j = if j = i.toNat then some (decI w) else st.names.get? j)
    (hlv : st'.levels = st.levels) (hex : st'.exprs = st.exprs) (he : EID ∉ A := by tapart)
    (hdc : st'.decls = st.decls := by rfl) (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart)
    (hs : ∀ x ∈ A, x ∉ idArrs := by tctl) (hc : ∀ x ∈ C, x ∉ idCtl := by tctl) :
    StateDR m₂ st' := by
  have h₁ := h.frame hf hn hl he hd hq hs hc
  have hfr := tblPutW_frame (.inl rfl) hp
  refine ⟨h₁.names.put (.inl rfl) i w hw hp hst, ?_, ?_, ?_,
    by rw [hfr.2.2.1, hfr.2.2.1]; exact h₁.ifs⟩
  · rw [hlv]; exact h₁.levels.frameD hfr (.inr (.inl rfl)) (by decide) (by decide) (by decide) (by decide)
  · rw [hex]; exact h₁.exprs.frameD hfr (.inr (.inr rfl)) (by decide) (by decide) (by decide) (by decide)
  · rw [hfr.1 DECL (by decide) (by decide), hfr.1 DLP (by decide) (by decide), hdc]
    exact h₁.decls

/-- Level id `i` bound to `w` after a frame: the level table with `i` bound to `w`. -/
theorem StateDR.putLevel {A : List ArrId} {C : List Word} {m m₁ m₂ : Mem} {st : StateD}
    (h : StateDR m st) (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (i w : Word)
    (hp : tblPutW m₁ LID i w = some m₂) (hw : w.toNat < 2 ^ 32) (st' : StateD)
    (hst : ∀ j, st'.levels.get? j = if j = i.toNat then some (decI w) else st.levels.get? j)
    (hnm : st'.names = st.names) (hex : st'.exprs = st.exprs) (he : EID ∉ A := by tapart)
    (hdc : st'.decls = st.decls := by rfl) (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart)
    (hs : ∀ x ∈ A, x ∉ idArrs := by tctl) (hc : ∀ x ∈ C, x ∉ idCtl := by tctl) :
    StateDR m₂ st' := by
  have h₁ := h.frame hf hn hl he hd hq hs hc
  have hfr := tblPutW_frame (.inr (.inl rfl)) hp
  refine ⟨?_, h₁.levels.put (.inr (.inl rfl)) i w hw hp hst, ?_, ?_,
    by rw [hfr.2.2.1, hfr.2.2.1]; exact h₁.ifs⟩
  · rw [hnm]; exact h₁.names.frameD hfr (.inl rfl) (by decide) (by decide) (by decide) (by decide)
  · rw [hex]; exact h₁.exprs.frameD hfr (.inr (.inr rfl)) (by decide) (by decide) (by decide) (by decide)
  · rw [hfr.1 DECL (by decide) (by decide), hfr.1 DLP (by decide) (by decide), hdc]
    exact h₁.decls

/-- Expression id `i` bound to `w` after a frame: the expression table with `i` bound to `w`. -/
theorem StateDR.putExpr {A : List ArrId} {C : List Word} {m m₁ m₂ : Mem} {st : StateD}
    (h : StateDR m st) (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (he : EID ∉ A)
    (i w : Word) (hp : tblPutW m₁ EID i w = some m₂) (hw : w.toNat < 2 ^ 32) (st' : StateD)
    (hst : ∀ j, st'.exprs.get? j = if j = i.toNat then some (decI w) else st.exprs.get? j)
    (hnm : st'.names = st.names) (hlv : st'.levels = st.levels)
    (hdc : st'.decls = st.decls := by rfl) (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart)
    (hs : ∀ x ∈ A, x ∉ idArrs := by tctl) (hc : ∀ x ∈ C, x ∉ idCtl := by tctl) :
    StateDR m₂ st' := by
  have h₁ := h.frame hf hn hl he hd hq hs hc
  have hfr := tblPutW_frame (.inr (.inr rfl)) hp
  refine ⟨?_, ?_, h₁.exprs.put (.inr (.inr rfl)) i w hw hp hst, ?_,
    by rw [hfr.2.2.1, hfr.2.2.1]; exact h₁.ifs⟩
  · rw [hnm]; exact h₁.names.frameD hfr (.inl rfl) (by decide) (by decide) (by decide) (by decide)
  · rw [hlv]; exact h₁.levels.frameD hfr (.inr (.inl rfl)) (by decide) (by decide) (by decide) (by decide)
  · rw [hfr.1 DECL (by decide) (by decide), hfr.1 DLP (by decide) (by decide), hdc]
    exact h₁.decls

/-! ## Each interning under `ArenaD`, with its memory frame -/

/-- An interning into a table outside the two expression tiers keeps `DerR`'s arena side. -/
theorem derR_lss {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (L : Lens α δ k)
    (hP : ∀ a t, (L.setP a t).store.pers = a.store.pers ∧ (L.setP a t).store.scr = a.store.scr)
    (hS : ∀ a t, (L.setS a t).store.pers = a.store.pers ∧ (L.setS a t).store.scr = a.store.scr)
    {a a' : AState} {m : Mem} (hst : a' = a ∨ (∃ t, a' = L.setP a t) ∨ ∃ t, a' = L.setS a t)
    (hD : DerR m a) : DerR m a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact hD
  · exact DerR.congrSt (hP a t).1 (hP a t).2 hD
  · exact DerR.congrSt (hS a t).1 (hS a t).2 hD

section interns
variable (m : Mem) (a : AState) (hA : ArenaD m a) (w : Word) (m' : Mem)
include hA

theorem nanon_A (hI : nainternW m = some (w, m')) :
    AM.ok (internNNode .anonymous) a ∧ ArenaD m' (AM.st (internNNode .anonymous) a) ∧
    AM.res (internNNode .anonymous) a = decI w ∧
    MemFrame [nanonSch.ra, tier1 nanonSch.ra, nanonSch.sa, tier1 nanonSch.sa] [nanonSch.ca, nanonSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := naintern_correct m a hR.nanon _ _ hI
  have hf := consInternM_frame nanonCS_wf hI
  have hst := AM.st_proto nanonLens _ _ _ _ _ _ a (internNNode_anon_run a) hok
  exact ⟨hok, ⟨hR.lift_nanon _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem zero_A (hI : zinternW m = some (w, m')) :
    AM.ok (internLNode .zero) a ∧ ArenaD m' (AM.st (internLNode .zero) a) ∧
    AM.res (internLNode .zero) a = decI w ∧
    MemFrame [zeroSch.ra, tier1 zeroSch.ra, zeroSch.sa, tier1 zeroSch.sa] [zeroSch.ca, zeroSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := zintern_correct m a hR.zero _ _ hI
  have hL := zintern_hp m a hR.zero hR.zeroHp _ _ hI
  have hf := consInternM_frame zeroCS_wf hI
  have hst := AM.st_proto zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok
  exact ⟨hok, ⟨hR.lift_zero _ _ _ _ ⟨hX, hL⟩ hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem nstr_A (q o l : Word) (hqw : q.toNat < 2 ^ 32) (hq : SliceOK m o l) (s : String)
    (hk : sliceL (vpool m) o.toNat l.toNat = strWords s) (hq0 : m.flag = 0 → o.toNat < 2 ^ 40) (hI : nsinternW m q o l = some (w, m')) :
    AM.ok (internNNode (.str (decI q) s)) a ∧ ArenaD m' (AM.st (internNNode (.str (decI q) s)) a) ∧
    AM.res (internNNode (.str (decI q) s)) a = decI w ∧
    MemFrame [nstrSch.ra, tier1 nstrSch.ra, nstrSch.sa, tier1 nstrSch.sa] [nstrSch.ca, nstrSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := nsintern_correct m a hR.lit.1 hR.nstr q o l hqw hq s hk hq0 _ _ hI
  have hf := consInternM_frame nstrCS_wf hI
  have hst := AM.st_proto nstrLens _ _ _ _ _ _ a (internNNode_str_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_nstr _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem nnum_A (q u : Word) (hqw : q.toNat < 2 ^ 32) (hI : nninternW m q u = some (w, m')) :
    AM.ok (internNNode (.num (decI q) u.toNat)) a ∧
    ArenaD m' (AM.st (internNNode (.num (decI q) u.toNat)) a) ∧
    AM.res (internNNode (.num (decI q) u.toNat)) a = decI w ∧
    MemFrame [nnumSch.ra, tier1 nnumSch.ra, nnumSch.sa, tier1 nnumSch.sa] [nnumSch.ca, nnumSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := nnintern_correct m a hR.nnum q u hqw _ _ hI
  have hf := consInternM_frame nnumCS_wf hI
  have hst := AM.st_proto nnumLens _ _ _ _ _ _ a (internNNode_num_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_nnum _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem succ_A (u : Word) (hu : u.toNat < 2 ^ 32) (hI : sinternW m u = some (w, m')) :
    AM.ok (internLNode (.succ (decI u))) a ∧ ArenaD m' (AM.st (internLNode (.succ (decI u))) a) ∧
    AM.res (internLNode (.succ (decI u))) a = decI w ∧
    MemFrame [succSch.ra, tier1 succSch.ra, succSch.sa, tier1 succSch.sa, SHP, tier1 SHP] [succSch.ca, succSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hR.succ u hu _ _ hI
  have hL := sintern_hp m a hR.succ u hu hR.succHp (lvlHPW_ok m a hR u hu) _ _ hI
  have hf := sinternW_frame m u _ _ hI
  have hst := AM.st_proto succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok
  exact ⟨hok, ⟨hR.lift_succ _ _ _ _ ⟨hX, hL⟩ hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem max_A (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hI : minternW m u v = some (w, m')) :
    AM.ok (internLNode (.max (decI u) (decI v))) a ∧
    ArenaD m' (AM.st (internLNode (.max (decI u) (decI v))) a) ∧
    AM.res (internLNode (.max (decI u) (decI v))) a = decI w ∧
    MemFrame [maxSch.ra, tier1 maxSch.ra, maxSch.sa, tier1 maxSch.sa, MHP, tier1 MHP] [maxSch.ca, maxSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := mintern_correct m a hR.max u v hu hv _ _ hI
  have hL := mintern_hp m a hR.max u v hu hv hR.maxHp (lvlHPW_or m a hR u v hu hv) _ _ hI
  have hf := minternW_frame m u v _ _ hI
  have hst := AM.st_proto maxLens _ _ _ _ _ _ a (internLNode_max_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_max _ _ _ _ ⟨hX, hL⟩ hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem imax_A (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hI : iminternW m u v = some (w, m')) :
    AM.ok (internLNode (.imax (decI u) (decI v))) a ∧
    ArenaD m' (AM.st (internLNode (.imax (decI u) (decI v))) a) ∧
    AM.res (internLNode (.imax (decI u) (decI v))) a = decI w ∧
    MemFrame [imaxSch.ra, tier1 imaxSch.ra, imaxSch.sa, tier1 imaxSch.sa, IHP, tier1 IHP] [imaxSch.ca, imaxSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := imintern_correct m a hR.imax u v hu hv _ _ hI
  have hL := imintern_hp m a hR.imax u v hu hv hR.imaxHp (lvlHPW_or m a hR u v hu hv) _ _ hI
  have hf := iminternW_frame m u v _ _ hI
  have hst := AM.st_proto imaxLens _ _ _ _ _ _ a (internLNode_imax_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_imax _ _ _ _ ⟨hX, hL⟩ hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem param_A (u : Word) (hu : u.toNat < 2 ^ 32) (hI : pinternW m u = some (w, m')) :
    AM.ok (internLNode (.param (decI u))) a ∧ ArenaD m' (AM.st (internLNode (.param (decI u))) a) ∧
    AM.res (internLNode (.param (decI u))) a = decI w ∧
    MemFrame [paramSch.ra, tier1 paramSch.ra, paramSch.sa, tier1 paramSch.sa] [paramSch.ca, paramSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hR.param u hu _ _ hI
  have hL := pintern_hp m a hR.param u hu hR.paramHp _ _ hI
  have hf := consInternM_frame paramCS_wf hI
  have hst := AM.st_proto paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok
  exact ⟨hok, ⟨hR.lift_param _ _ _ _ ⟨hX, hL⟩ hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

end interns

/-! ## The arena side -/

/-- An operation followed by a pure function of its result. -/
theorem AM.bind_pure {α β : Type} [Inhabited α] [Inhabited β] (x : AM α) (f : α → β) (a : AState)
    (h : AM.ok x a) :
    AM.ok (x >>= fun v => pure (f v)) a ∧ AM.st (x >>= fun v => pure (f v)) a = AM.st x a ∧
    AM.res (x >>= fun v => pure (f v)) a = f (AM.res x a) := by
  have hok : AM.ok (x >>= fun v => pure (f v)) a := by rw [AM.ok_bind]; exact ⟨h, trivial⟩
  exact ⟨hok, by rw [AM.st_bind _ _ _ hok]; rfl, by rw [AM.res_bind _ _ _ h]; rfl⟩

/-- The `none`-free part of a `putK`: what the L code wrote. -/
theorem putK_eq {b : ArrId} {i : Word} {x : Option (Word × Mem)} {m' : Mem}
    (h : putK b i x = some m') :
    ∃ w m₁, x = some (w, m₁) ∧ w.toNat < 2 ^ 32 ∧ tblPutW m₁ b i w = some m' := by
  match x, h with
  | some (w, m₁), h =>
    rw [putK_some] at h
    split at h
    · rename_i hc
      exact ⟨w, m₁, rfl, by simpa [UInt64.lt_iff_toNat_lt] using hc, h⟩
    · simp at h

/-! ## Name entries -/

section names
variable (m m' : Mem) (a : AState) (st : StateD) (hR : ArenaD m a) (hD : StateDR m st)
include hR hD

theorem applyNStrW_refines (i pre o l : Word) (hq : SliceOK m o l) (s : String)
    (hk : sliceL (vpool m) o.toNat l.toNat = strWords s) (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)
    (h : applyNStrW m i pre o l = some m') :
    AM.ok (parseNameEntryD st i.toNat (.str pre.toNat s)) a ∧
    ArenaD m' (AM.st (parseNameEntryD st i.toNat (.str pre.toNat s)) a) ∧
    StateDR m' (AM.res (parseNameEntryD st i.toNat (.str pre.toNat s)) a) ∧ (ModeOK m → ModeOK m') := by
  simp only [applyNStrW] at h
  split at h
  · rename_i hc
    obtain ⟨hok, hfr⟩ := hc
    obtain ⟨hget, hP⟩ := hD.names.read _ _ _ _ hok
    have hnone := hD.names.fresh _ _ _ _ hfr
    obtain ⟨w, m₁, hI, hw, hp⟩ := putK_eq h
    obtain ⟨hok', hR₁, hres, hf⟩ := nstr_A m a hR w m₁ _ o l hP hq s hk hq0 hI
    have hX : parseNameEntryD st i.toNat (.str pre.toNat s) =
        (internNNode (.str (decI (tblW m NID pre)) s) >>= fun h =>
          pure { st with names := st.names.insert i.toNat h }) := by
      simp [parseNameEntryD, StateD.name, hget, StateD.freshName, IdTable.bound_eq, hnone]
    obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
      (fun h => { st with names := st.names.insert i.toNat h }) a hok'
    rw [hX]
    refine ⟨hok₂, by rw [hst₂]; exact ArenaD.putT _ _ _ hR₁ NID (.inl rfl) _ _ hp, ?_⟩
    rw [hres₂, hres]
    exact ⟨hD.putName hf (by tapart) (by tapart) i w hp hw _
      (fun j => IdTable.get?_insert _ _ _ _) rfl rfl,
      fun hmo => MemFrame.modeOK (tblPutW_frame (.inl rfl) hp) (h := MemFrame.modeOK hf (h := hmo))⟩
  · simp at h

theorem applyNNumW_refines (i pre x : Word) (h : applyNNumW m i pre x = some m') :
    AM.ok (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a ∧
    ArenaD m' (AM.st (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a) ∧
    StateDR m' (AM.res (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a) ∧ (ModeOK m → ModeOK m') := by
  simp only [applyNNumW] at h
  split at h
  · rename_i hc
    obtain ⟨hok, hfr⟩ := hc
    obtain ⟨hget, hP⟩ := hD.names.read _ _ _ _ hok
    have hnone := hD.names.fresh _ _ _ _ hfr
    obtain ⟨w, m₁, hI, hw, hp⟩ := putK_eq h
    obtain ⟨hok', hR₁, hres, hf⟩ := nnum_A m a hR w m₁ _ x hP hI
    have hX : parseNameEntryD st i.toNat (.num pre.toNat x.toNat) =
        (internNNode (.num (decI (tblW m NID pre)) x.toNat) >>= fun h =>
          pure { st with names := st.names.insert i.toNat h }) := by
      simp [parseNameEntryD, StateD.name, hget, StateD.freshName, IdTable.bound_eq, hnone]
    obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
      (fun h => { st with names := st.names.insert i.toNat h }) a hok'
    rw [hX]
    refine ⟨hok₂, by rw [hst₂]; exact ArenaD.putT _ _ _ hR₁ NID (.inl rfl) _ _ hp, ?_⟩
    rw [hres₂, hres]
    exact ⟨hD.putName hf (by tapart) (by tapart) i w hp hw _
      (fun j => IdTable.get?_insert _ _ _ _) rfl rfl,
      fun hmo => MemFrame.modeOK (tblPutW_frame (.inl rfl) hp) (h := MemFrame.modeOK hf (h := hmo))⟩
  · simp at h

end names

/-! ## Level entries -/

/-- The level record of `apply_level`'s words: kind `k` (1 `succ`, 2 `max`, 3 `imax`, 4 `param`;
`apply_level` aborts on any other kind) and the ids `a`, `c`. -/
def levelRecW (k a c : Word) : LevelRec :=
  if k = 1 then .succ a.toNat
  else if k = 2 then .max a.toNat c.toNat
  else if k = 3 then .imax a.toNat c.toNat
  else .param a.toNat

section levels
variable (m m' : Mem) (a : AState) (st : StateD) (hR : ArenaD m a) (hD : StateDR m st)

include hD in
/-- The common end of a level entry: the interning `x` succeeded at `w` into `m₁`, `LID[i]` was
written. -/
theorem levelFinish {A : List ArrId} {C : List Word} (i w : Word) (r : LevelRec) (x : AM LIdx)
    (m₁ m₂ : Mem) (hX : parseLevelEntryD st i.toNat r =
      (x >>= fun l => pure { st with levels := st.levels.insert i.toNat l }))
    (hok : AM.ok x a) (hR₁ : ArenaD m₁ (AM.st x a)) (hres : AM.res x a = decI w)
    (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (he : EID ∉ A)
    (hp : tblPutW m₁ LID i w = some m₂)
    (hw : w.toNat < 2 ^ 32) (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart)
    (hs : ∀ x ∈ A, x ∉ idArrs := by tctl) (hc : ∀ x ∈ C, x ∉ idCtl := by tctl)
    (h0 : (0 : Word) ∉ C := by t01) (h1 : (1 : Word) ∉ C := by t01) :
    AM.ok (parseLevelEntryD st i.toNat r) a ∧
    ArenaD m₂ (AM.st (parseLevelEntryD st i.toNat r) a) ∧
    StateDR m₂ (AM.res (parseLevelEntryD st i.toNat r) a) ∧ (ModeOK m → ModeOK m₂) := by
  obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
    (fun l => { st with levels := st.levels.insert i.toNat l }) a hok
  rw [hX]
  refine ⟨hok₂, by rw [hst₂]; exact ArenaD.putT _ _ _ hR₁ LID (.inr (.inl rfl)) _ _ hp, ?_⟩
  rw [hres₂, hres]
  exact ⟨hD.putLevel hf hn hl i w hp hw _ (fun j => IdTable.get?_insert _ _ _ _) rfl rfl he rfl hd hq
    hs hc, fun hmo => MemFrame.modeOK (tblPutW_frame (.inr (.inl rfl)) hp) (h := MemFrame.modeOK hf h0 h1 hmo)⟩

include hR hD in
theorem applyLevelW_refines (i k a' c : Word) (h : applyLevelW m i k a' c = some m') :
    AM.ok (parseLevelEntryD st i.toNat (levelRecW k a' c)) a ∧
    ArenaD m' (AM.st (parseLevelEntryD st i.toNat (levelRecW k a' c)) a) ∧
    StateDR m' (AM.res (parseLevelEntryD st i.toNat (levelRecW k a' c)) a) ∧ (ModeOK m → ModeOK m') := by
  simp only [applyLevelW] at h
  split at h
  · rename_i hfr
    have hnone := hD.levels.fresh _ _ _ _ hfr
    obtain ⟨w, m₁, hI, hw, hp⟩ := putK_eq h
    simp only [levelW] at hI
    by_cases k1 : k = 1
    · rw [ite_eq_left k1] at hI
      split at hI
      · rename_i ha
        obtain ⟨hga, hPa⟩ := hD.levels.read _ _ _ _ ha
        obtain ⟨hok', hR₁, hres, hf⟩ := succ_A m a hR w m₁ _ hPa hI
        refine levelFinish _ _ _ hD i w _ _ m₁ _ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hp hw
        simp [parseLevelEntryD, levelRecW, k1, StateD.level, hga, StateD.freshLevel,
          IdTable.bound_eq, hnone]
      · simp at hI
    by_cases k2 : k = 2
    · rw [ite_eq_right k1, ite_eq_left k2] at hI
      split at hI
      · rename_i ha
        obtain ⟨hga, hPa⟩ := hD.levels.read _ _ _ _ ha.1
        obtain ⟨hgc, hPc⟩ := hD.levels.read _ _ _ _ ha.2
        obtain ⟨hok', hR₁, hres, hf⟩ := max_A m a hR w m₁ _ _ hPa hPc hI
        refine levelFinish _ _ _ hD i w _ _ m₁ _ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hp hw
        simp [parseLevelEntryD, levelRecW, k2, StateD.level, hga, hgc, StateD.freshLevel,
          IdTable.bound_eq, hnone]
      · simp at hI
    by_cases k3 : k = 3
    · rw [ite_eq_right k1, ite_eq_right k2, ite_eq_left k3] at hI
      split at hI
      · rename_i ha
        obtain ⟨hga, hPa⟩ := hD.levels.read _ _ _ _ ha.1
        obtain ⟨hgc, hPc⟩ := hD.levels.read _ _ _ _ ha.2
        obtain ⟨hok', hR₁, hres, hf⟩ := imax_A m a hR w m₁ _ _ hPa hPc hI
        refine levelFinish _ _ _ hD i w _ _ m₁ _ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hp hw
        simp [parseLevelEntryD, levelRecW, k3, StateD.level, hga, hgc,
          StateD.freshLevel, IdTable.bound_eq, hnone]
      · simp at hI
    by_cases k4 : k = 4
    · rw [ite_eq_right k1, ite_eq_right k2, ite_eq_right k3, ite_eq_left k4] at hI
      split at hI
      · rename_i ha
        obtain ⟨hga, hPa⟩ := hD.names.read _ _ _ _ ha
        obtain ⟨hok', hR₁, hres, hf⟩ := param_A m a hR w m₁ _ hPa hI
        refine levelFinish _ _ _ hD i w _ _ m₁ _ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hp hw
        simp [parseLevelEntryD, levelRecW, k1, k2, k3, StateD.name, hga, StateD.freshLevel,
          IdTable.bound_eq, hnone]
      · simp at hI
    · rw [ite_eq_right k1, ite_eq_right k2, ite_eq_right k3, ite_eq_right k4] at hI
      simp at hI
  · simp at h

end levels

/-! ## The name triples -/

section triples
variable (p : Prog) (hL : FrontLookups p) (a₀ : AState) (st : StateD) (n : Nat) (s₀ : St)
  (hR : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem st)

include hL hR hD in
/-- **`apply_nstr(i, pre, o, l)` refines `parseNameEntryD st i (.str pre s)`** under `ArenaD` and
`StateDR`, for the string `s` whose bytes the pool slice `(o, l)` holds. -/
@[refines_part ConRon.Arena.Frontend.parseNameEntryD "str"]
theorem applyNStr_refines (hp : p.lookup "apply_nstr" = some applyNStr) (i pre o l : Word)
    (hq : SliceOK s₀.mem o l) (s : String)
    (hk : sliceL (vpool s₀.mem) o.toNat l.toNat = strWords s)
    (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_nstr" [i, pre, o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (parseNameEntryD st i.toNat (.str pre.toNat s)) a₀ ∧
      ArenaD s'.mem (AM.st (parseNameEntryD st i.toNat (.str pre.toNat s)) a₀) ∧
      StateDR s'.mem (AM.res (parseNameEntryD st i.toNat (.str pre.toNat s)) a₀); ⊤⦄ := by
  have hps := hR.1.lit.1.2.2.1
  have htop := hR.1.lit.1.2.2.2.1
  have hspec := applyNStr_spec p hL hp n s₀ i pre o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨y1, y2, y3, -⟩ := applyNStrW_refines _ _ _ _ hR hD i pre o l hq s hk hq0 hW
  exact ⟨hloc, y1, y2, y3⟩

include hL hR hD in
/-- **`apply_nnum(i, pre, x)` refines `parseNameEntryD st i (.num pre x)`** under `ArenaD` and
`StateDR`. -/
@[refines_part ConRon.Arena.Frontend.parseNameEntryD "num"]
theorem applyNNum_refines (hp : p.lookup "apply_nnum" = some applyNNum) (i pre x : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_nnum" [i, pre, x]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a₀ ∧
      ArenaD s'.mem (AM.st (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a₀) ∧
      StateDR s'.mem (AM.res (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (applyNNum_spec p hL hp n s₀ i pre x)
  subst hs
  obtain ⟨y1, y2, y3, -⟩ := applyNNumW_refines _ _ _ _ hR hD i pre x hW
  exact ⟨hloc, y1, y2, y3⟩

include hL hR hD in
/-- **`apply_level(i, k, a, c)` refines `parseLevelEntryD st i (levelRecW k a c)`** under
`ArenaD` and `StateDR` (`levelRecW 1 a c = .succ a`, `2`: `.max a c`, `3`: `.imax a c`, `4`:
`.param a`; on another `k` the L code aborts). -/
@[refines ConRon.Arena.Frontend.parseLevelEntryD]
theorem applyLevel_refines (hp : p.lookup "apply_level" = some applyLevel) (i k a c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_level" [i, k, a, c]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (parseLevelEntryD st i.toNat (levelRecW k a c)) a₀ ∧
      ArenaD s'.mem (AM.st (parseLevelEntryD st i.toNat (levelRecW k a c)) a₀) ∧
      StateDR s'.mem (AM.res (parseLevelEntryD st i.toNat (levelRecW k a c)) a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (applyLevel_spec p hL hp n s₀ i k a c)
  subst hs
  obtain ⟨y1, y2, y3, -⟩ := applyLevelW_refines _ _ _ _ hR hD i k a c hW
  exact ⟨hloc, y1, y2, y3⟩

end triples

/-! ## `str_put`: the copy loop's model -/

/-! ## The initial state -/

section init
variable (m m' : Mem) (a : AState) (hR : ArenaD m a) (hD : StateDR m StateD.blank)

include hR hD in
theorem frontInitW_refines (h : frontInitW m = some m') :
    AM.ok StateD.init a ∧ ArenaD m' (AM.st StateD.init a) ∧ StateDR m' (AM.res StateD.init a) := by
  simp only [frontInitW] at h
  cases h1 : putK NID 0 (nainternW m) with
  | none => rw [h1] at h; simp [initK] at h
  | some m₂ =>
    rw [h1, initK_some] at h
    obtain ⟨w₁, m₁, hI1, hw1, hp1⟩ := putK_eq h1
    obtain ⟨w₂, m₃, hI2, hw2, hp2⟩ := putK_eq h
    obtain ⟨ok1, R1, res1, hf1⟩ := nanon_A m a hR w₁ m₁ hI1
    have R2 := ArenaD.putT _ _ _ R1 NID (.inl rfl) 0 w₁ hp1
    obtain ⟨ok2, R3, res2, hf2⟩ := zero_A _ _ R2 w₂ m₃ hI2
    have hX : StateD.init = (internNNode .anonymous >>= fun n0 => internLNode .zero >>= fun l0 =>
        pure ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD)) := rfl
    let n0 := AM.res (internNNode .anonymous) a
    obtain ⟨okI, stI, resI⟩ := AM.bind_pure (internLNode .zero)
      (fun l0 => ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD))
      (AM.st (internNNode .anonymous) a) ok2
    have okX : AM.ok StateD.init a := by rw [hX, AM.ok_bind]; exact ⟨ok1, okI⟩
    have D1 : StateDR m₂
        { names := IdTable.singleton (decI w₁), levels := {} } :=
      hD.putName hf1 (by tapart) (by tapart) 0 w₁ hp1 hw1 _
        (fun j => by simp [IdTable.get?_singleton, StateD.blank, IdTable.get?_empty]) rfl rfl
    refine ⟨okX, ?_, ?_⟩
    · rw [hX] at okX ⊢
      rw [AM.st_bind _ _ _ okX, stI]
      exact ArenaD.putT _ _ _ R3 LID (.inr (.inl rfl)) _ _ hp2
    · rw [hX, AM.res_bind _ _ _ ok1, resI, res2]
      simp only [n0, res1]
      exact D1.putLevel hf2 (by tapart) (by tapart) 0 w₂ hp2 hw2 _
        (fun j => by simp [IdTable.get?_singleton, IdTable.get?_empty]) rfl rfl

end init

/-- **`front_init()` refines `StateD.init`** under `ArenaD`, from a memory whose `NID`/`LID`
represent the empty tables (`StateDR m StateD.blank`: all zero, e.g. `initMem`,
`stateDR_initMem`). -/
@[refines ConRon.Arena.Frontend.StateD.init]
theorem frontInit_refines (p : Prog) (hL : FrontLookups p)
    (hp : p.lookup "front_init" = some frontInit) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem StateD.blank) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_init" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok StateD.init a₀ ∧ ArenaD s'.mem (AM.st StateD.init a₀) ∧
      StateDR s'.mem (AM.res StateD.init a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun (frontInit_spec p hL hp n s₀)
  subst hs
  exact ⟨hloc, frontInitW_refines _ _ _ hR hD hW⟩

end L.Front
