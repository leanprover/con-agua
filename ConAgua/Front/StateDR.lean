import ConAgua.Front.ApplyDecl
import ConAgua.Arena.DerRel
import ConAgua.Arena.EnvRec
import ConAgua.Front.IndFields
import ConRon.Arena.Frontend.ExportC
import ConAgua.Census.Attr

/-!
# The parse state relation `StateDR`, and the refinement of the front functions

`StateDR m st`: the name, level and expression id tables of con-ron's `StateD`
(`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:99`) are the L tables `NID`, `LID`, `EID`
(`IdTable.lean`'s `TblR`: a dense array plus a sparse overflow, every handle word below `2^32`, as
the stores' refinements require); the declarations are `DECL`/`DLP` (`DeclsR`).

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

set_option linter.unusedSimpArgs false

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
  · simp only [Ne.symm hj, false_and, if_false]
    by_cases ht : j < min (t + 1) P.size
    · rw [if_pos ht, if_pos ht, h j (by omega) (by omega)]
    · rw [if_neg ht, if_neg ht]

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

/-- **The declarations** `ds` are the records of `D` (word `0` their number), their universe
parameters slices of `P` (word `0` its top). -/
structure DeclsR (D P : Array Word) (ds : Array IDeclaration) : Prop where
  dsize : D.size < 2 ^ 63
  psize : P.size < 2 ^ 63
  count : (D[0]?.getD 0).toNat = ds.size
  room : 1 + 8 * ds.size ≤ D.size
  ptop : (P[0]?.getD 0).toNat + 1 ≤ P.size
  recs : ∀ i (h : i < ds.size), DeclAt D P i ds[i]

/-- Record `i` represents the declaration, inductive blocks included (`IndDeclAt`): the
front's records. (`DeclAt` is the one-constant kinds, the records lane `decls`' loop reads so far,
`DeclsR`.) -/
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
macro "tapart" : tactic => `(tactic| simp [nanonSch, NAREC, NASLOT, zeroSch, ZREC, ZSLOT, nstrSch,
  NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC,
  ISLOT, paramSch, PREC, PSLOT, POOL, NID, LID, EID, lsSch, LSREC, LSSLOT, sortSch, SOREC, SOSLOT,
  constSch, CREC, CSLOT, bvarSch, BREC, BSLOT, litSch, REC, SLOT, appSch, AREC, ASLOT, lamSch, LAREC,
  LASLOT, forallSch, FAREC, FASLOT, letSch, LEREC, LESLOT, projSch, PJREC, PJSLOT, ADER, LADER, FADER,
  LEDER, PJDER, DECL, DLP])

/-- A store's arrays are outside the id tables' (`idArrs`), its `CTL` words outside `idCtl`
(concrete schemas). -/
macro "tctl" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) [nanonSch, NAREC, NASLOT, zeroSch, ZREC, ZSLOT, nstrSch,
  NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC,
  ISLOT, paramSch, PREC, PSLOT, POOL, lsSch, LSREC, LSSLOT, sortSch, SOREC, SOSLOT,
  constSch, CREC, CSLOT, bvarSch, BREC, BSLOT, litSch, REC, SLOT, appSch, AREC, ASLOT, lamSch, LAREC,
  LASLOT, forallSch, FAREC, FASLOT, letSch, LEREC, LESLOT, projSch, PJREC, PJSLOT, idArrs, idCtl,
  DECL, DLP]) <;> decide)

/-- `StateDR` reads only the id tables (arrays `64‥66`, `72‥74`, `CTL` words `64‥72`) and
`DECL`, `DLP`. -/
theorem StateDR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {st : StateD}
    (hf : MemFrame A C m m') (hn : NID ∉ A) (hl : LID ∉ A) (he : EID ∉ A := by tapart)
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
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42 ∨ 46 < b) (hD : DerR m a) : DerR m' a :=
  DerR.frameM A C m m' hf hA a hD

/-- A table write keeps `ArenaD`. -/
theorem ArenaD.putT (m m' : Mem) (a : AState) (hA : ArenaD m a) (b : ArrId) (hb : TblIx b)
    (i w : Word) (h : tblPutW m b i w = some m') : ArenaD m' a := by
  have hf := tblPutW_frame hb h
  exact ⟨ArenaR.frame_ext _ _ (by rcases hb with rfl | rfl | rfl <;> simp)
      (by rcases hb with rfl | rfl | rfl <;> simp [szC, spS]) m m' hf a hA.1,
    DerR.frameT hf (by rcases hb with rfl | rfl | rfl <;> simp) hA.2⟩

/-- Appending to the pool keeps `ArenaD`. -/
theorem ArenaD.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hA : ArenaD m a) : ArenaD m' a :=
  ⟨ArenaR.grow m m' hg a hA.1, DerR.frameT (grows_frame m m' hg) (by simp [POOL]) hA.2⟩

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
    MemFrame [nanonSch.ra, nanonSch.sa] [nanonSch.ca, nanonSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := naintern_correct m a hR.nanon _ _ hI
  rw [nainternW_eq] at hI
  have hf := internM_frame _ nanonSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto nanonLens _ _ _ _ _ _ a (internNNode_anon_run a) hok
  exact ⟨hok, ⟨hR.lift_nanon _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem zero_A (hI : zinternW m = some (w, m')) :
    AM.ok (internLNode .zero) a ∧ ArenaD m' (AM.st (internLNode .zero) a) ∧
    AM.res (internLNode .zero) a = decI w ∧
    MemFrame [zeroSch.ra, zeroSch.sa] [zeroSch.ca, zeroSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := zintern_correct m a hR.zero _ _ hI
  have hL := zintern_hp m a hR.zero hR.zeroHp _ _ hI
  rw [zinternW_eq] at hI
  have hf := internM_frame _ zeroSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok
  exact ⟨hok, ⟨hR.lift_zero _ _ _ _ ⟨hX, hL⟩ hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem nstr_A (q o l : Word) (hqw : q.toNat < 2 ^ 32) (hq : SliceOK m o l) (s : String)
    (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = strWords s) (hI : nsinternW m q o l = some (w, m')) :
    AM.ok (internNNode (.str (decI q) s)) a ∧ ArenaD m' (AM.st (internNNode (.str (decI q) s)) a) ∧
    AM.res (internNNode (.str (decI q) s)) a = decI w ∧
    MemFrame [nstrSch.ra, nstrSch.sa] [nstrSch.ca, nstrSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := nsintern_correct m a hR.lit.1 hR.nstr q o l hqw hq s hk _ _ hI
  rw [nsinternW_eq] at hI
  have hf := internM_frame _ nstrSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto nstrLens _ _ _ _ _ _ a (internNNode_str_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_nstr _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem nnum_A (q u : Word) (hqw : q.toNat < 2 ^ 32) (hI : nninternW m q u = some (w, m')) :
    AM.ok (internNNode (.num (decI q) u.toNat)) a ∧
    ArenaD m' (AM.st (internNNode (.num (decI q) u.toNat)) a) ∧
    AM.res (internNNode (.num (decI q) u.toNat)) a = decI w ∧
    MemFrame [nnumSch.ra, nnumSch.sa] [nnumSch.ca, nnumSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := nnintern_correct m a hR.nnum q u hqw _ _ hI
  rw [nninternW_eq] at hI
  have hf := internM_frame _ nnumSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto nnumLens _ _ _ _ _ _ a (internNNode_num_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_nnum _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem succ_A (u : Word) (hu : u.toNat < 2 ^ 32) (hI : sinternW m u = some (w, m')) :
    AM.ok (internLNode (.succ (decI u))) a ∧ ArenaD m' (AM.st (internLNode (.succ (decI u))) a) ∧
    AM.res (internLNode (.succ (decI u))) a = decI w ∧
    MemFrame [succSch.ra, succSch.sa, SHP] [succSch.ca, succSch.ca + 1] m m' := by
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
    MemFrame [maxSch.ra, maxSch.sa, MHP] [maxSch.ca, maxSch.ca + 1] m m' := by
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
    MemFrame [imaxSch.ra, imaxSch.sa, IHP] [imaxSch.ca, imaxSch.ca + 1] m m' := by
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
    MemFrame [paramSch.ra, paramSch.sa] [paramSch.ca, paramSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hR.param u hu _ _ hI
  have hL := pintern_hp m a hR.param u hu hR.paramHp _ _ hI
  rw [pinternW_eq] at hI
  have hf := internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ hI
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
    (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = strWords s)
    (h : applyNStrW m i pre o l = some m') :
    AM.ok (parseNameEntryD st i.toNat (.str pre.toNat s)) a ∧
    ArenaD m' (AM.st (parseNameEntryD st i.toNat (.str pre.toNat s)) a) ∧
    StateDR m' (AM.res (parseNameEntryD st i.toNat (.str pre.toNat s)) a) := by
  simp only [applyNStrW] at h
  split at h
  · rename_i hc
    obtain ⟨hok, hfr⟩ := hc
    obtain ⟨hget, hP⟩ := hD.names.read _ _ _ _ hok
    have hnone := hD.names.fresh _ _ _ _ hfr
    obtain ⟨w, m₁, hI, hw, hp⟩ := putK_eq h
    obtain ⟨hok', hR₁, hres, hf⟩ := nstr_A m a hR w m₁ _ o l hP hq s hk hI
    have hX : parseNameEntryD st i.toNat (.str pre.toNat s) =
        (internNNode (.str (decI (tblW m NID pre)) s) >>= fun h =>
          pure { st with names := st.names.insert i.toNat h }) := by
      simp [parseNameEntryD, StateD.name, hget, StateD.freshName, IdTable.bound_eq, hnone]
    obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
      (fun h => { st with names := st.names.insert i.toNat h }) a hok'
    rw [hX]
    refine ⟨hok₂, by rw [hst₂]; exact ArenaD.putT _ _ _ hR₁ NID (.inl rfl) _ _ hp, ?_⟩
    rw [hres₂, hres]
    exact hD.putName hf (by tapart) (by tapart) i w hp hw _
      (fun j => IdTable.get?_insert _ _ _ _) rfl rfl
  · simp at h

theorem applyNNumW_refines (i pre x : Word) (h : applyNNumW m i pre x = some m') :
    AM.ok (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a ∧
    ArenaD m' (AM.st (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a) ∧
    StateDR m' (AM.res (parseNameEntryD st i.toNat (.num pre.toNat x.toNat)) a) := by
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
    exact hD.putName hf (by tapart) (by tapart) i w hp hw _
      (fun j => IdTable.get?_insert _ _ _ _) rfl rfl
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

theorem levelRecW_succ (a c : Word) : levelRecW 1 a c = .succ a.toNat := rfl
theorem levelRecW_max (a c : Word) : levelRecW 2 a c = .max a.toNat c.toNat := rfl
theorem levelRecW_imax (a c : Word) : levelRecW 3 a c = .imax a.toNat c.toNat := rfl
theorem levelRecW_param (a c : Word) : levelRecW 4 a c = .param a.toNat := rfl

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
    (hs : ∀ x ∈ A, x ∉ idArrs := by tctl) (hc : ∀ x ∈ C, x ∉ idCtl := by tctl) :
    AM.ok (parseLevelEntryD st i.toNat r) a ∧
    ArenaD m₂ (AM.st (parseLevelEntryD st i.toNat r) a) ∧
    StateDR m₂ (AM.res (parseLevelEntryD st i.toNat r) a) := by
  obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
    (fun l => { st with levels := st.levels.insert i.toNat l }) a hok
  rw [hX]
  refine ⟨hok₂, by rw [hst₂]; exact ArenaD.putT _ _ _ hR₁ LID (.inr (.inl rfl)) _ _ hp, ?_⟩
  rw [hres₂, hres]
  exact hD.putLevel hf hn hl i w hp hw _ (fun j => IdTable.get?_insert _ _ _ _) rfl rfl he rfl hd hq
    hs hc

include hR hD in
theorem applyLevelW_refines (i k a' c : Word) (h : applyLevelW m i k a' c = some m') :
    AM.ok (parseLevelEntryD st i.toNat (levelRecW k a' c)) a ∧
    ArenaD m' (AM.st (parseLevelEntryD st i.toNat (levelRecW k a' c)) a) ∧
    StateDR m' (AM.res (parseLevelEntryD st i.toNat (levelRecW k a' c)) a) := by
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
        simp [parseLevelEntryD, levelRecW, k1, k2, StateD.level, hga, hgc, StateD.freshLevel,
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
        simp [parseLevelEntryD, levelRecW, k1, k2, k3, StateD.level, hga, hgc,
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
    (hk : sliceL (s₀.mem.arr64 POOL) o.toNat l.toNat = strWords s) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_nstr" [i, pre, o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (parseNameEntryD st i.toNat (.str pre.toNat s)) a₀ ∧
      ArenaD s'.mem (AM.st (parseNameEntryD st i.toNat (.str pre.toNat s)) a₀) ∧
      StateDR s'.mem (AM.res (parseNameEntryD st i.toNat (.str pre.toNat s)) a₀); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hR.1.lit.1
  have hspec := applyNStr_spec p hL hp n s₀ i pre o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, applyNStrW_refines _ _ _ _ hR hD i pre o l hq s hk hW⟩

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
  exact ⟨hloc, applyNNumW_refines _ _ _ _ hR hD i pre x hW⟩

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
  exact ⟨hloc, applyLevelW_refines _ _ _ _ hR hD i k a c hW⟩

end triples

/-! ## `str_put`: the copy loop's model -/

/-- Byte `k` of the input, as a word. -/
def inB (m : Mem) (k : Nat) : Word := ((m.arr8 IN)[k]?.getD 0).toUInt64

/-- **The copy loop** from `j` writes input byte `vs + (x - top)` to every pool word `x` in
`[top + j, top + n)` and changes nothing else. -/
theorem putW_facts (top vs n : Word) (hv : vs.toNat + n.toNat < 2 ^ 64) :
    ∀ (d : Nat) (m : Mem) (j : Word), n.toNat - j.toNat = d → j ≤ n →
      top.toNat + n.toNat ≤ (m.arr64 POOL).size → (m.arr64 POOL).size < 2 ^ 63 →
      Frame POOL m (putW m top vs n j) ∧
      ((putW m top vs n j).arr64 POOL).size = (m.arr64 POOL).size ∧
      ∀ x, ((putW m top vs n j).arr64 POOL)[x]? =
        if top.toNat + j.toNat ≤ x ∧ x < top.toNat + n.toNat then some (inB m (vs.toNat + (x - top.toNat)))
        else (m.arr64 POOL)[x]? := by
  intro d
  induction d with
  | zero =>
    intro m j hd hj _ _
    have hjn : ¬ j < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [putW_end _ _ _ _ _ hjn]
    refine ⟨Frame.refl _ _, rfl, fun x => ?_⟩
    have : ¬ (top.toNat + j.toNat ≤ x ∧ x < top.toNat + n.toNat) := by
      have := UInt64.le_iff_toNat_le.mp hj; omega
    simp [this]
  | succ d ih =>
    intro m j hd hj hp hs
    have hjn : j < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have htj : (top + j).toNat = top.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hvj : (vs + j).toNat = vs.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    rw [putW]; simp only [hjn, ↓reduceIte]
    have hsz : ((m.set64 POOL (top + j) (rdB (m.arr8 IN) (vs + j))).arr64 POOL).size = (m.arr64 POOL).size :=
      size_set64 _ _ _ _ _
    obtain ⟨hf, hsz', hx⟩ := ih (m.set64 POOL (top + j) (rdB (m.arr8 IN) (vs + j))) (j + 1) (by omega)
      (UInt64.le_iff_toNat_le.mpr (by omega)) (by omega) (by omega)
    refine ⟨Frame.trans _ _ _ _ (Frame.set64 _ _ _ _ _ (Frame.refl _ _)) hf, by omega, fun x => ?_⟩
    rw [hx, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have hb : (m.set64 POOL (top + j) (rdB (m.arr8 IN) (vs + j))).arr8 IN = m.arr8 IN := by simp [Mem.set64, Mem.arr8]
    simp only [inB, hb, htj, hj1]
    by_cases h1 : top.toNat + (j.toNat + 1) ≤ x ∧ x < top.toNat + n.toNat
    · have h2 : top.toNat + j.toNat ≠ x := by omega
      simp [h1, h2, show top.toNat + j.toNat ≤ x by omega]
    · by_cases h2 : top.toNat + j.toNat = x
      · subst h2
        simp [show top.toNat + j.toNat < (m.arr64 POOL).size by omega, rdB, hvj]
        intro h; omega
      · simp only [h1, ↓reduceIte, h2, false_and, ↓reduceIte]
        have : ¬ (top.toNat + j.toNat ≤ x ∧ x < top.toNat + n.toNat) := by omega
        simp [this]

/-- The input bytes `[vs, ve)` as words, one per byte. -/
def inWords (m : Mem) (vs ve : Nat) : List Word :=
  ((m.arr8 IN).extract vs ve).toList.map UInt8.toUInt64

/-- **`str_put`'s memory**: the pool grew by the input bytes `[vs, ve)`, at the old top. -/
theorem strPutW_facts (m : Mem) (vs ve : Word) (hpool : PoolOK m) (hok : strPutOK m vs ve) :
    Grows m ((putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))) ∧
    SliceOK ((putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))) m.top (ve - vs) ∧
    sliceL (((putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))).arr64 POOL)
      m.top.toNat (ve - vs).toNat = inWords m vs.toNat ve.toNat := by
  obtain ⟨hw, hc, hps, htop⟩ := hpool
  obtain ⟨h1, h2, h3, h4⟩ := hok
  have hle := UInt64.le_iff_toNat_le.mp h1
  have hn : (ve - vs).toNat = ve.toNat - vs.toNat := UInt64.toNat_sub_of_le _ _ h1
  have hin : ve.toNat ≤ (m.arr8 IN).size := by
    have := UInt64.le_iff_toNat_le.mp h2
    simp only [Mem.len8, UInt64.toNat_ofNat'] at this
    have := Nat.mod_le (m.arr8 IN).size (2 ^ 64); omega
  have hlen : (m.len64 POOL).toNat = (m.arr64 POOL).size := by
    simp only [Mem.len64]; exact toNat_ofNat_size _ hps
  have hroom : (ve - vs).toNat ≤ (m.arr64 POOL).size - m.top.toNat := by
    have := UInt64.le_iff_toNat_le.mp h4
    rwa [UInt64.toNat_sub_of_le _ _ h3, hlen] at this
  have hve := ve.toNat_lt
  obtain ⟨hf, hsz, hx⟩ := putW_facts m.top vs (ve - vs) (by omega) _ m 0 rfl
    (UInt64.le_iff_toNat_le.mpr (by simp)) (by omega) hps
  simp only [UInt64.toNat_zero, Nat.add_zero] at hx
  have hT : (m.top + (ve - vs)).toNat = m.top.toNat + (ve - vs).toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hctl : 0 < ((putW m m.top vs (ve - vs) 0).arr64 CTL).size := by
    rw [hf.2.2 CTL (by decide)]; exact hc
  have hpool' : ((putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))).arr64 POOL =
      (putW m m.top vs (ve - vs) 0).arr64 POOL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop' := Mem.top_set64 _ (m.top + (ve - vs)) hctl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [htop']; exact Frame.set64_both _ _ _ _ _ _ hf (by decide)
  · intro x hxt; rw [hpool', hx]; simp; omega
  · rw [htop', hT]; omega
  · rw [htop', hT, hpool', hsz]; omega
  · rw [hpool', hsz]
  · simp only [SliceOK, htop', hT]; omega
  · rw [hpool', sliceL, inWords, List.ext_getElem_iff]
    refine ⟨by simp; omega, fun k hk₁ hk₂ => ?_⟩
    simp only [List.length_ofFn] at hk₁
    simp only [List.getElem_ofFn, hx, List.getElem_map, Array.getElem_toList, Array.getElem_extract,
      inB]
    simp [show m.top.toNat + k < m.top.toNat + (ve - vs).toNat by omega,
      show vs.toNat + k < (m.arr8 IN).size by omega]

/-- **`str_put(vs, ve)`** copies the input bytes `[vs, ve)` to the pool top, one per word, and
returns the slice `(o, l)` = (old top, `ve - vs`): the pool grows (`Grows`), the slice is in use
(`SliceOK`) and holds the bytes; `ArenaD` and `StateDR` are carried. -/
theorem strPut_spec (p : Prog) (hp : p.lookup "str_put" = some strPut) (n : Nat) (s₀ : St)
    (a₀ : AState) (st : StateD) (hR : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem st) (vs ve : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_put" [vs, ve]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [s₀.mem.top, ve - vs] ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem s₀.mem.top (ve - vs) ∧
      sliceL (s'.mem.arr64 POOL) s₀.mem.top.toNat (ve - vs).toNat =
        ((s₀.mem.arr8 IN).extract vs.toNat ve.toNat).toList.map UInt8.toUInt64 ∧
      ArenaD s'.mem a₀ ∧ StateDR s'.mem st; ⊤⦄ := by
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hok, hr, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (strPut_specW p hp n s₀ vs ve)
  subst hs
  obtain ⟨hg, hsl, hk⟩ := strPutW_facts s'.mem vs ve hR.1.lit.1 hok
  rw [← hm] at hg hsl hk
  exact ⟨hloc, hr, hg, hsl, hk, ArenaD.grow _ _ hg _ hR,
    hD.frame (grows_frame _ _ hg) (by tapart) (by tapart)⟩

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

/-- The all-zero id tables, `DECL`, `DLP` represent the empty tables and no declaration. -/
theorem stateDR_initMem (sizes : List Nat) (hn : sizes[64]?.getD 0 < 2 ^ 63)
    (hl : sizes[65]?.getD 0 < 2 ^ 63) (he : sizes[66]?.getD 0 < 2 ^ 63)
    (hd : 1 ≤ sizes[67]?.getD 0 ∧ sizes[67]?.getD 0 < 2 ^ 63)
    (hq : 1 ≤ sizes[68]?.getD 0 ∧ sizes[68]?.getD 0 < 2 ^ 63) (hf : sizes[70]?.getD 0 < 2 ^ 62 ∧ sizes[71]?.getD 0 < 2 ^ 62)
    (hctl : 73 ≤ sizes[1]?.getD 0) :
    StateDR (initMem sizes) StateD.blank := by
  have hc : 73 ≤ ((initMem sizes).arr64 CTL).size := by rw [initMem_arr]; simpa using hctl
  have hT : ∀ (b : ArrId) {k : IdxKind}, TblIx b → sizes[b]?.getD 0 < 2 ^ 63 →
      TblR (initMem sizes) b ({} : IdTable (Idx k)) := fun b _ hb hs =>
    TblR.zero _ b hb (initMem_rd sizes) (by rw [initMem_arr]; simpa using hs) hc
  refine ⟨hT NID (.inl rfl) hn, hT LID (.inr (.inl rfl)) hl, hT EID (.inr (.inr rfl)) he, ?_, by
    rw [initMem_arr, initMem_arr]; simpa using hf⟩
  rw [initMem_arr, initMem_arr]
  refine ⟨by simpa using hd.2, by simpa using hq.2, ?_, ?_, ?_, fun i h => by
    simp [StateD.blank] at h⟩
  · rw [Array.getElem?_replicate]; split <;> simp [StateD.blank]
  · simpa [StateD.blank] using hd.1
  · have := hq.1; rw [Array.getElem?_replicate]; split <;> simp <;> omega

end L.Front
