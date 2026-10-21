import ConAgua.Front.Apply
import ConAgua.Arena.DerRel
import ConRon.Arena.Frontend.ExportC

/-!
# The parse state relation `StateDR`, and the refinement of the front functions

`StateDR m st`: the name and level id tables of con-ron's `StateD`
(`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:99`) are the L arrays `NID` and `LID`
(`Apply.lean`): entry `i` decodes to `st.T.get? i` (`tblGet`: `none` past the end or at `0`, else
the handle `decI (entry - 1)`), every entry is at most `2^32` (so a stored handle word is below
`2^32`, as the stores' refinements require), the arrays have fewer than `2^63` words. The
expression table and the declarations are not represented (not mentioned).

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

/-- Entry `i` of a handle table, decoded: `none` past the end or where it is `0`, else the handle
`entry - 1`. -/
def tblGet {k : IdxKind} (arr : Array Word) (i : Nat) : Option (Idx k) :=
  match arr[i]? with
  | some e => if e = 0 then none else some (decI (e - 1))
  | none => none

/-- A handle table array represents an `IdTable`. -/
structure TblR {k : IdxKind} (arr : Array Word) (t : IdTable (Idx k)) : Prop where
  get : ∀ i, t.get? i = tblGet arr i
  bound : ∀ (i : Nat) (e : Word), arr[i]? = some e → e.toNat ≤ 2 ^ 32
  size : arr.size < 2 ^ 63

/-- **The parse state relation**: `NID` represents the name table, `LID` the level table, `EID`
the expression table. -/
structure StateDR (m : Mem) (st : StateD) : Prop where
  names : TblR (m.arr64 NID) st.names
  levels : TblR (m.arr64 LID) st.levels
  exprs : TblR (m.arr64 EID) st.exprs

/-! ## Reads and writes of a table -/


section tbl
variable {k : IdxKind} (m : Mem) (b : ArrId) (t : IdTable (Idx k))

theorem TblR.read (h : TblR (m.arr64 b) t) (i : Word) (hok : tblOK m b i = true) :
    t.get? i.toNat = some (decI (tblW m b i)) ∧ (tblW m b i).toNat < 2 ^ 32 := by
  have hs := h.size
  simp only [tblOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Mem.len64,
    UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat] at hok
  obtain ⟨hi, he⟩ := hok
  have hi' : i.toNat < (m.arr64 b).size := by rw [toNat_ofNat_size _ hs] at hi; exact hi
  have hr : rdW (m.arr64 b) i = (m.arr64 b)[i.toNat] := rdW_eq _ _ _ rfl hi'
  have hbd := h.bound i.toNat _ (Array.getElem?_eq_getElem hi')
  rw [← hr] at hbd
  have hne : (rdW (m.arr64 b) i).toNat ≠ 0 := fun h0 => he (UInt64.toNat_inj.mp (by simpa using h0))
  refine ⟨?_, ?_⟩
  · rw [h.get, tblGet, Array.getElem?_eq_getElem hi', ← hr]
    simp only [he, ↓reduceIte, tblW]
  · have h1 : (1 : Word) ≤ rdW (m.arr64 b) i := UInt64.le_iff_toNat_le.mpr (by simp; omega)
    simp only [tblW]
    rw [UInt64.toNat_sub_of_le _ _ h1]
    simp; omega

theorem TblR.fresh (h : TblR (m.arr64 b) t) (i : Word) (hf : tblFresh m b i = true) :
    t.get? i.toNat = none := by
  have hs := h.size
  simp only [tblFresh, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Mem.len64,
    UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat] at hf
  obtain ⟨hi, he⟩ := hf
  have hi' : i.toNat < (m.arr64 b).size := by rw [toNat_ofNat_size _ hs] at hi; exact hi
  have hr : rdW (m.arr64 b) i = (m.arr64 b)[i.toNat] := rdW_eq _ _ _ rfl hi'
  rw [h.get, tblGet, Array.getElem?_eq_getElem hi', ← hr]
  simp [he]

/-- Writing `w + 1` at entry `i` represents the table `t'` that is `t` with `i` bound to `w`. -/
theorem TblR.put (arr : Array Word) (h : TblR arr t) (i w : Word) (hi : i.toNat < arr.size)
    (hw : w.toNat < 2 ^ 32) (t' : IdTable (Idx k))
    (ht' : ∀ j, t'.get? j = if j = i.toNat then some (decI w) else t.get? j) :
    TblR (arr.set! i.toNat (w + 1)) t' := by
  have hw1 : (w + 1).toNat = w.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨fun j => ?_, fun j e he => ?_, by simpa using h.size⟩
  · rw [ht', tblGet, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hj : j = i.toNat
    · subst hj
      have hne : w + 1 ≠ 0 := fun h0 => by
        have := congrArg UInt64.toNat h0; rw [hw1] at this; simp at this
      simp [hi, hne]
    · simp only [hj, ↓reduceIte, Ne.symm hj, h.get, tblGet]
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at he
    by_cases hj : i.toNat = j
    · simp only [hj, ↓reduceIte] at he
      simp [← hj, hi] at he
      subst he; omega
    · simp only [hj, ↓reduceIte] at he
      exact h.bound j e he

end tbl

theorem IdTable.get?_empty {α : Type} (i : Nat) : (({} : IdTable α)).get? i = none := by
  simp [IdTable.get?]

/-! ## Frames -/

/-- `NID`, `LID` are not among a store's arrays (concrete schemas, by their array ids). -/
macro "tapart" : tactic => `(tactic| simp [nanonSch, NAREC, NASLOT, zeroSch, ZREC, ZSLOT, nstrSch,
  NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC,
  ISLOT, paramSch, PREC, PSLOT, POOL, NID, LID, EID, lsSch, LSREC, LSSLOT, sortSch, SOREC, SOSLOT,
  constSch, CREC, CSLOT, bvarSch, BREC, BSLOT, litSch, REC, SLOT, appSch, AREC, ASLOT, lamSch, LAREC,
  LASLOT, forallSch, FAREC, FASLOT, letSch, LEREC, LESLOT, projSch, PJREC, PJSLOT, ADER, LADER, FADER,
  LEDER, PJDER])

/-- `StateDR` reads only `NID`, `LID` and `EID`. -/
theorem StateDR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {st : StateD}
    (hf : MemFrame A C m m') (hn : NID ∉ A) (hl : LID ∉ A) (he : EID ∉ A := by tapart)
    (h : StateDR m st) : StateDR m' st :=
  ⟨by rw [hf.1 NID hn (by decide)]; exact h.names, by rw [hf.1 LID hl (by decide)]; exact h.levels,
    by rw [hf.1 EID he (by decide)]; exact h.exprs⟩

/-- `ArenaR` does not read `NID`, `LID` and `EID`. -/
theorem ArenaR.frameT (m m' : Mem) (a : AState) (hR : ArenaR m a) (hf : MemFrame [64, 65, 66] [] m m') :
    ArenaR m' a :=
  ArenaR.frame_ext [64, 65, 66] [] (by decide) (by simp) m m' hf a hR

/-- A write to `NID`, `LID` or `EID` keeps `ArenaR`. -/
theorem ArenaR.setT (m : Mem) (a : AState) (hR : ArenaR m a) (b : ArrId)
    (hb : b = NID ∨ b = LID ∨ b = EID) (i v : Word) : ArenaR (m.set64 b i v) a :=
  ArenaR.frameT _ _ _ hR ((MemFrame.set64 m b (by rcases hb with rfl | rfl | rfl <;> decide) i v).mono
    (by rcases hb with rfl | rfl | rfl <;> simp) (by simp))

/-- `DerR` reads the arena state only through its two expression tiers. -/
theorem DerR.congrSt {m : Mem} {a a' : AState} (hp : a'.store.pers = a.store.pers)
    (hs : a'.store.scr = a.store.scr) (hD : DerR m a) : DerR m a' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hD
  constructor <;> simp only [DerT2, hp, hs] <;> assumption

/-- A memory frame that leaves the five derived arrays alone keeps `DerR`. -/
theorem DerR.frameT {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42 ∨ 46 < b) (hD : DerR m a) : DerR m' a :=
  DerR.frameM A C m m' hf hA a hD

/-- A write to `NID`, `LID` or `EID` keeps `ArenaD`. -/
theorem ArenaD.setT (m : Mem) (a : AState) (hA : ArenaD m a) (b : ArrId)
    (hb : b = NID ∨ b = LID ∨ b = EID) (i v : Word) : ArenaD (m.set64 b i v) a :=
  ⟨ArenaR.setT m a hA.1 b hb i v,
    DerR.frameT (MemFrame.set64 m b (by rcases hb with rfl | rfl | rfl <;> decide) i v)
      (by rcases hb with rfl | rfl | rfl <;> simp <;> decide) hA.2⟩

/-- Appending to the pool keeps `ArenaD`. -/
theorem ArenaD.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hA : ArenaD m a) : ArenaD m' a :=
  ⟨ArenaR.grow m m' hg a hA.1, DerR.frameT (grows_frame m m' hg) (by simp [POOL]) hA.2⟩

/-- Entry `i` of `NID` written: the name table with `i` bound to `w`. -/
theorem StateDR.putName {A : List ArrId} {C : List Word} {m m₁ : Mem} {st : StateD}
    (h : StateDR m st) (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (i w : Word)
    (hi : i.toNat < (m₁.arr64 NID).size) (hw : w.toNat < 2 ^ 32) (st' : StateD)
    (hst : ∀ j, st'.names.get? j = if j = i.toNat then some (decI w) else st.names.get? j)
    (hlv : st'.levels = st.levels) (hex : st'.exprs = st.exprs) (he : EID ∉ A := by tapart) :
    StateDR (m₁.set64 NID i (w + 1)) st' := by
  have h₁ := h.frame hf hn hl he
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.arr64_set64_same]; exact TblR.put _ _ h₁.names i w hi hw _ hst
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hlv]; exact h₁.levels
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hex]; exact h₁.exprs

/-- Entry `i` of `LID` written: the level table with `i` bound to `w`. -/
theorem StateDR.putLevel {A : List ArrId} {C : List Word} {m m₁ : Mem} {st : StateD}
    (h : StateDR m st) (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (i w : Word)
    (hi : i.toNat < (m₁.arr64 LID).size) (hw : w.toNat < 2 ^ 32) (st' : StateD)
    (hst : ∀ j, st'.levels.get? j = if j = i.toNat then some (decI w) else st.levels.get? j)
    (hnm : st'.names = st.names) (hex : st'.exprs = st.exprs) (he : EID ∉ A := by tapart) :
    StateDR (m₁.set64 LID i (w + 1)) st' := by
  have h₁ := h.frame hf hn hl he
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hnm]; exact h₁.names
  · rw [Mem.arr64_set64_same]; exact TblR.put _ _ h₁.levels i w hi hw _ hst
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hex]; exact h₁.exprs

/-- Entry `i` of `EID` written: the expression table with `i` bound to `w`. -/
theorem StateDR.putExpr {A : List ArrId} {C : List Word} {m m₁ : Mem} {st : StateD}
    (h : StateDR m st) (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (he : EID ∉ A)
    (i w : Word) (hi : i.toNat < (m₁.arr64 EID).size) (hw : w.toNat < 2 ^ 32) (st' : StateD)
    (hst : ∀ j, st'.exprs.get? j = if j = i.toNat then some (decI w) else st.exprs.get? j)
    (hnm : st'.names = st.names) (hlv : st'.levels = st.levels) :
    StateDR (m₁.set64 EID i (w + 1)) st' := by
  have h₁ := h.frame hf hn hl he
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hnm]; exact h₁.names
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hlv]; exact h₁.levels
  · rw [Mem.arr64_set64_same]; exact TblR.put _ _ h₁.exprs i w hi hw _ hst

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
  rw [zinternW_eq] at hI
  have hf := internM_frame _ zeroSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok
  exact ⟨hok, ⟨hR.lift_zero _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
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
    MemFrame [succSch.ra, succSch.sa] [succSch.ca, succSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hR.succ u hu _ _ hI
  rw [sinternW_eq] at hI
  have hf := internM_frame _ succSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok
  exact ⟨hok, ⟨hR.lift_succ _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem max_A (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hI : minternW m u v = some (w, m')) :
    AM.ok (internLNode (.max (decI u) (decI v))) a ∧
    ArenaD m' (AM.st (internLNode (.max (decI u) (decI v))) a) ∧
    AM.res (internLNode (.max (decI u) (decI v))) a = decI w ∧
    MemFrame [maxSch.ra, maxSch.sa] [maxSch.ca, maxSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := mintern_correct m a hR.max u v hu hv _ _ hI
  rw [minternW_eq] at hI
  have hf := internM_frame _ maxSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto maxLens _ _ _ _ _ _ a (internLNode_max_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_max _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem imax_A (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hI : iminternW m u v = some (w, m')) :
    AM.ok (internLNode (.imax (decI u) (decI v))) a ∧
    ArenaD m' (AM.st (internLNode (.imax (decI u) (decI v))) a) ∧
    AM.res (internLNode (.imax (decI u) (decI v))) a = decI w ∧
    MemFrame [imaxSch.ra, imaxSch.sa] [imaxSch.ca, imaxSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := imintern_correct m a hR.imax u v hu hv _ _ hI
  rw [iiminternW_eq] at hI
  have hf := internM_frame _ iimaxSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto imaxLens _ _ _ _ _ _ a (internLNode_imax_run _ _ a) hok
  exact ⟨hok, ⟨hR.lift_imax _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
    (DerR.frameT hf (by tapart) hA.2)⟩, hres, hf⟩

theorem param_A (u : Word) (hu : u.toNat < 2 ^ 32) (hI : pinternW m u = some (w, m')) :
    AM.ok (internLNode (.param (decI u))) a ∧ ArenaD m' (AM.st (internLNode (.param (decI u))) a) ∧
    AM.res (internLNode (.param (decI u))) a = decI w ∧
    MemFrame [paramSch.ra, paramSch.sa] [paramSch.ca, paramSch.ca + 1] m m' := by
  have hR := hA.1
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hR.param u hu _ _ hI
  rw [pinternW_eq] at hI
  have hf := internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ hI
  have hst := AM.st_proto paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok
  exact ⟨hok, ⟨hR.lift_param _ _ _ _ hX hf hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hst
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
    ∃ w m₁, x = some (w, m₁) ∧ w.toNat < 2 ^ 32 ∧ i.toNat < (m₁.arr64 b).size ∧
      m' = m₁.set64 b i (w + 1) := by
  match x, h with
  | some (w, m₁), h =>
    rw [putK_some] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      exact ⟨w, m₁, rfl, by have := hc.1; simpa [UInt64.lt_iff_toNat_lt] using this, hc.2, h.symm⟩
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
    obtain ⟨w, m₁, hI, hw, hi, rfl⟩ := putK_eq h
    obtain ⟨hok', hR₁, hres, hf⟩ := nstr_A m a hR w m₁ _ o l hP hq s hk hI
    have hX : parseNameEntryD st i.toNat (.str pre.toNat s) =
        (internNNode (.str (decI (tblW m NID pre)) s) >>= fun h =>
          pure { st with names := st.names.insert i.toNat h }) := by
      simp [parseNameEntryD, StateD.name, hget, StateD.freshName, IdTable.bound_eq, hnone]
    obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
      (fun h => { st with names := st.names.insert i.toNat h }) a hok'
    rw [hX]
    refine ⟨hok₂, by rw [hst₂]; exact ArenaD.setT _ _ hR₁ _ (.inl rfl) _ _, ?_⟩
    rw [hres₂, hres]
    exact hD.putName hf (by tapart) (by tapart) i w hi hw _
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
    obtain ⟨w, m₁, hI, hw, hi, rfl⟩ := putK_eq h
    obtain ⟨hok', hR₁, hres, hf⟩ := nnum_A m a hR w m₁ _ x hP hI
    have hX : parseNameEntryD st i.toNat (.num pre.toNat x.toNat) =
        (internNNode (.num (decI (tblW m NID pre)) x.toNat) >>= fun h =>
          pure { st with names := st.names.insert i.toNat h }) := by
      simp [parseNameEntryD, StateD.name, hget, StateD.freshName, IdTable.bound_eq, hnone]
    obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
      (fun h => { st with names := st.names.insert i.toNat h }) a hok'
    rw [hX]
    refine ⟨hok₂, by rw [hst₂]; exact ArenaD.setT _ _ hR₁ _ (.inl rfl) _ _, ?_⟩
    rw [hres₂, hres]
    exact hD.putName hf (by tapart) (by tapart) i w hi hw _
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
    (m₁ : Mem) (hX : parseLevelEntryD st i.toNat r =
      (x >>= fun l => pure { st with levels := st.levels.insert i.toNat l }))
    (hok : AM.ok x a) (hR₁ : ArenaD m₁ (AM.st x a)) (hres : AM.res x a = decI w)
    (hf : MemFrame A C m m₁) (hn : NID ∉ A) (hl : LID ∉ A) (he : EID ∉ A)
    (hi : i.toNat < (m₁.arr64 LID).size)
    (hw : w.toNat < 2 ^ 32) :
    AM.ok (parseLevelEntryD st i.toNat r) a ∧
    ArenaD (m₁.set64 LID i (w + 1)) (AM.st (parseLevelEntryD st i.toNat r) a) ∧
    StateDR (m₁.set64 LID i (w + 1)) (AM.res (parseLevelEntryD st i.toNat r) a) := by
  obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
    (fun l => { st with levels := st.levels.insert i.toNat l }) a hok
  rw [hX]
  refine ⟨hok₂, by rw [hst₂]; exact ArenaD.setT _ _ hR₁ _ (.inr (.inl rfl)) _ _, ?_⟩
  rw [hres₂, hres]
  exact hD.putLevel hf hn hl i w hi hw _ (fun j => IdTable.get?_insert _ _ _ _) rfl rfl he

include hR hD in
theorem applyLevelW_refines (i k a' c : Word) (h : applyLevelW m i k a' c = some m') :
    AM.ok (parseLevelEntryD st i.toNat (levelRecW k a' c)) a ∧
    ArenaD m' (AM.st (parseLevelEntryD st i.toNat (levelRecW k a' c)) a) ∧
    StateDR m' (AM.res (parseLevelEntryD st i.toNat (levelRecW k a' c)) a) := by
  simp only [applyLevelW] at h
  split at h
  · rename_i hfr
    have hnone := hD.levels.fresh _ _ _ _ hfr
    obtain ⟨w, m₁, hI, hw, hi, rfl⟩ := putK_eq h
    simp only [levelW] at hI
    by_cases k1 : k = 1
    · rw [ite_eq_left k1] at hI
      split at hI
      · rename_i ha
        obtain ⟨hga, hPa⟩ := hD.levels.read _ _ _ _ ha
        obtain ⟨hok', hR₁, hres, hf⟩ := succ_A m a hR w m₁ _ hPa hI
        refine levelFinish _ _ _ hD i w _ _ m₁ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hi hw
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
        refine levelFinish _ _ _ hD i w _ _ m₁ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hi hw
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
        refine levelFinish _ _ _ hD i w _ _ m₁ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hi hw
        simp [parseLevelEntryD, levelRecW, k1, k2, k3, StateD.level, hga, hgc,
          StateD.freshLevel, IdTable.bound_eq, hnone]
      · simp at hI
    by_cases k4 : k = 4
    · rw [ite_eq_right k1, ite_eq_right k2, ite_eq_right k3, ite_eq_left k4] at hI
      split at hI
      · rename_i ha
        obtain ⟨hga, hPa⟩ := hD.names.read _ _ _ _ ha
        obtain ⟨hok', hR₁, hres, hf⟩ := param_A m a hR w m₁ _ hPa hI
        refine levelFinish _ _ _ hD i w _ _ m₁ ?_ hok' hR₁ hres hf (by tapart) (by tapart) (by tapart) hi hw
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
    obtain ⟨w₁, m₁, hI1, hw1, hi1, rfl⟩ := putK_eq h1
    obtain ⟨w₂, m₃, hI2, hw2, hi2, rfl⟩ := putK_eq h
    obtain ⟨ok1, R1, res1, hf1⟩ := nanon_A m a hR w₁ m₁ hI1
    have R2 := ArenaD.setT _ _ R1 NID (.inl rfl) 0 (w₁ + 1)
    obtain ⟨ok2, R3, res2, hf2⟩ := zero_A _ _ R2 w₂ m₃ hI2
    have hX : StateD.init = (internNNode .anonymous >>= fun n0 => internLNode .zero >>= fun l0 =>
        pure ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD)) := rfl
    let n0 := AM.res (internNNode .anonymous) a
    obtain ⟨okI, stI, resI⟩ := AM.bind_pure (internLNode .zero)
      (fun l0 => ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD))
      (AM.st (internNNode .anonymous) a) ok2
    have okX : AM.ok StateD.init a := by rw [hX, AM.ok_bind]; exact ⟨ok1, okI⟩
    have D1 : StateDR (m₁.set64 NID 0 (w₁ + 1))
        { names := IdTable.singleton (decI w₁), levels := {} } :=
      hD.putName hf1 (by tapart) (by tapart) 0 w₁ hi1 hw1 _
        (fun j => by simp [IdTable.get?_singleton, StateD.blank, IdTable.get?_empty]) rfl rfl
    refine ⟨okX, ?_, ?_⟩
    · rw [hX] at okX ⊢
      rw [AM.st_bind _ _ _ okX, stI]
      exact ArenaD.setT _ _ R3 LID (.inr (.inl rfl)) _ _
    · rw [hX, AM.res_bind _ _ _ ok1, resI, res2]
      simp only [n0, res1]
      exact D1.putLevel hf2 (by tapart) (by tapart) 0 w₂ hi2 hw2 _
        (fun j => by simp [IdTable.get?_singleton, IdTable.get?_empty]) rfl rfl

end init

/-- **`front_init()` refines `StateD.init`** under `ArenaD`, from a memory whose `NID`/`LID`
represent the empty tables (`StateDR m StateD.blank`: all zero, e.g. `initMem`,
`stateDR_initMem`). -/
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

/-- The all-zero `NID`/`LID`/`EID` represent the empty tables. -/
theorem stateDR_initMem (sizes : List Nat) (hn : sizes[64]?.getD 0 < 2 ^ 63)
    (hl : sizes[65]?.getD 0 < 2 ^ 63) (he : sizes[66]?.getD 0 < 2 ^ 63) : StateDR (initMem sizes) StateD.blank := by
  have hT : ∀ (b : ArrId) {k : IdxKind}, sizes[b]?.getD 0 < 2 ^ 63 →
      TblR ((initMem sizes).arr64 b) ({} : IdTable (Idx k)) := by
    intro b k hb
    rw [initMem_arr]
    refine ⟨fun i => ?_, fun i e he => ?_, by simpa using hb⟩
    · rw [IdTable.get?_empty, tblGet, Array.getElem?_replicate]
      by_cases h : i < sizes[b]?.getD 0 <;> simp [h]
    · rw [Array.getElem?_replicate] at he
      split at he <;> simp at he; subst he; simp
  exact ⟨hT NID hn, hT LID hl, hT EID he⟩

end L.Front
