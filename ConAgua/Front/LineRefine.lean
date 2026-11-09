module

public import ConAgua.Front.Line
public import ConAgua.Front.UnescapeLink
public import ConAgua.Front.StateDR
public import ConLeche.Frontend.ExportC
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Scan.LineLink

@[expose] public section

/-!
# The pieces of con-ron's per-line step

`LineStep`: con-leche's scanner reads a record `r` at `i` with `next` the position after it
(`scanLineFwd`), and con-ron's `applyRecord st r` succeeds from the arena state `a₀` with a parse
state `st'` such that the memory after is related to its arena state by `ArenaD` and to `st'` by
`StateDR`. A name or level line's fields applied are that step (`lineRecW_refines`); the
expression and declaration lines' are `ApplyExprRefine.lean`'s and `ApplyDLineRef.lean`'s.
`front_line`'s refinement is `frontLine_ref` (`LineRef.lean`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open ConLeche.Frontend hiding StateD RecordVerdict applyLine
open ConAgua.Scan ConAgua.Scan.RecordsLink ConAgua.Scan.LineLink
open ConAgua.Front.FieldsLink
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- **One line, as con-ron applies it**: the scanner reads the record `r` at `i` and the next
position `q` (the word `nx`), `r` stands where it may (`lineRecPlaced first`), `applyRecord st r`
succeeds from `a₀` with the parse state `st'`, and the memory `m` is related to the arena state
after by `ArenaD` and to `st'` by `StateDR`. -/
def LineStep (b : ByteArray) (i : USize) (first : Bool) (nx : Word) (st : StateD) (a₀ : AState)
    (m : Mem) : Prop :=
  ∃ r q st', scanLineFwd b i = .ok r q ∧ q.toUInt64 = nx ∧ lineRecPlaced first r = true ∧
    AM.ok (applyRecord st r) a₀ ∧
    AM.res (applyRecord st r) a₀ = .inl st' ∧ ArenaD m (AM.st (applyRecord st r) a₀) ∧ StateDR m st'

/-- The pure arena steps of `applyLine`. -/
theorem applyLine_pure (st : StateD) (a₀ : AState) (r : LineRec)
    (hr : r = .header ∨ r = .blank) :
    AM.ok (applyRecord st r) a₀ ∧ AM.res (applyRecord st r) a₀ = .inl st ∧
      AM.st (applyRecord st r) a₀ = a₀ := by
  rcases hr with rfl | rfl <;> exact ⟨trivial, rfl, rfl⟩

theorem applyLine_name (st : StateD) (a₀ : AState) (i : Nat) (r : NameRec)
    (h : AM.ok (parseNameEntryD st i r) a₀) :
    AM.ok (applyRecord st (.name i r)) a₀ ∧
      AM.res (applyRecord st (.name i r) : AM (StateD ⊕ RecordVerdict)) a₀ = .inl (AM.res (parseNameEntryD st i r) a₀) ∧
      AM.st (applyRecord st (.name i r)) a₀ = AM.st (parseNameEntryD st i r) a₀ := by
  obtain ⟨h1, h2, h3⟩ := AM.bind_pure (parseNameEntryD st i r) (Sum.inl : StateD → StateD ⊕ RecordVerdict) a₀ h
  exact ⟨h1, h3, h2⟩

theorem applyLine_level (st : StateD) (a₀ : AState) (i : Nat) (r : LevelRec)
    (h : AM.ok (parseLevelEntryD st i r) a₀) :
    AM.ok (applyRecord st (.level i r)) a₀ ∧
      AM.res (applyRecord st (.level i r) : AM (StateD ⊕ RecordVerdict)) a₀ = .inl (AM.res (parseLevelEntryD st i r) a₀) ∧
      AM.st (applyRecord st (.level i r)) a₀ = AM.st (parseLevelEntryD st i r) a₀ := by
  obtain ⟨h1, h2, h3⟩ := AM.bind_pure (parseLevelEntryD st i r) (Sum.inl : StateD → StateD ⊕ RecordVerdict) a₀ h
  exact ⟨h1, h3, h2⟩

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A name or level line: the fields `f` against the record `r`, applied. -/
theorem lineRecW_refines (m m' : Mem) (_hm : m.arr8 IN = b.data) (a₀ : AState) (st : StateD)
    (hR : ArenaD m a₀) (hD : StateDR m st) (hmode : ModeOK m) (f : Fld) (r : LineRec)
    (hRec : f.pl ≠ 0 → RecR b r f) (h : lineRecW b.data m f.pl f.idx f.a f.c f.d = some m') :
    ∃ st', AM.ok (applyRecord st r) a₀ ∧ AM.res (applyRecord st r) a₀ = .inl st' ∧
      ArenaD m' (AM.st (applyRecord st r) a₀) ∧ StateDR m' st' ∧ ModeOK m' := by
  unfold lineRecW at h
  split at h
  · cases h
  rename_i hpl0
  have hRR := hRec hpl0
  split at h
  · -- the header
    rename_i hpl7
    simp only [Option.some.injEq] at h
    subst h
    have hr : r = .header := by
      rcases r with ⟨_, _ | _⟩ | ⟨_, _ | _ | _ | _⟩ | _ | _ | _ | _ <;>
        simp_all [RecR, PlR, NameR]
    obtain ⟨h1, h2, h3⟩ := applyLine_pure st a₀ r (.inl hr)
    exact ⟨st, h1, h2, by rw [h3]; exact hR, hD, hmode⟩
  rename_i hpl7
  split at h
  · cases h
  rename_i hnone
  simp only [not_or] at hnone
  obtain ⟨hidx, ha⟩ := hnone
  split at h
  · -- a `str` name
    rename_i hpl1
    unfold applyStrW at h
    split at h
    · cases h
    rename_i hc0
    cases hP : L.Front.Unescape.strPutEscW b.data m f.c f.d with
    | none => rw [hP, strK_none] at h; cases h
    | some q =>
    obtain ⟨l, m₁⟩ := q
    rw [hP] at h
    replace h := strK_intern h
    rcases r with ⟨I, (⟨P, S⟩ | ⟨P, N⟩)⟩ | ⟨_, (_ | ⟨_, _⟩ | ⟨_, _⟩ | _)⟩ | _ | _ | _ | _ <;>
      simp only [RecR, PlR, NameR] at hRR
    · obtain ⟨hI, -, hP', hS⟩ := hRR
      obtain ⟨hg, hq, hk⟩ := ConAgua.Front.UnescapeLink.strPutEsc_link h64 b hsize m m₁ hR.base.lit.1 f.c f.d S
        (hS hc0) l hP
      have hmo₁ := ModeOK.growsF hmode hg
      obtain ⟨hok', hR', hD', hM'⟩ := applyNStrW_refines m₁ m' a₀ st
        (ArenaD.grow _ _ hg _ hR) (hD.frame (grows_frame _ _ hg) (by tapart) (by tapart))
        f.idx f.a m.top l hq S hk (ModeOK.slice0 hmo₁ hq) h
      rw [hI hidx, hP' ha] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_name st a₀ I (.str P S) hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmo₁⟩
    all_goals simp_all
  rename_i hpl1
  split at h
  · cases h
  rename_i hcn
  split at h
  · -- a `num` name
    rename_i hpl2
    have hc : f.c ≠ NONE := fun h' => hcn ⟨h', .inl hpl2⟩
    rcases r with ⟨I, (⟨P, S⟩ | ⟨P, N⟩)⟩ | ⟨_, (_ | ⟨_, _⟩ | ⟨_, _⟩ | _)⟩ | _ | _ | _ | _ <;>
      simp only [RecR, PlR, NameR] at hRR
    · exact absurd (hRR.2.1.symm.trans hpl2) (by decide)
    · obtain ⟨hI, -, hP, hN⟩ := hRR
      obtain ⟨hok', hR', hD', hM'⟩ := applyNNumW_refines m m' a₀ st hR hD f.idx f.a f.c h
      rw [hI hidx, hP ha, hN hc] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_name st a₀ I (.num P N) hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    all_goals simp_all
  · -- a level
    rename_i hpl2
    obtain ⟨hok', hR', hD', hM'⟩ := applyLevelW_refines m m' a₀ st hR hD f.idx (f.pl - 2) f.a f.c h
    rcases r with ⟨_, (⟨_, _⟩ | ⟨_, _⟩)⟩ | ⟨I, (U | ⟨U, V⟩ | ⟨U, V⟩ | U)⟩ | _ | _ | _ | _ <;>
      simp only [RecR, PlR, NameR] at hRR
    · simp_all
    · simp_all
    · obtain ⟨hI, hp, hU⟩ := hRR
      have hk : levelRecW (f.pl - 2) f.a f.c = .succ U := by
        rw [hp]; show LevelRec.succ f.a.toNat = _; rw [hU ha]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    · obtain ⟨hI, hp, hU, hV⟩ := hRR
      have hc : f.c ≠ NONE := fun h' => hcn ⟨h', .inr (.inl hp)⟩
      have hk : levelRecW (f.pl - 2) f.a f.c = .max U V := by
        rw [hp]; show LevelRec.max f.a.toNat f.c.toNat = _; rw [hU ha, hV hc]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    · obtain ⟨hI, hp, hU, hV⟩ := hRR
      have hc : f.c ≠ NONE := fun h' => hcn ⟨h', .inr (.inr hp)⟩
      have hk : levelRecW (f.pl - 2) f.a f.c = .imax U V := by
        rw [hp]; show LevelRec.imax f.a.toNat f.c.toNat = _; rw [hU ha, hV hc]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    · obtain ⟨hI, hp, hU⟩ := hRR
      have hk : levelRecW (f.pl - 2) f.a f.c = .param U := by
        rw [hp]; show LevelRec.param f.a.toNat = _; rw [hU ha]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    all_goals simp_all

omit h64 hsize in
/-- An expression line, as `applyLine` applies it. -/
theorem applyLine_expr (st : StateD) (a₀ : AState) (i : Nat) (r : ExprRec)
    (h : AM.ok (parseExprEntryD st i r) a₀) :
    AM.ok (applyRecord st (.expr i r)) a₀ ∧
      AM.res (applyRecord st (.expr i r) : AM (StateD ⊕ RecordVerdict)) a₀ =
        .inl (AM.res (parseExprEntryD st i r) a₀) ∧
      AM.st (applyRecord st (.expr i r)) a₀ = AM.st (parseExprEntryD st i r) a₀ := by
  obtain ⟨h1, h2, h3⟩ := AM.bind_pure (parseExprEntryD st i r)
    (Sum.inl : StateD → StateD ⊕ RecordVerdict) a₀ h
  exact ⟨h1, h3, h2⟩

end refine

end L.Front
