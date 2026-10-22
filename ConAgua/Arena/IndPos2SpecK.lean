import ConAgua.Arena.IndPos2SpecJ

/-! # `IndPos2`, the frame's helpers (lane `indproofs2`, helper `pos2`): records decoded below the
tops (`DecB`) as the words L reads; `NestKey` equality and membership; `nestAcceptGroup`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decoded below the tops: the reads lie below the top -/

theorem pos2_hslice_get {k : IdxKind} {a : Array Word} :
    ∀ {o n : Nat} {l : List (Idx k)}, hslice? a o n = some l →
    l.length = n ∧ ∀ j, j < n → ∃ w, a[o + j]? = some w ∧ H w ∧ l[j]? = some (decI w)
  | o, 0, l, h => by simp [hslice?] at h; subst h; simp
  | o, n + 1, l, h => by
    rw [hslice?_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := pos2_hslice_get hxs
    obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hx
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => exact ⟨w, by simpa using hw, hwl, rfl⟩
    | succ j =>
      obtain ⟨w', h1', h2', h3'⟩ := h2 j (by omega)
      exact ⟨w', by rw [show o + (j + 1) = o + 1 + j by omega]; exact h1', h2', by simpa using h3'⟩

/-- A handle slice decoded in the cut pool lies below the top. -/
theorem pos2_decHL_trunc {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL (truncM m) o l = some xs) : ∀ j < l, o + j < iwTop m := fun j hj => by
  obtain ⟨-, hg⟩ := pos2_hslice_get h
  obtain ⟨w, hw, -⟩ := hg j hj
  exact (truncM_iw_get hw).1

theorem pos2_iwN_trunc {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    i < iwTop m ∧ iwN m i = some v := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp [iwN, nat?, hw']⟩

theorem pos2_iwH_trunc {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : iwH (truncM m) i = some x) :
    i < iwTop m ∧ iwH m i = some x := by
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp only [iwH, hd?]; rw [hw']; simp [hl]⟩

/-- A key record decoded below the tops: its words and its `ds` slice below the top. -/
theorem pos2_nk_in {m : Mem} {p : Nat} {kk : NestKey} (h : DecB (fun m => decNK m p) m kk) :
    decNK m p = some kk ∧ NKIn m p (· < iwTop m) := by
  refine ⟨h.get (decNK_mono p), ?_⟩
  have h' : decNK (truncM m) p = some kk := h
  simp only [decNK, decAt, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h'
  obtain ⟨c, hc, u, hu, ds, ⟨o, ho, l, hl, hds⟩, -⟩ := h'
  obtain ⟨h0, -⟩ := pos2_iwH_trunc hc
  obtain ⟨h1, -⟩ := pos2_iwH_trunc hu
  obtain ⟨h2, ho'⟩ := pos2_iwN_trunc ho
  obtain ⟨h3, hl'⟩ := pos2_iwN_trunc hl
  refine ⟨fun j hj => ?_, fun o' l' ho2 hl2 j hj => ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simpa using ‹_›
  · rw [ho'] at ho2; rw [hl'] at hl2; cases ho2; cases hl2
    exact pos2_decHL_trunc hds j hj

/-- **A key decoded below the tops, as the words L reads.** -/
theorem pos2_nk_fields {m : Mem} {key : Word} {kk : NestKey} (h : DecB (fun m => decNK m key.toNat) m kk)
    (htop : iwTop m < 2 ^ 64) :
    H (rdW (m.arr64 IW) key) ∧ decI (rdW (m.arr64 IW) key) = kk.cname ∧
    H (rdW (m.arr64 IW) (key + 1)) ∧ decI (rdW (m.arr64 IW) (key + 1)) = kk.lvls ∧
    decHL m (rdW (m.arr64 IW) (key + 2)).toNat (rdW (m.arr64 IW) (key + 3)).toNat = some kk.ds ∧
    (∀ j < (rdW (m.arr64 IW) (key + 3)).toNat, (rdW (m.arr64 IW) (key + 2)).toNat + j < iwTop m) ∧
    key.toNat + 4 ≤ iwTop m := by
  obtain ⟨h1, h2⟩ := pos2_nk_in h
  exact nk_fields h1 h2 htop

/-- A slice of record pointers decoded below the tops: each element is. -/
theorem pos2_decPL_trunc {α : Type} {f : Mem → Nat → Option α} {m : Mem} :
    ∀ {o l : Nat} {xs : List α}, decPL (truncM m) (f (truncM m)) o l = some xs →
    xs.length = l ∧ ∀ j (hj : j < l), ∃ v, o + j < iwTop m ∧ iwN m (o + j) = some v ∧
      ∃ hx : j < xs.length, f (truncM m) v = some xs[j]
  | o, 0, xs, h => by simp [decPL] at h; subst h; simp
  | o, l + 1, xs, h => by
    obtain ⟨v0, x, xs', rfl, hv0, hx, hxs'⟩ := decPL_cons h
    obtain ⟨h1, h2⟩ := pos2_decPL_trunc hxs'
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero =>
      obtain ⟨hi, hv⟩ := pos2_iwN_trunc hv0
      exact ⟨v0, by simpa using hi, by simpa using hv, by simp, by simpa using hx⟩
    | succ j =>
      obtain ⟨v, h1', h2', hx', h3'⟩ := h2 j (by omega)
      refine ⟨v, by rw [show o + (j + 1) = o + 1 + j by omega]; exact h1',
        by rw [show o + (j + 1) = o + 1 + j by omega]; exact h2', by simp; omega, ?_⟩
      simpa using h3'

end L.Ind
