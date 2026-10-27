import ConAgua.Arena.IndPartsSpec.IndPartsProg2

/-!
# PartsAt

`MaProg`, `partsAnyM_cons`, `partsPL_bound`, `partsAt`, `memberNamesW_room`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `mentions_any_const`. -/
structure MaProg (p : Prog) : Prop where
  view : p.lookup "e_view" = some eView
  cont : p.lookup "sl_contains" = some slContains
  find : p.lookup "ma_find" = some (memoFindG maSch)
  put : p.lookup "ma_put" = some (memoPutG maSch)
  go : p.lookup "mentions_any_go" = some mentionsAnyGo
  node : p.lookup "mentions_any_node" = some mentionsAnyNode
  clr : p.lookup "ma_clear" = some (memoClearG maSch)
  ma : p.lookup "mentions_any_const" = some mentionsAnyConst

/-! ## `block_raw_rec` -/

theorem partsAnyM_cons {m : Type → Type} [Monad m] {α : Type} (f : α → m Bool) (a : α) (l : List α) :
    List.anyM f (a :: l) = (do let b ← f a; if b then pure true else List.anyM f l) := by
  simp only [List.anyM]; congr 1; funext b; cases b <;> rfl

/-- A pointer slice decoded below the tops, nonempty, lies below the top. -/
theorem partsPL_bound {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : decPL (truncM m) (f (truncM m)) o l = some xs) : l = 0 ∨ o + l ≤ iwTop m := by
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · exact Or.inl h0
  · right
    obtain ⟨v, hv, -⟩ := decPL_getH (truncM m) h (l - 1) (by omega)
    have := partsIwLt hv; omega

/-- A decoded slice-at-a-header, as words and a slice below the tops. -/
theorem partsAt {α : Type} {f : Mem → Nat → Option α} (_hf : ∀ q, OMono (fun m => f m q)) {m : Mem}
    {i : Nat} {xs : List α} (h : decAt (truncM m) (decPL (truncM m) (f (truncM m))) i = some xs) :
    ∃ o l : Word, iwN (truncM m) i = some o.toNat ∧ iwN (truncM m) (i + 1) = some l.toNat ∧
      DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs ∧ (l = 0 ∨ o.toNat + l.toNat ≤ iwTop m) := by
  simp only [decAt, bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, hd⟩ := h
  have hv64 : ∀ {i v : Nat}, iwN (truncM m) i = some v → v < 2 ^ 64 := by
    intro i v h; simp only [iwN, nat?, Option.map_eq_some_iff] at h; obtain ⟨w, -, rfl⟩ := h; exact w.toNat_lt
  have hob := hv64 ho
  have hlb := hv64 hl
  refine ⟨UInt64.ofNat o, UInt64.ofNat l, by rw [UInt64.toNat_ofNat_of_lt' hob]; exact ho,
    by rw [UInt64.toNat_ofNat_of_lt' hlb]; exact hl, ?_, ?_⟩
  · show decPL _ _ _ _ = _; rw [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]; exact hd
  · rcases partsPL_bound hd with h0 | h0
    · left; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_ofNat_of_lt' hlb]; simpa using h0
    · right; rw [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]; exact h0

theorem memberNamesW_room {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + (rdW (m.arr64 IW) (p + 1)).toNat ≤ (m.arr64 IW).size := by
  unfold memberNamesW at h
  cases hal : allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

end L.Ind

end
