import ConAgua.Arena.PromoteCIRef.StPNat
import ConRon.Bridge.Grind

/-!
# PmDecRuleWords

`nat?_get`, `bool?_get`, `pmDecRule_words`, `FireWords.mono`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem nat?_get {a : Array Word} {i x : Nat} (h : nat? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat = x := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem bool?_get {a : Array Word} {i : Nat} {x : Bool} (h : bool? a i = some x) :
    ∃ w, a[i]? = some w ∧ (w != 0) = x := by
  simp only [bool?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

/-- The words a decoded rule record reads. -/
theorem pmDecRule_words {a : Array Word} {q : Nat} {rl : IRecRule} (h : decRule a q = some rl) :
    ∃ w0 w1 w2 w8 w9 w10 : Word, a[q]? = some w0 ∧ w0.toNat < 2 ^ 32 ∧ rl.ctor = decI w0 ∧
      a[q + 1]? = some w1 ∧ w1.toNat = rl.nfields ∧ a[q + 2]? = some w2 ∧
      w2.toNat = rl.ctorParams ∧ a[q + 8]? = some w8 ∧ w8.toNat < 2 ^ 32 ∧ rl.rhs = decI w8 ∧
      a[q + 9]? = some w9 ∧ (w9 != 0) = rl.k ∧ a[q + 10]? = some w10 ∧ (w10 != 0) = rl.eta := by
  unfold decRule at h
  cases hk : nat? a (q + 3) with
  | none => simp [hk] at h
  | some t =>
    simp only [hk, Option.bind_eq_bind, Option.bind_some] at h
    rcases t with _ | _ | t
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨c, hc, nf, hnf, cpr, hcp, r, hr, kb, hkb, eb, heb, rfl⟩ := h
      obtain ⟨w0, e0, l0, rfl⟩ := hd?_some hc
      obtain ⟨w1, e1, rfl⟩ := nat?_get hnf
      obtain ⟨w2, e2, rfl⟩ := nat?_get hcp
      obtain ⟨w8, e8, l8, rfl⟩ := hd?_some hr
      obtain ⟨w9, e9, rfl⟩ := bool?_get hkb
      obtain ⟨w10, e10, rfl⟩ := bool?_get heb
      exact ⟨w0, w1, w2, w8, w9, w10, e0, l0, rfl, e1, rfl, e2, rfl, e8, l8, rfl, e9, rfl, e10, rfl⟩
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨l1, hl1, l2, hl2, c, hc, nf, hnf, cpr, hcp, r, hr, kb, hkb, eb, heb, rfl⟩ := h
      obtain ⟨w0, e0, l0, rfl⟩ := hd?_some hc
      obtain ⟨w1, e1, rfl⟩ := nat?_get hnf
      obtain ⟨w2, e2, rfl⟩ := nat?_get hcp
      obtain ⟨w8, e8, l8, rfl⟩ := hd?_some hr
      obtain ⟨w9, e9, rfl⟩ := bool?_get hkb
      obtain ⟨w10, e10, rfl⟩ := bool?_get heb
      exact ⟨w0, w1, w2, w8, w9, w10, e0, l0, rfl, e1, rfl, e2, rfl, e8, l8, rfl, e9, rfl, e10, rfl⟩
    · simp at h

theorem FireWords.mono {A B : Array Word} (h : ArrExt A B) {k q b r y : Word} {fire : IRecRuleFire}
    (hf : FireWords A k q b r y fire) : FireWords B k q b r y fire := by
  rcases hf with hf | ⟨hk, lv, ps, rfl, h1, h2⟩
  · exact Or.inl hf
  · exact Or.inr ⟨hk, lv, ps, rfl, h.hslice? h1, h.hslice? h2⟩

end L.Arena
