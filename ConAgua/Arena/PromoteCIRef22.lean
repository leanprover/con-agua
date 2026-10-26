import ConAgua.Arena.PromoteCIRef21

/-!
# `promote_ci` refines `promoteCI`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem decCV_bound {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    q + 3 < a.size := by
  unfold decCV at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨n, hn, l, hl, t, ht, -⟩ := h
  obtain ⟨w, hw, -⟩ := hd?_some ht
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decCaps_bound {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {caps : IIndCaps} (h : decCaps a dn q = some caps) : q + 14 < a.size := by
  obtain ⟨-, -, hc, -⟩ := decCaps_words h
  obtain ⟨o, c, -, hc1, -⟩ := hlist?_unfold hc
  obtain ⟨w, hw, -⟩ := nat?_get hc1
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem pmDecTbl_bound {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    q + 12 < a.size := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, -⟩ := h
  obtain ⟨o, c, -, hc1, -⟩ := hlist?_unfold h9
  obtain ⟨w, hw, -⟩ := nat?_get hc1
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decHint_move' {a b : Array Word} {i j : Nat} {h : ConLeche.ReducibilityHint}
    (hw0 : b[j]? = a[i]?) (hw1 : a[i + 1]? = none ∨ b[j + 1]? = a[i + 1]?)
    (hd : decHint a i = some h) : decHint b j = some h := by
  unfold decHint at hd ⊢
  cases hk : nat? a i with
  | none => simp [hk] at hd
  | some t =>
    have hk' : nat? b j = some t := nat?_move hw0 hk
    simp only [hk, hk', Option.bind_eq_bind, Option.bind_some] at hd ⊢
    rcases t with _ | _ | _ | t
    · exact hd
    · exact hd
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hd ⊢
      obtain ⟨x, hx, rfl⟩ := hd
      rcases hw1 with h1 | h1
      · obtain ⟨w, hw, -⟩ := nat?_get hx; rw [h1] at hw; cases hw
      · exact ⟨x, nat?_move h1 hx, rfl⟩
    · simp at hd

/-- The word of a decoded `nat?`, read in the pool `m` (below `D`). -/
theorem nat_word_pre {m : Mem} {D i k : Nat} (h : nat? (preE m D) i = some k) :
    ∃ w, (m.arr64 EREC)[i]? = some w ∧ w.toNat = k ∧ i < D := by
  obtain ⟨w, hw, hk, hi⟩ := nat?_pre h
  exact ⟨w, hw, hk, hi⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

end rel

end L.Arena
