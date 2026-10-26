import ConAgua.Arena.PromoteCIRef8

/-!
# `promote_caps` and `promote_proj_table` refine `promoteCaps` and `promoteProjTable`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem nat?_move {a b : Array Word} {i j x : Nat} (hw : b[j]? = a[i]?) (h : nat? a i = some x) :
    nat? b j = some x := by
  simp only [L.Arena.nat?] at h ⊢; rw [hw]; exact h

theorem bool?_move {a b : Array Word} {i j : Nat} {x : Bool} (hw : b[j]? = a[i]?)
    (h : bool? a i = some x) : bool? b j = some x := by
  simp only [L.Arena.bool?] at h ⊢; rw [hw]; exact h

/-- A list handle whose two words are copied and whose slice is stable. -/
theorem hlist?_move {a b : Array Word} {i j : Nat} {k : IdxKind} {xs : List (Idx k)}
    (hw0 : b[j]? = a[i]?) (hw1 : b[j + 1]? = a[i + 1]?)
    (hs : ∀ x y : Nat, nat? a i = some x → nat? a (i + 1) = some y → hslice? a x y = some xs →
      hslice? b x y = some xs)
    (h : hlist? a i = some xs) : hlist? b j = some xs := by
  simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨o, ho, c, hc, hsl⟩ := h
  exact ⟨o, nat?_move hw0 ho, c, nat?_move hw1 hc, hs o c ho hc hsl⟩

theorem decPW_move {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q d : Nat}
    {pw : ConLeche.PropWhen}
    (hw : ∀ i, i < 3 → b[d + i]? = a[q + i]?)
    (hs : ∀ x y : Nat, nat? a (q + 1) = some x → nat? a (q + 2) = some y →
      ∀ xs : List NIdx, hslice? a x y = some xs → hslice? b x y = some xs)
    (h : decPW a dn q = some pw) : decPW b dn d = some pw := by
  unfold decPW at h ⊢
  cases hk : nat? a q with
  | none => simp [hk] at h
  | some t =>
    have hk' : nat? b d = some t := nat?_move (by simpa using hw 0 (by omega)) hk
    simp only [hk, hk', Option.bind_eq_bind, Option.bind_some] at h ⊢
    rcases t with _ | _ | t
    · exact h
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨l, hl, ns, hns, rfl⟩ := h
      refine ⟨l, hlist?_move (hw 1 (by omega)) (by simpa [Nat.add_assoc] using hw 2 (by omega))
        (fun x y h1 h2 => hs x y h1 h2 _) hl, ns, hns, rfl⟩
    · simp at h

theorem decCaps_move {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q d : Nat}
    {caps : IIndCaps} {ec : NIdx} {al cs : List NIdx}
    (hA : decCaps a dn q = some caps)
    (hw : ∀ i, i < 15 → i ≠ 1 → i ≠ 10 → i ≠ 13 → b[d + i]? = a[q + i]?)
    (hpw : decPW b dn (d + 7) = some caps.sortZ)
    (h1 : hd? b (d + 1) = some ec) (h10 : hlist? b (d + 10) = some al)
    (h13 : hlist? b (d + 13) = some cs) :
    decCaps b dn d = some { caps with etaCtor := ec, all := al, ctors := cs } := by
  unfold decCaps at hA ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hA ⊢
  obtain ⟨e1, h1', e2, h2', e3, h3', e4, h4', e5, h5', e6, h6', e7, h7', e8, h8', e9, h9',
    e10, h10', e11, h11', rfl⟩ := hA
  refine ⟨e1, bool?_move (by simpa using hw 0 (by omega) (by omega) (by omega) (by omega)) h1',
    ec, h1, e3, nat?_move (hw 2 (by omega) (by omega) (by omega) (by omega)) h3',
    e4, nat?_move (hw 3 (by omega) (by omega) (by omega) (by omega)) h4',
    e5, bool?_move (hw 4 (by omega) (by omega) (by omega) (by omega)) h5',
    e6, nat?_move (hw 5 (by omega) (by omega) (by omega) (by omega)) h6',
    e7, bool?_move (hw 6 (by omega) (by omega) (by omega) (by omega)) h7',
    e8, hpw, al, h10, e10, nat?_move (hw 12 (by omega) (by omega) (by omega) (by omega)) h10',
    cs, h13, rfl⟩

end L.Arena
