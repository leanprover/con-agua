import ConAgua.Arena.IndIface

/-!
# HlistUnfold

`hlist?_unfold`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem hlist?_unfold {a : Array Word} {i : Nat} {k : IdxKind} {xs : List (Idx k)}
    (h : hlist? a i = some xs) :
    ∃ o c : Nat, nat? a i = some o ∧ nat? a (i + 1) = some c ∧ hslice? a o c = some xs := by
  simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  exact ⟨o, c, ho, hc, hs⟩

end L.Arena
