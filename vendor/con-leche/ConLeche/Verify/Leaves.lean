module

import ConLeche.Kernel.ExprOps
import ConLeche.Verify.Shift
public import ConLeche.Verify.Abstract
import ConLeche.Verify.Knot

public section

/-!
# The free-variable leaf closure

`fvarLeaves e` lists every reachable `fvar` leaf of `e` together with,
hereditarily, the leaves of their type annotations.  The local-context
assumptions (`LeavesBounded`, `LeafCond`) are conditions on exactly this list, so every
syntactic transformation only needs a subset lemma here.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Expr

/-- Closed terms have no leaves. -/
theorem fvarLeaves_eq_nil_of_not_hasFvar :
    ∀ {e : Expr}, e.hasFvar = false → e.fvarLeaves = [] := by
  intro e
  induction e <;> simp_all [hasFvar, fvarLeaves]

/-- Instantiation only introduces the substituted term's leaves. -/
theorem fvarLeaves_instantiate1 {a : Expr} :
    ∀ (e : Expr) (k : Nat) {l}, l ∈ (e.instantiate1 a k).fvarLeaves →
      l ∈ e.fvarLeaves ∨ l ∈ a.fvarLeaves := by
  intro e
  induction e with
  | bvar i =>
    intro k l hl
    simp only [instantiate1] at hl
    split at hl
    · exact Or.inr hl
    · split at hl <;> simp [fvarLeaves] at hl
  | fvar idx ty _ =>
    intro k l hl
    simp only [instantiate1] at hl
    exact Or.inl hl
  | app f b ihf ihb =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihf k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb k hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lam ty body ihty ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | forallE ty body ihty ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | letE ty v body ihty ihv ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases ihv k hl with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | proj s i e ih =>
    intro k l hl
    simp only [instantiate1, fvarLeaves] at hl ⊢
    exact ih k hl
  | sort u => intro k l hl; simp [instantiate1, fvarLeaves] at hl
  | const n us => intro k l hl; simp [instantiate1, fvarLeaves] at hl
  | lit ll => intro k l hl; simp [instantiate1, fvarLeaves] at hl

/-- Well-scopedness gives bounds and scoping for every closure leaf. -/
theorem WScoped_leaves : ∀ (e : Expr) {d : Nat}, WScoped d e →
    ∀ l ∈ e.fvarLeaves, l.1 < d ∧ WScoped l.1 l.2 := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨hw.1, hw.2⟩
    · obtain ⟨h1, h2⟩ := ih hw.2 l hl
      exact ⟨by omega, h2⟩
  | app f a ihf iha =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf hw.1 l hl
    · exact iha hw.2 l hl
  | lam ty body ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | forallE ty body ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | letE ty val body ihty ihval ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact ihty hw.1 l hl
    · exact ihval hw.2.1 l hl
    · exact ihbody hw.2.2 l hl
  | proj s i e ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves] at hl
    exact ih hw l hl
  | bvar i => intro d _ l hl; simp [fvarLeaves] at hl
  | sort u => intro d _ l hl; simp [fvarLeaves] at hl
  | const n us => intro d _ l hl; simp [fvarLeaves] at hl
  | lit ll => intro d _ l hl; simp [fvarLeaves] at hl

/-- Abstracting the scope's top index removes exactly its leaves: the
survivors are original leaves strictly below it. -/
theorem fvarLeaves_abstract1_lt {D : Nat} :
    ∀ (e : Expr) (k : Nat), WScoped (D + 1) e →
      ∀ l ∈ (e.abstract1 D k).fvarLeaves, l ∈ e.fvarLeaves ∧ l.1 < D := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · next hne =>
      simp only [fvarLeaves, List.mem_cons] at hl
      have hidx : idx < D := by omega
      rcases hl with rfl | hl
      · exact ⟨by simp [fvarLeaves], hidx⟩
      · exact ⟨by simp [fvarLeaves, hl],
          Nat.lt_trans (fvarLeaves_lt_of_wscoped hw.2 l hl) hidx⟩
  | app f a ihf iha =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihf k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := iha k hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | lam ty body ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | forallE ty body ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | letE ty val body ihty ihval ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihval k hw.2.1 l hl
      exact ⟨Or.inl (Or.inr h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | proj sn i e ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih k hw l hl
  | bvar i => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | sort u => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | const n us => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | lit ll => intro k _ l hl; simp [abstract1, fvarLeaves] at hl

end ConLeche.Expr
