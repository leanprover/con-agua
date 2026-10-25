module

public import ConAgua.L.Logic

@[expose] public section

/-!
# More fuel, the same successful run

The interpreter is monotone in its continuation (`step_mono`), so a run that succeeds with fuel
`n` succeeds with the same result at every larger fuel (`exec_mono`, `exec_le`). For specs:
`invoke_fuel_le` moves a partial-correctness triple at fuel `n` down to any `k ≤ n`, which is what
the `…UpTo p n := ∀ j ≤ n, Spec p j` families were introduced for (DESIGN.md, "Proof tooling").
Moved here from `Front/RunModel.lean` (lane `prooftools`), which re-exports the names.
-/

open Std.WP
open scoped Lean.Order

namespace L

/-- `k'` succeeds wherever `k` does, with the same result. -/
def KExt (k k' : Stmt → M Sig) : Prop := ∀ c s r, (k c).run s = .ok r → (k' c).run s = .ok r

theorem run_bind_ok {α β : Type} {x : M α} {g : α → M β} {s : St} {r : β × St}
    (h : (x >>= g).run s = .ok r) : ∃ a s', x.run s = .ok (a, s') ∧ (g a).run s' = .ok r := by
  rw [StateT.run_bind] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok q => rw [hx] at h; exact ⟨q.1, q.2, rfl, h⟩

theorem run_bind_of {α β : Type} {x : M α} {g : α → M β} {s : St} {a : α} {s' : St} {r : β × St}
    (hx : x.run s = .ok (a, s')) (hg : (g a).run s' = .ok r) : (x >>= g).run s = .ok r := by
  rw [StateT.run_bind, hx]; exact hg

theorem invoke_mono {p : Prog} {k k' : Stmt → M Sig} (hk : KExt k k') {f : FnName} {vs : List Word}
    {s : St} {r : List Word × St} (h : (invoke p k f vs).run s = .ok r) :
    (invoke p k' f vs).run s = .ok r := by
  unfold invoke at h ⊢
  obtain ⟨fd, s1, h1, h2⟩ := run_bind_ok h
  refine run_bind_of h1 ?_
  unfold callFn at h2 ⊢
  obtain ⟨s2, s3, h3, h4⟩ := run_bind_ok h2
  refine run_bind_of h3 ?_
  obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
  refine run_bind_of h5 ?_
  obtain ⟨rr, s5, h7, h8⟩ := run_bind_ok h6
  exact run_bind_of (hk _ _ _ h7) h8

theorem step_mono (p : Prog) {k k' : Stmt → M Sig} (hk : KExt k k') :
    ∀ c s r, (step p k c).run s = .ok r → (step p k' c).run s = .ok r := by
  intro c
  induction c with
  | skip => intro s r h; exact h
  | set x e => intro s r h; exact h
  | st8 a i e => intro s r h; exact h
  | st64 a i e => intro s r h; exact h
  | brk => intro s r h; exact h
  | ret es => intro s r h; exact h
  | abort e => intro s r h; exact h
  | gset g e => intro s r h; exact h
  | st64t a t i e => intro s r h; exact h
  | copy64 d di s si n => intro s r h; exact h
  | copy8w d di s si n => intro s r h; exact h
  | scan8 x s i e c => intro s r h; exact h
  | seq c₁ c₂ ih₁ ih₂ =>
    intro s r h
    obtain ⟨a, s', h1, h2⟩ := run_bind_ok h
    refine run_bind_of (ih₁ _ _ h1) ?_
    cases a with
    | normal => exact ih₂ _ _ h2
    | brk => exact h2
    | ret v => exact h2
  | ite c c₁ c₂ ih₁ ih₂ =>
    intro s r h
    obtain ⟨bv, s', h1, h2⟩ := run_bind_ok h
    refine run_bind_of h1 ?_
    cases bv with
    | false => exact ih₂ _ _ h2
    | true => exact ih₁ _ _ h2
  | «while» c c₁ ih =>
    intro s r h
    obtain ⟨bv, s', h1, h2⟩ := run_bind_ok h
    refine run_bind_of h1 ?_
    cases bv with
    | false => exact h2
    | true =>
      obtain ⟨a, s'', h3, h4⟩ := run_bind_ok h2
      refine run_bind_of (ih _ _ h3) ?_
      cases a with
      | normal => exact hk _ _ _ h4
      | brk => exact h4
      | ret v => exact h4
  | call xs f args =>
    intro s r h
    obtain ⟨vs, s1, h1, h2⟩ := run_bind_ok h
    refine run_bind_of h1 ?_
    obtain ⟨rs, s2, h3, h4⟩ := run_bind_ok h2
    exact run_bind_of (invoke_mono hk h3) h4

/-- **More fuel, the same successful run.** -/
theorem exec_mono (p : Prog) : ∀ n, KExt (exec p n) (exec p (n + 1))
  | 0 => fun c s r h => by simp [exec] at h; cases h
  | n + 1 => fun c s r h => step_mono p (exec_mono p n) c s r h

theorem exec_le (p : Prog) {n n' : Nat} (hn : n ≤ n') : KExt (exec p n) (exec p n') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => exact fun _ _ _ h => h
  | succ d ih => exact fun c s r h => exec_mono p (n + d) c s r (ih (by omega) c s r h)

end L
