import ConAgua.L.Logic

/-!
# The run of a function as its model

`runF p f vs m`: the memory after a successful run of `f vs` on `m` with some fuel (`none` if no
fuel gives one). It is well defined because a run that succeeds with fuel `n` gives the same result
with more fuel (`exec_mono`, the interpreter is monotone in its continuation: `step_mono`), and the
caller's locals do not matter (`invoke_loc`). `runF_spec`: every successful run of `f` ends in
`runF`'s memory, so a function whose own model carries a fuel index (the apply step of an
`inductive` line) can be called from a fuel-free model.
-/

open Std.WP
open scoped Lean.Order

namespace L.Front

open L

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
  | abort => intro s r h; exact h
  | gset g e => intro s r h; exact h
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

/-- A call's run does not depend on the caller's locals, which it restores. -/
theorem invoke_loc {p : Prog} {k : Stmt → M Sig} {f : FnName} {vs : List Word} {s : St}
    {r : List Word} {t : St} (h : (invoke p k f vs).run s = .ok (r, t)) :
    t.loc = s.loc ∧ ∀ s' : St, s'.mem = s.mem → (invoke p k f vs).run s' = .ok (r, { t with loc := s'.loc }) := by
  unfold invoke at h ⊢
  obtain ⟨fd, s1, h1, h2⟩ := run_bind_ok h
  have hl : ∀ s' : St, (lookupFn p f).run s' = .ok (fd, s') ∧ s1 = s := by
    intro s'
    unfold lookupFn at h1 ⊢
    cases hp : p.lookup f with
    | none => rw [hp] at h1; cases h1
    | some fd' =>
      rw [hp] at h1
      simp only [StateT.run_pure, Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨rfl, rfl⟩
  obtain ⟨-, rfl⟩ := hl s
  unfold callFn at h2
  obtain ⟨s2, s3, h3, h4⟩ := run_bind_ok h2
  simp only [StateT.run_get, Except.ok.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
  simp only [StateT.run_set, Except.ok.injEq, Prod.mk.injEq] at h5
  obtain ⟨-, rfl⟩ := h5
  obtain ⟨rr, s5, h7, h8⟩ := run_bind_ok h6
  obtain ⟨u2, s6, h9, h10⟩ := run_bind_ok h8
  simp only [StateT.run_modify, Except.ok.injEq, Prod.mk.injEq] at h9
  obtain ⟨-, rfl⟩ := h9
  simp only [StateT.run_pure, Except.ok.injEq, Prod.mk.injEq] at h10
  obtain ⟨rfl, rfl⟩ := h10
  refine ⟨rfl, fun s' hs' => ?_⟩
  refine run_bind_of (hl s').1 ?_
  unfold callFn
  refine run_bind_of (s' := s') (a := s') rfl ?_
  refine run_bind_of (a := ()) (s' := { s' with loc := Locals.init vs }) rfl ?_
  have e : ({ s' with loc := Locals.init vs } : St) = { s1 with loc := Locals.init vs } := by
    cases s1; cases s'; simp only at hs'; subst hs'; rfl
  rw [e]
  refine run_bind_of h7 ?_
  refine run_bind_of (a := ()) (s' := { s5 with loc := s'.loc }) rfl ?_
  rfl

/-- The run of `f vs` on `m` with fuel `n`: its results and final state. -/
def RunOK (p : Prog) (f : FnName) (vs : List Word) (m : Mem) (x : Nat × List Word × St) : Prop :=
  (invoke p (exec p x.1) f vs).run ⟨m, Locals.init []⟩ = .ok (x.2.1, x.2.2)

open Classical in
/-- **The memory after a successful run of `f vs` on `m`** (any fuel), `none` if there is none. -/
noncomputable def runF (p : Prog) (f : FnName) (vs : List Word) (m : Mem) : Option Mem :=
  if h : ∃ x, RunOK p f vs m x then some (Classical.choose h).2.2.mem else none

/-- Two successful runs from the same memory end in the same memory. -/
theorem runOK_mem {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {x y : Nat × List Word × St}
    (hx : RunOK p f vs m x) (hy : RunOK p f vs m y) : x.2.2.mem = y.2.2.mem := by
  unfold RunOK at hx hy
  have h1 := invoke_mono (exec_le p (Nat.le_max_left x.1 y.1)) hx
  have h2 := invoke_mono (exec_le p (Nat.le_max_right x.1 y.1)) hy
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  rw [h2.2]

theorem runF_of {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {x : Nat × List Word × St}
    (hx : RunOK p f vs m x) : runF p f vs m = some x.2.2.mem := by
  have h : ∃ x, RunOK p f vs m x := ⟨x, hx⟩
  unfold runF
  rw [dif_pos h, runOK_mem (Classical.choose_spec h) hx]

theorem runF_some {p : Prog} {f : FnName} {vs : List Word} {m m' : Mem} (h : runF p f vs m = some m') :
    ∃ x, RunOK p f vs m x ∧ x.2.2.mem = m' := by
  unfold runF at h
  split at h
  · rename_i hx
    simp only [Option.some.injEq] at h
    exact ⟨_, Classical.choose_spec hx, h⟩
  · cases h

/-- **Every successful run of `f` is `runF`'s.** -/
theorem runF_spec (p : Prog) (f : FnName) (vs : List Word) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun _ s' => LocEq s' s₀ ∧ runF p f vs s₀.mem = some s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs h
  subst hs
  obtain ⟨hl, h'⟩ := invoke_loc h
  refine ⟨hl, ?_⟩
  have := h' ⟨s.mem, Locals.init []⟩ rfl
  exact runF_of (x := (n, r, { s' with loc := Locals.init [] })) this

end L.Front
