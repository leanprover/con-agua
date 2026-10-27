import ConAgua.L.FuelMono
import ConAgua.L.ErrSpec

/-!
# More fuel, the same error of class `1`/`2` (lane `verdicts-b`, helper `ia2`, fork `top`)

The error half of `FuelMono.lean`: a run that fails with an error of class other than `0` at fuel
`n` fails with the same error at every larger fuel (running out of fuel is class `0`). So a claim
proved for the fuels from some `n₀` on extends to the smaller ones (`callE_err_mono`).
-/

namespace L

/-- `x'` fails wherever `x` fails with a class other than `0`, and succeeds where it does. -/
def MExt {α : Type} (x x' : M α) : Prop :=
  ∀ s, (∀ r, x.run s = .ok r → x'.run s = .ok r) ∧
    (∀ e, x.run s = .error e → e.cls ≠ 0 → x'.run s = .error e)

theorem MExt.refl {α : Type} (x : M α) : MExt x x := fun _ => ⟨fun _ h => h, fun _ h _ => h⟩

theorem MExt.bind {α β : Type} {x x' : M α} {g g' : α → M β} (hx : MExt x x') (hg : ∀ a, MExt (g a) (g' a)) :
    MExt (x >>= g) (x' >>= g') := fun s => by
  constructor
  · intro r h
    rw [StateT.run_bind] at h ⊢
    cases h1 : x.run s with
    | error e => rw [h1] at h; cases h
    | ok q => rw [h1] at h; rw [(hx s).1 q h1]; exact (hg q.1 q.2).1 r h
  · intro e h hk
    rw [StateT.run_bind] at h ⊢
    cases h1 : x.run s with
    | error e1 => rw [h1] at h; cases h; rw [(hx s).2 _ h1 hk]; rfl
    | ok q => rw [h1] at h; rw [(hx s).1 q h1]; exact (hg q.1 q.2).2 e h hk

/-- The ok and the class-`1`/`2` error runs of `k` are `k'`'s. -/
def KExtE (k k' : Stmt → M Sig) : Prop := ∀ c, MExt (k c) (k' c)

theorem invoke_monoE {p : Prog} {k k' : Stmt → M Sig} (hk : KExtE k k') (f : FnName) (vs : List Word) :
    MExt (invoke p k f vs) (invoke p k' f vs) := by
  unfold invoke callFn
  refine MExt.bind (MExt.refl _) fun fd => ?_
  refine MExt.bind (MExt.refl _) fun s => ?_
  refine MExt.bind (MExt.refl _) fun _ => ?_
  exact MExt.bind (hk _) fun _ => MExt.refl _

theorem step_monoE (p : Prog) {k k' : Stmt → M Sig} (hk : KExtE k k') : KExtE (step p k) (step p k') := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [step]
    exact MExt.bind ih₁ fun a => by cases a <;> first | exact ih₂ | exact MExt.refl _
  | ite c c₁ c₂ ih₁ ih₂ =>
    simp only [step]
    exact MExt.bind (MExt.refl _) fun b => by cases b <;> first | exact ih₁ | exact ih₂
  | «while» c c₁ ih =>
    simp only [step]
    refine MExt.bind (MExt.refl _) fun b => ?_
    cases b with
    | false => exact MExt.refl _
    | true =>
      exact MExt.bind ih fun a => by cases a <;> first | exact hk _ | exact MExt.refl _
  | call xs f args =>
    simp only [step]
    exact MExt.bind (MExt.refl _) fun vs => MExt.bind (invoke_monoE hk f vs) fun _ => MExt.refl _
  | _ => exact MExt.refl _

theorem exec_monoE (p : Prog) : ∀ n, KExtE (exec p n) (exec p (n + 1))
  | 0 => fun c s => ⟨fun r h => (by simp [exec] at h; cases h), fun e h hk => (by
      simp [exec] at h; cases h; exact absurd Err.cls_outOfFuel hk)⟩
  | n + 1 => step_monoE p (exec_monoE p n)

theorem MExt.trans {α : Type} {x y z : M α} (h1 : MExt x y) (h2 : MExt y z) : MExt x z := fun s =>
  ⟨fun r h => (h2 s).1 r ((h1 s).1 r h), fun e h hk => (h2 s).2 e ((h1 s).2 e h hk) hk⟩

theorem exec_leE (p : Prog) {n n' : Nat} (hn : n ≤ n') : KExtE (exec p n) (exec p n') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => exact fun c => MExt.refl _
  | succ d ih => exact fun c => (ih (by omega) c).trans (exec_monoE p (n + d) c)

/-- **More fuel, the same error of class `1`/`2`.** -/
theorem callE_err_mono {p : Prog} {n n' : Nat} (hn : n ≤ n') {f : FnName} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) (hk : e.cls ≠ 0) : callE p n' f vs m = .error e := by
  have H := ((invoke_monoE (p := p) (exec_leE p hn) f vs) ⟨m, Locals.init []⟩).2
  simp only [callE] at h ⊢
  split at h
  · cases h
  · rename_i e' he'
    cases h
    rw [H _ he' hk]

end L
