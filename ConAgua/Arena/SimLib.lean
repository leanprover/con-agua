import ConAgua.Arena.StoreRel
import ConAgua.L.Logic

/-!
# `Sim`: relational lemmas as composable facts (lane `prooftools`)

The light-weight home of lane `indproofs2`'s `Sim` (`IndSim.lean` has the same definition in
`L.Ind`, behind `IndMaster`; this one sits right above the store relation, so the walks and the
stores can use it). DESIGN.md, "Proof tooling", has the how-to.

`Sim mo op a Q`: if the word model `mo` returns `(r, m')`, the twin run `op` from `a` succeeds with
some `x`, state `a'`, and `Q r x m' a'`. A relational lemma about a model built from continuations
(`K none = none`, `K (some (r, m₁)) = body r m₁`, both `rfl`) is a chain of
`refine Sim.bindK rfl (fun _ _ => rfl) (callee_sim …) fun r x m₁ a₁ hQ => ?_`, one per callee: no
`cases h : callee … | none => … | some …`, no dead branches, no replay of the twin's binds.

The walks' existing statements have the *decoded* form
`model = some (r, m') → ∃ a', op.run a = .ok (dec r, a') ∧ R m' a'`; `SimD dec mo op a R` is that
form as a `Sim` (`Sim.ofD`/`SimD.exists` convert), and `Sim.bindD` composes it with the result
already substituted. `Sim.triple` turns a model spec and a `Sim` into the census triple.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The model result `mo` is simulated by the twin run `op` from `a`**: if the model returns
`(r, m')`, the twin succeeds with some `x`, state `a'`, and `Q r x m' a'`. -/
def Sim {β α : Type} (mo : Option (β × Mem)) (op : AM α) (a : AState)
    (Q : β → α → Mem → AState → Prop) : Prop :=
  ∀ r m', mo = some (r, m') → ∃ x a', op.run a = .ok (x, a') ∧ Q r x m' a'

/-- The decoded form: the twin returns `dec r`, and `R` relates the final states. -/
abbrev SimD {β α : Type} (dec : β → α) (mo : Option (β × Mem)) (op : AM α) (a : AState)
    (R : Mem → AState → Prop) : Prop :=
  Sim mo op a (fun r x m' a' => x = dec r ∧ R m' a')

section sim
variable {β γ α δ : Type}

/-- The end of a chain: the model returned `(r, m)`, the twin `pure x`. -/
theorem Sim.ret {r : β} {m : Mem} {x : α} {a : AState} {Q : β → α → Mem → AState → Prop}
    (h : Q r x m a) : Sim (some (r, m)) (pure x : AM α) a Q := by
  intro r' m' e; simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
  exact ⟨x, a, rfl, h⟩

/-- A model that does not return. -/
theorem Sim.of_none {op : AM α} {a : AState} {Q : β → α → Mem → AState → Prop} :
    Sim (none : Option (β × Mem)) op a Q := fun _ _ e => by cases e

/-- **One callee, then the rest**: the model's continuation `K` over the callee's result, the
twin's bind. -/
theorem Sim.bindK {K : Option (β × Mem) → Option (γ × Mem)} {body : β → Mem → Option (γ × Mem)}
    {mo : Option (β × Mem)} {op : AM α} {g : α → AM δ} {a : AState}
    {Q : β → α → Mem → AState → Prop} {R : γ → δ → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁)
    (h1 : Sim mo op a Q) (h2 : ∀ r x m₁ a₁, Q r x m₁ a₁ → Sim (body r m₁) (g x) a₁ R) :
    Sim (K mo) (op >>= g) a R := by
  intro r m' e
  cases hmo : mo with
  | none => rw [hmo, hn] at e; cases e
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    rw [hmo, hs] at e
    obtain ⟨x, a₁, hr1, hQ⟩ := h1 r₁ m₁ hmo
    obtain ⟨y, a₂, hr2, hR⟩ := h2 r₁ x m₁ a₁ hQ r m' e
    exact ⟨y, a₂, by simp only [StateT.run_bind, hr1]; exact hr2, hR⟩

/-- **`Sim.bindK` for a decoded callee**: the rest sees the twin's result as `dec r`. -/
theorem Sim.bindD {K : Option (β × Mem) → Option (γ × Mem)} {body : β → Mem → Option (γ × Mem)}
    {mo : Option (β × Mem)} {dec : β → α} {op : AM α} {g : α → AM δ} {a : AState}
    {R₁ : Mem → AState → Prop} {R : γ → δ → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁)
    (h1 : SimD dec mo op a R₁) (h2 : ∀ r m₁ a₁, R₁ m₁ a₁ → Sim (body r m₁) (g (dec r)) a₁ R) :
    Sim (K mo) (op >>= g) a R :=
  Sim.bindK hn hs h1 fun r _ m₁ a₁ ⟨e, hR⟩ => e ▸ h2 r m₁ a₁ hR

/-- **A twin-only step** (the model does nothing for it: a view, a pin read, a pure computation):
its run from `a` is known. -/
theorem Sim.bind_twin {mo : Option (β × Mem)} {op : AM α} {g : α → AM δ} {a a₁ : AState} {x : α}
    {R : β → δ → Mem → AState → Prop} (hr : op.run a = .ok (x, a₁)) (h : Sim mo (g x) a₁ R) :
    Sim mo (op >>= g) a R := by
  intro r m' e
  obtain ⟨y, a₂, h2, hR⟩ := h r m' e
  exact ⟨y, a₂, by simp only [StateT.run_bind, hr]; exact h2, hR⟩

/-- Weaken the post. -/
theorem Sim.mono {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q Q' : β → α → Mem → AState → Prop}
    (h : Sim mo op a Q) (hq : ∀ r x m a', Q r x m a' → Q' r x m a') : Sim mo op a Q' := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, hq _ _ _ _ h2⟩

/-- Rewrite the twin side. -/
theorem Sim.congr {mo : Option (β × Mem)} {op op' : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop}
    (h : Sim mo op a Q) (e : op = op') : Sim mo op' a Q := e ▸ h

/-- **The decoded form from the existential one** (the walks' `…OK` statements). -/
theorem Sim.ofD {mo : Option (β × Mem)} {dec : β → α} {op : AM α} {a : AState}
    {R : Mem → AState → Prop}
    (h : ∀ r m', mo = some (r, m') → ∃ a', op.run a = .ok (dec r, a') ∧ R m' a') :
    SimD dec mo op a R := by
  intro r m' e; obtain ⟨a', h1, h2⟩ := h r m' e; exact ⟨_, a', h1, rfl, h2⟩

/-- **The existential form from the decoded one.** -/
theorem SimD.exists {mo : Option (β × Mem)} {dec : β → α} {op : AM α} {a : AState}
    {R : Mem → AState → Prop} (h : SimD dec mo op a R) {r : β} {m' : Mem} (e : mo = some (r, m')) :
    ∃ a', op.run a = .ok (dec r, a') ∧ R m' a' := by
  obtain ⟨x, a', h1, rfl, h2⟩ := h r m' e; exact ⟨a', h1, h2⟩

/-- **The `AM.ok`/`AM.st`/`AM.res` form** (the stores' `…_correct` lemmas) as a `Sim`. -/
theorem Sim.ofOk [Inhabited α] {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop}
    (h : ∀ r m', mo = some (r, m') → AM.ok op a ∧ Q r (AM.res op a) m' (AM.st op a)) :
    Sim mo op a Q := by
  intro r m' e
  obtain ⟨hok, hQ⟩ := h r m' e
  exact ⟨_, _, AM.run_of_ok op a hok, hQ⟩

/-- **The census form**: a model run that returned gives `AM.ok`, and the post at
`AM.res`/`AM.st`. -/
theorem Sim.run [Inhabited α] {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} {r : β} {m' : Mem} (h : Sim mo op a Q)
    (hm : mo = some (r, m')) :
    AM.ok op a ∧ Q r (AM.res op a) m' (AM.st op a) := by
  obtain ⟨x, a', h1, h2⟩ := h r m' hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ h1
  exact ⟨hok, by rw [hst, hres]; exact h2⟩

end sim

/-! ## Model-only facts (frames of a model's memory) -/

/-- **Whatever the model `mo` returns satisfies `Q`** (a model-only `Sim`: frames, bounds). -/
def MPost {β : Type} (mo : Option (β × Mem)) (Q : β → Mem → Prop) : Prop :=
  ∀ r m', mo = some (r, m') → Q r m'

/-- **One callee, then the rest**, for a model-only fact. -/
theorem MPost.bindK {β γ : Type} {K : Option (β × Mem) → Option (γ × Mem)}
    {body : β → Mem → Option (γ × Mem)} {mo : Option (β × Mem)} {Q : β → Mem → Prop}
    {R : γ → Mem → Prop} (hn : K Option.none = Option.none)
    (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁) (h1 : MPost mo Q)
    (h2 : ∀ r m₁, Q r m₁ → MPost (body r m₁) R) : MPost (K mo) R := by
  intro r m' e
  cases hmo : mo with
  | none => rw [hmo, hn] at e; cases e
  | some p => obtain ⟨r₁, m₁⟩ := p; rw [hmo, hs] at e; exact h2 r₁ m₁ (h1 r₁ m₁ hmo) r m' e

theorem MPost.ret {β : Type} {r : β} {m : Mem} {Q : β → Mem → Prop} (h : Q r m) :
    MPost (some (r, m)) Q := fun _ _ e => by cases e; exact h

/-- **The decoded census form** (the stores' `…_correct` lemmas) as a `SimD`. -/
theorem Sim.ofOkD {β α : Type} [Inhabited α] {mo : Option (β × Mem)} {dec : β → α} {op : AM α}
    {a : AState} {R : Mem → AState → Prop}
    (h : ∀ r m', mo = some (r, m') → AM.ok op a ∧ R m' (AM.st op a) ∧ AM.res op a = dec r) :
    SimD dec mo op a R :=
  Sim.ofOk fun r m' e => let ⟨h1, h2, h3⟩ := h r m' e; ⟨h1, h3, h2⟩

/-- **From a model spec and a `Sim` to the census triple.** `hspec` is the L spec
(`⦃s = s₀⦄ prog ⦃LocEq s' s₀ ∧ mo = some (r.headD 0, s'.mem)⦄`, `mo` the model at `s₀.mem`),
`hsim` the model's refinement; the post is the usual `LocEq ∧ AM.ok ∧ …` at `AM.res`/`AM.st`. -/
theorem Sim.triple {α : Type} [Inhabited α] {prog : M (List Word)} {s₀ : St}
    {mo : Option (Word × Mem)} {op : AM α} {a₀ : AState} {Q : Word → α → Mem → AState → Prop}
    (hspec : ⦃fun s => s = s₀⦄ prog ⦃fun r s' => LocEq s' s₀ ∧ mo = some (r.headD 0, s'.mem); ⊤⦄)
    (hsim : Sim mo op a₀ Q) :
    ⦃fun s => s = s₀⦄ prog
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok op a₀ ∧ Q (r.headD 0) (AM.res op a₀) s'.mem
        (AM.st op a₀); ⊤⦄ :=
  M.triple_of_run fun _ _ _ hs hrun => by
    obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
    exact ⟨hloc, hsim.run hI⟩

/-- **`Sim.triple` in the decoded form**: the post
`LocEq ∧ AM.ok op a₀ ∧ R s'.mem (AM.st op a₀) ∧ AM.res op a₀ = dec (r.headD 0)` of the stores'
and walks' `…_refines`. -/
theorem Sim.tripleD {α : Type} [Inhabited α] {prog : M (List Word)} {s₀ : St}
    {mo : Option (Word × Mem)} {dec : Word → α} {op : AM α} {a₀ : AState} {R : Mem → AState → Prop}
    (hspec : ⦃fun s => s = s₀⦄ prog ⦃fun r s' => LocEq s' s₀ ∧ mo = some (r.headD 0, s'.mem); ⊤⦄)
    (hsim : SimD dec mo op a₀ R) :
    ⦃fun s => s = s₀⦄ prog
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok op a₀ ∧ R s'.mem (AM.st op a₀) ∧
      AM.res op a₀ = dec (r.headD 0); ⊤⦄ :=
  M.triple_of_run fun _ _ _ hs hrun => by
    obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
    obtain ⟨hok, e, hR⟩ := hsim.run hI
    exact ⟨hloc, hok, hR, e⟩

/-! ## Peeling a returned model (hypotheses `model = some …`) -/

/-- **One callee off a model's continuation**: if `K o` returned, `o` returned some `x` and the
continuation of `x` returned (`obtain ⟨⟨r, m⟩, hc, h⟩ := of_K h rfl`). -/
theorem of_K {β γ : Type} {K : Option β → Option γ} {o : Option β} {y : γ}
    (h : K o = some y) (hn : K none = none) : ∃ x, o = some x ∧ K (some x) = some y := by
  cases o with
  | none => rw [hn] at h; cases h
  | some x => exact ⟨x, rfl, h⟩

/-- **A failing guard** of a returned model: `(if c then none else e) = some y`. -/
theorem of_ite_none {γ : Type} {c : Prop} [Decidable c] {e : Option γ} {y : γ}
    (h : (if c then none else e) = some y) : ¬ c ∧ e = some y := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; cases h
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩

/-- **A passing guard** of a returned model: `(if c then e else none) = some y`. -/
theorem of_ite_none' {γ : Type} {c : Prop} [Decidable c] {e : Option γ} {y : γ}
    (h : (if c then e else none) = some y) : c ∧ e = some y := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact ⟨hc, h⟩
  · rw [ite_eq_right hc] at h; cases h

end L.Arena
