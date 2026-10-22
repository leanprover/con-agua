import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndPos2SpecB

/-!
# Composing relational lemmas (lane `indproofs2`)

Lane `indproofs` measured ~19 proof lines per L line, two thirds in the relational lemmas: per
callee, `cases h : callee … with | none => … | some x => obtain …; rw [h, K_some] at h; obtain … :=
callee_ok …`, then the twin's run rewritten bind by bind. `Sim mo op a Q` packages one callee's
relational fact (its model result `mo` is simulated by the twin run `op` from `a`, with `Q` after);
`Sim.bindK` composes a model continuation (`K none = none`, `K (some (r, m₁)) = body r m₁`, the
template's continuation defs, both by `rfl`) with the twin's `>>=`, so a straight-line wrapper's
relational lemma is one `refine Sim.bindK rfl (fun _ _ => rfl) (callee_sim …) fun r x m₁ a₁ hQ => ?_`
per callee. Also here: the pieces every wrapper repeated (`pin_word(53)` as `zeroLevel`, the slice
bound below `2^64` from `IWOK`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **The model result `mo` is simulated by the twin run `op` from `a`**: if the model returns
`(r, m')`, the twin succeeds with some `x`, state `a'`, and `Q r x m' a'`. -/
def Sim {β α : Type} (mo : Option (β × Mem)) (op : AM α) (a : AState)
    (Q : β → α → Mem → AState → Prop) : Prop :=
  ∀ r m', mo = some (r, m') → ∃ x a', op.run a = .ok (x, a') ∧ Q r x m' a'

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

/-- **A twin-only step** (the model does nothing for it: a pin read, a pure computation): its run
from `a` is known. -/
theorem Sim.bind_twin {mo : Option (β × Mem)} {op : AM α} {g : α → AM δ} {a a₁ : AState} {x : α}
    {R : β → δ → Mem → AState → Prop} (hr : op.run a = .ok (x, a₁)) (h : Sim mo (g x) a₁ R) :
    Sim mo (op >>= g) a R := by
  intro r m' e
  obtain ⟨y, a₂, h2, hR⟩ := h r m' e
  exact ⟨y, a₂, by simp only [StateT.run_bind, hr]; exact h2, hR⟩

/-- Weaken the post. -/
theorem Sim.mono {mo : Option (β × Mem)} {op : AM α} {a : AState} {Q Q' : β → α → Mem → AState → Prop}
    (h : Sim mo op a Q) (hq : ∀ r x m a', Q r x m a' → Q' r x m a') : Sim mo op a Q' := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, hq _ _ _ _ h2⟩

/-- Rewrite the twin side. -/
theorem Sim.congr {mo : Option (β × Mem)} {op op' : AM α} {a : AState} {Q : β → α → Mem → AState → Prop}
    (h : Sim mo op a Q) (e : op = op') : Sim mo op' a Q := e ▸ h

/-- **The census form**: a model run that returned gives `AM.ok`, and the post at `AM.res`/`AM.st`. -/
theorem Sim.run [Inhabited α] {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} {r : β} {m' : Mem} (h : Sim mo op a Q) (hm : mo = some (r, m')) :
    AM.ok op a ∧ Q r (AM.res op a) m' (AM.st op a) := by
  obtain ⟨x, a', h1, h2⟩ := h r m' hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ h1
  exact ⟨hok, by rw [hst, hres]; exact h2⟩

end sim

/-! ## Pieces every wrapper repeated -/

/-- **`pin_word(53)` is `zeroLevel`** under the stage relation (the read leaves the memory). -/
theorem pinZero_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {z : Word} (hS : StageR dn vis fe m a) (hz : pinWordV m 53 = some z) :
    zeroLevel.run a = .ok (decI z, a) ∧ H z := by
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by intro h0; simp [pinWordV, h0] at hz
  have hz' : z = pinW m 53 := by
    simp only [pinWordV, hpne, if_false, Option.some.injEq] at hz; rw [← hz]; rfl
  have hfull := hS.1.pins.full hpne
  subst hz'
  exact ⟨pinZeroLevel_run hfull, hfull.lv_lt.2.1⟩

/-- A slice below the pool's top has its end below `2^64` (`IWOK`). -/
theorem StageR.lt64 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR dn vis fe m a) {x : Nat} (h : x ≤ iwTop m) : x < 2 ^ 64 := by
  obtain ⟨h1, -, h3, -, -⟩ := hS.2; omega

end L.Ind
