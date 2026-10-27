import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndStubs

/-!
# Composing relational lemmas (lane `indproofs2`)

Lane `indproofs` measured ~19 proof lines per L line, two thirds in the relational lemmas: per
callee, `cases h : callee … with | none => … | some x => obtain …; rw [h, K_some] at h; obtain … :=
callee_ok …`, then the twin's run rewritten bind by bind. `Sim mo op a Q` (`SimLib.lean`) packages one callee's
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

/-! ## Pieces every wrapper repeated -/

/-- **`pin_word(53)` is `zeroLevel`** under the stage relation (the read leaves the memory). -/
theorem pinZero_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {z : Word} (hS : StageR dn vis fe m a) (hz : pinWordV m 53 = some z) :
    zeroLevel.run a = .ok (decI z, a) ∧ H z := by
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by intro h0; simp [pinWordV, h0] at hz
  have hz' : z = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hz; rw [← hz]; rfl
  have hfull := hS.1.pins.full hpne
  subst hz'
  exact ⟨pinZeroLevel_run hfull, hfull.lv_lt.2.1⟩

/-- A slice below the pool's top has its end below `2^64` (`IWOK`). -/
theorem StageR.lt64 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR dn vis fe m a) {x : Nat} (h : x ≤ iwTop m) : x < 2 ^ 64 := by
  obtain ⟨h1, -, h3, -, -⟩ := hS.2; omega

/-- A memory fact of the model's result, added to a `Sim`'s post. -/
theorem _root_.L.Arena.Sim.withFr {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} {F : Mem → Prop}
    (h : Sim mo op a Q) (hf : ∀ r m', mo = some (r, m') → F m') :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ F m') := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, hf r m' e⟩

end L.Ind
