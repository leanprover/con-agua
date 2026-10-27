import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.IndRealNames

/-!
# `AFr` in model chains (`RSim`) (lane `indproofs4`, helper `abs`)

Kept apart from `IndRealAbs.lean`: `RecSim` and `IndRealNames` bring `L.Ind.fuelW` and a second
`inferTypeCore_spec` into the declaration files, whose names then clash.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem recW_afr {m m' : Mem} {k : Word} {ws r : List Word} (h : recW m k ws = some (r, m')) :
    AFr m m' := by
  simp only [recW] at h
  split at h; · cases h
  rename_i q m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr h1).trans (AFr.of_frame (wrIW_frame _ _ _))

theorem naF_afr {m m' : Mem} {args r : List Word} (h : naF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (naF_frame h)

/-- An `AFr` fact added to a model chain's post. -/
theorem RSim.withF {β α : Type} {o : Option β} {op : AM α} {a : AState} {Q : β → AState → α → Prop}
    {F : β → Prop} (h : RSim o op a Q) (hf : ∀ b, o = some b → F b) :
    RSim o op a (fun b a' x => Q b a' x ∧ F b) := fun b hb =>
  let ⟨x, a', h1, h2⟩ := h b hb
  ⟨x, a', h1, h2, hf b hb⟩

end L.Ind
