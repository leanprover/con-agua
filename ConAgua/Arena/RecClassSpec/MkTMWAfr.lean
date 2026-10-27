import ConAgua.Arena.RecCheckSpec.TargetMajorAt2

/-!
# MkTMWAfr

`mkTMW_afr`, `tmdW_afr`, `tmaW_afr`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem mkTMW_afr {m m' : Mem} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word} {r : List Word}
    (h : mkTMW m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = some (r, m')) : AFr m m' := by
  simp only [mkTMW] at h
  split at h; · cases h
  rename_i q m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr h1).trans (by simp only [tmWr]; afr_set)

theorem tmdW_afr {m m' : Mem} {r : List Word} (h : tmdW m = some (r, m')) : AFr m m' := by
  simp only [tmdW, tmdK1.eq_def, tmdK2.eq_def, tmdK3.eq_def] at h
  afr_auto h [naF_afr, mkTMW_afr]

theorem tmaW_afr {n : Nat} {m m' : Mem} {mo ml c : Word} {r : List Word} (h : tmaW n m mo ml c = some (r, m')) :
    AFr m m' := by
  rcases n with _ | n
  · simp [tmaW] at h
  simp only [tmaW, tmaK.eq_def] at h
  cases n <;> simp only [fuelW] at h <;> afr_auto h [tmdW_afr]

end sims

end L.Ind

end
