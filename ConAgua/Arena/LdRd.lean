module

public import ConAgua.Arena.SlotGrow
public import ConAgua.L.Logic

@[expose] public section

/-!
# A word load answering `rdW` (lane buildtime)

`vcgen`'s own unfolding of `ld64` leaves each read as `a[i.toNat]'h`, the bound hypothesis `h` a
proof argument inside the term: `simp` cannot rewrite under it, so the locals stay unnormalized
`setLoc` chains and `grind` crawls them. `ld64_rd_spec` answers `rdW` and leaves no bound
hypothesis behind (`L.Arena.ld64_rdW_spec`, `InferBodyIntern.lean`, keeps the bound).
-/

open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem ld64_rd_spec (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, by simp [rdW, h]⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

end L.Arena
