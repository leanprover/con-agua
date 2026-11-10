module

public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.L.Examples
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndIface

@[expose] public section

/-!
# Pos3MapMProj

`decNFS`, `decKSS`, `pos3_mapM_proj`, `pos3_decPL_proj`, `pnm_spec`, `pnmW`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decoders of the results -/

/-- A member's normal forms: a pointer to `[off, len]` of handles. -/
def decNFS (m : Mem) (q : Nat) : Option (List EIdx) := decAt m (fun o l => decHL m o l) q

/-- A member's kinds: a pointer to `[off, len]` of pointers to `[k.off, k.len]` kinds slices. -/
def decKSS (m : Mem) (q : Nat) : Option (List (List NestFieldKind)) :=
  decAt m (fun o l => decPL m (fun v => decAt m (decKL m) v) o l) q

theorem pos3_mapM_proj {α β γ : Type} (F : γ → Option α) (G : γ → Option β) (h : α → β)
    (hFG : ∀ c x, F c = some x → G c = some (h x)) :
    ∀ (L : List γ) (xs : List α), L.mapM F = some xs → L.mapM G = some (xs.map h)
  | [], xs, e => by simp at e; subst e; rfl
  | c :: L, xs, e => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at e ⊢
    obtain ⟨x, hx, ys, hys, rfl⟩ := e
    exact ⟨h x, hFG c x hx, ys.map h, pos3_mapM_proj F G h hFG L ys hys, rfl⟩

theorem pos3_decPL_proj {α β : Type} {m : Mem} {f : Nat → Option α} {g : Nat → Option β} (h : α → β)
    (hfg : ∀ v x, f v = some x → g v = some (h x)) {o l : Nat} {xs : List α}
    (e : decPL m f o l = some xs) : decPL m g o l = some (xs.map h) := by
  unfold decPL at e ⊢
  refine pos3_mapM_proj _ _ h (fun j x hx => ?_) _ _ e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, hx⟩ := hx
  exact ⟨v, hv, hfg v x hx⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `check_block_positivity_nfs` -/

end L.Ind
