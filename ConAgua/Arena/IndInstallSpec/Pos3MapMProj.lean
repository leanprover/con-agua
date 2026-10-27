import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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

/-- **`check_block_positivity_nfs_member` is its model `pnmW`** (generated). -/
l_model pnm_spec (p : Prog)
    (hp : p.lookup "check_block_positivity_nfs_member" = some checkBlockPositivityNfsMember)
  fns [hp ↦ pnmW]
  specs [callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-! ## `check_block_positivity_nfs` -/

/-- **`check_block_positivity_nfs` is its model `pnfW`** (generated). -/
l_model pnf_spec (p : Prog) (hp : p.lookup "check_block_positivity_nfs" = some checkBlockPositivityNfs)
  fns [hp ↦ pnfW]
  specs [callW_spec p n "check_block_positivity_nfs_member", callW_spec p n "rec2", callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

end L.Ind
