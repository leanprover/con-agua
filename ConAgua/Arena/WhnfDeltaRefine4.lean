module

public import ConAgua.Arena.WhnfDeltaRefine3
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic

@[expose] public section

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 4 (`reduce_nat`'s dispatch, `whnf_step`)

Split from `WhnfDeltaRefine.lean`. The dispatch's twin pieces; `reduce_nat`'s refinement (both
outcomes, `reduceNat_refines`) is `Verdict/WhnfNatE.lean`'s.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `reduce_nat`: the dispatch -/

/-- The `.const c us` arm of `reduceNat`'s `match ← view f`. -/
def redConstT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us : LsIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let el ← emptyLevels
  if us != el then pure none else redSuccT r fe depth c b

/-- The `.app g a` arm of `reduceNat`'s `match ← view f`. -/
def redAppT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g a b : EIdx) : AM (Option EIdx) := do
  if g.tag == ETag.const then
    match ← view g with
    | .const c us => do
      let el ← emptyLevels
      if us != el then pure none else redBinT r fe depth c a b
    | _ => pure none
  else pure none

/-- `reduceNat` past the application node. -/
def redHeadT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) : AM (Option EIdx) := do
  match ← view f with
  | .const c us => redConstT r fe depth c us b
  | .app g a => redAppT r fe depth g a b
  | _ => pure none

theorem bne_and_bne (x y : Word) : ((x != 0) && (y != 0)) = decide (x ≠ 0 ∧ y ≠ 0) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

theorem view_nca (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : TRec) (hv : viewOK m h c)
    (hcg : (tagW h = 0 ∧ c = BVAR) ∨ (tagW h = 1 ∧ c = FVAR) ∨ (tagW h = 2 ∧ c = SORT) ∨
      (tagW h = 5 ∧ c = LAM) ∨ (tagW h = 6 ∧ c = FORALL) ∨ (tagW h = 7 ∧ c = LET) ∨
      (tagW h = 8 ∧ c = LIT) ∨ (tagW h = 9 ∧ c = PROJ)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ c us, v ≠ .const c us) ∧ (∀ g x, v ≠ .app g x) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨l, hw⟩ := view_lit m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩

/-- `ReduceNatSpec` with the L fuel bounded by the `2^62` that the knot's `whnf` slot needs. -/
def ReduceNatSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decOptR s₀ a₀ dn vis fe MM eb
      ResW

/-- `whnf_step(mode, vis, d, e)` refines `whnfStep` at every knot fuel `F ≥ n`, given `KnotUpTo p n`
and the fuel bound `n ≤ 2 ^ 62` (the knot's slots need it). -/
def WhnfStepSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decStep s₀ a₀ dn vis fe MM eb
      ResW

end L.Arena
