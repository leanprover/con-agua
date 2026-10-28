import ConAgua.Arena.WhnfDeltaRefine3
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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

theorem reduceNat_head_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b : EIdx) (a : AState)
    (h : (e.tag == ETag.app) = true) (hv : a.store.view e = some (.app f b)) :
    (reduceNat r fe depth e).run a = (redHeadT r fe depth f b).run a := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, redHeadT,
    redConstT, redSuccT, redAppT, redBinT, redOpT, redWfT]
  rfl

theorem redHead_other (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) (a : AState)
    (v : ENodeView) (hvf : a.store.view f = some v) (hc : ∀ c us, v ≠ .const c us)
    (hp : ∀ g x, v ≠ .app g x) : (redHeadT r fe depth f b).run a = .ok (none, a) := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]
  cases v with
  | const c us => exact absurd rfl (hc c us)
  | app g x => exact absurd rfl (hp g x)
  | _ => rfl

theorem redHead_const (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) (a : AState)
    (c : NIdx) (us : LsIdx) (hvf : a.store.view f = some (.const c us)) :
    (redHeadT r fe depth f b).run a = (redConstT r fe depth c us b).run a := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]

theorem redHead_app (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b g x : EIdx) (a : AState)
    (hvf : a.store.view f = some (.app g x)) :
    (redHeadT r fe depth f b).run a = (redAppT r fe depth g x b).run a := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]

theorem redConst_ne (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us el : LsIdx) (b : EIdx)
    (a : AState) (hel : emptyLevels.run a = .ok (el, a)) (hne : (us != el) = true) :
    (redConstT r fe depth c us b).run a = .ok (none, a) := by
  simp only [redConstT, StateT.run_bind, hel, except_ok_bind, hne]; rfl

theorem redConst_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us el : LsIdx) (b : EIdx)
    (a : AState) (hel : emptyLevels.run a = .ok (el, a)) (heq : (us != el) = false) :
    (redConstT r fe depth c us b).run a = (redSuccT r fe depth c b).run a := by
  simp only [redConstT, StateT.run_bind, hel, except_ok_bind, heq]; rfl

theorem redApp_notconst (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (hg : (g.tag == ETag.const) = false) : (redAppT r fe depth g x b).run a = .ok (none, a) := by
  simp only [redAppT, hg]; rfl

theorem redApp_ne (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (hg : (g.tag == ETag.const) = true)
    (hv : a.store.view g = some (.const c us)) (hel : emptyLevels.run a = .ok (el, a))
    (hne : (us != el) = true) : (redAppT r fe depth g x b).run a = .ok (none, a) := by
  simp only [redAppT, hg, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hel, hne]; rfl

theorem redApp_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (hg : (g.tag == ETag.const) = true)
    (hv : a.store.view g = some (.const c us)) (hel : emptyLevels.run a = .ok (el, a))
    (heq : (us != el) = false) :
    (redAppT r fe depth g x b).run a = (redBinT r fe depth c x b).run a := by
  simp only [redAppT, hg, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hel, heq]; rfl

theorem natOpStored_run_pure (fe : IFEnv) (c : NIdx) (a : AState) :
    ∃ b, (natOpStored fe c).run a = .ok (b, a) := by
  unfold natOpStored
  cases fe.find? c with
  | none => exact ⟨false, rfl⟩
  | some ci => cases ci <;> exact ⟨_, rfl⟩

theorem bne_and_bne (x y : Word) : ((x != 0) && (y != 0)) = decide (x ≠ 0 ∧ y ≠ 0) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

theorem view_nca (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : TRec) (hv : viewOK m h c)
    (hcg : (h >>> 28 = 0 ∧ c = BVAR) ∨ (h >>> 28 = 1 ∧ c = FVAR) ∨ (h >>> 28 = 2 ∧ c = SORT) ∨
      (h >>> 28 = 5 ∧ c = LAM) ∨ (h >>> 28 = 6 ∧ c = FORALL) ∨ (h >>> 28 = 7 ∧ c = LET) ∨
      (h >>> 28 = 8 ∧ c = LIT) ∨ (h >>> 28 = 9 ∧ c = PROJ)) :
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
