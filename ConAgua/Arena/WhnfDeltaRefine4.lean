import ConAgua.Arena.CoreNatOp
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 4 (`reduce_nat`'s dispatch, `whnf_step`)

Split from `WhnfDeltaRefine.lean`.
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

/-! ## `whnf_step` -/

/-- The model of `whnf_step`: `(flag, result, memory)`. -/
def whnfStepW (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word) : Option (Word × Word × Mem) :=
  match callW p n "whnf_core" [mode, 0, vis, d, e] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 ≠ 0 then some (1, r₂.tail.headD 0, m₂)
  else
  match callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₃.headD 0 ≠ 0 then some (1, r₃.tail.headD 0, m₃) else some (0, r₁.headD 0, m₃)

theorem whnfStep_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_step" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      whnfStepW p n s₀.mem mode vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.whnfStep]
  simp only [callFn, whnfStepL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "whnf_core", callW_spec p n "reduce_nat", callW_spec p n "unfold_definition"] <;>
  simp_all [whnfStepW, Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem whnfStep_run_nat (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ e₂ : EIdx) (a a₁ a₂ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (some e₂, a₂)) :
    (whnfStep r fe depth e).run a = .ok (.cont e₂, a₂) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr]; rfl

theorem whnfStep_run_unf (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ e₂ : EIdx) (a a₁ a₂ a₃ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (none, a₂))
    (hu : (unfoldDefinition fe e₁).run a₂ = .ok (some e₂, a₃)) :
    (whnfStep r fe depth e).run a = .ok (.cont e₂, a₃) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr, hu]; rfl

theorem whnfStep_run_done (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ : EIdx) (a a₁ a₂ a₃ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (none, a₂))
    (hu : (unfoldDefinition fe e₁).run a₂ = .ok (none, a₃)) :
    (whnfStep r fe depth e).run a = .ok (.done e₁, a₃) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr, hu]; rfl

/-- `WhnfStepSpec` with the fuel bound `n ≤ 2 ^ 62` (the knot's slots need it). -/
def WhnfStepSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decStep s₀ a₀ dn vis fe MM eb
      ResW

section refs25
variable (p : Prog)

theorem whnfStep_refines' (hp : WhnfDeltaProg' p) (hlp : InstLPOK p) (n : Nat)
    (hrn : ∀ k, k ≤ n → ReduceNatSpec' p k) : WhnfStepSpec' p n := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk
  have hC := hS.rel
  apply CoreSpec.of_call
  intro r m' h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (whnfStep_spec p hp.toWhnfDeltaProg n s₀ mode vis d e) h
  unfold whnfStepW at hW
  have hkn : KnotOK p n := hk n (by omega)
  cases h1 : callW p n "whnf_core" [mode, 0, vis, d, e] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnfCore F s₀ a₀ dn vis fe MM eb mode 0 d e (by omega) (by omega) hS he) h1
  rw [show ((0 : Word) != 0) = false from rfl] at hok1 hS₁ hres1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnfCore false d.toNat (decE e)) a₀ = a₁ at hrun1 hS₁
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  cases h2 : callW p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW
    (hrn n (by omega) F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega)
      hSP1 hrw1 (hk.mono (by omega))) h2
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  generalize AM.st (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₁.headD 0))) a₁ = a₂ at hrun2 hS₂
  by_cases hf2 : r₂.headD 0 ≠ 0
  · rw [ite_eq_left hf2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hsome : decOptR r₂ = some (decE (r₂.tail.headD 0)) := by simp only [decOptR, decOpt, ite_eq_right hf2]
    rw [hsome] at hrun2
    have hz := whnfStep_run_nat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) _ a₀ a₁ a₂
      (by rw [hrun1]; rfl) hrun2
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩
    · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
    · unfold ResW at hrw2 ⊢; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw2.2⟩
  rw [ite_eq_right hf2] at hW
  have hnone : decOptR r₂ = none := by simp only [decOptR, decOpt]; rw [ite_eq_left (by simpa using hf2)]
  rw [hnone] at hrun2
  have hSP2 : SlotPre ⟨m₂, Locals.init []⟩ a₂ dn vis fe M₂ eb mode := ⟨hS₂, hS.mode4, hS.eb_mode⟩
  cases h3 : callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (unfoldDefinition_refines' p hp n ⟨m₂, Locals.init []⟩ a₂ dn vis fe M₂ eb (r₁.headD 0) hS₂ hrw1 hlp) h3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st (unfoldDefinition fe (decE (r₁.headD 0))) a₂ = a₃ at hrun3 hS₃
  by_cases hf3 : r₃.headD 0 ≠ 0
  · rw [ite_eq_left hf3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hsome : decOptR r₃ = some (decE (r₃.tail.headD 0)) := by simp only [decOptR, decOpt, ite_eq_right hf3]
    rw [hsome] at hrun3
    have hz := whnfStep_run_unf (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) _ a₀ a₁ a₂ a₃
      (by rw [hrun1]; rfl) hrun2 hrun3
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩
    · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
    · unfold ResW at hrw3 ⊢; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw3.2⟩
  rw [ite_eq_right hf3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hnone3 : decOptR r₃ = none := by simp only [decOptR, decOpt]; rw [ite_eq_left (by simpa using hf3)]
  rw [hnone3] at hrun3
  have hz := whnfStep_run_done (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) a₀ a₁ a₂ a₃
    (by rw [hrun1]; rfl) hrun2 hrun3
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩
  · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
  · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw1⟩

end refs25

end L.Arena
