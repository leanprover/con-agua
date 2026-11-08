module

import ConAgua.Arena.DefEqStuckCert
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.DefEqStuck

@[expose] public section

/-!
# `struct_unit_cert` refines `structUnitCert` (lane `defeq`, helper `defeq-top`)

In L's pieces: `struct_unit_cert` (`a`'s type), `struct_unit_head` (its head, family and spine;
the record words read before any call after `env_find`, the twin's pure readers first),
`struct_unit_tail` (`b`'s type against it). One refinement per piece for both outcomes (`RefE`
over its unified model, `Verdict/WhnfModels7E.lean`): the errors are the knot's slots'.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin in L's pieces -/

/-- `structUnitCert` once the family is certified, copied. -/
def suTailT (r : CoreFnsA) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  if isForallE wtb then pure false
  else r.defeq depth wta wtb

/-- `structUnitCert` past `a`'s type `wta`, copied. -/
def suHeadT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel wta
  if hh.tag == ETag.const then
    view hh >>= fun v => match v with
      | .const T us' =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          let targs ← getAppArgs coreWalkFuel wta
          let reserved ← reservedBasisNames
          match ← viewLsLen us' with
          | none => failDanglingLs
          | some uslen =>
          if caps.unitlike = true ∧ reserved.contains T = false ∧
              targs.length = caps.unitParams ∧
              uslen = cvT.levelParams.length then
            suTailT r depth b wta
          else pure false
        | _ => pure false
      | _ => pure false
  else pure false

theorem structUnitCert_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    structUnitCert r fe depth a b = (do
      let ta ← r.inferIO depth a
      let wta ← r.whnf depth ta
      suHeadT r fe depth b wta) := by rfl

section headRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b wta : EIdx) (st : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel wta).run st = .ok (hh, st))

include hgaf

theorem suHead_nonconst (ht : (hh.tag == ETag.const) = false) :
    (suHeadT r fe depth b wta).run st = .ok (false, st) := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem suHead_other (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const T us'))
    (hf : ∀ cv caps, fe.find? T ≠ some (.indInfo cv caps)) :
    (suHeadT r fe depth b wta).run st = .ok (false, st) := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? T with _ | ⟨_ | _ | _ | ⟨cv, caps⟩ | _ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv caps)

theorem suHead_ind (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (targs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel wta).run st = .ok (targs, st)) {m : Mem}
    (hP : PinsFull m st.pins) (uslen : Nat) (hvl : st.store.lss.viewLen us' = some uslen) :
    (suHeadT r fe depth b wta).run st =
      (if caps.unitlike = true ∧ st.pins.reserved.contains T = false ∧
          targs.length = caps.unitParams ∧ uslen = cvT.levelParams.length then
        suTailT r depth b wta
      else pure false).run st := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    hargs, reservedBasisNames_run hP, viewLsLen_run, hvl]

end headRuns

/-! ## `struct_unit_tail` -/

/-- **`struct_unit_tail` refines `suTailT`, both outcomes**: the errors are the `infer_io`, `whnf`
and `defeq` slots'. -/
@[refines_part ConRon.Arena.structUnitCert "b's type against a's (suTailT)"]
theorem sut_ref (p : Prog) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    RefE (KnotUpToE p n) (sutE p (n + 1) s₀.mem mode vis d b wta)
      (suTailT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE b) (decE wta)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [sutE]
  unfold suTailT
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d b hF hn hs hb)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d b hF hn hs hb)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [sutE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁ h₁.resOk)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁
      h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  have hh2 : HW (r₂.headD 0) := h₂.resOk
  simp only [sutE.k_whnf, isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]
  by_cases h6 : tagW (r₂.headD 0) = 6
  · simp only [h6, decide_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl hw0)
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  rw [← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeq _ _ _)]
  exact RefE.bind_callE (fun _ => rfl) (hK.defeq F _ _ dn vis fe M₂ eb mode d wta _ hF hn hs₂ hwta hh2)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d wta _ hF hn
      hs₂ hwta hh2)
    fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩

/-! ## `struct_unit_head` -/

/-- The tests of `struct_unit_head`, all passed. -/
def uhOK (ul up lpn tn uslen : Word) (r : List Word) : Prop :=
  ul ≠ 0 ∧ r.headD 0 = 0 ∧ tn = up ∧ uslen = lpn

/-- **`struct_unit_head` refines `suHeadT`, both outcomes** (the top put back): the errors are
`struct_unit_tail`'s. -/
@[refines_part ConRon.Arena.structUnitCert "a's type's head, family and spine (suHeadT)"]
theorem suh_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    RefE (KnotUpToE p n) (suhE p (n + 1) s₀.mem mode vis d b wta)
      (suHeadT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE b) (decE wta)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

/-! ## `struct_unit_cert` -/

/-- **`struct_unit_cert` refines `structUnitCert`, both outcomes**: the errors are the `infer_io`,
`whnf` slots' and `struct_unit_head`'s. -/
theorem suc_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (sucE p (n + 1) s₀.mem mode vis d a b)
      (structUnitCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [sucE]
  rw [structUnitCert_eq]
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [sucE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁ h₁.resOk)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁
      h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [sucE.k_whnf]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (suh_ref p hq hc N (hk.mono (Nat.le_succ N)) F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d b
      (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb h₂.resOk)

/-- **`struct_unit_cert` refines `structUnitCert`** at the knot (`suc_ref`'s ok half). -/
@[refines ConRon.Arena.structUnitCert]
theorem suCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (sucE_spec p hq.sunit hq.suHead hq.suTail (n + 1) s₀ mode vis d a b)
    (suc_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
