import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclPins

/-!
# The specs of phase A's step and phase B's check (`install_step_go`, `check_value_group`)

The two callees of the declaration loop's skeleton (`Checker.lean`) that `DeclStep.lean`
translates, with the specs the skeleton is proved from.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-! ## The loop's relation across a step's callee -/

/-- A grown pool keeps every record of the old one, inside the new pool's records. -/
theorem IWGrow.erecPExt {m m' : Mem} (h : L.Ind.IWGrow m m') : ArrExt (erecP m) (erecP m') := by
  intro i v hv
  have hv' := hv
  simp only [erecP, Array.getElem?_extract] at hv ⊢
  split at hv
  · rename_i hi
    simp only [Nat.zero_add] at hv ⊢
    have hi' : i < L.Ind.erTop m := by simp [L.Ind.erTop, erecTop] at hi ⊢; omega
    have h1 := h.2.1
    have h2 := h.2.2.2 i hi'
    rw [h2]
    have hs : i < (m'.arr64 EREC).size := by
      have := (Array.getElem?_eq_some_iff.mp (h2.trans hv)).1; exact this
    rw [ite_eq_left (by simp [L.Ind.erTop, erecTop] at h1 hi' ⊢; omega)]
    exact hv
  · simp at hv

/-- **The pending checks across a step's callee**: `PEND` and its count unchanged, the records
only extended. -/
theorem PendR.ext {m m' : Mem} {pend : Array PendingCheck} (hP : m'.arr64 PEND = m.arr64 PEND)
    (hc : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130) (hx : ArrExt (erecP m) (erecP m'))
    (h : PendR m pend) : PendR m' pend := by
  refine ⟨by simp only [pendCount, hc]; exact h.count, fun j hj => ?_,
    by simp only [pendCount, hc]; exact h.bound⟩
  have := h.recs j hj
  simp only [decPend, hP, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at this ⊢
  obtain ⟨g, hg, vg, hvg, p, hp, v, hv, he⟩ := this
  exact ⟨g, hg, vg, ArrExt.decVG hx hvg, p, hp, v, hv, he⟩

/-- **The loop's relation after a step's callee**: the stage relation after it (at any view and
environment), a frame of the step's write set (`stepA`, `stepC`: nothing of `PEND`, `DECL`,
`DLP`, `CTL[130]`), and the records only extended. -/
theorem step_keeps : PEND ∉ stepA ∧ DECL ∉ stepA ∧ DLP ∉ stepA ∧ (130 : Word) ∉ stepC := by
  decide +kernel

/-- The step's write set misses the pin variant list's header. -/
theorem step_pins : (150 : Word) ∉ stepC ∧ (151 : Word) ∉ stepC := by decide +kernel

/-- The step's write set misses the promotion memo (arrays 146‥149, `CTL` 140‥147). -/
theorem step_pmemo : (∀ b ∈ stepA, b < 146 ∨ 149 < b) ∧
    (∀ x ∈ stepC, x.toNat < 140 ∨ 147 < x.toNat) := by
  refine ⟨fun b hb => ?_, fun x hx => ?_⟩
  · simp only [stepA, List.mem_filter, decide_eq_true_eq] at hb; exact hb.2.2.2.2
  · simp only [stepC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨k, ⟨hk, -, -, -, hr⟩, rfl⟩ := hx
    rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]; exact hr

theorem LoopR.of_step {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis vis' : Word} {fe fe' : IFEnv}
    {pend : Array PendingCheck} {ds : Array IDeclaration} (h : LoopR pins dn m a vis fe pend ds)
    (hS : L.Ind.StageR dn vis' fe' m' a') (hf : MemFrame stepA stepC m m')
    (hx : ArrExt (erecP m) (erecP m')) : LoopR pins dn m' a' vis' fe' pend ds := by
  have hP : m'.arr64 PEND = m.arr64 PEND := hf.1 _ step_keeps.1 (by decide)
  have hD1 : m'.arr64 DECL = m.arr64 DECL := hf.1 _ step_keeps.2.1 (by decide)
  have hD2 : m'.arr64 DLP = m.arr64 DLP := hf.1 _ step_keeps.2.2.1 (by decide)
  have hc : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130 := hf.2.1 _ step_keeps.2.2.2
  exact ⟨hS.1, h.pend.ext hP hc hx, by rw [hD1, hD2]; exact h.decls, hS.2,
    h.pmemo.imp fun _ hq => hq.frame step_pmemo.1 step_pmemo.2 hf,
    PinSetsR.grow h.pinsets (RecGrow.of_ext h.iw hx) (hf.2.1 _ step_pins.1) (hf.2.1 _ step_pins.2)⟩

end L.Arena
