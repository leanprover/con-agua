module

import ConAgua.Arena.WhnfCoreSlot
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.DerRel
public import ConAgua.Arena.WhnfBase

@[expose] public section

/-!
# The knot's `whnf` slot and the `whnf` loop

`whnf(mode, vis, d, e)` (`WhnfDelta.lean`) refines the `whnf` slot of `coreKnot mode eager fe id (F + 1)`:
a stuck tag (`sort`/`fvar`/`lam`/`forallE`/`lit`, `whnfStuckTag`) answers `e` without touching the
memo or the store, a memo hit (`whnfC`, array 98, at the current generation) answers the entry, a
miss runs `whnf_loop` (the body, `whnfBody … (coreKnot … F)`), records it and answers it.

Here: the tags, the relation across the memo's `find; put`, the twin's slot and loop runs. The
refinements (`whnf_ref`, `wloop_ref`, `wstep_ref`) are in `WhnfSlotRefine.lean`, over the unified
models.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Tags -/

/-- `whnfStuckTag` off the handle word: `sort` (2), `fvar` (1), `lam` (5), `forallE` (6), `lit` (8). -/
theorem whnfStuck_iff (e : Word) (he : HW e) :
    whnfStuckTag (decE e) =
      decide (tagW e = 2 ∨ tagW e = 1 ∨ tagW e = 5 ∨ tagW e = 6 ∨ tagW e = 8) := by
  have h : (tagW e).toNat < 2 ^ 32 := Nat.lt_trans (tagW_lt e he) (by decide)
  simp only [whnfStuckTag, decE_tag e he, ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit]
  rw [show (2 : UInt32) = (2 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (1 : UInt32) = (1 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (5 : UInt32) = (5 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (6 : UInt32) = (6 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (8 : UInt32) = (8 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  by_cases h2 : tagW e = 2 <;> by_cases h1 : tagW e = 1 <;> by_cases h5 : tagW e = 5 <;>
    by_cases h6 : tagW e = 6 <;> by_cases h8 : tagW e = 8 <;> simp_all

/-! ## The relation across the `whnf` memo's `find; put` -/

/-- A memo's relation across a write of one other core memo (array `A`, stamp word `C`). -/
theorem MemoRV.frame1 {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey κ}
    {VR : Mem → Word → ν → Prop} {m m' : Mem} {mp : Std.HashMap κ ν} {A : ArrId} {C : Word}
    (hf : MemFrame [A] [C] m m') (h : MemoRV S K VR m mp)
    (hV : ∀ w v, VR m w v → VR m' w v := by exact fun _ _ h => h)
    (hS : S.WF := by exact coreSch_wf _ _ (by decide) (by decide)) (hA : S.arr ≠ A := by decide)
    (hC : S.cs ≠ C := by decide) : MemoRV S K VR m' mp :=
  memoRV_frame S hS K VR [A] [C] (by simpa using hA) (by simpa using hC) m m' hf hV mp h

/-- A mode memo's relation across a write of one other core memo. -/
theorem ModeR.frame1 {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {VR : Mem → Word → ν → Prop} {m m' : Mem} {M : Std.HashMap (κ × Word) ν} {eb : Word}
    {t te : Std.HashMap κ ν} {A : ArrId} {C : Word} (hf : MemFrame [A] [C] m m')
    (h : ModeR S K VR m M eb t te) (hV : VConst VR := by exact fun _ _ _ _ h => h)
    (hS : S.WF := by exact coreSch_wf _ _ (by decide) (by decide)) (hA : S.arr ≠ A := by decide)
    (hC : S.cs ≠ C := by decide) : ModeR S K VR m' M eb t te :=
  h.frame hS hV (by simpa using hA) (by simpa using hC) hf

/-- **`CoreS` across a write of one core memo** (array `A` and stamp word `C` in 96‥127), the core
tier at the new caches and maps given (the readback caches unchanged). -/
theorem CoreS.set_core {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M M' : ModeMaps} {eb : Word} {c : Caches} {A : ArrId} {C : Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame [A] [C] m m') (hcore : CoreRM m' c M' eb)
    (h1 : c.readLC = a.caches.readLC) (h2 : c.readLsC = a.caches.readLsC)
    (h3 : c.readNC = a.caches.readNC) (hA : 96 ≤ A ∧ A < 128 := by decide)
    (hC : 96 ≤ C.toNat ∧ C.toNat < 128 := by decide) :
    CoreS dn m' { a with caches := c } vis fe M' eb ∧ StackKept m m' := by
  sorry

/-- `whnfC` gains an entry (at `whSch`: array 98, `CTL` 100/101). -/
theorem CoreS.set_wh {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG whSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfC := a.caches.whnfC.insert (decE e) (decE x) } } vis fe
      { M with wh := M.wh.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [(WH : TieredArray)] [101] m m' := msetG_frame whSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have c := hS.core
  exact hS.set_core hf ⟨c.wc.frame1 hf, c.wk.frame1 hf,
    c.wh.setE (coreSch_wf _ _ (by decide) (by decide)) c.eb1 e x he hx m' hs, c.inf.frame1 hf,
    c.io.frame1 hf, c.de.frame1 hf, c.eb1, c.ct.frame1 hf, c.cv.frame1 hf, c.rr.frame1 hf,
    c.lq.frame1 hf, c.lsq.frame1 hf⟩ rfl rfl rfl

/-- `Kept0` across an insert in the eager bank `eb ≠ 0`. -/
theorem Kept0.insert {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] {M M' : Std.HashMap (κ × Word) ν}
    {eb : Word} (h : Kept0 M M') (h0 : eb ≠ 0) (k : κ) (v : ν) : Kept0 M (M'.insert (k, eb) v) :=
  fun k' => by
    rw [Std.HashMap.getElem?_insert]
    have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
    simp only [this, Bool.false_eq_true, ↓reduceIte]; exact h k'

/-- `KeptAll` across a `whnf` memo insert. -/
theorem KeptAll.wh {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with wh := M'.wh.insert (k, eb) v } eb := fun h0 =>
  let ⟨a1, b1, c1, d1, e1, f1⟩ := h h0; ⟨a1, b1, c1.insert h0 k v, d1, e1, f1⟩

/-! ## The twin's `whnf` slot -/

section twin
variable (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (F : Nat) (d : Nat) (e : EIdx) (a : AState)

theorem knot_whnf_stuck (h : whnfStuckTag e = true) :
    ((coreKnot mode eager fe id (F + 1)).whnf d e).run a = .ok (e, a) := by
  simp [coreKnot, h]; rfl

theorem knot_whnf_hit (h : whnfStuckTag e = false) (x : EIdx)
    (hm : a.caches.whnfC[e]? = some x) :
    ((coreKnot mode eager fe id (F + 1)).whnf d e).run a = .ok (x, a) := by
  simp [coreKnot, h, hm]; rfl

theorem knot_whnf_miss (h : whnfStuckTag e = false)
    (hm : a.caches.whnfC[e]? = none) (x : EIdx) (a₁ : AState)
    (hb : (whnfBody (coreKnot mode eager fe id F) fe d e).run a = .ok (x, a₁)) :
    ((coreKnot mode eager fe id (F + 1)).whnf d e).run a =
      .ok (x, { a₁ with caches := { a₁.caches with
        whnfC := a₁.caches.whnfC.insert e x } }) := by
  simp [coreKnot, h, hm, StateT.run_bind, hb, whnfSet]; rfl

end twin

end L.Arena
