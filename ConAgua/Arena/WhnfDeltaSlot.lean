import ConAgua.Arena.WhnfCoreSlot
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The knot's `whnf` slot and the `whnf` loop

`whnf(mode, vis, d, e)` (`WhnfDelta.lean`) refines the `whnf` slot of `coreKnot mode fe id (F + 1)`:
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
      decide (e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8) := by
  have h : (e >>> 28).toNat < 2 ^ 32 := Nat.lt_trans (shr28_lt e he) (by decide)
  simp only [whnfStuckTag, decE_tag e he, ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit]
  rw [show (2 : UInt32) = (2 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (1 : UInt32) = (1 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (5 : UInt32) = (5 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (6 : UInt32) = (6 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (8 : UInt32) = (8 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  by_cases h2 : e >>> 28 = 2 <;> by_cases h1 : e >>> 28 = 1 <;> by_cases h5 : e >>> 28 = 5 <;>
    by_cases h6 : e >>> 28 = 6 <;> by_cases h8 : e >>> 28 = 8 <;> simp_all

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
  have nA : ∀ b : TieredArray, (b.arr < 96 ∨ 128 ≤ b.arr) → b ∉ ([A] : List TieredArray) := fun b hb h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h
    change A < 96 ∨ 128 ≤ A at hb; simp only [ArrId] at hA hb; omega
  have nC : ∀ x : Word, (x.toNat < 96 ∨ 128 ≤ x.toNat) → x ∉ [C] := fun x hx h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; omega
  have gA : ∀ b ∈ ([A] : List TieredArray), InHigh b := fun b h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h
    refine ⟨rfl, ?_⟩; show 64 ≤ A; simp only [ArrId] at hA ⊢; omega
  have gC : ∀ x ∈ [C], 64 ≤ x.toNat := fun x h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; omega
  have eA : AvoidA 129 144 ([A] : List TieredArray) := fun b h => .inl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h
    show A < 129; simp only [ArrId] at hA ⊢; omega)
  have eC : AvoidC 128 136 [C] := fun x h => .inl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; omega)
  have lf : LvlFree [C] := fun x hx => nC _ (by
    simp only [lvlCtlW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [A] [C] gA gC m m' hf a hS.arena.1),
      DerR.of_store _ _ _ (DerR.frameM [A] [C] m m' hf
        (fun b hb => by have := gA b hb; simp only [InHigh] at this; omega) a hS.arena.2) rfl⟩,
      hcore, hS.pins.congr (hf.arr PINS (nA _ (by decide)) (by decide)),
      hS.env.frame eA eC hf,
      fun h l e => hS.readL h l (h1 ▸ e), fun h l e => hS.readLs h l (h2 ▸ e), hS.nwf,
      hf.size EREC ▸ hS.erec, hf.size SPN ▸ hS.spn,
      hS.memos.frame hf ⟨nA _ (by decide), nA _ (by decide)⟩ ⟨nC _ (by decide), nC _ (by decide)⟩
        ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
        ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩
        ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
        ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩, hf.size BSTK ▸ hS.bstk,
      (hS.den.frameE (hf.arr EREC (nA _ (by decide)) (by decide))).caches rfl rfl h3,
      hS.mode.frame hf (nC _ (by decide)) (nC _ (by decide))⟩,
    StackKept.of_frame hf ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
      ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩ lf (nA _ (by decide)) (nA _ (by decide))⟩

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
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e : EIdx) (a : AState)

theorem knot_whnf_stuck (h : whnfStuckTag e = true) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a = .ok (e, a) := by
  simp [coreKnot, h]; rfl

theorem knot_whnf_hit (h : whnfStuckTag e = false) (x : EIdx)
    (hm : a.caches.whnfC[e]? = some x) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a = .ok (x, a) := by
  simp [coreKnot, h, hm]; rfl

theorem knot_whnf_miss (h : whnfStuckTag e = false)
    (hm : a.caches.whnfC[e]? = none) (x : EIdx) (a₁ : AState)
    (hb : (whnfBody (coreKnot mode fe id F) fe d e).run a = .ok (x, a₁)) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a =
      .ok (x, { a₁ with caches := { a₁.caches with
        whnfC := a₁.caches.whnfC.insert e x } }) := by
  simp [coreKnot, h, hm, StateT.run_bind, hb, whnfSet]; rfl

end twin

/-! ## The loop's twin runs -/

theorem whnfLoop_done (r : CoreFnsA) (fe : IFEnv) (d K : Nat) (e v : EIdx) (a a₁ : AState)
    (hs : (whnfStep r fe d e).run a = .ok (.done v, a₁)) :
    (whnfLoop r fe d (K + 1) e).run a = .ok (v, a₁) := by
  simp only [whnfLoop, StateT.run_bind, hs, except_ok_bind]; rfl

theorem whnfLoop_cont (r : CoreFnsA) (fe : IFEnv) (d K : Nat) (e e' : EIdx) (a a₁ : AState)
    (hs : (whnfStep r fe d e).run a = .ok (.cont e', a₁)) :
    (whnfLoop r fe d (K + 1) e).run a = (whnfLoop r fe d K e').run a₁ := by
  simp only [whnfLoop, StateT.run_bind, hs, except_ok_bind]

end L.Arena
