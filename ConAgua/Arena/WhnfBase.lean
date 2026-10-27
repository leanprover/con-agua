import ConAgua.Arena.NatArms
import ConAgua.Arena.LevelArena
import ConAgua.Arena.StoreDen
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The whnf family's shared statements: arguments, the spine stack, the relation, the knot

Everything the L code of `whnfCore`/`whnf` and their arms (`WhnfSpine.lean`, `WhnfCore.lean`,
`WhnfDelta.lean`, `WhnfIota.lean`) is stated against.

**Arguments.** The twin's bodies take `mode : CheckMode`, the knot record `r : CoreFnsA`, the
environment view `fe : IFEnv` and `depth : Nat`. In L: a mode word (`decMode`: `0` verified, `1`
trusted, `2` verified-eager, `3` trusted-eager; bit 0 is "trusted", bit 1 "eager"), the view word
`vis` (`EnvR dn m vis fe`), the depth word; the record is the program itself (the knot's slots
are L functions, `whnf_core`, `whnf`, `infer`, `infer_io`, `defeq`), tied at the twin's knot
`coreKnot mode fe id F` for every `F` at or above the L fuel (the `GoOK` shape of `WalkRefine`).

**The spine stack.** The twin's `Array EIdx`/`List EIdx` values (spines, accumulators, rule
arguments) live in the word array `SPN` (144) as slices `(off, cnt)`; `CTL[136]` is the top.
A function that needs room pushes above the top and puts the top back before it returns
(`StackKept`); one that returns a slice leaves it at the old top (`StackGrew`). `SpineR m off len
xs`: the slice denotes `xs` (handle words, each below `2^32`). Overflow is an `abort` (a
capacity, as every table's).

**The relation.** `CoreS dn m a vis fe M eb`: `ArenaD`, the core tier at explicit maps
(`CoreRM`, so that an eager run can state that it keeps the plain banks), the filled pin table, the
environment. After a core run: `CoreAfter` (some maps that, inside the eager tower, keep the plain
banks, `KeptAll`, and the stack below the top).

**Callees.** The refinements take their callees' specs as a bundle (`WhnfCallees`); the knot
(`DefEqKnot.lean`) proves it, and the census-tagged theorems (`KnotTagged.lean`) use that.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## Arguments -/

/-- The mode word. -/
def decMode (w : Word) : ConLeche.CheckMode :=
  if w = 0 then .verified else if w = 1 then .trusted else if w = 2 then .verifiedEager
  else .trustedEager

/-- A handle word (an index `< 2^32` of any kind). -/
def HW (w : Word) : Prop := w.toNat < 2 ^ 32

/-- A `Bool` result word. -/
def decBool (r : List Word) : Bool := r.headD 0 != 0

/-- A handle result word. -/
def decH (r : List Word) : EIdx := decE (r.headD 0)

/-- An `Option EIdx` result: `(flag, handle)`. -/
def decOptR (r : List Word) : Option EIdx := decOpt (r.headD 0) (r.tail.headD 0)

/-- A `WhnfStep` result: `(0, e)` is `.done e`, `(1, e)` is `.cont e`. -/
def decStep (r : List Word) : WhnfStep :=
  if r.headD 0 = 0 then .done (decE (r.tail.headD 0)) else .cont (decE (r.tail.headD 0))

/-! ## The spine stack: array 144, top `CTL[136]` -/

abbrev SPN : ArrId := 144

/-- The stack top. -/
def spTop (m : Mem) : Word := rdW (m.arr64 CTL) 136

/-- Word `i` of the stack. -/
def spW (m : Mem) (i : Word) : Word := rdW (m.arr64 SPN) i

/-- **A slice of the stack denotes a handle array.** -/
structure SpineR (m : Mem) (off cnt : Word) (xs : Array EIdx) : Prop where
  size : xs.size = cnt.toNat
  bound : off.toNat + cnt.toNat ≤ (m.arr64 SPN).size
  lt : ∀ i : Nat, i < cnt.toNat → (spW m (off + i.toUInt64)).toNat < 2 ^ 32
  get : ∀ (i : Nat) (h : i < xs.size), xs[i] = decE (spW m (off + i.toUInt64))

/-! ### The binder stack and the limb pool across a core run

Every core run also keeps lane `defeq`'s binder stack (`BSTK`, array 145, top `CTL[137]`: only the
telescopes `infer_lams`/`infer_pis` push onto it, and they put the top back) and only appends to
the limb pool (`POOL` below the old top `CTL[0]` unchanged, the top no lower, the size the same:
the `Nat` arithmetic and the interning of literals, level lists and string names write above the
top). Both are fields of `StackKept`/`StackGrew`, so `CoreAfter` carries them (lane `whnf3`). -/

/-- The binder stack (lane `defeq`'s, `Infer.lean`). -/
abbrev BSTK : ArrId := 145

/-- The binder stack's top. -/
def bTop (m : Mem) : Word := rdW (m.arr64 CTL) 137

/-- The binder stack below its top is kept, and so is the top. -/
def BKept (m m' : Mem) : Prop :=
  bTop m' = bTop m ∧ (m'.arr64 BSTK).size = (m.arr64 BSTK).size ∧
    ∀ j : Word, j < bTop m → rdW (m'.arr64 BSTK) j = rdW (m.arr64 BSTK) j

theorem BKept.refl (m : Mem) : BKept m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem BKept.trans {m₁ m₂ m₃ : Mem} (h₁ : BKept m₁ m₂) (h₂ : BKept m₂ m₃) : BKept m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun j hj => (h₂.2.2 j (h₁.1 ▸ hj)).trans (h₁.2.2 j hj)⟩

theorem BKept.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : BSTK ∉ A) (hC : (137 : Word) ∉ C) : BKept m m' := by
  have hb : m'.arr64 BSTK = m.arr64 BSTK := hf.1 BSTK hA (by decide)
  exact ⟨hf.2.1 137 hC, by rw [hb], fun j _ => by rw [hb]⟩

/-- The `CTL` words of the level tables' counts (`succ` 6/7, `zero` 8/9, `max` 10/11, `imax`
12/13, `param` 14/15), the level-list table's (40/41) and the scratch flag (1). -/
def lvlCtlW : List Word := [1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 40, 41]

/-- A writer that avoids the level tables' counts and the scratch flag. -/
def LvlFree (C : List Word) : Prop := ∀ x ∈ lvlCtlW, x ∉ C

theorem LvlFree.intro {C : List Word} (h1 : (1 : Word) ∉ C) (h6 : (6 : Word) ∉ C)
    (h7 : (7 : Word) ∉ C) (h8 : (8 : Word) ∉ C) (h9 : (9 : Word) ∉ C) (h10 : (10 : Word) ∉ C)
    (h11 : (11 : Word) ∉ C) (h12 : (12 : Word) ∉ C) (h13 : (13 : Word) ∉ C) (h14 : (14 : Word) ∉ C)
    (h15 : (15 : Word) ∉ C) (h40 : (40 : Word) ∉ C) (h41 : (41 : Word) ∉ C) : LvlFree C := by
  intro x hx
  simp only [lvlCtlW, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- Decide `LvlFree C` for a concrete `C`, word by word. -/
macro "lvl_free" : tactic => `(tactic| exact LvlFree.intro (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide))

theorem LvlFree.of_ge {C : List Word} (hC : ∀ x ∈ C, 42 ≤ x.toNat) : LvlFree C := by
  intro x hx h
  have := hC x h
  simp only [lvlCtlW, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at this

/-- **The level tables only grow** (lane `defeq2`): the scratch flag is kept and no level table's
count drops, so a level handle `lv_node` accepts stays accepted (`lvNodeW_mono`). Part of
`PoolGrew` (the store's growth), so `CoreAfter` carries it. -/
structure LvlCnt (m m' : Mem) : Prop where
  flag : rdW (m'.arr64 CTL) 1 = rdW (m.arr64 CTL) 1
  cnt : ∀ x ∈ lvlCtlW, (rdW (m.arr64 CTL) x).toNat ≤ (rdW (m'.arr64 CTL) x).toNat

theorem LvlCnt.refl (m : Mem) : LvlCnt m m := ⟨rfl, fun _ _ => Nat.le_refl _⟩

theorem LvlCnt.trans {m₁ m₂ m₃ : Mem} (h₁ : LvlCnt m₁ m₂) (h₂ : LvlCnt m₂ m₃) : LvlCnt m₁ m₃ :=
  ⟨h₂.flag.trans h₁.flag, fun x hx => Nat.le_trans (h₁.cnt x hx) (h₂.cnt x hx)⟩

theorem LvlCnt.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hL : LvlFree C) : LvlCnt m m' :=
  ⟨hf.2.1 1 (hL 1 (by decide)), fun x hx => by rw [hf.2.1 x (hL x hx)]; exact Nat.le_refl _⟩

/-- **The limb pool only grew**: below the old top unchanged, the top no lower and in its tier
(lane tierpool: a tier-0 top stays below `2^40`), the capacity and the saved tier-0 top the same;
and the level tables only grew (`lvl`). -/
structure PoolGrew (m m' : Mem) : Prop where
  top : m.top.toNat ≤ m'.top.toNat
  size : pcap m' = pcap m
  below : Agree (vpool m') (vpool m) m.top.toNat
  lvl : LvlCnt m m'
  tier : m'.top.toNat < 2 ^ 40 ∨ 2 ^ 40 ≤ m.top.toNat
  pt0 : m'.ptop0 = m.ptop0

theorem PoolGrew.refl (m : Mem) : PoolGrew m m :=
  ⟨Nat.le_refl _, rfl, Agree.refl _ _, LvlCnt.refl m, by omega, rfl⟩

theorem PoolGrew.trans {m₁ m₂ m₃ : Mem} (h₁ : PoolGrew m₁ m₂) (h₂ : PoolGrew m₂ m₃) :
    PoolGrew m₁ m₃ :=
  ⟨Nat.le_trans h₁.top h₂.top, h₂.size.trans h₁.size,
    fun j hj => (h₂.below j (Nat.lt_of_lt_of_le hj h₁.top)).trans (h₁.below j hj),
    h₁.lvl.trans h₂.lvl, by have := h₁.tier; have := h₂.tier; omega, h₂.pt0.trans h₁.pt0⟩

/-- The pool's part of a frame: its two tier arrays and the saved tier-0 top kept, so `vpool`,
`pcap` and `ptop0`. -/
theorem PoolGrew.of_eq {m m' : Mem} (hp : m'.arr64 POOL = m.arr64 POOL)
    (hp1 : m'.arr64 POOL1 = m.arr64 POOL1) (hpt : m'.arr64 PT0 = m.arr64 PT0) (ht : m'.top = m.top)
    (hlc : LvlCnt m m') : PoolGrew m m' :=
  ⟨by rw [ht]; exact Nat.le_refl _, pcap_congr' hp hp1, fun j _ => by rw [vpool_congr hp hp1], hlc,
    by rw [ht]; omega, ptop0_congr hpt⟩

theorem PoolGrew.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : POOL ∉ A) (hC : (0 : Word) ∉ C) (hL : LvlFree C := by lvl_free)
    (hA1 : POOL1 ∉ A := by decide) (hA2 : PT0 ∉ A := by decide) : PoolGrew m m' :=
  PoolGrew.of_eq (hf.1 POOL hA (by decide)) (hf.1 POOL1 hA1 (by decide)) (hf.1 PT0 hA2 (by decide))
    (hf.top_eq hC) (LvlCnt.of_frame hf hL)

theorem PoolGrew.of_grows {m m' : Mem} (h : Grows m m') : PoolGrew m m' :=
  ⟨h.le, h.pcapEq, h.agree, LvlCnt.of_frame (grows_frame m m' h) (by lvl_free), h.tier,
    by have hf := grows_frame m m' h
       exact ptop0_congr (hf.1 PT0 (by decide) (by decide))⟩

/-- **The mode survives the pool's growth**: the flag is kept, a tier-0 top stays in tier 0. -/
theorem ModeOK.poolGrew {m m' : Mem} (h : ModeOK m) (hg : PoolGrew m m') : ModeOK m' := by
  have hfl : m'.flag = m.flag := hg.lvl.flag
  rcases h with h | h
  · exact .inl (by rw [hfl]; exact h)
  · rcases hg.tier with h' | h'
    · exact .inr h'
    · omega

/-- A slice in use stays in use across the pool's growth. -/
theorem SliceOK.poolGrew {m m' : Mem} {o l : Word} (h : SliceOK m o l) (hg : PoolGrew m m') :
    SliceOK m' o l := by
  obtain ⟨h1, h2⟩ := h
  have := hg.top; have := hg.tier
  refine ⟨by omega, ?_⟩
  rw [hg.pt0]; omega

theorem RSlice.poolGrew {m m' : Mem} {t o l : Word} (h : RSlice m t o l) (hg : PoolGrew m m') :
    RSlice m' t o l := ⟨h.1.poolGrew hg, h.2⟩

/-- The stack below the top is unchanged, and so is the top; the binder stack is kept and the
limb pool only grew. -/
structure StackKept (m m' : Mem) : Prop where
  top : spTop m' = spTop m
  size : (m'.arr64 SPN).size = (m.arr64 SPN).size
  below : ∀ i : Word, i < spTop m → spW m' i = spW m i
  bstk : BKept m m'
  pool : PoolGrew m m'

/-- The stack below the old top is unchanged; the top may have grown (a returned slice). The
binder stack is kept and the limb pool only grew. -/
structure StackGrew (m m' : Mem) : Prop where
  top : spTop m ≤ spTop m'
  size : (m'.arr64 SPN).size = (m.arr64 SPN).size
  below : ∀ i : Word, i < spTop m → spW m' i = spW m i
  bstk : BKept m m'
  pool : PoolGrew m m'

theorem StackKept.refl (m : Mem) : StackKept m m :=
  ⟨rfl, rfl, fun _ _ => rfl, BKept.refl m, PoolGrew.refl m⟩

theorem StackKept.trans {m₁ m₂ m₃ : Mem} (h₁ : StackKept m₁ m₂) (h₂ : StackKept m₂ m₃) :
    StackKept m₁ m₃ :=
  ⟨h₂.top.trans h₁.top, h₂.size.trans h₁.size,
    fun i hi => (h₂.below i (h₁.top ▸ hi)).trans (h₁.below i hi), h₁.bstk.trans h₂.bstk,
    h₁.pool.trans h₂.pool⟩

theorem StackGrew.refl (m : Mem) : StackGrew m m :=
  ⟨UInt64.le_refl _, rfl, fun _ _ => rfl, BKept.refl m, PoolGrew.refl m⟩

theorem StackGrew.trans {m₁ m₂ m₃ : Mem} (h₁ : StackGrew m₁ m₂) (h₂ : StackGrew m₂ m₃) :
    StackGrew m₁ m₃ :=
  ⟨UInt64.le_trans h₁.top h₂.top, h₂.size.trans h₁.size,
    fun i hi => (h₂.below i (UInt64.lt_of_lt_of_le hi h₁.top)).trans (h₁.below i hi),
    h₁.bstk.trans h₂.bstk, h₁.pool.trans h₂.pool⟩

theorem StackKept.toGrew {m₁ m₂ : Mem} (h : StackKept m₁ m₂) : StackGrew m₁ m₂ :=
  ⟨by rw [h.top]; exact UInt64.le_refl _, h.size, h.below, h.bstk, h.pool⟩

/-- **A writer of the spine stack alone** (a slice pushed above the top) grows the stack. -/
theorem StackGrew.of_spnFrame {m m' : Mem} (hf : MemFrame [SPN] [136] m m') (ht : spTop m ≤ spTop m')
    (hb : ∀ i : Word, i < spTop m → spW m' i = spW m i) : StackGrew m m' :=
  ⟨ht, hf.2.2.1 SPN, hb, BKept.of_frame hf (by decide) (by decide),
    PoolGrew.of_frame hf (by decide) (by decide)⟩

/-- **A writer of the spine stack alone** that puts the top back keeps the stack. -/
theorem StackKept.of_spnFrame {m m' : Mem} (hf : MemFrame [SPN] [136] m m') (ht : spTop m' = spTop m)
    (hb : ∀ i : Word, i < spTop m → spW m' i = spW m i) : StackKept m m' :=
  ⟨ht, hf.2.2.1 SPN, hb, BKept.of_frame hf (by decide) (by decide),
    PoolGrew.of_frame hf (by decide) (by decide)⟩

/-- **A frame that avoids both stacks and the pool keeps them.** -/
theorem StackKept.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : SPN ∉ A ∧ BSTK ∉ A ∧ POOL ∉ A := by decide)
    (hC : (136 : Word) ∉ C ∧ (137 : Word) ∉ C ∧ (0 : Word) ∉ C := by decide)
    (hL : LvlFree C := by lvl_free) (hA1 : POOL1 ∉ A := by decide) (hA2 : PT0 ∉ A := by decide) :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN hA.1 (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 hC.1
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn],
    BKept.of_frame hf hA.2.1 hC.2.1, PoolGrew.of_frame hf hA.2.2 hC.2.2 hL hA1 hA2⟩

/-- `StackKept.of_frame` for a writer of the level tables, their growth given (`hlc`). -/
theorem StackKept.of_frameL {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : SPN ∉ A ∧ BSTK ∉ A ∧ POOL ∉ A) (hC : (136 : Word) ∉ C ∧ (137 : Word) ∉ C ∧ (0 : Word) ∉ C)
    (hlc : LvlCnt m m') (hA1 : POOL1 ∉ A := by decide) (hA2 : PT0 ∉ A := by decide) :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN hA.1 (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 hC.1
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn],
    BKept.of_frame hf hA.2.1 hC.2.1,
    PoolGrew.of_eq (hf.1 POOL hA.2.2 (by decide)) (hf.1 POOL1 hA1 (by decide))
      (hf.1 PT0 hA2 (by decide)) (hf.top_eq hC.2.2) hlc⟩

/-- **A frame inside arrays 1‥143 and `CTL` words 1‥135** keeps the stacks and the pool. -/
theorem StackKept.of_frame_range {m m' : Mem} {A : List ArrId} {C : List Word}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, 1 ≤ b ∧ b < 144)
    (hC : ∀ x ∈ C, 1 ≤ x.toNat ∧ x.toNat < 136) (hL : LvlFree C := by lvl_free)
    (hA2 : PT0 ∉ A := by decide) : StackKept m m' :=
  StackKept.of_frame hf
    ⟨fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega,
     fun h => by have := hA _ h; simp only [BSTK, ArrId] at this; omega,
     fun h => by have := hA _ h; simp only [POOL, ArrId] at this; omega⟩
    ⟨fun h => by have := hC _ h; simp at this, fun h => by have := hC _ h; simp at this,
     fun h => by have := hC _ h; simp at this⟩ hL
    (fun h => by have := hA _ h; simp only [POOL1, ArrId] at this; omega) hA2

/-- **Appending to the pool** keeps the stacks. -/
theorem StackKept.of_grows {m m' : Mem} (hg : Grows m m') : StackKept m m' := by
  have hgf : MemFrame [POOL, POOL1] [0] m m' := grows_frame m m' hg
  have hspn : m'.arr64 SPN = m.arr64 SPN := hgf.1 SPN (by decide) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hgf.2.1 136 (by decide)
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn],
    BKept.of_frame hgf (by decide) (by decide), PoolGrew.of_grows hg⟩

/-- **A frame that avoids both stacks and appends to the pool** (`Grows` on the pool's part). -/
theorem StackKept.of_frame_grows {m m₁ m' : Mem} {A : List ArrId} {C : List Word}
    (hg : Grows m m₁) (hf : MemFrame A C m₁ m')
    (hA : SPN ∉ A ∧ BSTK ∉ A ∧ POOL ∉ A := by decide)
    (hC : (136 : Word) ∉ C ∧ (137 : Word) ∉ C ∧ (0 : Word) ∉ C := by decide)
    (hL : LvlFree C := by lvl_free) (hA1 : POOL1 ∉ A := by decide) (hA2 : PT0 ∉ A := by decide) :
    StackKept m m' := by
  exact (StackKept.of_grows hg).trans (StackKept.of_frame hf hA hC hL hA1 hA2)

/-! ## The relation the core runs under -/

/-- A map keeps its plain bank (eager bit `0`). -/
def Kept0 {κ ν : Type} [BEq κ] [Hashable κ] (M M' : Std.HashMap (κ × Word) ν) : Prop :=
  ∀ k : κ, M'[(k, (0 : Word))]? = M[(k, (0 : Word))]?

/-- **Inside the eager tower** (`eb ≠ 0`) a run keeps the six plain banks (the eager slot's saved
set); outside it nothing is promised (the twin tracks both sets in its state). -/
def KeptAll (M M' : ModeMaps) (eb : Word) : Prop :=
  eb ≠ 0 → Kept0 M.wc M'.wc ∧ Kept0 M.wk M'.wk ∧ Kept0 M.wh M'.wh ∧ Kept0 M.inf M'.inf ∧
    Kept0 M.io M'.io ∧ Kept0 M.de M'.de

theorem KeptAll.refl (M : ModeMaps) (eb : Word) : KeptAll M M eb :=
  fun _ => ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem KeptAll.trans {M₁ M₂ M₃ : ModeMaps} {eb : Word} (h₁ : KeptAll M₁ M₂ eb)
    (h₂ : KeptAll M₂ M₃ eb) : KeptAll M₁ M₃ eb := fun h => by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h₁ h
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h₂ h
  exact ⟨fun k => (a2 k).trans (a1 k), fun k => (b2 k).trans (b1 k), fun k => (c2 k).trans (c1 k),
    fun k => (d2 k).trans (d1 k), fun k => (e2 k).trans (e1 k), fun k => (f2 k).trans (f1 k)⟩

/-- The twin's name readback cache holds readbacks (as `ReadLCOK` for levels; `CoreS` has no such
field yet: `readNameM` answers a cached row without looking at the store). Used by lane `defeq`'s
`Knot.lean` and the `instLP` proofs. -/
def ReadNCOK (a : AState) : Prop :=
  ∀ (h : NIdx) (x : ConLeche.Name), a.caches.readNC[h]? = some x → denoteN a.store.ns h = some x

/-! ## The walk memos the core's walks reuse

`instantiateListFast` (`instLC`, array 50 `ILMEMO`, `CTL[50‥51]`) and `abstract1Fast`/
`abstractRangeFast` (`abs1C`, array 49 `ABMEMO`, `CTL[48‥49]`) clear their memo on entry and on
exit, so the twin's map never matters to a caller; but L's clear is an epoch bump, sound only on a
well-formed memo. `CoreMemos m`: both arrays hold a well-formed memo (of *some* map). A memory-only
invariant: it survives every writer that avoids the two arrays and their stamp words, whatever the
twin state does. -/

/-- `InstList.lean`'s `ilSch` (array 50, `CTL[50]`), restated here (`WhnfBase` does not import the
walks; `ilSch` unfolds to it). -/
abbrev coreIlSch : MemoSch := ⟨50, 50⟩
/-- `Abs1.lean`'s `abSch` (array 49, `CTL[48]`), restated here. -/
abbrev coreAbSch : MemoSch := ⟨49, 48⟩

/-- The walk-local memos of `wscopedBFast` (array 151, `CTL[152]`) and of `leafGuard`'s two walks
(`fvarLeavesGo`'s `seen`, array 152, `CTL[154]`; `leavesSubGo`'s memo, array 153, `CTL[156]`),
restated here (`WalkScope.lean`'s `wsSch`, `WalkLeaves.lean`'s `flSch`/`lsbSch` unfold to them). Each
walk clears its memo on entry (the twin starts from `∅`), so only well-formedness is carried. -/
abbrev coreWsSch : MemoSch := ⟨151, 152⟩
abbrev coreFlSch : MemoSch := ⟨152, 154⟩
abbrev coreLsbSch : MemoSch := ⟨153, 156⟩

/-- `InstLP.lean`'s three walk memos (`lpSch`, `lplSch`, `lplsSch`: arrays 52‥54, `CTL[54‥59]`),
restated here. -/
abbrev coreLpSch : MemoSch := ⟨52, 54⟩
abbrev coreLplSch : MemoSch := ⟨53, 56⟩
abbrev coreLplsSch : MemoSch := ⟨54, 58⟩

/-- A one-word level (or level-list) key: the handle word, second word `0`. -/
def ilKey {k : IdxKind} : MemoKey (Idx k) where
  dk k1 _ := decI k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by simp only [(word_decI _ k1 h.1).mpr rfl, h.2]
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- A level-valued memo's value relation: a handle word that denotes the entry. -/
def VI {k : IdxKind} (_ : Mem) (w : Word) (v : Idx k) : Prop := v = decI w ∧ w.toNat < 2 ^ 32

/-- **The `instLP` walk's memos are well formed** (at some maps): `inst_lp_core` clears them on
entry (an epoch bump, sound on a well-formed memo; the twin starts from `∅`). -/
def LPMemos (m : Mem) : Prop :=
  (∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRV coreLpSch lfKey VH m mp) ∧
  (∃ mp : Std.HashMap LIdx LIdx, MemoRV coreLplSch ilKey VI m mp) ∧
  (∃ mp : Std.HashMap LsIdx LsIdx, MemoRV coreLplsSch ilKey VI m mp)

theorem coreLpSch_wf : coreLpSch.WF := ⟨by decide, by decide⟩
theorem coreLplSch_wf : coreLplSch.WF := ⟨by decide, by decide⟩
theorem coreLplsSch_wf : coreLplsSch.WF := ⟨by decide, by decide⟩

/-- **`LPMemos` across a writer** that avoids arrays 52‥54 and `CTL` words 54, 56, 58. -/
theorem LPMemos.frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C) (h : LPMemos m) : LPMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1;
    ⟨mp, memoRV_frame coreLpSch coreLpSch_wf lfKey VH A C hA.1 hC.1 m m' hf (fun _ _ h => h) mp hm⟩,
    let ⟨mp, hm⟩ := h.2.1;
    ⟨mp, memoRV_frame coreLplSch coreLplSch_wf ilKey VI A C hA.2.1 hC.2.1 m m' hf (fun _ _ h => h) mp hm⟩,
    let ⟨mp, hm⟩ := h.2.2;
    ⟨mp, memoRV_frame coreLplsSch coreLplsSch_wf ilKey VI A C hA.2.2 hC.2.2 m m' hf (fun _ _ h => h) mp hm⟩⟩

/-- The walk-local memos are well formed (lane `whnf3`'s three, and the `instLP` walk's). -/
def WalkMemos (m : Mem) : Prop :=
  (∃ mp : Std.HashMap (EIdx × Nat) Bool, MemoRG coreWsSch lfKey (fun w => w != 0) m mp) ∧
    (∃ mp : Std.HashMap EIdx Unit, MemoRG coreFlSch bmKey (fun _ => ()) m mp) ∧
    (∃ mp : Std.HashMap EIdx Bool, MemoRG coreLsbSch bmKey (fun w => w != 0) m mp) ∧ LPMemos m

/-- The walk memos are well formed (`MemoRG` at some map). -/
def CoreMemos (m : Mem) : Prop :=
  (∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG coreIlSch lfKey decE m mp) ∧
    (∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG coreAbSch lfKey decE m mp) ∧ WalkMemos m

theorem coreIlSch_wf : coreIlSch.WF := ⟨by decide, by decide⟩
theorem coreAbSch_wf : coreAbSch.WF := ⟨by decide, by decide⟩
theorem coreWsSch_wf : coreWsSch.WF := ⟨by decide, by decide⟩
theorem coreFlSch_wf : coreFlSch.WF := ⟨by decide, by decide⟩
theorem coreLsbSch_wf : coreLsbSch.WF := ⟨by decide, by decide⟩

/-- **`WalkMemos` across a writer** that avoids arrays 151‥153 and `CTL` words 152, 154, 156. -/
theorem WalkMemos.frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C) (h : WalkMemos m)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide) : WalkMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1; ⟨mp, memoRG_frame coreWsSch coreWsSch_wf lfKey _ A C hA.1 hC.1 m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.1; ⟨mp, memoRG_frame coreFlSch coreFlSch_wf bmKey _ A C hA.2.1 hC.2.1 m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.2.1; ⟨mp, memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ A C hA.2.2 hC.2.2 m m' hf mp hm⟩,
    h.2.2.2.frame hf hLA hLC⟩

/-- **`CoreMemos` across a writer** that avoids arrays 49, 50, 151‥153 and `CTL` words 48, 50, 152,
154, 156 (the last two avoidances are auto-params: `decide` on concrete lists). -/
theorem CoreMemos.frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A) (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C) (h : CoreMemos m)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A := by decide)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide) :
    CoreMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1; ⟨mp, memoRG_frame coreIlSch coreIlSch_wf lfKey decE A C hA.1 hC.1 m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.1; ⟨mp, memoRG_frame coreAbSch coreAbSch_wf lfKey decE A C hA.2 hC.2 m m' hf mp hm⟩,
    h.2.2.frame hf hWA hWC hLA hLC⟩

/-- **`CoreMemos` across a write of the `instLP` walk's memos** (arrays 52‥54, `CTL[54‥59]`), the
walk memos after it given. -/
theorem CoreMemos.frameLP {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (h : CoreMemos m) (hLP : LPMemos m')
    (hA : ∀ b ∈ A, 52 ≤ b ∧ b ≤ 54 := by decide) (hC : ∀ x ∈ C, 54 ≤ x.toNat ∧ x.toNat ≤ 59 := by simp) :
    CoreMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1; ⟨mp, memoRG_frame coreIlSch coreIlSch_wf lfKey decE A C
      (fun e => absurd (hA _ e) (by decide)) (fun e => absurd (hC _ e) (by decide)) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.1; ⟨mp, memoRG_frame coreAbSch coreAbSch_wf lfKey decE A C
      (fun e => absurd (hA _ e) (by decide)) (fun e => absurd (hC _ e) (by decide)) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.2.1; ⟨mp, memoRG_frame coreWsSch coreWsSch_wf lfKey _ A C
      (fun e => absurd (hA _ e) (by decide)) (fun e => absurd (hC _ e) (by decide)) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.2.2.1; ⟨mp, memoRG_frame coreFlSch coreFlSch_wf bmKey _ A C
      (fun e => absurd (hA _ e) (by decide)) (fun e => absurd (hC _ e) (by decide)) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.2.2.2.1; ⟨mp, memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ A C
      (fun e => absurd (hA _ e) (by decide)) (fun e => absurd (hC _ e) (by decide)) m m' hf mp hm⟩,
    hLP⟩

/-- **`CoreMemos` across a writer at or above array 64** (and `CTL` word 64), away from the walk
memos (arrays 151‥153, `CTL` 152‥157). -/
theorem CoreMemos.frame_hi {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat) (h : CoreMemos m)
    (hWA : ∀ b ∈ A, b < 151 ∨ 153 < b := by decide)
    (hWC : ∀ x ∈ C, x.toNat < 152 ∨ 157 < x.toNat := by simp) : CoreMemos m' :=
  h.frame hf ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide)⟩
    ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩
    ⟨fun h => absurd (hWA _ h) (by decide), fun h => absurd (hWA _ h) (by decide),
      fun h => absurd (hWA _ h) (by decide)⟩
    ⟨fun h => absurd (hWC _ h) (by decide), fun h => absurd (hWC _ h) (by decide),
      fun h => absurd (hWC _ h) (by decide)⟩
    ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide),
      fun h => absurd (hA _ h) (by decide)⟩
    ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
      fun h => absurd (hC _ h) (by decide)⟩

/-- **The core's relation** at explicit cache maps. -/
structure CoreS (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word) : Prop where
  arena : ArenaD m a
  core : CoreRM m a.caches M eb
  pins : PinsFull m a.pins
  env : EnvR dn m vis fe
  /-- The twin's readback caches hold readbacks (L has no readback; the twin computes on them). -/
  readL : ReadLCOK a
  readLs : ReadLsCOK a
  /-- The name store is well formed (`denoteN` injective: names compared by word). -/
  nwf : NStoreWF a.store.lss.ls.ns
  /-- The record pool's size (a capacity checked at entry): record offsets do not wrap. -/
  erec : (m.arr64 EREC).size < 2 ^ 63
  /-- The spine stack's size (a capacity checked at entry): slice offsets do not wrap. -/
  spn : (m.arr64 SPN).size < 2 ^ 63
  /-- The walk memos `instLC`/`abs1C` are well formed (their walks clear them on entry). -/
  memos : CoreMemos m
  /-- The binder stack's size (lane `defeq`'s `BSTK`, array 145; a capacity checked at entry):
  its offsets do not wrap. -/
  bstk : (m.arr64 145).size < 2 ^ 63
  /-- **Stored levels read back** (`StoreDen.lean`, lane `defeq2`): what the level readers need,
  since the twin compares levels on their readbacks. -/
  den : StoreDen dn m a fe
  /-- **The pool's mode** (lane tierpool): outside the scratch tier the top is in tier 0, so the
  slices the core interns are tier-0 slices when the flag is off (`ModeOK.slice0`). -/
  mode : ModeOK m

/-- **The relation across a writer outside every tier and the spine stack**, the walk memos given
(`hmem`): arrays `≥ 145` (or the front's 64‥95), `CTL` words `≥ 137` (or 64‥95): the binder stack,
the level heap, the walk-local memos. -/
theorem CoreS.frameSM {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ (b < 96 ∨ 145 ≤ b) ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 137 ≤ x.toNat))
    (hmem : CoreMemos m') :
    CoreS dn m' a vis fe M eb := by
  have aA : ∀ lo hi : Nat, 96 ≤ lo → hi ≤ 145 → AvoidA lo hi A := fun lo hi h1 h2 b hb => by
    have := hA b hb; simp only [ArrId] at this ⊢; omega
  have aC : ∀ lo hi : Nat, 96 ≤ lo → hi ≤ 137 → AvoidC lo hi C := fun lo hi h1 h2 x hx => by
    have := hC x hx; omega
  exact ⟨⟨ArenaR.frame_ext A C (fun b hb => ⟨(hA b hb).1, (hA b hb).2.2⟩) (fun x hx => (hC x hx).1) m m'
        hf a hS.arena.1,
      DerR.frameM A C m m' hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
        a hS.arena.2⟩,
    hS.core.frame (aA 96 128 (by decide) (by decide)) (aC 96 128 (by decide) (by decide)) hf,
    hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp only [PINS, ArrId] at this; omega)
      (by decide)),
    hS.env.frame (aA 129 144 (by decide) (by decide)) (aC 128 136 (by decide) (by decide)) hf
      (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega),
    hS.readL, hS.readLs, hS.nwf, hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
    hmem, hf.2.2.1 145 ▸ hS.bstk,
    hS.den.frameE (hf.1 EREC (fun h => by have := hA _ h; simp only [EREC, ArrId] at this; omega)
      (by decide)),
    hS.mode.frame hf (fun h => by have := hC _ h; simp at this)
      (fun h => by have := hC _ h; simp at this)⟩

/-- `CoreS.frameSM` away from the walk-local memos (arrays 151‥153, `CTL` 152‥157). -/
theorem CoreS.frameS {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ (b < 96 ∨ 145 ≤ b) ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 137 ≤ x.toNat))
    (hWA : ∀ b ∈ A, b < 151 ∨ 153 < b := by decide)
    (hWC : ∀ x ∈ C, x.toNat < 152 ∨ 157 < x.toNat := by simp) :
    CoreS dn m' a vis fe M eb :=
  hS.frameSM hf hA hC (hS.memos.frame_hi hf (fun b hb => ⟨(hA b hb).1, (hA b hb).2.2⟩) (fun x hx => (hC x hx).1) hWA hWC)

/-- **The relation across a writer outside every tier and the stacks**, the walk memos given:
arrays `≥ 146` (or 64‥95), `CTL` words `≥ 138` (or 64‥95). The stacks and the pool are kept. -/
theorem CoreS.frameM {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ (b < 96 ∨ 146 ≤ b) ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 138 ≤ x.toNat))
    (hmem : CoreMemos m') :
    CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
  refine ⟨hS.frameSM hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
    (fun x hx => by have := hC x hx; omega) hmem, ?_⟩
  exact StackKept.of_frame hf
    ⟨fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega,
     fun h => by have := hA _ h; simp only [BSTK, ArrId] at this; omega,
     fun h => by have := hA _ h; simp only [POOL, ArrId] at this; omega⟩
    ⟨fun h => by have := hC _ h; simp at this, fun h => by have := hC _ h; simp at this,
     fun h => by have := hC _ h; simp at this⟩
    (LvlFree.of_ge fun x hx => by have := hC x hx; omega)
    (fun h => by have := hA _ h; simp only [POOL1, ArrId] at this; omega)
    (fun h => by have := hA _ h; simp only [PT0, ArrId] at this; omega)

/-- **The relation across a writer outside every tier and the stacks**, away from the walk-local
memos: the level heap (`LH`, `CTL[192]`), say. -/
theorem CoreS.frame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ (b < 96 ∨ 146 ≤ b) ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 138 ≤ x.toNat))
    (hWA : ∀ b ∈ A, b < 151 ∨ 153 < b := by decide)
    (hWC : ∀ x ∈ C, x.toNat < 152 ∨ 157 < x.toNat := by simp) :
    CoreS dn m' a vis fe M eb ∧ StackKept m m' :=
  hS.frameM hf hA hC (hS.memos.frame_hi hf (fun b hb => ⟨(hA b hb).1, (hA b hb).2.2⟩) (fun x hx => (hC x hx).1) hWA hWC)

/-- **After a core run** from `m₀` at maps `M`, `G`, generation `g`: the relation holds at some
maps that keep every other generation's bank, and the stack below the top is as it was. -/
def CoreAfter (dn : NIdx → Option ConLeche.Name) (m₀ m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) : Prop :=
  ∃ M', CoreS dn m a vis fe M' eb ∧ KeptAll M M' eb ∧ StackKept m₀ m

/-- Two core runs in a row. -/
theorem CoreAfter.trans {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m₂ : Mem} {a₁ a₂ : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (h₁ : CoreAfter dn m₀ m₁ a₁ vis fe M eb)
    (h₂ : ∀ M', CoreS dn m₁ a₁ vis fe M' eb → CoreAfter dn m₁ m₂ a₂ vis fe M' eb) :
    CoreAfter dn m₀ m₂ a₂ vis fe M eb := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁
  obtain ⟨M'', hS', hK', hSt'⟩ := h₂ M' hS
  exact ⟨M'', hS', hK.trans hK', hSt.trans hSt'⟩

/-- A core run after a core run, at the first run's maps. -/
theorem CoreAfter.comp {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m₂ : Mem} {a₂ : AState}
    {vis : Word} {fe : IFEnv} {M M' : ModeMaps} {eb : Word}
    (hK : KeptAll M M' eb) (hSt : StackKept m₀ m₁)
    (h₂ : CoreAfter dn m₁ m₂ a₂ vis fe M' eb) : CoreAfter dn m₀ m₂ a₂ vis fe M eb := by
  obtain ⟨M'', hS', hK', hSt'⟩ := h₂
  exact ⟨M'', hS', hK.trans hK', hSt.trans hSt'⟩

/-- The result word is below `2^32` (a handle, a `Bool`, a level answer): what `decE` needs to
be faithful when the caller computes with the word itself. The default validity of a result. -/
def ResH (r : List Word) : Prop := HW (r.headD 0)

/-- The first two result words are below `2^32` (an `Option EIdx`, a `WhnfStep`). -/
def ResW (r : List Word) : Prop := HW (r.headD 0) ∧ HW (r.tail.headD 0)

/-- **The refinement post of a core function**: the twin run `T` from `a₀` succeeds, the relation
holds after it, and the result words decode (`dec`) to its result. -/
def CoreRef {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m : Mem) (ok : List Word → Prop := ResH) : Prop :=
  AM.ok T a₀ ∧ CoreAfter dn m₀ m (AM.st T a₀) vis fe M eb ∧ AM.res T a₀ = dec r ∧ ok r



/-- The spec shape: from `s₀` under `CoreS`, the call refines `T`. -/
def CoreSpec {α : Type} [Inhabited α] (p : Prog) (n : Nat) (f : FnName) (args : List Word)
    (T : AM α) (dec : List Word → α) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop := ResH) : Prop :=
  ⦃fun s => s = s₀⦄
  invoke p (exec p n) f args
  ⦃fun r s' => LocEq s' s₀ ∧ CoreRef T a₀ dec dn s₀.mem vis fe M eb r s'.mem ok; ⊤⦄

/-! ## Calls as functions of the memory

A callee's run depends on the caller's memory alone (`callFn` starts a fresh frame), so it is a
function `callW p n f vs m`. Every call meets its own run (`callW_spec`); a callee's refinement
spec turns a run into the twin's (`CoreSpec.of_callW`). This lets a caller's word-level model
call its callees through `callW`, proved by `vcgen` + `finish` with `callW_spec` as the callee
spec, and its refinement use the callees' specs on those runs. -/

/-- The result of calling `f` on `vs` from memory `m`. -/
def callW (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (m : Mem) :
    Option (List Word × Mem) :=
  match (invoke p (exec p n) f vs).run ⟨m, Locals.init []⟩ with
  | .ok (r, s) => some (r, s.mem)
  | .error _ => none

theorem invoke_run_loc (p : Prog) (k : Stmt → M Sig) (f : FnName) (vs : List Word) (s : St) :
    (invoke p k f vs).run s =
      ((invoke p k f vs).run ⟨s.mem, Locals.init []⟩).map
        (fun (r, s') => (r, ({ s' with loc := s.loc } : St))) := by
  simp only [invoke, lookupFn]
  cases p.lookup f with
  | none => rfl
  | some fd =>
    simp only [callFn, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_modify]
    simp [Except.map]
    cases (k fd.body).run { mem := s.mem, loc := Locals.init vs } <;> rfl

/-- **Every call meets its own run.** -/
theorem callW_spec (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun r s' => LocEq s' s₀ ∧ callW p n f vs s₀.mem = some (r, s'.mem); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  rw [invoke_run_loc] at hrun
  simp only [callW]
  cases h : (invoke p (exec p n) f vs).run { mem := s.mem, loc := Locals.init [] } with
  | error e => simp [h, Except.map] at hrun
  | ok q =>
    simp [h, Except.map] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, rfl⟩

theorem callW_zero (p : Prog) (f : FnName) (vs : List Word) (m : Mem) : callW p 0 f vs m = none := by
  simp only [callW, invoke, lookupFn]
  cases p.lookup f with
  | none => rfl
  | some fd => rfl

/-- **A triple applies to a run**: the post holds of the run's result, at a state with the run's
memory and the caller's locals. -/
theorem triple_of_callW {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {Q : List Word → St → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => Q r s'; ⊤⦄)
    {r : List Word} {m' : Mem} (hc : callW p n f args s₀.mem = some (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' := by
  simp only [callW] at hc
  cases hr : (invoke p (exec p n) f args).run { mem := s₀.mem, loc := Locals.init [] } with
  | error e => simp [hr] at hc
  | ok q =>
    simp only [hr, Option.some.injEq] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    have hrun : (invoke p (exec p n) f args).run s₀ = .ok (q.1, { q.2 with loc := s₀.loc }) := by
      rw [invoke_run_loc, hr]; rfl
    exact ⟨{ q.2 with loc := s₀.loc }, rfl, L.M.of_run (P := fun s => s = s₀) rfl hrun h⟩

/-- **A refinement spec applies to a run.** -/
theorem CoreSpec.of_callW {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop}
    (h : CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok) {r : List Word} {m' : Mem}
    (hc : callW p n f args s₀.mem = some (r, m')) :
    CoreRef T a₀ dec dn s₀.mem vis fe M eb r m' ok := by
  simp only [callW] at hc
  cases hr : (invoke p (exec p n) f args).run { mem := s₀.mem, loc := Locals.init [] } with
  | error e => simp [hr] at hc
  | ok q =>
    simp only [hr, Option.some.injEq] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    have hrun : (invoke p (exec p n) f args).run s₀ = .ok (q.1, { q.2 with loc := s₀.loc }) := by
      rw [invoke_run_loc, hr]; rfl
    exact (L.M.of_run (P := fun s => s = s₀) rfl hrun h).2

/-! ## The knot's slots

`coreKnot mode fe id F` is the twin's record; the L slot at fuel `n` refines it at every
`F ≥ n`. The two `whnf` slots are this lane's (`WhnfCore.lean`, `WhnfDelta.lean`); `infer`,
`infer_io` and `defeq` are phases 6–7, stubs here. -/

/-- The common hypotheses of a slot call. -/
structure SlotPre (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) (mode : Word) : Prop where
  rel : CoreS dn s₀.mem a₀ vis fe M eb
  mode4 : mode < 4
  /-- The memos' eager bit is the mode's. -/
  eb_mode : eb = (mode >>> 1) &&& 1

/-- `whnf_core(mode, cheap, vis, d, e)` refines the knot's `whnfCore` slot. -/
def WhnfCoreSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode cheap d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW e →
    CoreSpec p n "whnf_core" [mode, cheap, vis, d, e]
      ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE e)) decH s₀ a₀ dn vis
      fe M eb

/-- `whnf(mode, vis, d, e)` refines the knot's `whnf` slot. -/
def WhnfSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpec p n "whnf" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE e)) decH s₀ a₀ dn vis fe M eb

/-- `infer(mode, vis, d, e)` refines the knot's full-grade `infer` slot (phase 7). -/
def InferSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpec p n "infer" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).infer d.toNat (decE e)) decH s₀ a₀ dn vis fe M eb

/-- `infer_io(mode, vis, d, e)` refines the knot's io-grade `inferIO` slot (phase 7). -/
def InferIOSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpec p n "infer_io" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE e)) decH s₀ a₀ dn vis fe M eb

/-- `defeq(mode, vis, d, a, b)` refines the knot's `defeq` slot (phase 6). -/
def DefeqSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW x →
    HW y →
    CoreSpec p n "defeq" [mode, vis, d, x, y]
      ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe
      M eb

/-- **The knot at L fuel `n`**: every slot. -/
structure KnotOK (p : Prog) (n : Nat) : Prop where
  whnfCore : WhnfCoreSlot p n
  whnf : WhnfSlot p n
  infer : InferSlot p n
  inferIO : InferIOSlot p n
  defeq : DefeqSlot p n

/-- **The knot at every L fuel up to `n`**: what a body at fuel `n + 1` assumes of the slots it
calls (a call inside a loop runs at less fuel than the body, and L has no fuel monotonicity
lemma, so the hypothesis covers every smaller fuel). -/
def KnotUpTo (p : Prog) (n : Nat) : Prop := ∀ k, k ≤ n → KnotOK p k

theorem KnotUpTo.mono {p : Prog} {n m : Nat} (h : KnotUpTo p n) (hm : m ≤ n) : KnotUpTo p m :=
  fun k hk => h k (Nat.le_trans hk hm)

/-! ## The callees of the whnf family

Each is a named L function with the spec of its twin. `WhnfCallees p` bundles them; the
whnf family's refinements take it as a hypothesis, the census-tagged ones get it from
`KnotAllProg.whnfC` (`DefEqKnot.lean`; tagged statements in `KnotTagged.lean`). -/

/-- `inst_list(e, off, cnt, d)` refines `instantiateListFast coreWalkFuel e xs d` (phase 4),
the accumulator a stack slice. -/
def InstListOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e off cnt d : Word) (xs : Array EIdx), CoreS dn s₀.mem a₀ vis fe M eb →
    HW e → SpineR s₀.mem off cnt xs → off.toNat + cnt.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "inst_list" [e, off, cnt, d]
      (instantiateListFast coreWalkFuel (decE e) xs d.toNat) decH s₀ a₀ dn vis fe M eb

/-- `inst_lp(po, pl, us, e)` refines `instLPFast coreWalkFuel lps us e` (phase 4), the level
parameters a slice of the environment's record pool (`EREC`). -/
def InstLPOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb po pl us e : Word) (lps : List NIdx), CoreS dn s₀.mem a₀ vis fe M eb →
    HW e → HW us → hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    CoreSpec p n "inst_lp" [po, pl, us, e]
      (instLPFast coreWalkFuel lps (decI us) (decE e)) decH s₀ a₀ dn vis fe M eb

/-- `str_lit_ctor(h)` refines `strLitToConstructor s` at a string literal `h` (the `lit` store
does not keep a string's characters yet: see DESIGN.md). -/
def StrLitCtorOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb h : Word) (s : String), CoreS dn s₀.mem a₀ vis fe M eb → HW h →
    a₀.store.view (decE h) = some (.lit (.strVal s)) →
    CoreSpec p n "str_lit_ctor" [h] (strLitToConstructor s) decH s₀ a₀ dn vis fe M eb

/-- `str_lit_supported(vis)` refines `strLitSupported fe`. -/
def StrLitSupportedOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn s₀.mem a₀ vis fe M eb →
    CoreSpec p n "str_lit_supported" [vis] (strLitSupported fe) decBool s₀ a₀ dn vis fe M eb

/-- **The stub callees.** (It held the knot's `infer`/`infer_io`/`defeq` slot steps too; no proof
used them, and lane `defeq`'s knot proves those steps from facts that themselves come from proofs
over this bundle, so they were dropped: helper `whnf4-knot`.) -/
structure WhnfCallees (p : Prog) : Prop where
  instList : InstListOK p
  instLP : InstLPOK p
  strLitCtor : StrLitCtorOK p
  strLitSupported : StrLitSupportedOK p

/-- **`strLitSupported` keeps every stored node's view** (it reads the pins and the environment
and interns the nodes it compares against, which only adds nodes). `StrLitSupportedOK` says
nothing about the store; `proj_lit_to_ctor` carries a `view` fact across the call. -/
def SupKeep (fe : IFEnv) : Prop :=
  ∀ (a : AState) (h : EIdx) (w : ENodeView), a.store.view h = some w →
    (AM.st (strLitSupported fe) a).store.view h = some w

end L.Arena
