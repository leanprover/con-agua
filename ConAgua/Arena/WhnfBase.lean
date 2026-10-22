import ConAgua.Arena.CoreRefine
import ConAgua.Arena.View
import ConAgua.Arena.NatArms
import ConAgua.Arena.Pins
import ConAgua.Arena.LevelArena
import ConRon.Arena.Core
import ConAgua.Census.Attr

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

**Stubs.** Callees whose L code does not exist yet are named L functions with an abstract
spec (`WhnfCallees`); the refinements are proved from it, and the census-tagged theorems
instantiate it with `whnfCallees_stub` (a `sorry`) until the callees land.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedVariables false

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

/-- The stack below the top is unchanged, and so is the top. -/
def StackKept (m m' : Mem) : Prop :=
  spTop m' = spTop m ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
    ∀ i : Word, i < spTop m → spW m' i = spW m i

/-- The stack below the old top is unchanged; the top may have grown (a returned slice). -/
def StackGrew (m m' : Mem) : Prop :=
  spTop m ≤ spTop m' ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
    ∀ i : Word, i < spTop m → spW m' i = spW m i

theorem StackKept.refl (m : Mem) : StackKept m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem StackKept.trans {m₁ m₂ m₃ : Mem} (h₁ : StackKept m₁ m₂) (h₂ : StackKept m₂ m₃) :
    StackKept m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1,
    fun i hi => (h₂.2.2 i (h₁.1 ▸ hi)).trans (h₁.2.2 i hi)⟩

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

/-- The three walk-local memos are well formed (lane `whnf3`). -/
def WalkMemos (m : Mem) : Prop :=
  (∃ mp : Std.HashMap (EIdx × Nat) Bool, MemoRG coreWsSch lfKey (fun w => w != 0) m mp) ∧
    (∃ mp : Std.HashMap EIdx Unit, MemoRG coreFlSch bmKey (fun _ => ()) m mp) ∧
    (∃ mp : Std.HashMap EIdx Bool, MemoRG coreLsbSch bmKey (fun w => w != 0) m mp)

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
    (hC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C) (h : WalkMemos m) : WalkMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1; ⟨mp, memoRG_frame coreWsSch coreWsSch_wf lfKey _ A C hA.1 hC.1 m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.1; ⟨mp, memoRG_frame coreFlSch coreFlSch_wf bmKey _ A C hA.2.1 hC.2.1 m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.2; ⟨mp, memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ A C hA.2.2 hC.2.2 m m' hf mp hm⟩⟩

/-- **`CoreMemos` across a writer** that avoids arrays 49, 50, 151‥153 and `CTL` words 48, 50, 152,
154, 156 (the last two avoidances are auto-params: `decide` on concrete lists). -/
theorem CoreMemos.frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A) (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C) (h : CoreMemos m)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A := by decide)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide) :
    CoreMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1; ⟨mp, memoRG_frame coreIlSch coreIlSch_wf lfKey decE A C hA.1 hC.1 m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := h.2.1; ⟨mp, memoRG_frame coreAbSch coreAbSch_wf lfKey decE A C hA.2 hC.2 m m' hf mp hm⟩,
    h.2.2.frame hf hWA hWC⟩

/-- **`CoreMemos` across a writer at or above array 64** (and `CTL` word 64), away from the walk
memos (arrays 151‥153, `CTL` 152‥157). -/
theorem CoreMemos.frame_hi {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b) (hC : ∀ x ∈ C, 64 ≤ x.toNat) (h : CoreMemos m)
    (hWA : ∀ b ∈ A, b < 151 ∨ 153 < b := by decide)
    (hWC : ∀ x ∈ C, x.toNat < 152 ∨ 157 < x.toNat := by simp) : CoreMemos m' :=
  h.frame hf ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide)⟩
    ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩
    ⟨fun h => absurd (hWA _ h) (by decide), fun h => absurd (hWA _ h) (by decide),
      fun h => absurd (hWA _ h) (by decide)⟩
    ⟨fun h => absurd (hWC _ h) (by decide), fun h => absurd (hWC _ h) (by decide),
      fun h => absurd (hWC _ h) (by decide)⟩

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

/-- **The relation across a writer outside every tier and the stack**, the walk memos given
(`hmem`): a writer of the walk-local memos (arrays 151‥153) proves them itself. -/
theorem CoreS.frameM {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ (b < 96 ∨ 145 ≤ b)) (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 137 ≤ x.toNat))
    (hmem : CoreMemos m') :
    CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
  have aA : ∀ lo hi : Nat, 96 ≤ lo → hi ≤ 145 → AvoidA lo hi A := fun lo hi h1 h2 b hb => by
    have := hA b hb; simp only [ArrId] at this ⊢; omega
  have aC : ∀ lo hi : Nat, 96 ≤ lo → hi ≤ 137 → AvoidC lo hi C := fun lo hi h1 h2 x hx => by
    have := hC x hx; omega
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => by have := hC _ h; simp at this)
  refine ⟨⟨⟨ArenaR.frame_ext A C (fun b hb => (hA b hb).1) (fun x hx => (hC x hx).1) m m' hf a hS.arena.1,
      DerR.frameM A C m m' hf (fun b hb => .inr (by have := (hA b hb).1; simp only [ArrId] at this ⊢; omega))
        a hS.arena.2⟩,
    hS.core.frame (aA 96 128 (by decide) (by decide)) (aC 96 128 (by decide) (by decide)) hf,
    hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp only [PINS, ArrId] at this; omega)
      (by decide)),
    hS.env.frame (aA 132 144 (by decide) (by decide)) (aC 128 136 (by decide) (by decide)) hf,
    hS.readL, hS.readLs, hS.nwf, hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
    hmem,
    hf.2.2.1 145 ▸ hS.bstk⟩, ?_⟩
  refine ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- **The relation across a writer outside every tier and the stack**: arrays `≥ 145` (or the
front's 64‥95), `CTL` words `≥ 137` (or 64‥95), away from the walk-local memos: the level heap
(`LH`, `CTL[192]`), say. -/
theorem CoreS.frame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 64 ≤ b ∧ (b < 96 ∨ 145 ≤ b)) (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 137 ≤ x.toNat))
    (hWA : ∀ b ∈ A, b < 151 ∨ 153 < b := by decide)
    (hWC : ∀ x ∈ C, x.toNat < 152 ∨ 157 < x.toNat := by simp) :
    CoreS dn m' a vis fe M eb ∧ StackKept m m' :=
  hS.frameM hf hA hC (hS.memos.frame_hi hf (fun b hb => (hA b hb).1) (fun x hx => (hC x hx).1) hWA hWC)

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

/-! ## Stubs: callees whose L code is not written yet

Each is a named L function with the spec its twin will get. `WhnfCallees p` bundles them; the
whnf family's refinements take it as a hypothesis, the census-tagged ones get it from
`whnfCallees_stub` (a `sorry`, listed in DESIGN.md). -/

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

/-- **The stub callees.** -/
structure WhnfCallees (p : Prog) : Prop where
  instList : InstListOK p
  instLP : InstLPOK p
  strLitCtor : StrLitCtorOK p
  strLitSupported : StrLitSupportedOK p
  /-- The knot's `infer`, `infer_io`, `defeq` slots one level up from the whnf slots: their
  induction step is phases 6–7. -/
  inferStep : ∀ n, KnotUpTo p n → InferSlot p (n + 1)
  inferIOStep : ∀ n, KnotUpTo p n → InferIOSlot p (n + 1)
  defeqStep : ∀ n, KnotUpTo p n → DefeqSlot p (n + 1)

/-- **The stubs' specs, assumed** until their L code lands (phases 4, 6, 7; string literals). -/
theorem whnfCallees_stub (p : Prog) : WhnfCallees p := sorry

/-- **`strLitSupported` keeps every stored node's view** (it reads the pins and the environment
and interns the nodes it compares against, which only adds nodes). `StrLitSupportedOK` says
nothing about the store; `proj_lit_to_ctor` carries a `view` fact across the call. -/
def SupKeep (fe : IFEnv) : Prop :=
  ∀ (a : AState) (h : EIdx) (w : ENodeView), a.store.view h = some w →
    (AM.st (strLitSupported fe) a).store.view h = some w

/-- `SupKeep`, assumed until `strLitSupported`'s store monotonicity is proved (DESIGN.md). -/
theorem supKeep_twin (fe : IFEnv) : SupKeep fe := sorry

end L.Arena
