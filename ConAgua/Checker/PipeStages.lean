module

public import ConAgua.Checker.Pipeline
import ConAgua.Checker.RomProg
import ConAgua.Checker.RomProgInit
public import ConAgua.Checker.PreLoopWS
import ConAgua.Checker.RomProg0
import ConRon.Bridge.Checker.Pins
public import ConAgua.Checker.CapCheck

@[expose] public section

/-!
# The relations between `check`'s stages, and the first stages (lane `pipeline`)

`Checker/Pipeline.lean` composes `check` from eight relational stage specs over relations
`PipeRels`. Here are the relations the checker's program keeps, and the stages `cap_check`,
`pb_check`, `intern_reserved_pins` at `checkerProg`.

Every relation after `pb_check` carries the facts that hold since the loaded memory
`l = loadMem b pb sz` (`Since`): the byte arrays and the sizes are `l`'s (`Keep`, the program
has no byte store), `l`'s capacities are `CapsOK`, the pin data starts with `romData`, and the
memory differs from `l` only in the arrays and `CTL` words the stages before the loop store into
(`MemFrame preLoopA preLoopC`, `PreLoopWS.lean`).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

/-- The pin data starts with `romData` (`pb_check`). -/
def PbPre (pb : ByteArray) : Prop := pb.data.toList = romData ++ pb.data.toList.drop romData.length

/-- **What holds since the loaded memory** `l`. -/
structure Since (l m : Mem) (pb : ByteArray) : Prop where
  keep : L.Keep l m
  caps : CapsOK l
  pbpre : PbPre pb
  frame : MemFrame preLoopA preLoopC l m

/-- The twin's state facts every stage before the loop keeps (con-ron's bridge invariants). -/
structure TwinFacts (a : AState) : Prop where
  ok : ConRon.Bridge.StateOK a
  off : a.store.scratchOn = false
  pins : ConRon.Bridge.PinsOK a
  pers : ConRon.Bridge.PersPins a
  ready : PinsReadyP a

/-- After `cap_check`. -/
def R1 (l m : Mem) : Prop := m = l ∧ CapsOK l

/-- After `pb_check`. -/
def R2 (l m : Mem) (pb : ByteArray) : Prop := m = l ∧ CapsOK l ∧ PbPre pb

/-- The words the ground hoist (`prepare_prelude`) and the pool `IW`/`EREC` start from: still the
loaded memory's zeros. -/
structure HZ (m : Mem) : Prop where
  c73 : rdW (m.arr64 CTL) 73 = 0
  c75 : rdW (m.arr64 CTL) 75 = 0
  c129 : rdW (m.arr64 CTL) 129 = 0
  c200 : rdW (m.arr64 CTL) 200 = 0
  seen : ∀ j, rdW (m.arr64 HSEEN) j = 0
  nix : ∀ j, rdW (m.arr64 HNIX) j = 0

theorem HZ.frame {A : List TieredArray} {C : List Word} {m m' : Mem} (h : HZ m) (hf : MemFrame A C m m')
    (h75 : (HSEEN : TieredArray) ∉ A) (h76 : (HNIX : TieredArray) ∉ A) (c73 : (73 : Word) ∉ C) (c75 : (75 : Word) ∉ C)
    (c129 : (129 : Word) ∉ C) (c200 : (200 : Word) ∉ C) : HZ m' :=
  ⟨by rw [hf.ctl _ c73]; exact h.c73, by rw [hf.ctl _ c75]; exact h.c75,
    by rw [hf.ctl _ c129]; exact h.c129, by rw [hf.ctl _ c200]; exact h.c200,
    fun j => by rw [hf.arr _ h75 (by decide)]; exact h.seen j,
    fun j => by rw [hf.arr _ h76 (by decide)]; exact h.nix j⟩

/-- **After `intern_reserved_pins`**. -/
structure R3 (l m : Mem) (pb : ByteArray) (a : AState) : Prop where
  since : Since l m pb
  arena : ArenaD m a
  sdr : StateDR m StateD.blank
  rset : RsetR m
  stk : stkTop m = 0
  pinsFull : PinsFull m a.pins
  pin0 : pinW m 0 ≠ 0
  twin : TwinFacts a
  caches : a.caches = Caches.empty
  hz : HZ m
  mode : ModeOK m

/-! ## Combining several specs of one call -/

theorem triple_and {α : Type} {prog : M α} {s₀ : St} {Q₁ Q₂ : α → St → Prop}
    (h₁ : ⦃fun s => s = s₀⦄ prog ⦃fun r s => Q₁ r s; ⊤⦄)
    (h₂ : ⦃fun s => s = s₀⦄ prog ⦃fun r s => Q₂ r s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ prog ⦃fun r s => Q₁ r s ∧ Q₂ r s; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  exact ⟨M.of_run (P := fun s => s = s₀) hs hrun h₁, M.of_run (P := fun s => s = s₀) hs hrun h₂⟩

/-- Keep and the frame before the loop, for a stage. -/
theorem stage_since (n : Nat) {f : FnName} (hf : f ∈ preLoopFns) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) f []
    ⦃fun _ s' => LocEq s' s₀ ∧ L.Keep s₀.mem s'.mem ∧ MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ := by
  sorry

theorem Since.step {l m m' : Mem} {pb : ByteArray} (h : Since l m pb) (hk : L.Keep m m')
    (hf : MemFrame preLoopA preLoopC m m') : Since l m' pb :=
  ⟨⟨hk.1.trans h.keep.1, fun a => (hk.2 a).trans (h.keep.2 a)⟩, h.caps, h.pbpre, h.frame.trans hf⟩

/-! ## `cap_check`, `pb_check` -/

theorem capStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (hs : ∀ s, sz s < 2 ^ 64) :
    RelSpec checkerProg "cap_check" (· = loadMem b pb sz)
      fun _ m => R1 (loadMem b pb sz) m := by
  sorry

theorem pbStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63) :
    RelSpec checkerProg "pb_check" (R1 (loadMem b pb sz))
      fun _ m => R2 (loadMem b pb sz) m pb := by
  sorry

/-! ## `intern_reserved_pins` -/

theorem storeC_idCtl : ∀ x ∈ StoreC, x ∉ idCtl := by
  intro x hx hm
  simp only [idCtl, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact not_mem_storeC _ (by decide) hx

theorem pinA_idArrs : ∀ x ∈ PinA, x ∉ idArrs := by
  intro x hx hm
  simp only [idArrs, List.mem_cons, List.not_mem_nil, or_false, NID, LID, EID, NIDS, LIDS, EIDS] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hx <;> decide

theorem pinA_not {x : TieredArray} (h : InHigh x) (h' : x ≠ PINS) : x ∉ PinA := by
  intro hx
  rcases List.mem_cons.mp hx with hx | hx
  · exact h' hx
  · exact h.not_storeTier (storeTier_of_mem hx)

theorem irpStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63) :
    RelSpec checkerProg "intern_reserved_pins" (fun m => R2 (loadMem b pb sz) m pb)
      fun _ m => ∃ a', internReservedPins (AState.init EStore.empty) = .ok ((), a') ∧
        R3 (loadMem b pb sz) m pb a' := by
  sorry

end L.Checker
