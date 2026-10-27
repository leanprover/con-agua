import ConAgua.Checker.Pipeline
import ConAgua.Checker.RomProg
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.PreLoopWS

/-!
# The relations between `check`'s stages, and the first stages (lane `pipeline`)

`Checker/Pipeline.lean` composes `check` from eight relational stage specs over relations
`PipeRels`. Here are the relations the checker's program keeps, and the stages `cap_check`,
`pb_check`, `intern_reserved_pins` at `checkerProg`.

Every relation after `pb_check` carries the facts that hold since the loaded memory
`l = loadMem b pb s8 s64` (`Since`): the byte arrays and the sizes are `l`'s (`Keep`, the program
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
  seen : ∀ j, rdW (m.arr64 75) j = 0
  nix : ∀ j, rdW (m.arr64 76) j = 0

theorem HZ.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : HZ m) (hf : MemFrame A C m m')
    (h75 : 75 ∉ A) (h76 : 76 ∉ A) (c73 : (73 : Word) ∉ C) (c75 : (75 : Word) ∉ C)
    (c129 : (129 : Word) ∉ C) (c200 : (200 : Word) ∉ C) : HZ m' :=
  ⟨by rw [hf.2.1 _ c73]; exact h.c73, by rw [hf.2.1 _ c75]; exact h.c75,
    by rw [hf.2.1 _ c129]; exact h.c129, by rw [hf.2.1 _ c200]; exact h.c200,
    fun j => by rw [hf.1 75 h75 (by decide)]; exact h.seen j,
    fun j => by rw [hf.1 76 h76 (by decide)]; exact h.nix j⟩

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
  apply M.triple_of_run
  intro s r s' hs hrun
  have h1 := M.of_run (P := fun s => s = s₀) hs hrun
    (Triple.keep checkerProg_noSt8 (Q := fun _ _ => True) (M.triple_of_run fun _ _ _ _ _ => trivial))
  have h2 := M.of_run (P := fun s => s = s₀) hs hrun (preLoop_frame n hf s₀)
  exact ⟨h1.2.2, h1.2.1, h2⟩

theorem Since.step {l m m' : Mem} {pb : ByteArray} (h : Since l m pb) (hk : L.Keep m m')
    (hf : MemFrame preLoopA preLoopC m m') : Since l m' pb :=
  ⟨⟨hk.1.trans h.keep.1, fun a => (hk.2 a).trans (h.keep.2 a)⟩, h.caps, h.pbpre, h.frame.trans hf⟩

/-! ## `cap_check`, `pb_check` -/

theorem capStage_checker (b pb : ByteArray) (s8 s64 : List Nat) (hs : ∀ n ∈ s64, n < 2 ^ 64) :
    RelSpec checkerProg "cap_check" (· = loadMem b pb s8 s64)
      fun _ m => R1 (loadMem b pb s8 s64) m := by
  intro n _hn s₀ hm
  refine triple_post (capCheck_spec checkerProg checkerProg_capCheck n s₀
    (hm ▸ loadMem_wordsFit b pb s8 s64 hs)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · rw [h2, hm]
  · rw [← hm]; exact h3

theorem pbStage_checker (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63) :
    RelSpec checkerProg "pb_check" (R1 (loadMem b pb s8 s64))
      fun _ m => R2 (loadMem b pb s8 s64) m pb := by
  intro n _hn s₀ ⟨hm, hc⟩
  refine triple_post (checkerProg_pbCheck_PB pb.data.toList (by simpa [RomOK] using hpb) n s₀
    (by rw [hm]; exact loadMem_pb b pb s8 s64)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, hc, h3⟩
  rw [h2, hm]

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

theorem pinA_not {x : ArrId} (h : 64 ≤ x ∧ x < 256) (h' : x ≠ PINS) : x ∉ PinA := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, n = x := ⟨x, rfl⟩
  intro hx
  simp only [tier1, tierOff, PinA, StoreA, lowTierArrs, List.mem_cons, List.mem_append, List.mem_range,
    List.mem_map] at hx
  rcases hx with hx | hx | ⟨y, -, e⟩
  · exact h' hx
  · simp only [ArrId] at *; omega
  · simp only [ArrId] at *; omega

theorem irpStage_checker (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63) :
    RelSpec checkerProg "intern_reserved_pins" (fun m => R2 (loadMem b pb s8 s64) m pb)
      fun _ m => ∃ a', internReservedPins (AState.init EStore.empty) = .ok ((), a') ∧
        R3 (loadMem b pb s8 s64) m pb a' := by
  intro n _hn s₀ ⟨hm, hc, hpre⟩
  have hirp := checkerProg_internReservedPins_PB pb.data.toList (by simpa [RomOK] using hpb) hpre n
    s₀ (AState.init EStore.empty) (by rw [hm]; exact loadMem_pb b pb s8 s64)
    (by rw [hm]; exact arenaD_loadMem b pb s8 s64 hc)
    (by rw [hm]; exact Or.inr (by show (rdW ((loadMem b pb s8 s64).arr64 CTL) 0).toNat < 2 ^ 40
                                  rw [loadMem_rd]; decide))
  refine triple_post (triple_and hirp (stage_since n (preLoop_mem "intern_reserved_pins"
    (by decide +kernel)) s₀)) fun _ s' ⟨⟨hl, hok, hA, hfull, hp0, hfr, hmo⟩, _, hk, hpf⟩ => ⟨hl, ?_⟩
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : internReservedPins (AState.init EStore.empty) =
      .ok ((), AM.st internReservedPins (AState.init EStore.empty)) := hrun
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    ConRon.Bridge.internReservedPins_run ⟨EStore.empty_wf⟩ rfl hrun'
  refine ⟨_, hrun', ?_⟩
  rw [hm] at hk hpf hfr
  refine ⟨⟨hk, hc, by simpa [PbPre] using hpre, hpf⟩, hA, ?_, ?_, ?_, hfull, hp0,
    ⟨hokA, hoffA, hpinsA, hppA, hfull.names_size⟩, hcachesA, ?_, hmo⟩
  · exact (stateDR_loadMem b pb s8 s64 hc).frame hfr (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide)) pinA_idArrs storeC_idCtl
  · exact (rsetR_loadMem b pb s8 s64 hc).frame hfr (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
  · have := hfr.2.1 131 (not_mem_storeC _ (by decide))
    simp only [stkTop] at this ⊢
    rw [this]; exact stkTop_loadMem b pb s8 s64
  · have z := loadMem_rd b pb s8 s64
    exact HZ.frame ⟨z _ _, z _ _, z _ _, z _ _, z _, z _⟩ hfr (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
      (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))

end L.Checker
