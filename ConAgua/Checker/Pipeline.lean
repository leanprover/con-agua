import ConAgua.Checker.Entry
import ConAgua.Front.RunModel
import ConAgua.Final.Twin

/-!
# `check`'s stages composed (lane `pipeline`)

Entry 1 (`check_a`, `Checker/Entry.lean`) calls the seven stages before the declaration loop in
order. Each stage's refinement is stated here as a **stage spec** (`StageSpec`): a returning call
keeps the caller's locals, and if the memory before it satisfies the stage's precondition, the
memory after it satisfies its postcondition. The conditions are predicates on the memory only;
the twin's states and values live inside them, existentially (`Checker/PipeFinal.lean` picks
them, `checkerRels`). So the composition (`checkA_of_stages`, `Checker/ParEntryA.lean`) is a
chain of implications between named predicates; `stageSpecs_of_rels` gives the seven stage specs
from the relational ones.
-/

namespace L.Checker

open L L.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- **A stage spec**: every returning call of `f` (no arguments) keeps the caller's locals and
takes memory satisfying `Pre` to memory satisfying `Post r` (`r` the results). -/
def StageSpec (p : Prog) (f : FnName) (Pre : Mem → Prop) (Post : List Word → Mem → Prop) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) f []
    ⦃fun r s' => LocEq s' s₀ ∧ (Pre s₀.mem → Post r s'.mem); ⊤⦄

/-! ## The stages' relations and the twin's prefix

The stage specs are stated relationally (`RelSpec`, a precondition on the memory before the call,
a postcondition with the twin's step after it), over five relations between the L memory and the
twin's state (`PipeRels`), picked when the stages are discharged. `Q3`‥`Q7` are the memory
predicates between the stages (`stageSpecs_of_rels`): the twin's stages so far ran from `AState.init EStore.empty`, and
the last relation holds. -/

open ConRon.Arena ConRon.Arena.Frontend ConAgua.Final

/-- **A relational stage spec**: from memory satisfying `Pre`, a returning call of `f` keeps the
caller's locals and ends in memory satisfying `Post r`. -/
def RelSpec (p : Prog) (f : FnName) (Pre : Mem → Prop) (Post : List Word → Mem → Prop) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St), Pre s₀.mem → ⦃fun s => s = s₀⦄ invoke p (exec p n) f []
    ⦃fun r s' => LocEq s' s₀ ∧ Post r s'.mem; ⊤⦄

/-- **The relations between `check`'s stages**, for the input bytes `b`, the pin-data bytes `pb`
and the capacities `s8`, `s64`: after `cap_check` (`R1`), after `pb_check` (`R2`), and after
each twin stage, with the twin's state and the values the later stages read. -/
structure PipeRels (b pb : ByteArray) (s8 s64 : List Nat) where
  /-- After `cap_check`. -/
  R1 : Mem → Prop
  /-- After `pb_check`. -/
  R2 : Mem → Prop
  /-- After `intern_reserved_pins`. -/
  R3 : Mem → AState → Prop
  /-- After `builtin_prelude`: the prelude's index. -/
  R4 : Mem → PreludeIx → AState → Prop
  /-- After `front_run`: the prelude's index, the stream's parse. -/
  R5 : Mem → PreludeIx → ParseResultD → AState → Prop
  /-- After `prepare_prelude`: the prepared records. -/
  R6 : Mem → Array IDeclaration → AState → Prop
  /-- After `intern_all_pins`: the prepared records, the interned pin list. -/
  R7 : Mem → Array IDeclaration → List INatOpPinSet → AState → Prop

/-- What every stage may assume of the inputs: a 64-bit platform, both buffers below `2^63`
bytes, every word array below `2^64` words. -/
def InputsOK (b pb : ByteArray) (s64 : List Nat) : Prop :=
  System.Platform.numBits = 64 ∧ b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ ∀ n ∈ s64, n < 2 ^ 64

/-- The twin's stages before the fold ran, from `AState.init EStore.empty`. -/
def TwinPrefix (b : ByteArray) (sA : AState) (pre : PreludeIx) (sB : AState) (rc : ParseResultD)
    (sC : AState) (ds : Array IDeclaration) (sD : AState) (pins : List ConLeche.NatOpPinSet)
    (ipins : List INatOpPinSet) (sE : AState) : Prop :=
  internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks [b] sB = .ok (.ok rc, sC) ∧
    preparePrelude pre rc.decls sC = .ok (ds, sD) ∧ internAllPins pins sD = .ok (ipins, sE)

/-- The twin's stages before `internAllPins` ran, from `AState.init EStore.empty`. -/
def TwinPrefix4 (b : ByteArray) (sA : AState) (pre : PreludeIx) (sB : AState) (rc : ParseResultD)
    (sC : AState) (ds : Array IDeclaration) (sD : AState) : Prop :=
  internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks [b] sB = .ok (.ok rc, sC) ∧
    preparePrelude pre rc.decls sC = .ok (ds, sD)

section stages
variable (p : Prog) (ρ : ∀ b pb s8 s64, PipeRels b pb s8 s64)

/-- **Stage `cap_check`**: from the loaded memory to `R1`. -/
def CapStage : Prop := ∀ b pb s8 s64, InputsOK b pb s64 →
  RelSpec p "cap_check" (· = loadMem b pb s8 s64) fun _ => (ρ b pb s8 s64).R1

/-- **Stage `pb_check`**: `R1` to `R2`. -/
def PbStage : Prop := ∀ b pb s8 s64, InputsOK b pb s64 →
  RelSpec p "pb_check" (ρ b pb s8 s64).R1 fun _ => (ρ b pb s8 s64).R2

/-- **Stage `intern_reserved_pins`** refines `internReservedPins` from the twin's start state. -/
def IrpStage : Prop := ∀ b pb s8 s64, InputsOK b pb s64 →
  RelSpec p "intern_reserved_pins" (ρ b pb s8 s64).R2 fun _ m =>
    ∃ a', internReservedPins (AState.init EStore.empty) = .ok ((), a') ∧ (ρ b pb s8 s64).R3 m a'

/-- **Stage `builtin_prelude`** refines `builtinPreludeE`. -/
def PreludeStage : Prop := ∀ b pb s8 s64 a, InputsOK b pb s64 →
  RelSpec p "builtin_prelude" ((ρ b pb s8 s64).R3 · a) fun _ m =>
    ∃ pre a', builtinPreludeE a = .ok (.ok pre, a') ∧ (ρ b pb s8 s64).R4 m pre a'

/-- **Stage `front_run`** refines `parseChunks [b]` (on its result `0`). -/
def FrontStage : Prop := ∀ b pb s8 s64 pre a, InputsOK b pb s64 →
  RelSpec p "front_run" ((ρ b pb s8 s64).R4 · pre a) fun r m => r.headD 0 = 0 →
    ∃ rc a', parseChunks [b] a = .ok (.ok rc, a') ∧ (ρ b pb s8 s64).R5 m pre rc a'

/-- **Stage `prepare_prelude`** refines `preparePrelude`. -/
def PrepareStage : Prop := ∀ b pb s8 s64 pre rc a, InputsOK b pb s64 →
  RelSpec p "prepare_prelude" ((ρ b pb s8 s64).R5 · pre rc a) fun _ m =>
    ∃ ds a', preparePrelude pre rc.decls a = .ok (ds, a') ∧ (ρ b pb s8 s64).R6 m ds a'

/-- **Stage `intern_all_pins`** refines `internAllPins` at some pin list (the one `pb` decodes
to). -/
def PinsStage : Prop := ∀ b pb s8 s64 sA pre sB rc sC ds a, InputsOK b pb s64 →
  TwinPrefix4 b sA pre sB rc sC ds a →
  RelSpec p "intern_all_pins" ((ρ b pb s8 s64).R6 · ds a) fun _ m =>
    ∃ pins ipins a', internAllPins pins a = .ok (ipins, a') ∧ (ρ b pb s8 s64).R7 m ds ipins a'

end stages

section twinPrefix
variable (b : ByteArray) {pb : ByteArray} {s8 s64 : List Nat} (ρ : PipeRels b pb s8 s64)

/-- After `intern_reserved_pins`. -/
def Q3 (m : Mem) : Prop :=
  ∃ sA, internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧ ρ.R3 m sA

/-- After `builtin_prelude`. -/
def Q4 (m : Mem) : Prop :=
  ∃ sA pre sB, internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ ρ.R4 m pre sB

/-- After `front_run`. -/
def Q5 (m : Mem) : Prop :=
  ∃ sA pre sB rc sC, internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks [b] sB = .ok (.ok rc, sC) ∧
    ρ.R5 m pre rc sC

/-- After `prepare_prelude`. -/
def Q6 (m : Mem) : Prop :=
  ∃ sA pre sB rc sC ds sD, internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks [b] sB = .ok (.ok rc, sC) ∧
    preparePrelude pre rc.decls sC = .ok (ds, sD) ∧ ρ.R6 m ds sD

/-- After `intern_all_pins`. -/
def Q7 (m : Mem) : Prop :=
  ∃ sA pre sB rc sC ds sD pins ipins sE, internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks [b] sB = .ok (.ok rc, sC) ∧
    preparePrelude pre rc.decls sC = .ok (ds, sD) ∧ internAllPins pins sD = .ok (ipins, sE) ∧
    ρ.R7 m ds ipins sE

end twinPrefix

/-- A relational spec is a stage spec once its precondition is unpacked: `hpre` turns `Pre` into
some `x`'s precondition, `hpost` the `x`-spec's post (with the unpacked fact) into `Post`. -/
theorem StageSpec.of_rel {p : Prog} {f : FnName} {X : Type} {Pre : Mem → Prop}
    {Post : List Word → Mem → Prop} (P : X → Mem → Prop) (PostX : X → List Word → Mem → Prop)
    (h : ∀ x, RelSpec p f (P x) (PostX x)) (hpre : ∀ m, Pre m → ∃ x, P x m ∧
      ∀ r m', PostX x r m' → Post r m') : StageSpec p f Pre Post := by
  intro n hn s₀
  apply M.triple_of_run
  intro s r s' hs hrun
  refine ⟨hs ▸ (L.Front.invoke_loc hrun).1, fun hP => ?_⟩
  obtain ⟨x, hx, hpost⟩ := hpre _ hP
  exact hpost _ _ (M.of_run (P := fun s => s = s₀) hs hrun (h x n hn s₀ hx)).2

/-- **The seven stage specs before the loop**, from the relational ones (the memory predicates
`Q3`‥`Q7` between them). -/
theorem stageSpecs_of_rels {p : Prog} (ρ : ∀ b pb s8 s64, PipeRels b pb s8 s64)
    (h1 : CapStage p ρ) (h2 : PbStage p ρ) (h3 : IrpStage p ρ) (h4 : PreludeStage p ρ)
    (h5 : FrontStage p ρ) (h6 : PrepareStage p ρ) (h7 : PinsStage p ρ)
    (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64) :
    StageSpec p "cap_check" (· = loadMem b pb s8 s64) (fun _ => (ρ b pb s8 s64).R1) ∧
    StageSpec p "pb_check" (ρ b pb s8 s64).R1 (fun _ => (ρ b pb s8 s64).R2) ∧
    StageSpec p "intern_reserved_pins" (ρ b pb s8 s64).R2 (fun _ => Q3 b (ρ b pb s8 s64)) ∧
    StageSpec p "builtin_prelude" (Q3 b (ρ b pb s8 s64)) (fun _ => Q4 b (ρ b pb s8 s64)) ∧
    StageSpec p "front_run" (Q4 b (ρ b pb s8 s64))
      (fun r m => r.headD 0 = 0 → Q5 b (ρ b pb s8 s64) m) ∧
    StageSpec p "prepare_prelude" (Q5 b (ρ b pb s8 s64)) (fun _ => Q6 b (ρ b pb s8 s64)) ∧
    StageSpec p "intern_all_pins" (Q6 b (ρ b pb s8 s64)) (fun _ => Q7 b (ρ b pb s8 s64)) := by
  let r := ρ b pb s8 s64
  exact ⟨(StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _) (fun _ => h1 b pb s8 s64 hin)
      fun m hm => ⟨(), hm, fun _ _ h => h⟩),
    (StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _) (fun _ => h2 b pb s8 s64 hin)
      fun m hm => ⟨(), hm, fun _ _ h => h⟩),
    (StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _) (fun _ => h3 b pb s8 s64 hin)
      fun m hm => ⟨(), hm, fun _ _ h => h⟩),
    (StageSpec.of_rel (fun x : AState => (r.R3 · x)) _ (fun x => h4 b pb s8 s64 x hin)
      fun m ⟨sA, hA, hR⟩ => ⟨sA, hR, fun _ _ ⟨pre, sB, hB, hR'⟩ => ⟨sA, pre, sB, hA, hB, hR'⟩⟩),
    (StageSpec.of_rel (fun x : AState × PreludeIx × AState => (r.R4 · x.2.1 x.2.2)) _
      (fun x => h5 b pb s8 s64 x.2.1 x.2.2 hin)
      fun m ⟨sA, pre, sB, hA, hB, hR⟩ => ⟨(sA, pre, sB), hR, fun _ _ h h0 => by
        obtain ⟨rc, sC, hC, hR'⟩ := h h0
        exact ⟨sA, pre, sB, rc, sC, hA, hB, hC, hR'⟩⟩),
    (StageSpec.of_rel (fun x : AState × PreludeIx × AState × ParseResultD × AState =>
        (r.R5 · x.2.1 x.2.2.2.1 x.2.2.2.2)) _
      (fun x => h6 b pb s8 s64 x.2.1 x.2.2.2.1 x.2.2.2.2 hin)
      fun m ⟨sA, pre, sB, rc, sC, hA, hB, hC, hR⟩ => ⟨(sA, pre, sB, rc, sC), hR,
        fun _ _ ⟨ds, sD, hD, hR'⟩ => ⟨sA, pre, sB, rc, sC, ds, sD, hA, hB, hC, hD, hR'⟩⟩),
    (StageSpec.of_rel (fun x : AState × PreludeIx × AState × ParseResultD × AState ×
          Array IDeclaration × AState =>
          fun m => TwinPrefix4 b x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 ∧
            r.R6 m x.2.2.2.2.2.1 x.2.2.2.2.2.2)
      (fun x _ m => ∃ pins ipins a', internAllPins pins x.2.2.2.2.2.2 = .ok (ipins, a') ∧
        r.R7 m x.2.2.2.2.2.1 ipins a')
      (fun x n hn s₀ hP => h7 b pb s8 s64 _ _ _ _ _ _ _ hin hP.1 n hn s₀ hP.2)
      fun m ⟨sA, pre, sB, rc, sC, ds, sD, hA, hB, hC, hD, hR⟩ => ⟨(sA, pre, sB, rc, sC, ds, sD),
        ⟨⟨hA, hB, hC, hD⟩, hR⟩,
        fun _ _ ⟨pins, ipins, sE, hE, hR'⟩ =>
          ⟨sA, pre, sB, rc, sC, ds, sD, pins, ipins, sE, hA, hB, hC, hD, hE, hR'⟩⟩)⟩

end L.Checker
