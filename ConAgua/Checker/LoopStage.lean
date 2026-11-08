module

public import ConAgua.Arena.LoopStart
import ConAgua.Checker.TwinShapeFront
import ConAgua.Checker.TwinCaches
import ConAgua.Arena.InitLink
import ConAgua.Checker.PreLoopWSBase
import ConAgua.Checker.RomProgInit
import ConAgua.Final.Twin
public import ConAgua.Checker.PipeRest

@[expose] public section

/-!
# The declaration loop's start, from the stages before it (lane `loopt3`)

What phase A's fold takes at its start (`installFoldGo_start`, `Arena/PhaseAEntry.lean`; used by
entry 1's run, `Checker/CheckARun.lean`, and the driver, `Checker/ParDriverTwin.lean`): the twin's
fold invariant at the loop's start from the twin's stages before it (`TwinPrefix`,
`Final/Twin.lean`'s `stages_frame`), the memory facts from `R7`.
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Checker

open L.Arena L.Rom

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The fold's start invariant from the twin's stages before the loop** (`stages_frame`). -/
theorem twinFold_of_prefix {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) :
    TwinFold ipins ds (mkIFEnv IEnv.empty) #[] sE := by
  sorry

-/

/-- The `CTL` words `LoopZero` asks zero, as a list. -/
def loopZeroCtls : List Nat :=
  [48, 50, 54, 56, 58, 152, 154, 156, 158, 128, 130, 140, 141, 142, 143, 144, 145, 146, 147, 202,
    203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 52, 133]

theorem loopZeroCtl_mem {x : Nat} (h : loopZeroCtl x) : x ∈ loopZeroCtls := by
  simp only [loopZeroCtl] at h
  simp only [loopZeroCtls, List.mem_cons, List.not_mem_nil, or_false]
  omega

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem preLoopA_loopZeroArrs : loopZeroArrs.all (fun b => !preLoopA.contains b) = true := by
  sorry

-/

theorem preLoopC_loopZeroCtls :
    (preLoopC.map UInt64.toNat).all (fun x => !loopZeroCtls.contains x) = true := by
  decide +kernel

/-- **The zeros the loop starts from**: the loaded memory's words (`loadMem_rd`), which no stage
before the loop writes (`Since.frame`: `preLoopA`, `preLoopC`). -/
theorem loopZero_of_since {b pb : ByteArray} {sz : TieredArray → Nat} {m : Mem}
    (h : Since (ConAgua.Final.loadMem b pb sz) m pb) : LoopZero m := by
  sorry

/-- `FrontDecls` from the twin prefix's shape fact (lane `pipeline`'s `prefix_frontDecls`). -/
theorem frontDecls_of_prefix {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) : L.Arena.FrontDecls ds :=
  fun i hi b nP e => prefix_frontDecls h b nP (by rw [← e]; simp)

theorem preLoopA_avoidCore : AvoidA 96 128 preLoopA := by
  intro b hb
  have : preLoopA.all (fun b => decide (b.arr < 96 ∨ 128 ≤ b.arr)) = true := by decide +kernel
  simpa using List.all_eq_true.mp this b hb

theorem preLoopC_avoidCoreN : (preLoopC.map UInt64.toNat).all (fun x => decide (x < 96 ∨ 128 ≤ x)) = true := by
  decide +kernel

theorem preLoopC_avoidCore : AvoidC 96 128 preLoopC := by
  intro x hx
  simpa using List.all_eq_true.mp preLoopC_avoidCoreN x.toNat (List.mem_map.mpr ⟨x, hx, rfl⟩)

/-- **The core tier at the loop's start**: the twin's caches are `AState.init`'s (lane `pipeline`'s
`prefix_caches`), the core's memos the loaded memory's zeros (lane `inits`' `cachesEmpty_refines`),
which no stage before the loop writes (`CoreRM.frame` over `preLoopA`, `preLoopC`). -/
theorem core_of_R7 {b pb : ByteArray} {sz : TieredArray → Nat} {sA : AState} {pre : PreludeIx}
    {sB : AState} {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE)
    (h7 : R7 (ConAgua.Final.loadMem b pb sz) m pb ds ipins sE) : CoreR m sE.caches := by
  rw [(prefix_caches hpx).1]
  have hctl : 120 ≤ sz CTL := by
    have := h7.since.caps.2.1
    rw [loadMem_arr] at this; simp only [Array.size_replicate, ctlMin] at this; omega
  obtain ⟨M, hM⟩ := cachesEmpty_refines sz hctl
  have hf0 : MemFrame [] [] (initMem sz) (ConAgua.Final.loadMem b pb sz) :=
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  exact ⟨M, (hM.frame (fun _ h => by simp at h) (fun _ h => by simp at h) hf0).frame
    preLoopA_avoidCore preLoopC_avoidCore h7.since.frame⟩

end L.Checker
