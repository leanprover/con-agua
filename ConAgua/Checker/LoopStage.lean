module

import ConAgua.Checker.TwinShapeFront
import ConAgua.Checker.TwinCaches
import ConAgua.Arena.InitLink
import ConAgua.Checker.RomProgInit
public import ConAgua.Checker.PipeRest
public import ConAgua.Arena.CheckerT

@[expose] public section

/-!
# The declaration loop's start, from the stages before it (lane `loopt3`)

What the declaration loop takes at its start from the stages before it: the front's declarations'
shape (`frontDecls_of_prefix`, from `TwinPrefix`) and the core tier's memos (`core_of_R7`, from
`R7`).
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Checker

open L.Arena L.Rom

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
theorem core_of_R7' {b pb : ByteArray} {sz : TieredArray → Nat} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (hc : sE.caches = (AState.init EStore.empty).caches)
    (h7 : R7 (ConAgua.Final.loadMem b pb sz) m pb ds ipins sE) : CoreR m sE.caches := by
  rw [hc]
  have hctl : 120 ≤ sz CTL := by
    have := h7.since.caps.2.1
    rw [loadMem_arr] at this; simp only [Array.size_replicate, ctlMin] at this; omega
  obtain ⟨M, hM⟩ := cachesEmpty_refines sz hctl
  have hf0 : MemFrame [] [] (initMem sz) (ConAgua.Final.loadMem b pb sz) :=
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  exact ⟨M, (hM.frame (fun _ h => by simp at h) (fun _ h => by simp at h) hf0).frame
    preLoopA_avoidCore preLoopC_avoidCore h7.since.frame⟩

theorem core_of_R7 {b pb : ByteArray} {sz : TieredArray → Nat} {sA : AState} {pre : PreludeIx}
    {sB : AState} {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE)
    (h7 : R7 (ConAgua.Final.loadMem b pb sz) m pb ds ipins sE) : CoreR m sE.caches :=
  core_of_R7' (prefix_caches hpx).1 h7

end L.Checker
