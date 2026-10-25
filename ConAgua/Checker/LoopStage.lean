import ConAgua.Arena.LoopStart
import ConAgua.Checker.PipeFinal
import ConAgua.Final.Twin
import ConAgua.Checker.TwinShapeFront
import ConAgua.Checker.TwinShapeQuot
import ConAgua.Checker.TwinCaches
import ConAgua.Arena.InitLink
import ConAgua.Checker.LoopProg

/-!
# The declaration loop as lane `pipeline`'s last stage (lane `loopt3`)

`LoopStage` (`Pipeline.lean`) from `installThenCheck_start` (`Arena/LoopStart.lean`): the twin's
fold invariant at the loop's start from the twin's stages before it (`TwinPrefix`,
`Final/Twin.lean`'s `stages_frame`), the memory facts from `R7`.
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Checker

open L.Arena L.Rom

/-- **The fold's start invariant from the twin's stages before the loop** (`stages_frame`). -/
theorem twinFold_of_prefix {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) :
    TwinFold ipins ds (mkIFEnv IEnv.empty) #[] sE := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := h
  obtain ⟨hoff, hfold, hpd, hpp, hdp, _, _, -, hden⟩ :=
    ConAgua.Final.stages_frame (chunks := [b]) hA hB hC hD hE
  exact ⟨⟨ConLeche.Env.empty, hfold, by simp [ConLeche.NodupNames, ConLeche.Env.empty]⟩,
    ⟨_, hpd⟩, hpp, hdp, ⟨_, hden⟩, by simp, hoff⟩

/-- The arrays `LoopZero` asks zero, as a list. -/
def loopZeroArrs : List Nat :=
  [49, 50, 52, 53, 54, 151, 152, 153, 132, 133, 134, 146, 147, 148, 149, 155, 201, 202, 203, 204,
    205, 206, 207, 208, 51, 140, 141, 142]

/-- The `CTL` words `LoopZero` asks zero, as a list. -/
def loopZeroCtls : List Nat :=
  [48, 50, 54, 56, 58, 152, 154, 156, 158, 128, 130, 140, 141, 142, 143, 144, 145, 146, 147, 202,
    203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 52]

theorem loopZeroArr_mem {b : Nat} (h : loopZeroArr b) : b ∈ loopZeroArrs := by
  simp only [loopZeroArr] at h
  simp only [loopZeroArrs, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem loopZeroCtl_mem {x : Nat} (h : loopZeroCtl x) : x ∈ loopZeroCtls := by
  simp only [loopZeroCtl] at h
  simp only [loopZeroCtls, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem preLoopA_loopZeroArrs : loopZeroArrs.all (fun b => !preLoopA.contains b) = true := by
  decide +kernel

theorem preLoopC_loopZeroCtls :
    (preLoopC.map UInt64.toNat).all (fun x => !loopZeroCtls.contains x) = true := by
  decide +kernel

/-- **The zeros the loop starts from**: the loaded memory's words (`loadMem_rd`), which no stage
before the loop writes (`Since.frame`: `preLoopA`, `preLoopC`). -/
theorem loopZero_of_since {b pb : ByteArray} {s8 s64 : List Nat} {m : Mem}
    (h : Since (ConAgua.Final.loadMem b pb s8 s64) m pb) : LoopZero m := by
  have hf := h.frame
  refine ⟨?_, fun a ha j => ?_, fun x hx => ?_⟩
  · rw [hf.2.2.1]; have := h.caps.2.1; simp only [ctlMin] at this; omega
  · have hm := loopZeroArr_mem ha
    have hn : a ∉ preLoopA := by
      intro hc
      have := List.all_eq_true.mp preLoopA_loopZeroArrs a hm
      simp [hc] at this
    have hc : a ≠ CTL := by
      intro e; subst e; simp [loopZeroArrs, CTL] at hm
    rw [hf.1 a hn hc]; exact loadMem_rd (b := b) (pb := pb) (s8 := s8) (s64 := s64) a j
  · rw [hf.2.1 x (not_mem_of_toNat preLoopC_loopZeroCtls x (loopZeroCtl_mem hx))]
    exact loadMem_rd (b := b) (pb := pb) (s8 := s8) (s64 := s64) _ x

/-- `FrontDecls` from the twin prefix's shape fact (lane `pipeline`'s `prefix_frontDecls`). -/
theorem frontDecls_of_prefix {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) : L.Arena.FrontDecls ds :=
  fun i hi b nP e => prefix_frontDecls h b nP (by rw [← e]; simp)

theorem preLoopA_avoidCore : AvoidA 96 128 preLoopA := by
  intro b hb
  have : preLoopA.all (fun b => decide (b < 96 ∨ 128 ≤ b)) = true := by decide +kernel
  simpa using List.all_eq_true.mp this b hb

theorem preLoopC_avoidCoreN : (preLoopC.map UInt64.toNat).all (fun x => decide (x < 96 ∨ 128 ≤ x)) = true := by
  decide +kernel

theorem preLoopC_avoidCore : AvoidC 96 128 preLoopC := by
  intro x hx
  simpa using List.all_eq_true.mp preLoopC_avoidCoreN x.toNat (List.mem_map.mpr ⟨x, hx, rfl⟩)

/-- **The core tier at the loop's start**: the twin's caches are `AState.init`'s (lane `pipeline`'s
`prefix_caches`), the core's memos the loaded memory's zeros (lane `inits`' `cachesEmpty_refines`),
which no stage before the loop writes (`CoreRM.frame` over `preLoopA`, `preLoopC`). -/
theorem core_of_R7 {b pb : ByteArray} {s8 s64 : List Nat} {sA : AState} {pre : PreludeIx}
    {sB : AState} {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE)
    (h7 : R7 (ConAgua.Final.loadMem b pb s8 s64) m pb ds ipins sE) : CoreR m sE.caches := by
  rw [(prefix_caches hpx).1]
  have hctl : 120 ≤ s64[1]?.getD 0 := by
    have := h7.since.caps.2.1
    rw [loadMem_arr] at this; simp only [Array.size_replicate, ctlMin, CTL] at this; omega
  obtain ⟨M, hM⟩ := cachesEmpty_refines s64 hctl
  have hf0 : MemFrame [] [] (initMem s64) (ConAgua.Final.loadMem b pb s8 s64) := by
    refine ⟨fun a _ _ => ?_, fun x _ => ?_, fun a => ?_, ?_⟩
    · rw [loadMem_arr, initMem_arr]
    · rw [loadMem_arr, initMem_arr]
    · rw [loadMem_arr, initMem_arr]
    · simp [ConAgua.Final.loadMem, initMem]
  exact ⟨M, (hM.frame (fun _ h => by simp at h) (fun _ h => by simp at h) hf0).frame
    preLoopA_avoidCore preLoopC_avoidCore h7.since.frame⟩

/-- **The declaration loop is lane `pipeline`'s last stage**, from the inductive arm's contract
(`IndArmSpec`, lane `indproofs4`) at the checker's program with the ROM substituted
(`checkerProg.subPB bs`: the ROM readers read the pin-data buffer `PB`, whose bytes `R7` fixes;
`triple_subPB` transfers the run back; the loop's program hypotheses there are helper
`loopt3-prog`'s `checkerProg_loopCalleesPB`, `checkerProg_loopTopPB`); the contract is needed only
for buffers `pb_check` accepts (`RomOK`, starting with `romData`). -/
theorem loopStage_of_rom
    (hIA : ∀ bs, RomOK bs → bs = romData ++ bs.drop romData.length →
      ∀ dn, L.Ind.DnInj dn → IndArmSpec (checkerProg.subPB bs) dn) :
    LoopStage checkerProg checkerRels := by
  intro b pb s8 s64 sA pre sB rc sC ds sD pins ipins sE hin hpx n hn s₀ h7
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hin.2.2.1
  have hLC := fun dn hdn hq => checkerProg_loopCalleesPB pb.data.toList
    hr h7.since.pbpre dn hdn (hIA _ hr h7.since.pbpre dn hdn) hq
  have hT := twinFold_of_prefix hpx
  have hcore := core_of_R7 hpx h7
  have hcaps := CapsOK.keep h7.since.keep h7.since.caps
  have hdn : L.Ind.DnInj (dnOf sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf sE.store) := by
    obtain ⟨k, hk, hd⟩ := prefix_quotU hpx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  have hpb : s₀.mem.arr8 PB = pb.data.toList.toArray := by
    rw [h7.since.keep.arr8]; exact loadMem_pb b pb s8 s64
  refine triple_subPB (bs := pb.data.toList) checkerProg_noSt8PB (fun s hs => hs ▸ hpb) ?_
  refine triple_post (installThenCheck_start (checkerProg_loopTopPB _) (hLC _ hdn hQd) (frontDecls_of_prefix hpx)
    n hn s₀ hT h7.arena hcore h7.pinsFull h7.decls h7.pinSets h7.iw (loopZero_of_since h7.since)
    h7.pin0 (by have := hcaps.1 EREC (by decide); omega) (by have := hcaps.1 SPN (by decide); omega)
    (by have := hcaps.1 145 (by decide); omega)) ?_
  rintro r s' ⟨hl, k, fe, pend, a', s'', h1, h2⟩
  exact ⟨hl, fe, a', k, pend, s'', h1, h2⟩

end L.Checker
