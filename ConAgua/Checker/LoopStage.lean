import ConAgua.Arena.LoopStart
import ConAgua.Checker.PipeFinal
import ConAgua.Final.Twin

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
    205, 206, 207, 208]

/-- The `CTL` words `LoopZero` asks zero, as a list. -/
def loopZeroCtls : List Nat :=
  [48, 50, 54, 56, 58, 152, 154, 156, 158, 128, 130, 140, 141, 142, 143, 144, 145, 146, 147, 202,
    203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219]

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

/-- **The declaration loop is lane `pipeline`'s last stage**, from: the inductive arm's contract
(`IndArmSpec`, lane `indproofs4`), the loop's program hypotheses at `checkerProg`
(`LoopCallees`, `LoopTopProg`), the start facts `R7` does not carry yet (`hX`: the core tier, the
pins, the pools) and two facts of the twin's prefix (`hFD`: the front's inductive blocks have the
front's shape; `hQ`: Quot's `u` has a persistent handle). -/
theorem loopStage_of
    (hLC : ∀ dn, L.Ind.DnInj dn → QuotDn dn → LoopCallees dn checkerProg)
    (hTop : LoopTopProg checkerProg)
    (hX : ∀ l m pb ds ipins a, R7 l m pb ds ipins a →
      CoreR m a.caches ∧ PinsFull m a.pins ∧ L.Ind.IWOK m)
    (hFD : ∀ b sA pre sB rc sC ds sD pins ipins sE,
      TwinPrefix b sA pre sB rc sC ds sD pins ipins sE → FrontDecls ds)
    (hQ : ∀ b sA pre sB rc sC ds sD pins ipins sE,
      TwinPrefix b sA pre sB rc sC ds sD pins ipins sE →
      ∃ k : NIdx, k.isPersistent = true ∧ denoteN sE.store.ns k = some (.str .anonymous "u")) :
    LoopStage checkerProg checkerRels := by
  intro b pb s8 s64 sA pre sB rc sC ds sD pins ipins sE _ hpx n hn s₀ h7
  have hT := twinFold_of_prefix hpx
  obtain ⟨hcore, hpf, hiw⟩ := hX _ _ _ _ _ _ h7
  have hcaps := CapsOK.keep h7.since.keep h7.since.caps
  have hdn : L.Ind.DnInj (dnOf sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf sE.store) := by
    obtain ⟨k, hk, hd⟩ := hQ _ _ _ _ _ _ _ _ _ _ _ hpx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  refine triple_post (installThenCheck_start hTop (hLC _ hdn hQd) (hFD _ _ _ _ _ _ _ _ _ _ _ hpx)
    n hn s₀ hT h7.arena hcore hpf h7.decls h7.pinSets hiw (loopZero_of_since h7.since) h7.pin0
    (by have := hcaps.1 EREC (by decide); omega) (by have := hcaps.1 SPN (by decide); omega)
    (by have := hcaps.1 145 (by decide); omega)) ?_
  rintro r s' ⟨hl, k, fe, pend, a', s'', h1, h2⟩
  exact ⟨hl, fe, a', k, pend, s'', h1, h2⟩

end L.Checker
