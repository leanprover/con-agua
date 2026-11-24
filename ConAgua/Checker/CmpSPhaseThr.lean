module

public import ConAgua.Final.CmpChainC
public import ConAgua.Checker.ParThreadTwin
public import ConAgua.Checker.CmpSPhase
public import ConAgua.Checker.CmpSPhaseT
import ConAgua.Checker.CmpThreadsC
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConAgua.Arena.LoopStart
import ConRon.Bridge.Compare.Mates

@[expose] public section

/-!
# Both phases' threads from the challenge's index state (lane compare2, design (i))

The compared run's one frozen image after mode `6`'s steps (`F6`, memory `m9`), read through two
headers: header C's view is `m9`, header S's view is `CsViewS m m9 mS`. A buffer `B` whose first
call agrees with a memory's fresh worker memory (`CsFirst B mS`, what a header's view gives)
starts every thread in the jobs' relation.

* `Side6.uniq`, `F6.jobMAt`: the challenge's job memory half at any witnesses of the steps.
* `Side6.stagesI`: the stages of the compared run up to the challenge's index build (`CmpStages`).
-/

open ConRon.Arena ConRon.Bridge

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

/-- **A buffer's first call starts at a memory's fresh worker memory**: from a fresh region (`INIT
= 0`, every owned array zero at its size in `m`), the memory after `check_b`'s seed copy on
`bufMem B r j` agrees with `freshMem m` on `thrS` (`thr_first` for `bufOf m`). -/
def CsFirst (B : Array Word) (m : Mem) : Prop :=
  ∀ (r : Mem) (j : Word), (∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size) → r.glob INIT = 0 →
    ∀ t, thrS t = true → (L.Checker.seedMem (bufMem B r j)).arr64 t = (freshMem m).arr64 t

section
variable {bC bS : ByteArray} {PS : PhaseS bC bS} {m : Mem} {c : Word}

/-- **Mode `6`'s steps are deterministic on the twin's side**: the preparation's records and state
and the side records. -/
theorem _root_.L.Checker.Side6.uniq {m2 m3 m2' m3' m4 m4' : Mem} {dsC dsC' : Array IDeclaration} {sG sG' : AState}
    {res res' : List IDeclaration} (h : Side6 PS m c m2 m3 dsC sG res m4)
    (h' : Side6 PS m c m2' m3' dsC' sG' res' m4') : dsC' = dsC ∧ sG' = sG ∧ res' = res := by
  have e := h.prep.run.symm.trans h'.prep.run
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have e2 := h.run.symm.trans h'.run
  simp only [Except.ok.injEq, Prod.mk.injEq] at e2
  exact ⟨rfl, rfl, e2.1.symm⟩

/-- **The challenge's job memory half at given witnesses of mode `6`'s steps** (`F6.jobM`). -/
theorem _root_.L.Checker.F6.jobMAt {pb : ByteArray} {sz : TieredArray → Nat} {m₇ : Mem}
    (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {m9 : Mem} (h6 : F6 PS m c m9)
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a')) :
    JobM PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I m9 a' ∧
      StoreWF a'.store ∧ a'.store.scratchOn = false ∧ ∀ t, (m9.arr64 t).size = (m.arr64 t).size := by
  obtain ⟨m2', m3', dsC', sG', res', m4', I', a'', h', hI', hJM, hwf, hoff, hsz⟩ := F6.jobM hF h6
  obtain ⟨-, rfl, rfl⟩ := h.uniq h'
  rw [hI] at hI'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hI'
  obtain ⟨rfl, rfl⟩ := hI'
  exact ⟨hJM, hwf, hoff, hsz⟩

end

/-- **The stages of the compared run up to the challenge's index build**, from mode `6`'s steps. -/
theorem _root_.L.Checker.Side6.stagesI {bC bS : ByteArray} {PS : PhaseS bC bS} {m : Mem} {c : Word}
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a')) :
    CmpStages bC bS PS.pins PS.ipins PS.dsS res PS.IS I a' := by
  obtain ⟨⟨hA, hB, hC'⟩, hCS, hDS⟩ := PS.pfx
  exact ⟨PS.sA, PS.sB, PS.sC, PS.sC', PS.sD, PS.sE, PS.sF, sG, sG, PS.pre, PS.rC, PS.rS, dsC,
    hA, hB, hC', hCS, hDS, PS.pinsR, PS.idx, h.prep.run, h.run, hI⟩

end ConAgua.Final
