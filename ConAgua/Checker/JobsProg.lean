module

public import ConAgua.Checker.LoopProg
public import ConAgua.Checker.JobsClosed
import ConAgua.Checker.IndMemoClosed
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgInd
meta import ConAgua.Checker.LoopProg
meta import ConAgua.Checker.JobsClosed
meta import ConAgua.Checker.IndMemoClosed
meta import ConAgua.Checker.LoopProgInd
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.Scratch
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.DeclAndPin
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.MemoLib

@[expose] public section

/-!
# The jobs' program facts at the substituted checker program

`JobProg` (`Arena/Jobs.lean`) at `Prog.subPB bs checkerProg`: the lookups, the bracket,
`and_pin_ok`'s inductive arm and `rom_and_pin` (`checkerProg_romRefsPB`), the write sets
(`Checker/JobsClosed.lean`, through `closedW_subPB`), and given `check_decl`'s facts `CdProg` and
the canonical comparisons' lookups `CanonProg` (the core area's bundles at the checker's program).
-/

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Arena

/-- **The jobs' program facts at the substituted checker program**, given `check_decl`'s
(`CdProg`) and the canonical comparisons' (`CanonProg`) there. -/
theorem checkerProg_jobProgPB (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) {pins : List INatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    (hcdP : CdProg pins dn ds (Prog.subPB bs checkerProg))
    (hcanon : L.Ind.CanonProg (Prog.subPB bs checkerProg)) :
    JobProg pins dn ds (Prog.subPB bs checkerProg) := by
  have hrom := checkerProg_romRefsPB bs
  have hap : ∃ F, "and_pin_ok" ∈ F ∧ closedA (Prog.subPB bs checkerProg) apA apC F = true :=
    let ⟨F, h, hc⟩ := checkerProg_apW; ⟨F, h, closedW_subPB bs hc⟩
  have hcd : ∃ F, "check_decl" ∈ F ∧ closedA (Prog.subPB bs checkerProg) cdA cdC F = true :=
    let ⟨F, h, hc⟩ := checkerProg_cdW; ⟨F, h, closedW_subPB bs hc⟩
  have hAP : AndPinIndProg (Prog.subPB bs checkerProg) := by
    refine ⟨hcdP.ibe, ?_, ?_, ?_, ?_, ?_, hcanon⟩ <;> chk_lk
  refine ⟨?_, ?_, hcdP, ?_, ?_, hAP, hrom.andPin, hap, hcd⟩
  · chk_lk
  · chk_lk
  · prog_bundle []
  · chk_lk

end L.Checker
