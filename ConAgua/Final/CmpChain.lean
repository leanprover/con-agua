module

import all ConAgua.Checker.Entry
import ConAgua.Checker.BlockRefsProg
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.IndArm
import ConAgua.Checker.StreamRecsProg
public import ConAgua.Checker.ParDriverTwin

@[expose] public section

/-!
# The compared run's L-level chain, for the checker (lane compare)

`checkerCdG_proved`: `check_decl`'s program facts at every injective record decoder, for the
compared run's phases.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- **`check_decl`'s program facts at every injective record decoder** (`CheckerCdG`; the
flat run's `checkerCd_proved` at any decoder). -/
theorem checkerCdG_proved : L.Checker.CheckerCdG := fun pb _ dn _ hpb hpre hdn =>
  have hr : L.Rom.RomOK pb.data.toList := by simpa [L.Rom.RomOK] using hpb
  ⟨L.Checker.checkerProg_defnLoopPB _ hr hpre,
    L.Checker.indArmSpec_checker _ hr hpre
      (L.Checker.cbRefs_checker _ hr hpre (L.Checker.snoSim_checker _)) dn hdn⟩

end ConAgua.Final
