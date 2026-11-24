module

import ConAgua.Verdict.IndArmTopE
import ConAgua.Verdict.DeclTopE
import ConAgua.Checker.IndArm
import ConAgua.Checker.ArmsT
import ConAgua.Verdict.KnotAllE
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.BlockRefsProg
import ConAgua.Verdict.TopE
import ConAgua.Checker.StreamRecsProg
public import ConAgua.Checker.PipeStages
public import ConAgua.Arena.Jobs

@[expose] public section

/-!
# The jobs' error claims at the checker for any record decoder (lane compare2)

`jobG_ofDn`: `jobG_checker` without the stages, for a record decoder that is injective and gives
`Quot`'s universe name a handle (the compared run's headers' decoders).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- **The jobs' error claims at the checker for any record decoder** that is injective and gives
`Quot`'s universe name a handle (`jobG_checker` without the stages). -/
theorem jobG_ofDn {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} (hinj : L.Ind.DnInj dn) (hq : L.Ind.QuotDn dn) (pb : ByteArray)
    (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobG ipins dn ds (Prog.subPB pb.data.toList checkerProg) := by
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have H := indArmProgs_checker _ hr hpre
  have hnv := checkerProg_nvPB pb.data.toList
  have hU : UceProg (Prog.subPB pb.data.toList checkerProg) :=
    ⟨checkerProg_uceLookupsPB _⟩
  have hG : VerdictCtxU (Prog.subPB pb.data.toList checkerProg) :=
    ⟨⟨hnv, checkerProg_coreStubsEPB _⟩, hU⟩
  exact jobG_of _ _ _ _
    (armsE_of _ _ _ _ (checkerProg_axArmPB _ hr hpre) (checkerProg_defnArmPB _ hr hpre)
      (checkerProg_thmArmPB _ hr hpre) (checkerProg_opqArmPB _ hr hpre) (checkerProg_quotArmPB _)
      (checkerProg_knotStagePB _) (checkerProg_leafClosedPB _) (checkerProg_apdPB _)
      (checkerProg_crKeepPB _) (checkerProg_crfPB _) (checkerProg_ccvSimsPB _ _)
      (checkerProg_quotSimsPB _ hr hpre hq) hinj hG)
    (indArmSpecE_checker _ hr hpre (cbRefs_checker _ hr hpre (snoSim_checker _)) _ hinj) hnv

end L.Checker
