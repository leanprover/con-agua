module

public import ConAgua.Verdict.TopE
import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Checker.IndArm
import ConAgua.Checker.IotaArm
import ConAgua.Checker.ArmsT
import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProg
import ConAgua.Verdict.KnotAllE
import ConAgua.Verdict.DeclTopE
import ConAgua.Verdict.CheckBE
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.BlockRefsProg
import ConAgua.Final.DrvFinal
import ConAgua.Verdict.FrontStageE
public import ConAgua.Final.ThreadsVerdict

@[expose] public section

/-!
# The inductive arm's verdict claim, proved (lane `verdicts-b`, helper `fin`)

`check_ind_decl`'s claim (`IndArmSpecE`): the error half of its refinement `cid_ref` (`RefE.run_err`,
under `CtsG`, built from the program facts), at the programs phase A runs (`IndArmVerdict`, mirroring the ok side's
`indArmSpec_checker`); hence the driver's verdict obligations `SeqVerdicts checkerProg` and
`ThreadVerdicts` without hypotheses.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section
variable {p : Prog}

/-- **`check_ind_decl`'s claim from program facts** (`IndArmSpecE`): `cid_ref`'s error half,
under the premises of the ok side's `indArmSpec_of` and the verdict context. -/
theorem indArmSpecE_of (P : CidProg2 p) (hbr : ∀ dn, DnInj dn → BlockRefS (VerdictCtxU p) p dn)
    {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC) (hG : VerdictCtxU p) :
    ∀ dn, DnInj dn → IndArmSpecE p dn := by
  intro dn hdn pins n hn m a vis fe env block nP o l w _ hw hdec hb _ hT _ hfold hden hlpd _ hM e hc
  subst hw
  exact RefE.run_err (cidE_spec p P.toCidProg n ⟨m, Locals.init []⟩ vis o l w) hG.nv hG
    (cid_ref P (hbr dn hdn) hclC hfC (N := n) (by omega) hT hfold hdec hb hden hM hlpd) hc

end

end L.Ind

namespace L.Checker

universe u

open L L.Arena L.Front L.Rom L.Compiler L.Ind ConAgua.Final

/-- **The inductive arm's error claim at the substituted checker program** (`indArmSpec_checker`'s
error half, from the same contracts). -/
theorem indArmSpecE_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length)
    (hR : ∀ dn, DnInj dn → CbRefs (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn) :
    ∀ dn, DnInj dn → IndArmSpecE (Prog.subPB bs checkerProg) dn := by
  have H := indArmProgs_checker bs hr hpre
  have hnv := checkerProg_nvPB bs
  have hU : UceProg (Prog.subPB bs checkerProg) :=
    ⟨checkerProg_uceLookupsPB bs⟩
  exact indArmSpecE_of ⟨H.cid, checkerProg_coreStagePB bs, H.lc, iotaArmProg_checker bs⟩
    (blockRefS_checker bs hR) (closedW_subPB bs checkerProg_armCid) armCid_frame
    ⟨⟨hnv, checkerProg_coreStubsEPB bs⟩, hU⟩


/-- **The jobs' error claims at the programs phase B runs** (`JobG`: `check_decl`'s arms' claims,
`armsE_of`, and the inductive arm's, `indArmSpecE_checker`), at every phase A. -/
theorem jobG_checker (b pb : ByteArray) (PA : PhaseA b) (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg) := by
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
      (checkerProg_quotSimsPB _ hr hpre PA.quotDn) PA.dnInj hG)
    (indArmSpecE_checker _ hr hpre (cbRefs_checker _ hr hpre (snoSim_checker _)) _ PA.dnInj) hnv

/-- **A thread's failing call is the pool's failure** (`ThreadEVerdict`): `threads_twinVerdictPooled`
at `check_decl`'s program facts (`checkerCd_proved`) and the jobs' error claims (`jobG_checker`). -/
theorem threadEVerdict_proved : ThreadEVerdict :=
  threads_twinVerdictPooled checkerCd_proved jobG_checker

/-- **The sequential driver's verdict claims**: entry 1's from its stages' error specs, entry 2's from the jobs' (`entry2Verdict_of`). -/
theorem seqVerdicts_proved : SeqVerdicts checkerProg where
  entry1 := entry1Verdict_of ⟨checker_preludeStageE, checker_frontStageE⟩
  entry2 := entry2Verdict_of checkerCd_proved jobG_checker

/-- **The threaded harness's verdict claims**, without hypotheses. -/
theorem threadVerdicts_proved : ThreadVerdicts where
  entry1 := entry1Verdict_of ⟨checker_preludeStageE, checker_frontStageE⟩
  thr := threadEVerdict_proved

/--
info: 'L.Checker.seqVerdicts_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms seqVerdicts_proved

-- TEMP (compare2-freeze): `sorryAx` from the stand-in `thr_ctl_next`
/--
info: 'L.Checker.threadVerdicts_proved' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms threadVerdicts_proved

end L.Checker
