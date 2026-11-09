module

public import ConAgua.Verdict.TopE
import ConAgua.Verdict.PosKnotE
import ConAgua.Arena.IndArmBridge2
import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Arena.StrLitSup
import ConAgua.Checker.IndArm
import ConAgua.Arena.IndArm
import ConAgua.Checker.BasisBlockProg
import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProg
import ConAgua.Verdict.KnotAllE
public import ConAgua.Arena.IndInstallSpec.BpRecBpassR
public import ConAgua.Arena.IndInstallSpec.ConsRecsTFSimOf
public import ConAgua.Arena.IndInstallSpec.OfClosed
public import ConAgua.Arena.IndInstallSpec.ShapeCVOfDecB
public import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.IndT.ArmMemos
public import ConAgua.Arena.IndT.GenRec2
public import ConAgua.Arena.IndT.Lift

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
variable {p : Prog} (hV : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
  (hcrf : CrfF p)

include hV hq hap hkp hcrf in
/-- **`check_ind_decl`'s claim from program facts** (`IndArmSpecE`): `cid_ref`'s error half,
under the premises of the ok side's `indArmSpec_of` and the verdict context. -/
theorem indArmSpecE_of (P : CidProg2 p) (hCS : ∀ dn, CcvSims p dn)
    (hcb : ∀ dn, DnInj dn → CbbRef p dn) (hbr : ∀ dn, DnInj dn → BlockRefS (VerdictCtxU p) p dn)
    {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC) (hG : VerdictCtxU p) :
    ∀ dn, DnInj dn → IndArmSpecE p dn := by
  intro dn hdn pins n hn m a vis fe env block nP o l w _ hw hdec hb _ hT _ hfold hden hlpd _ hM e hc
  subst hw
  exact RefE.run_err (cidE_spec p hV P.toCidProg n ⟨m, Locals.init []⟩ vis o l w) hG.nv hG
    (cid_ref hV hq hap hkp hcrf P id (hCS dn) (hcb dn hdn) (hbr dn hdn) hclC hfC (N := n) (by omega)
      hT hfold hdec hb hden hM hlpd) hc

end

end L.Ind

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler L.Ind ConAgua.Final

/-- **The inductive arm's error claim at the substituted checker program** (`indArmSpec_checker`'s
error half, from the same contracts). -/
theorem indArmSpecE_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length)
    (hCS : ∀ dn, CcvSims (Prog.subPB bs checkerProg) dn)
    (hB : BasisRefs (Prog.subPB bs checkerProg))
    (hcb : ∀ dn, DnInj dn → CbbRef (Prog.subPB bs checkerProg) dn)
    (hR : ∀ dn, DnInj dn → CbRefs (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn) :
    ∀ dn, DnInj dn → IndArmSpecE (Prog.subPB bs checkerProg) dn := by
  have H := indArmProgs_checker bs hr hpre
  have hV : CcvProg (Prog.subPB bs checkerProg) := (checkerProg_thmArmPB bs hr hpre).ccv
  have hcrf : CrfF (Prog.subPB bs checkerProg) := checkerProg_crfPB bs
  have hnv := checkerProg_nvPB bs
  have hU : UceProg (Prog.subPB bs checkerProg) :=
    ⟨checkerProg_uceLookupsPB bs, strLitStored_core _ H.kp.knot.str⟩
  exact indArmSpecE_of hV H.kp H.apd H.crk hcrf ⟨H.cid, hB, checkerProg_coreStagePB bs, H.lc⟩ hCS hcb
    (blockRefS_checker bs hR) (closedW_subPB bs checkerProg_armCid) armCid_frame
    ⟨⟨hnv, checkerProg_coreStubsEPB bs⟩, hU⟩

/-- **The sequential driver's verdict claims**, without hypotheses. -/
theorem seqVerdicts_proved : SeqVerdicts checkerProg := by
  sorry

/-- **The threaded harness's verdict claims**, without hypotheses. -/
theorem threadVerdicts_proved : ThreadVerdicts := by
  sorry

-- ronsync2 stage 2: /--
-- ronsync2 stage 2: info: 'L.Checker.seqVerdicts_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-- ronsync2 stage 2: -/
-- ronsync2 stage 2: #guard_msgs in #print axioms seqVerdicts_proved

-- ronsync2 stage 2: /--
-- ronsync2 stage 2: info: 'L.Checker.threadVerdicts_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-- ronsync2 stage 2: -/
-- ronsync2 stage 2: #guard_msgs in #print axioms threadVerdicts_proved

end L.Checker
