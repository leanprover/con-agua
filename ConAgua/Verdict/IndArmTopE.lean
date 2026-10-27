import ConAgua.Verdict.IndArmE
import ConAgua.Verdict.IndBWt
import ConAgua.Verdict.IndBNfs
import ConAgua.Verdict.IndBTka
import ConAgua.Verdict.TopE
import ConAgua.Verdict.IndA8

/-!
# The inductive arm's verdict claim, proved (lane `verdicts-b`, helper `fin`)

`check_ind_decl`'s claim (`IndArmSpecE`) from `cid_claim3` with part B's claims in its shapes
(`IndArmE.lean`), at the programs phase A runs (`IndArmVerdict`, mirroring the ok side's
`indArmSpec_checker`); hence the driver's verdict obligations `SeqVerdicts checkerProg` and
`ThreadVerdicts` without hypotheses.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`check_ind_decl`'s claim from program facts** and the claims of `classes_nfs`,
`target_k53_args`, `whnf_telescope`. -/
theorem indArmSpecE_of {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
    (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
    (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)
    (P : CidProg p) {fs fs2 fsR fsT fsC fsH fsM : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec") (hfB : "check_basis_decl" ∈ fsC)
    (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH)
    (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hU : UceProg p)
    (hW : WtE p)
    (hNfs : ∀ dn vis fe env, ConLeche.EnvWF env → ClassesNfsE p dn vis fe env)
    (hTka : ∀ dn vis fe env, ConLeche.EnvWF env → TkaE p dn vis fe env) :
    ∀ dn, DnInj dn → IndArmSpecE p dn := by
  intro dn hdn pins n hn m a vis fe env block nP o l w _ hw hdec hb _ hT _ hfold hden hlpd hM e hc
  subst hw
  have hcE : CoreStubsE p := hkp.toKnotTopProg.coreStubsE hnv
  have hCcv : CcvE p := ccvE_of hkp hV hApd hCrk hnv hcE hU.toUceLookups
  exact cid_claim3 hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT
    hclC hfC hkP hkt hkr hnv hU.toUceLookups (genRecCheckE_of hnv hcE hU hCcv hNfs hTka)
    (checkSumTeleE_of hnv hW hCcv) (checkSumCtorsE_of hnv hcE hCcv) (checkStructFieldSortsIE_of hnv hcE)
    (checkStructProjTableRE_of hnv) (classKeyOfE_of hnv) (classMajorsE_of hnv hcE) hn hdn hc hT hfold
    (decB_decEBlk_of_decCIs hdec) hb hden hM hfB hfRc hclH hfH hclM hfM hlpd

end L.Ind

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler L.Ind ConAgua.Final

/-- **The inductive arm's error claim at the programs phase A runs** (`indArmSpec_checker`'s
program facts). -/
theorem indArmVerdict_proved : IndArmVerdict := by
  intro bs hr hpre dn hdn _hQd
  have hrom := checkerProg_romRefsPB bs hr hpre
  have hkp : KnotStageProg (Prog.subPB bs checkerProg) := by
    prog_bundle [checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
      checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs,
      (closedW_subPB bs checkerProg_coreStage : L.Ind.CoreStageClosed (Prog.subPB bs checkerProg)),
      closedW_subPB bs checkerProg_coreErec, checkerProg_natAgreePB bs, checkerProg_lvlTextPB bs,
      hrom]
  have hV : ValProg (Prog.subPB bs checkerProg) := by
    prog_bundle [checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
      checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs,
      (closedW_subPB bs checkerProg_coreStage : L.Ind.CoreStageClosed (Prog.subPB bs checkerProg)),
      closedW_subPB bs checkerProg_coreErec, checkerProg_natAgreePB bs, checkerProg_lvlTextPB bs,
      hrom]
  have P : CidProg (Prog.subPB bs checkerProg) := by prog_bundle [hrom]
  have hOpf : OpfF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hLC : LvlCacheProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hLT : (Prog.subPB bs checkerProg).lookup "lv_leq_top" = some lvLeqTop := by prog_bundle []
  have hApd : ApdF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hCrk : CrKeep (Prog.subPB bs checkerProg) :=
    ⟨closedWL_subPB bs checkerProg_indMemo, by prog_bundle []⟩
  have hIlpf : IlpfF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hLz : LzcF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hk : ∀ f ∈ passKeepCalleesC ++ tailKeepCalleesC ++ ["block_raw_rec"],
      AbsKeep (Prog.subPB bs checkerProg) f := fun f hf =>
    absKeep_of_closed (closedW_subPB bs checkerProg_armAbs) armAbsA_free armAbsC_free (armAbs_split f hf)
  have hnv := checkerProg_nvPB bs
  have hU : UceProg (Prog.subPB bs checkerProg) :=
    ⟨checkerProg_uceLookupsPB bs, strLitSupported_core _ hkp.knot.str⟩
  have hW : WtE (Prog.subPB bs checkerProg) :=
    wtE_of hkp hnv (by prog_bundle []) (by prog_bundle []) (by prog_bundle []) (by prog_bundle [])
      (by prog_bundle []) (by prog_bundle [])
  have hcE : CoreStubsE (Prog.subPB bs checkerProg) := hkp.toKnotTopProg.coreStubsE hnv
  have hCns : CnsProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hK53 : K53Look (Prog.subPB bs checkerProg) := by prog_bundle []
  exact indArmSpecE_of hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P
    (closedW_subPB bs checkerProg_armPos) (by decide +kernel) (by decide +kernel)
    (closedW_subPB bs checkerProg_armHb) (by decide +kernel)
    (closedW_subPB bs checkerProg_armRc) (by decide +kernel)
    (closedW_subPB bs checkerProg_armTa) (by decide +kernel)
    (closedW_subPB bs checkerProg_armCid) (by decide +kernel)
    (fun f hf => hk f (by simp [hf]))
    (fun f hf => hk f (by simp [hf]))
    (hk _ (by simp))
    (by decide +kernel) (by decide +kernel)
    (closedW_subPB bs checkerProg_armRcHb) (by decide +kernel)
    (closedW_subPB bs checkerProg_armMa) (by decide +kernel)
    hnv hU hW
    (fun dn vis fe _env henv => classesNfsE_of hkp henv hCns hnv hcE dn vis fe)
    (fun dn vis fe _env henv => tkaE_of hkp henv hnv hcE hK53 dn vis fe) dn hdn

/-- **The sequential driver's verdict claims**, without hypotheses. -/
theorem seqVerdicts_proved : SeqVerdicts checkerProg := seqVerdicts_of indArmVerdict_proved

/-- **The threaded harness's verdict claims**, without hypotheses. -/
theorem threadVerdicts_proved : ThreadVerdicts := threadVerdicts_of indArmVerdict_proved

/--
info: 'L.Checker.seqVerdicts_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms seqVerdicts_proved

/--
info: 'L.Checker.threadVerdicts_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms threadVerdicts_proved

end L.Checker
