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
program facts, `indArmProgs_checker`). -/
theorem indArmVerdict_proved : IndArmVerdict := by
  intro bs hr hpre dn hdn _hQd
  have H := indArmProgs_checker bs hr hpre
  have hkp := H.kp
  have hk := indArmKeep_checker bs
  have hnv := checkerProg_nvPB bs
  have hU : UceProg (Prog.subPB bs checkerProg) :=
    ⟨checkerProg_uceLookupsPB bs, strLitSupported_core _ hkp.knot.str⟩
  have hW : WtE (Prog.subPB bs checkerProg) :=
    wtE_of hkp hnv (by prog_bundle []) (by prog_bundle []) (by prog_bundle []) (by prog_bundle [])
      (by prog_bundle []) (by prog_bundle [])
  have hcE : CoreStubsE (Prog.subPB bs checkerProg) := hkp.toKnotTopProg.coreStubsE hnv
  have hCns : CnsProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hK53 : K53Look (Prog.subPB bs checkerProg) := by prog_bundle []
  exact indArmSpecE_of hkp H.v H.opf H.lc H.lt H.apd H.crk H.ilpf H.lz H.cid
    (closedW_subPB bs checkerProg_armPos) armPos_pass armPos_raw
    (closedW_subPB bs checkerProg_armHb) armHb_tail
    (closedW_subPB bs checkerProg_armRc) armRc_tail
    (closedW_subPB bs checkerProg_armTa) armTa_block
    (closedW_subPB bs checkerProg_armCid) armCid_frame
    (fun f hf => hk f (by simp [hf]))
    (fun f hf => hk f (by simp [hf]))
    (hk _ (by simp))
    armCid_basis armRc_grc
    (closedW_subPB bs checkerProg_armRcHb) armRcHb_tables
    (closedW_subPB bs checkerProg_armMa) armMa_pass
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
