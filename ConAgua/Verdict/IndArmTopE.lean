import ConAgua.Verdict.IndArmE
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

/-- **`check_ind_decl`'s claim from program facts** and the claims of `target_k53_args`,
`whnf_telescope`. -/
theorem indArmSpecE_of {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
    (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
    (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)
    (P : CidProg p) {fs fs2 fsR fsT fsC fsH fsM fsMc : List FnName}
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
    (hclMc : closedA p mcFreeA mcFreeC fsMc = true) (hfMc : "check_block" ∈ fsMc)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hU : UceProg p)
    (hWt : WhnfTopE p) :
    ∀ dn, DnInj dn → IndArmSpecE p dn := by
  intro dn hdn pins n hn m a vis fe env block nP o l w _ hw hdec hb _ hT _ hfold hden hlpd hM e hc
  subst hw
  have hcE : CoreStubsE p := hkp.toKnotTopProg.coreStubsE hnv
  exact cid_claim3 hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT
    hclC hfC hkP hkt hkr hnv hU
    (checkSumTeleE_of ⟨⟨⟨hnv, hcE⟩, hU⟩, hWt⟩) (checkSumCtorsE_of hnv hcE hU) (checkStructFieldSortsIE_of hnv hcE)
    hn hdn hc hT hfold
    (decB_decEBlk_of_decCIs hdec) hb hden hM hfB hfRc hclH hfH hclM hfM hclMc hfMc hlpd

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
  have hWt : WhnfTopE (Prog.subPB bs checkerProg) :=
    whnfTop_stageE hkp.whnfTop hkp.knotOK (fun n => L.Arena.KnotAllProg.knotE_all hkp.knot hnv n)
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
    (closedW_subPB bs checkerProg_armMc) armMc_block
    hnv hU hWt dn hdn

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
