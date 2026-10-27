import ConAgua.Checker.LoopProg
import ConAgua.Checker.IndArmClosed
import ConAgua.Arena.IndArm

/-!
# The inductive arm's contract at the checker's program (lane `indproofs4`)

`indArmSpec_of` (`Arena/IndArm.lean`) at `checkerProg.subPB bs`: the lookups by `prog_bundle`,
the write sets from `Checker/IndArmClosed.lean` (carried to the substituted program by
`closedW_subPB`), the `AbsKeep` facts of the callees that reach no walk from their write set
(`absKeep_of_closed`). The callees whose closure writes the walk memos (`armAbsWalk`: they reach
the core or the `instantiate`/`abstract` walks) keep `AbsKeep` as a hypothesis.
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind L.Compiler

theorem armAbs_split : ∀ f ∈ passKeepCalleesC ++ tailKeepCalleesC ++ ["block_raw_rec"],
    f ∈ armAbsFns := by decide +kernel

/-- **The inductive arm's contract at the substituted checker program**, from `AbsKeep` of the
callees that reach the walks. -/
theorem indArmSpec_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) :
    ∀ dn, DnInj dn → IndArmSpec (Prog.subPB bs checkerProg) dn := by
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
  exact indArmSpec_of hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P
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
    (closedW_subPB bs checkerProg_armMc) (by decide +kernel)

end L.Checker
