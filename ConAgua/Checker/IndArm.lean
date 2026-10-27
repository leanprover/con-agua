import ConAgua.Checker.LoopProg
import ConAgua.Checker.IndArmClosed1
import ConAgua.Checker.IndArmClosed2
import ConAgua.Checker.IndArmClosed3
import ConAgua.Arena.IndArm

/-!
# The inductive arm's contract at the checker's program (lane `indproofs4`)

`indArmSpec_of` (`Arena/IndArm.lean`) at `checkerProg.subPB bs`: the lookups by `prog_bundle`
(`indArmProgs_checker`, shared with the verdict side's `indArmVerdict_proved`), the write sets
from `Checker/IndArmClosed.lean`'s per-function checks (carried to the substituted program by
`closedW_subPB`), the `AbsKeep` facts of the callees that reach no walk from their write set
(`absKeep_of_closed`). The callees whose closure writes the walk memos (`armAbsWalk`: they reach
the core or the `instantiate`/`abstract` walks) keep `AbsKeep` as a hypothesis.
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind L.Compiler

/-! ## The write sets (`Checker/IndArmClosed.lean`'s per-function checks) -/

theorem checkerProg_armPos : closedA checkerProg posFreeA posFreeC armPosFns = true :=
  closedW_of_all armPosTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armPosChk
theorem checkerProg_armHb : closedA checkerProg hbFreeA hbFreeC armHbFns = true :=
  closedW_of_all armHbTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armHbChk
theorem checkerProg_armRc : closedA checkerProg rcFreeA rcFreeC armRcFns = true :=
  closedW_of_all armRcTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armRcChk
theorem checkerProg_armTa : closedA checkerProg taFreeA taFreeC armTaFns = true :=
  closedW_of_all armTaTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armTaChk
theorem checkerProg_armCid : closedA checkerProg cidFreeA cidFreeC armCidFns = true :=
  closedW_of_all armCidTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armCidChk
theorem checkerProg_armRcHb : closedA checkerProg rcHbFreeA rcHbFreeC armRcHbFns = true :=
  closedW_of_all armRcHbTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armRcHbChk
theorem checkerProg_armMa : closedA checkerProg maFreeA maFreeC armMaFns = true :=
  closedW_of_all armMaTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armMaChk
theorem checkerProg_armMc : closedA checkerProg mcFreeA mcFreeC armMcFns = true :=
  closedW_of_all armMcTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armMcChk
theorem checkerProg_armAbs : closedA checkerProg armAbsA armAbsC armAbsFns = true :=
  closedW_of_all armAbsTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armAbsChk

/-! ## The roots in the function sets, by their name trees -/

/-- A list in a function set, from the set's name tree: `nameCode`s looked up in the tree, no
`String` comparison (`decide +kernel` on `l ⊆ fs` compares each name of `l` with every name of
`fs`, ~1 s per list). -/
theorem subset_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t)
    {l : List FnName} (h : l.all (fun f => (t.find (nameCode f)).isSome) = true) :
    ∀ f ∈ l, f ∈ fs := fun f hf => by
  have := List.all_eq_true.mp h f hf
  rw [namesTree_spec ht] at this
  exact of_decide_eq_true this

theorem mem_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t) {f : FnName}
    (h : (t.find (nameCode f)).isSome = true) : f ∈ fs := by
  rw [namesTree_spec ht] at h
  exact of_decide_eq_true h

theorem armPos_pass : ∀ f ∈ passCallees, f ∈ armPosFns := subset_of_tree armPosTree.eq (by decide +kernel)
theorem armPos_raw : "block_raw_rec" ∈ armPosFns := mem_of_tree armPosTree.eq (by decide +kernel)
theorem armHb_tail : ∀ f ∈ tailCallees, f ∈ armHbFns := subset_of_tree armHbTree.eq (by decide +kernel)
theorem armRc_tail : ∀ f ∈ tailRcCallees, f ∈ armRcFns := subset_of_tree armRcTree.eq (by decide +kernel)
theorem armTa_block : ∀ f ∈ blockTaCallees, f ∈ armTaFns :=
  subset_of_tree armTaTree.eq (by decide +kernel)
theorem armCid_frame : ∀ f ∈ cidFrameCallees, f ∈ armCidFns :=
  subset_of_tree armCidTree.eq (by decide +kernel)
theorem armCid_basis : "check_basis_decl" ∈ armCidFns := mem_of_tree armCidTree.eq (by decide +kernel)
theorem armRc_grc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ armRcFns :=
  subset_of_tree armRcTree.eq (by decide +kernel)
theorem armRcHb_tables : "check_block_tables" ∈ armRcHbFns :=
  mem_of_tree armRcHbTree.eq (by decide +kernel)
theorem armMa_pass : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ armMaFns :=
  subset_of_tree armMaTree.eq (by decide +kernel)
theorem armMc_block : "check_block" ∈ armMcFns := mem_of_tree armMcTree.eq (by decide +kernel)
theorem armAbs_split : ∀ f ∈ passKeepCalleesC ++ tailKeepCalleesC ++ ["block_raw_rec"],
    f ∈ armAbsFns := subset_of_tree armAbsTree.eq (by decide +kernel)

/-! ## The program facts at the substituted checker program -/

/-- The program facts `indArmSpec_of` takes (and the verdict side's `indArmSpecE_of`), as one
bundle: proved once (`indArmProgs_checker`) for both. -/
structure IndArmProgs (p : Prog) : Prop where
  kp : KnotStageProg p
  v : ValProg p
  opf : OpfF p
  lc : LvlCacheProg p
  lt : p.lookup "lv_leq_top" = some lvLeqTop
  apd : ApdF p
  crk : CrKeep p
  ilpf : IlpfF p
  lz : LzcF p
  cid : CidProg p

/-- **The inductive arm's program facts at the substituted checker program** (one `prog_bundle`:
a lookup two fields share is proved once). -/
theorem indArmProgs_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) : IndArmProgs (Prog.subPB bs checkerProg) := by
  have hrom := checkerProg_romRefsPB bs hr hpre
  prog_bundle [checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
    checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs,
    (closedW_subPB bs checkerProg_coreStage : L.Ind.CoreStageClosed (Prog.subPB bs checkerProg)),
    closedW_subPB bs checkerProg_coreErec, checkerProg_natAgreePB bs, checkerProg_lvlTextPB bs,
    hrom, closedWL_subPB bs checkerProg_indMemo]

/-- `AbsKeep` of the arm's callees that reach no walk, from their write set. -/
theorem indArmKeep_checker (bs : List UInt8) :
    ∀ f ∈ passKeepCalleesC ++ tailKeepCalleesC ++ ["block_raw_rec"],
      AbsKeep (Prog.subPB bs checkerProg) f := fun f hf =>
  absKeep_of_closed (closedW_subPB bs checkerProg_armAbs) armAbsA_free armAbsC_free (armAbs_split f hf)

/-- **The inductive arm's contract at the substituted checker program**, from `AbsKeep` of the
callees that reach the walks. -/
theorem indArmSpec_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) :
    ∀ dn, DnInj dn → IndArmSpec (Prog.subPB bs checkerProg) dn := by
  have H := indArmProgs_checker bs hr hpre
  have hk := indArmKeep_checker bs
  exact indArmSpec_of H.kp H.v H.opf H.lc H.lt H.apd H.crk H.ilpf H.lz H.cid
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

end L.Checker
