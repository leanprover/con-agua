module

public import ConAgua.Checker.Prog
public import ConAgua.Checker.IndArmTrees1
public import ConAgua.Checker.IndArmTrees2

@[expose] public section

/-!
# The write sets of the inductive arm's callees in `checkerProg` (lane `indproofs4`)

The per-function checks (`prog_all`) behind the `closedA` facts `cid_ref`
(`Arena/IndT/CheckIndDecl.lean`) takes, for the checker's program, over the call-closed function
sets of `Checker/IndArmFns.lean`; and behind the write set (apart from the walk memos) of the arm's
`AbsKeep` callees that reach no walk (`armAbsFns`). As `Checker/IndMemoClosed.lean`. They are put
together by `closedW_of_all` in `Checker/IndArm.lean`: this module needs only `checkerProg` and
the array names, so its kernel checks run early in the build, beside the arm's proofs. The
nine arms are checked together, one `prog_all` over `wsChkM` (each function's name code and body
reduced once per chunk check, not once per arm: ~26 CPU-s instead of ~90 in three modules).
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## The checks -/

prog_all checkerProg_armChk : checkerProg
  (wsChkM CTL [armPosT, armHbT, armRcT, armTaT, armCidT, armRcHbT, armMaT, armMcT, armAbsT])

theorem checkerProg_armPosChk :
    ∀ x ∈ checkerProg, wsChk CTL armPosT.1 armPosT.2.1 armPosT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armHbChk :
    ∀ x ∈ checkerProg, wsChk CTL armHbT.1 armHbT.2.1 armHbT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armRcChk :
    ∀ x ∈ checkerProg, wsChk CTL armRcT.1 armRcT.2.1 armRcT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armTaChk :
    ∀ x ∈ checkerProg, wsChk CTL armTaT.1 armTaT.2.1 armTaT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armCidChk :
    ∀ x ∈ checkerProg, wsChk CTL armCidT.1 armCidT.2.1 armCidT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armRcHbChk :
    ∀ x ∈ checkerProg, wsChk CTL armRcHbT.1 armRcHbT.2.1 armRcHbT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armMaChk :
    ∀ x ∈ checkerProg, wsChk CTL armMaT.1 armMaT.2.1 armMaT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armMcChk :
    ∀ x ∈ checkerProg, wsChk CTL armMcT.1 armMcT.2.1 armMcT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armAbsChk :
    ∀ x ∈ checkerProg, wsChk CTL armAbsT.1 armAbsT.2.1 armAbsT.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)

end L.Checker
