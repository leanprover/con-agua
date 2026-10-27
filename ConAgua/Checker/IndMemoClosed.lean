import ConAgua.Checker.Prog
import ConAgua.Arena.IndMemoFns
import ConAgua.Arena.LevelIntern
import ConAgua.Arena.LevelSubstLP

/-!
# The loop's non-inductive callees leave the inductive stage's memos alone (lane `indproofs4`)

`ConAgua/Arena/IndMemoFns.lean`'s program hypothesis `IndMemoClosed`, for the checker's program:
every function of `imFns` stores into arrays other than 51, 155, 201‥208 and into `CTL` words
other than 52, 158, 202‥219, and calls only into `imFns` and `consts_resolve_ffast`. Split into
per-chunk kernel checks as `checkerProg_coreStage` (`Checker/IndCore.lean`).
-/

namespace L.Checker

open L.Arena L.Compiler

/-- `imFns` and its leaves as a tree of name codes (the callees a body may name). -/
names_tree imCallTree : imFns ++ imLeaves

/-- The arrays of `imA`, as a test. -/
def imPa (a : ArrId) : Bool :=
  decide (a < 388) && a != 51 && a != 155 && (decide (a < 201) || decide (208 < a))

/-- The `CTL` words of `imC`, as a test. -/
def imPc (w : Word) : Bool :=
  decide (w.toNat < 1024) && w.toNat != 52 && w.toNat != 158 &&
    (decide (w.toNat < 202) || decide (219 < w.toNat))

theorem imPa_mem (a : ArrId) (h : imPa a = true) : a ∈ imA := by
  simp only [imPa, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  simp only [imA, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem imPc_mem (w : Word) (h : imPc w = true) : w ∈ imC := by
  simp only [imPc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  simp only [imC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨w.toNat, ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes the per-function check of `imFns`. -/
prog_all checkerProg_imChk : checkerProg (wsChkL CTL imPa imPc imTree imCallTree)

theorem checkerProg_indMemo : IndMemoClosed checkerProg :=
  closedWL_of_all imTree.eq imCallTree.eq imPa_mem imPc_mem checkerProg_imChk

end L.Checker
