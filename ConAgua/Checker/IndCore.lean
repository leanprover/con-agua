import ConAgua.Checker.Prog
import ConAgua.Arena.IndTwin
import ConAgua.Compiler.WriteSetSplit

/-!
# The core leaves the stage's pools and the pins alone (lane `indproofs3`)

`ConAgua/Arena/IndTwin.lean`'s program hypothesis `CoreStageClosed`, for the checker's program:
every function the stage's core entry points reach (`stageCoreFns`) stores into arrays other than
`IW`, `EREC`, `PINS`, and into `CTL` words other than `129`, `200`.

Split into per-chunk kernel checks as `checkerProg_coreErec` (lane `erecfix`,
`Compiler/WriteSetSplit.lean`): one `decide +kernel` on the whole closure took tens of GB.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `stageCoreFns` as a tree of name codes. -/
names_tree stageCoreTree : stageCoreFns

/-- The arrays of `coreStageA`, as a test. -/
def coreStagePa (a : ArrId) : Bool := decide (a < 388) && a != EREC && a != IW && a != PINS &&
  a != 51 && a != 155 && (decide (a < 201) || decide (208 < a))

/-- The `CTL` words of `coreStageC`, as a test. -/
def coreStagePc (w : Word) : Bool := decide (w.toNat < 256) && w.toNat != 129 && w.toNat != 200 &&
  w.toNat != 52 && w.toNat != 158 && (decide (w.toNat < 202) || decide (219 < w.toNat))

theorem coreStagePa_mem (a : ArrId) (h : coreStagePa a = true) : a ∈ coreStageA := by
  simp only [coreStagePa, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp [coreStageA, List.mem_filter, List.mem_range, h]

theorem coreStagePc_mem (w : Word) (h : coreStagePc w = true) : w ∈ coreStageC := by
  simp only [coreStagePc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [coreStageC, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨w.toNat, ⟨h.1.1.1.1.1, by simp only [decide_eq_true_eq]; omega⟩, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes the stage core's per-function check. -/
prog_all checkerProg_stageChk : checkerProg (wsChk CTL coreStagePa coreStagePc stageCoreTree)

theorem checkerProg_coreStage : CoreStageClosed checkerProg :=
  closedW_of_all stageCoreTree.eq coreStagePa_mem coreStagePc_mem checkerProg_stageChk

end L.Checker
