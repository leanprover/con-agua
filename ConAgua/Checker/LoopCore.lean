import ConAgua.Checker.Prog
import ConAgua.Arena.LoopT
import ConAgua.Compiler.WriteSetSplit

/-!
# The core leaves the declaration loop's state alone (lane `loopt`)

`ConAgua/Arena/LoopT.lean`'s program hypothesis `CoreLoopClosed`, for the checker's program: every
function the stage's core entry points reach (`stageCoreFns`) stores only into arrays a step may
write (`stepA`) other than `EREC`, `IW`, `PINS` and the stage memos 201‥208, and into `CTL` words a
step may write (`stepC`) other than `129`, `200` and 202‥219. So a core call keeps `LoopT`
(`LoopT.of_core`). Per-chunk kernel checks as lane `erecfix`'s `checkerProg_coreStage` (one
`decide +kernel` over the whole closure takes tens of GB).
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler
open L.Front (DECL DLP)

/-- `stageCoreFns` as a tree of name codes. -/
names_tree loopCoreTree : stageCoreFns

/-- The arrays of `coreLoopA`, as a test. -/
def coreLoopPa (a : ArrId) : Bool :=
  decide (a < 256) && a != PEND && a != DECL && a != DLP && (decide (a < 146) || decide (149 < a)) &&
    a != EREC && a != IW && a != PINS && (decide (a < 201) || decide (208 < a))

/-- The `CTL` words of `coreLoopC`, as a test. -/
def coreLoopPc (w : Word) : Bool :=
  decide (w.toNat < 1024) && w.toNat != 130 && w.toNat != 150 && w.toNat != 151 &&
    (decide (w.toNat < 140) || decide (147 < w.toNat)) && w.toNat != 129 && w.toNat != 200 &&
    (decide (w.toNat < 202) || decide (219 < w.toNat))

theorem coreLoopPa_mem (a : ArrId) (h : coreLoopPa a = true) : a ∈ coreLoopA := by
  simp only [coreLoopPa, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp [coreLoopA, stepA, List.mem_filter, List.mem_range, h]

theorem coreLoopPc_mem (w : Word) (h : coreLoopPc w = true) : w ∈ coreLoopC := by
  simp only [coreLoopPc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp only [coreLoopC, stepC, List.mem_filter, List.mem_map, List.mem_range]
  refine ⟨⟨w.toNat, ⟨h.1.1.1.1.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩, ?_⟩
  · simp only [decide_eq_true_eq]
    exact ⟨h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2⟩
  · simp only [decide_eq_true_eq]
    refine ⟨fun e => h.1.1.2 (by rw [e]; rfl), fun e => h.1.2 (by rw [e]; rfl), h.2⟩

/-- Every function of the checker passes the loop core's per-function check. -/
prog_all checkerProg_loopChk : checkerProg (wsChk CTL coreLoopPa coreLoopPc loopCoreTree)

theorem checkerProg_coreLoop : CoreLoopClosed checkerProg :=
  closedW_of_all loopCoreTree.eq coreLoopPa_mem coreLoopPc_mem checkerProg_loopChk

end L.Checker
