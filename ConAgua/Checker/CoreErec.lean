import ConAgua.Checker.Prog
import ConAgua.Arena.CoreErec
import ConAgua.Compiler.WriteSetSplit

/-!
# The checker's core leaves `EREC` alone (lane `whnf3`)

`ConAgua/Arena/CoreErec.lean`'s program hypothesis, for the checker's program: every function the
core reaches (`coreFns`) stores into arrays other than the record pool. Discharges the
`ErecKept*` hypotheses of the ι refinements at `checkerProg`.

One `decide +kernel` on `closedA checkerProg …` took 20 GB (lane `erecfix`): it is split into
per-chunk checks of the functions (`prog_all`, `Compiler/WriteSetSplit.lean`), with the function
set as a tree of name codes (`names_tree`) and the store sets as predicates.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- `coreFns` as a tree of name codes. -/
names_tree coreTree : coreFns

/-- The arrays of `coreErecA`, as a test. -/
def coreErecPa (a : ArrId) : Bool := decide (a < 388) && a != EREC

/-- The `CTL` words of `coreErecC`, as a test. -/
def coreErecPc (w : Word) : Bool := decide (w.toNat < 256)

theorem coreErecPa_mem (a : ArrId) (h : coreErecPa a = true) : a ∈ coreErecA := by
  simp only [coreErecPa, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp [coreErecA, List.mem_filter, List.mem_range, h.1, h.2]

theorem coreErecPc_mem (w : Word) (h : coreErecPc w = true) : w ∈ coreErecC := by
  simp only [coreErecPc, decide_eq_true_eq] at h
  simp only [coreErecC, List.mem_map, List.mem_range]
  exact ⟨w.toNat, h, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes the core's per-function check. -/
prog_all checkerProg_coreChk : checkerProg (wsChk CTL coreErecPa coreErecPc coreTree)

theorem checkerProg_coreErec : closedA checkerProg coreErecA coreErecC coreFns = true :=
  closedW_of_all coreTree.eq coreErecPa_mem coreErecPc_mem checkerProg_coreChk

end L.Checker
