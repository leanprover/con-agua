import ConAgua.L.Syntax

/-!
# The write sets of the inductive arm's callees in `checkerProg` (lane `indproofs4`)

The per-function checks (`prog_all`) behind the `closedA` facts `cidW_okC`
(`Arena/IndT/CheckIndDecl.lean`) takes, for the checker's program, over the call-closed function
sets of `Checker/IndArmFns.lean`; and behind the write set (apart from the walk memos) of the arm's
`AbsKeep` callees that reach no walk (`armAbsFns`). As `Checker/IndMemoClosed.lean`. They are put
together by `closedW_of_all` in `Checker/IndArm.lean`: this module needs only `checkerProg` and
the array names, so its kernel checks run early in the build, beside the arm's proofs. The
checks are in `IndArmClosed1`…`3`, three arms each: the kernel checks of one module run one after
another (`addDecl` waits for the checks before it), so the modules run them in parallel.
-/

namespace L.Checker

/-- An array test: below 320 (both tiers) and `f`. -/
def tA (f : Nat → Bool) (a : ArrId) : Bool := decide (a < 388) && f a

/-- A `CTL` word test: below 256 and `g`. -/
def tC (g : Nat → Bool) (w : Word) : Bool := decide (w.toNat < 256) && g w.toNat

theorem tA_mem {f : Nat → Bool} {a : ArrId} (h : tA f a = true) : a ∈ (List.range 388).filter f := by
  simp only [tA, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_filter, List.mem_range]
  exact ⟨h.1, h.2⟩

theorem tC_mem {g : Nat → Bool} {w : Word} (h : tC g w = true) :
    w ∈ ((List.range 256).filter g).map Nat.toUInt64 := by
  simp only [tC, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨w.toNat, ⟨h.1, h.2⟩, UInt64.ofNat_toNat⟩

end L.Checker
