module

public import ConAgua.Compiler.WriteSetSplit
public import ConAgua.Layout

@[expose] public section

/-! The tests behind `Checker/IndArmClosed.lean`'s per-function checks: an arm's array and `CTL`
tests, all arms' checks on one function (`wsChkM`). -/

namespace L.Checker

open L.Compiler

/-- An array test: one of the checker's word arrays (`checkerWordArrays`) and `f`. -/
def tA (f : TieredArray → Bool) (a : TieredArray) : Bool := checkerWordArrays.contains a && f a

/-- A `CTL` word test: below 256 and `g`. -/
def tC (g : Nat → Bool) (w : Word) : Bool := decide (w.toNat < 256) && g w.toNat

theorem tA_mem {f : TieredArray → Bool} {a : TieredArray} (h : tA f a = true) :
    a ∈ checkerWordArrays.filter f := by
  simp only [tA, Bool.and_eq_true, List.contains_iff_mem] at h
  exact List.mem_filter.2 h

theorem tC_mem {g : Nat → Bool} {w : Word} (h : tC g w = true) :
    w ∈ ((List.range 256).filter g).map Nat.toUInt64 := by
  simp only [tC, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨w.toNat, ⟨h.1, h.2⟩, UInt64.ofNat_toNat⟩

/-- The tests of one arm: the arrays and `CTL` words its functions may store to, the tree of
its function set. -/
abbrev ArmTest := (TieredArray → Bool) × (Word → Bool) × NTree

/-- All arms' write-set checks on one function. -/
def wsChkM (ctl : ArrId) (arms : List ArmTest) (x : FnName × FunDecl) : Bool :=
  arms.all fun a => wsChk ctl a.1 a.2.1 a.2.2 x

theorem wsChk_of_all {ctl : ArrId} {arms : List ArmTest} {p : Prog}
    (h : ∀ x ∈ p, wsChkM ctl arms x = true) {a : ArmTest} (ha : a ∈ arms) :
    ∀ x ∈ p, wsChk ctl a.1 a.2.1 a.2.2 x = true :=
  fun x hx => List.all_eq_true.mp (h x hx) a ha

end L.Checker
