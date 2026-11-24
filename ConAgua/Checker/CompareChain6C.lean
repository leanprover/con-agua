module

import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
public import ConAgua.Arena.FreezeCmpSpec
import all ConAgua.Checker.CmpSeqEntry
public import ConAgua.Checker.CompareEntry
meta import ConAgua.Checker.LoopProgTac
public import ConAgua.Checker.ParEntryA

@[expose] public section

/-!
# `check_c3()` from its steps (lane compare)

`checkC3_of_stages`: mode `6`'s entry `check_c3()` composed from step specs (as
`checkC2_of_stages` for mode `5`): the move, `cmp_restore`, `prepare_prelude`, the side records,
the mates, the index build (each with the count it is called with), the flag `CTL[224] := 1` and
`par_compact(0)`.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- A stage spec of a call with one argument (the count), its precondition reading it. -/
def StageSpecC (p : Prog) (f : FnName) (Pre : Word → Mem → Prop) (Post : Word → Mem → Prop) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (c : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) f [c]
    ⦃fun _ s' => LocEq s' s₀ ∧ (Pre c s₀.mem → Post c s'.mem); ⊤⦄

/-- The count `DECL[0]` (where `DECL` has a word). -/
def CntAt (c : Word) (m : Mem) : Prop := ∀ h : 0 < (m.arr64 L.Front.DECL).size, c = (m.arr64 L.Front.DECL)[0]

theorem cntAt_self (m : Mem) (h : 0 < (m.arr64 L.Front.DECL).size) :
    CntAt ((m.arr64 L.Front.DECL)[0]'h) m := fun _ => rfl

/-- **What `check_c3(k)` leaves after a memory `F`**: for `k = 0` the flat frozen buffer
(`par_compact(0, 0)`); otherwise the compared run's: the frozen buffer with header C at `hdrWW`
(`par_compact(1, hdrWW)`), then header S and its extra images (`cmp_hdr_s`). -/
def PostC3 (k : Word) (F : Mem → Prop) (m' : Mem) : Prop :=
  (k = 0 → PostPC 0 F m') ∧
  (k ≠ 0 → ∃ m9, F m9 ∧ parCompactOK m9 1 hdrWW = true ∧
    (2 * hdrW ≤ ((parCompactMem m9 1 hdrWW).arr64 OUT).size →
      CmpHdrSOK (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length) ∧
      m' = cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)))

set_option experimental.vcgen true in
/-- **`check_c3(k)` from its steps**: the solution's stash, the stages, the flag
`CTL[224] := 1` (a memory `F c`, `c` the challenge's count read after the preparation), then the
compaction(s) (`PostC3`); the result is `2^63 + c`. -/
theorem checkC3_of_stages {p : Prog} (hp : p.lookup "check_c3" = some checkC3L)
    (hpc : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i))
    (hhs : p.lookup "cmp_hdr_s" = some cmpHdrSL)
    (hfs : ∀ x ∈ fzsImgs, p.lookup (fzsName x.1) = some (fzsF x.1))
    {Q00 Q0 Q1 Q2 Q3 : Mem → Prop} {Q4 Q5 G F : Word → Mem → Prop}
    (h0 : StageSpec p "cmp_sstash" Q00 fun _ => Q0)
    (h1 : StageSpecC p "index_to_solution" (fun c m => Q0 m ∧ CntAt c m) fun _ m => Q1 m)
    (h2 : StageSpec p "cmp_restore" Q1 fun _ => Q2)
    (h3 : StageSpec p "prepare_prelude" Q2 fun _ => Q3)
    (h4 : StageSpecC p "side_records" (fun c m => Q3 m ∧ CntAt c m) Q4)
    (h5 : StageSpecC p "solution_of" Q4 Q5)
    (h6 : StageSpecC p "build_index" Q5 G)
    (hG : ∀ c m, G c m → F c (m.set64 CTL 224 1))
    (k : Word) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_c3" [k]
    ⦃fun r s' => Q00 s₀.mem → ∃ c, PostC3 k (F c) s'.mem ∧ r.headD 0 = (9223372036854775808 : Word) + c;
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkC3L]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, (h0 n hn' ·),
      (h1 n hn' · ·), (h2 n hn' ·), (h3 n hn' ·), (h4 n hn' · ·), (h5 n hn' · ·), (h6 n hn' · ·),
      (parCompact_spec hpc hfz n · · ·), (cmpHdrS_spec hhs (hfz 0 (by rw [frozen_length]; decide)) hfs n · ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, BinOp.eval, ite_true,
      UInt64.toNat_zero] at *)
    all_goals clear h0 h1 h2 h3 h4 h5 h6 hfz hp hpc hhs hfs
    all_goals (try simp only [SOLC] at *)
    all_goals trace_state
    all_goals sorry

end L.Checker
