module

public import ConAgua.Checker.CompareChain6S
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
import ConAgua.Checker.CheckARun
meta import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgTac

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

set_option experimental.vcgen true in
/-- **`check_c3()` from its steps**: on a return, the final memory is the frozen buffer's (header
only, `par_compact(0)`) after the flag's store on a memory `F c` (`c` the challenge's count, read
after the preparation), and the result is `2^63 + c`. -/
theorem checkC3_of_stages {p : Prog} (hp : p.lookup "check_c3" = some checkC3L)
    (hpc : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i))
    {Q0 Q1 Q2 Q3 : Mem → Prop} {Q4 Q5 G F : Word → Mem → Prop}
    (h1 : StageSpecC p "index_to_solution" (fun c m => Q0 m ∧ CntAt c m) fun _ m => Q1 m)
    (h2 : StageSpec p "cmp_restore" Q1 fun _ => Q2)
    (h3 : StageSpec p "prepare_prelude" Q2 fun _ => Q3)
    (h4 : StageSpecC p "side_records" (fun c m => Q3 m ∧ CntAt c m) Q4)
    (h5 : StageSpecC p "solution_of" Q4 Q5)
    (h6 : StageSpecC p "build_index" Q5 G)
    (hG : ∀ c m, G c m → F c (m.set64 CTL 224 1))
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_c3" []
    ⦃fun r s' => Q0 s₀.mem → ∃ c, PostPC 0 (F c) s'.mem ∧ r.headD 0 = (9223372036854775808 : Word) + c;
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkC3L]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      (h1 n hn' · ·), (h2 n hn' ·), (h3 n hn' ·), (h4 n hn' · ·), (h5 n hn' · ·), (h6 n hn' · ·),
      (parCompact_spec hpc hfz n · ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, BinOp.eval, ite_true, ite_false,
      UInt64.toNat_zero, bne_iff_ne, ne_eq, Decidable.not_not] at *)
    all_goals clear h1 h2 h3 h4 h5 h6 hfz hp hpc
    all_goals (try simp only [SOLC] at *)
    all_goals grind (gen := 30) (ematch := 40) [lang_grind, Locals.init_cons_zero, PostPC, cntAt_self]

end L.Checker
