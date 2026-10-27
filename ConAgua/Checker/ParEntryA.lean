import ConAgua.Checker.Pipeline
import ConAgua.Arena.FreezeSpec
import ConAgua.L.GrindAttr

/-!
# Entry 1 of the parallel mode: `check` with `MODE` `1` or `3` (lane parmode)

docs/design/parmode.md, "Step 4" (a). `check` with the global `MODE = 1` runs `check_a(1)`, with
`MODE = 3` `check_a(0)` (`Checker/Entry.lean`): the stages, phase A's fold
`install_fold_go(0, DECL[0], 0)` and `par_compact(v, c)`, returning `2^63 + CTL[130]`.

* `check_dispatchA`: `check` with `MODE = 1` (`3`) is `check_a(1)` (`check_a(0)`).
* `checkA_of_stages`: `check_a(c)` composed from the seven stage specs, a spec of the fold and
  `par_compact`'s run (`parCompact_spec`, `Arena/FreezeSpec.lean`): on a result other than `1`
  (a line that did not scan), the final memory is `parCompactMem m v c` for a memory `m` after
  the fold with result `v` (`F v m`), and the result is `2^63 + CTL[130]`.
-/

namespace L.Checker

open L L.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- The flag `check` passes to `check_a` for the mode word `w` (`1` images and header, `3` the
header only). -/
def modeFlag (w : Word) : Word := if w = 1 then 1 else 0

/-- **`check`'s dispatch to entry 1**: with the mode word `1` or `3`, `check` is
`check_a(modeFlag MODE)` from the same memory. -/
theorem check_dispatchA {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (P : Word → Mem → Prop)
    (hA : ∀ (s₁ : St) (c : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_a" [c]
      ⦃fun r s' => s₁.mem = s₀.mem → c = modeFlag (s₀.mem.glob MODE) → P (r.headD 0) s'.mem; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun r s' => (s₀.mem.glob MODE = 1 ∨ s₀.mem.glob MODE = 3) → P (r.headD 0) s'.mem; ⊤⦄ := by
  have h1 : s₀.mem.glob MODE = 1 → modeFlag (s₀.mem.glob MODE) = 1 := fun h => by
    simp [modeFlag, h]
  have h3 : s₀.mem.glob MODE = 3 → modeFlag (s₀.mem.glob MODE) = 0 := fun h => by
    simp [modeFlag, h]
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hA · ·),
    (L.invoke_loc p (exec p n) "check_b" [] ·)]
  all_goals (try simp only [Sig.retVal, Sig.retOr, St.setLoc_mem, List.headD_cons,
    St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
  all_goals grind [lang_grind]

/-- What `par_compact(v, c)` leaves after a fold that ended in `F v m`: the frozen buffer's memory
`parCompactMem m v c` of such an `m`, in bounds. -/
def PostPC (c : Word) (F : Word → Mem → Prop) (m' : Mem) : Prop :=
  ∃ m v, F v m ∧ parCompactOK m c = true ∧ m' = parCompactMem m v c

/-- `par_compact`'s spec in the stage style (the precondition in the post). -/
theorem parCompact_stage {p : Prog} (hpc : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i)) (c : Word)
    (F : Word → Mem → Prop) (n : Nat) (s₀ : St) (v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "par_compact" [v, c]
    ⦃fun _ s' => LocEq s' s₀ ∧ (F v s₀.mem → PostPC c F s'.mem); ⊤⦄ :=
  triple_post (parCompact_spec hpc hfz n s₀ v c) fun _ _ ⟨hl, hok, hm, _⟩ =>
    ⟨hl, fun hF => ⟨_, _, hF, hok, hm⟩⟩

/-- **`check_a(c)` from its stages**: the seven stage specs, the fold's spec from the stages'
end (`Q7`, with its count `DECL[0]`) and `par_compact`; on a result other than `1` (a line that did
not scan), the final memory is the frozen buffer's after a fold that ended in `F`, and the result
is `2^63 + CTL[130]`. -/
theorem checkA_of_stages {p : Prog} (hp : p.lookup "check_a" = some checkAL)
    (hpc : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i))
    {Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 : Mem → Prop} {F : Word → Mem → Prop}
    (h1 : StageSpec p "cap_check" Q0 fun _ => Q1)
    (h2 : StageSpec p "pb_check" Q1 fun _ => Q2)
    (h3 : StageSpec p "intern_reserved_pins" Q2 fun _ => Q3)
    (h4 : StageSpec p "builtin_prelude" Q3 fun _ => Q4)
    (h5 : StageSpec p "front_run" Q4 fun r m => r.headD 0 = 0 → Q5 m)
    (h6 : StageSpec p "prepare_prelude" Q5 fun _ => Q6)
    (h7 : StageSpec p "intern_all_pins" Q6 fun _ => Q7)
    (h8 : ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
      ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [0, cnt, 0]
      ⦃fun r s' => LocEq s' s₀ ∧ (Q7 s₀.mem →
        (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
        F (r.headD 0) s'.mem); ⊤⦄)
    (c : Word) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_a" [c]
    ⦃fun r s' => Q0 s₀.mem → r.headD 0 ≠ 1 → PostPC c F s'.mem ∧
      ∀ h : 130 < (s'.mem.arr64 CTL).size, r.headD 0 = (9223372036854775808 : Word) + (s'.mem.arr64 CTL)[130];
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkAL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      (h1 n hn' ·), (h2 n hn' ·), (h3 n hn' ·), (h4 n hn' ·), (h5 n hn' ·), (h6 n hn' ·),
      (h7 n hn' ·), (h8 n hn' · ·), (parCompact_stage hpc hfz · F n · ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, BinOp.eval, ite_true, ite_false, Nat.reduceEqDiff,
      UInt64.toNat_zero, bne_iff_ne, ne_eq, Decidable.not_not] at *)
    all_goals clear h1 h2 h3 h4 h5 h6 h7 h8 hfz hp hpc
    -- gen/ematch raised: the flag `c` reaches `par_compact` through eight calls' `LocEq`s (depth)
    all_goals grind (gen := 30) (ematch := 40) [lang_grind, Locals.init_cons_zero]

end L.Checker
