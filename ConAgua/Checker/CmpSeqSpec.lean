module

public import ConAgua.Checker.CmpSeqEntry
public import ConAgua.Checker.CmpSeqView
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.FreezeSpec
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Modes `8` and `9`'s copies (lane compare2, the sJ variant)

The memory functions of `check_bs`'s bank switch and `check_bc`'s switch back
(`Checker/CmpSeqEntry.lean`) and their specs:

* `cq_swap_*`: `cqRowsM c d s ca m`, the challenge's rows `d` kept in `c` and the solution's `s`
  copied into `d`, `cqRowsN m ca = 2 · CTL[ca]` words each.
* `cq_back_*`: `m.copy64 d 0 c 0 n`.
-/

namespace L.Checker

open L L.Arena L.Front
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- The words one row swap copies: `2 · CTL[ca]`. -/
def cqRowsN (m : Mem) (ca : Word) : Word := 2 * rdW (m.arr64 CTL) ca

/-- **The memory after `cq_swap_rows(c, d, s, ca)`**. -/
def cqRowsM (c d s : ArrId) (ca : Word) (m : Mem) : Mem :=
  (m.copy64 c 0 d 0 (cqRowsN m ca).toNat).copy64 d 0 s 0 (cqRowsN m ca).toNat

/-- What a returning row swap has checked: the count and both copies in bounds. -/
def CqRowsOK (c d s : ArrId) (ca : Word) (m : Mem) : Prop :=
  (rdW (m.arr64 CTL) ca).toNat < 2 ^ 62 ∧
    (cqRowsN m ca).toNat ≤ (m.arr64 c).size ∧ (cqRowsN m ca).toNat ≤ (m.arr64 d).size ∧
    (cqRowsN m ca).toNat ≤ (m.arr64 s).size

theorem cqSwapRows_spec (p : Prog) {f : FnName} {c d s : ArrId} {ca : Word}
    (hp : p.lookup f = some (cqSwapRowsG c d s ca)) (n : Nat) (s₀ : St) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) f []
    ⦃fun r s' => LocEq s' s₀ ∧ CqRowsOK c d s ca s₀.mem ∧ s'.mem = cqRowsM c d s ca s₀.mem ∧
      r.headD 0 = cqRowsN s₀.mem ca; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cqSwapRowsG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr]
    all_goals simp only [L.St.setLoc_mem, St.setLoc_loc, Cmp.eval, BinOp.eval, UInt64.toNat_zero,
      Locals.init, ite_true, Nat.zero_add, size_copy64] at *
    all_goals rename_i hc hlt h1 h2
    all_goals have e : rdW (s₀.mem.arr64 CTL) ca = (s₀.mem.arr64 CTL)[ca.toNat] := rdW_eq _ _ _ rfl hc
    case vc1 => exact rfl
    case vc2 =>
      refine ⟨by rw [e]; simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, ?_, ?_, ?_⟩ <;>
        simp only [cqRowsN, e] <;> grind
    case vc3 => simp only [cqRowsM, cqRowsN, e]
    case vc4 => simp only [cqRowsN, e]; rfl

/-- **A prefix copy's words below the extent** (`copy!(d, 0, s, 0, n)` in bounds): `s`'s. -/
theorem cq_copy64_lo {d s : ArrId} (hds : d ≠ s) (m : Mem) {n k : Nat} (hn : n < 2 ^ 63)
    (hd : n ≤ (m.arr64 d).size) (hs : n ≤ (m.arr64 s).size) (hk : k < n) :
    ((m.copy64 d 0 s 0 n).arr64 d)[k]? = (m.arr64 s)[k]? := by
  have h := getD_copy64 hds n m 0 0 (by simp; omega) (by simp; omega) k
  have h1 : k < ((m.copy64 d 0 s 0 n).arr64 d).size := by rw [size_copy64]; omega
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem (by omega)]
  simp only [UInt64.toNat_zero, Nat.zero_le, Nat.zero_add, Nat.sub_zero,
    show k < (m.arr64 d).size by omega, hk, and_self, ite_true, Array.getD, h1, dite_true,
    show k < (m.arr64 s).size by omega] at h
  exact congrArg some h

/-- **A prefix copy's words past the extent**: `d`'s. -/
theorem cq_copy64_hi {d s : ArrId} (hds : d ≠ s) (m : Mem) {n k : Nat} (hn : n < 2 ^ 63)
    (hk : ¬ k < n) : ((m.copy64 d 0 s 0 n).arr64 d)[k]? = (m.arr64 d)[k]? := by
  have h := getD_copy64 hds n m 0 0 (by simp; omega) (by simp; omega) k
  by_cases h1 : k < (m.arr64 d).size
  · have h1' : k < ((m.copy64 d 0 s 0 n).arr64 d).size := by rw [size_copy64]; omega
    rw [Array.getElem?_eq_getElem h1', Array.getElem?_eq_getElem h1]
    simp only [UInt64.toNat_zero, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and, hk, false_and,
      ite_false, Array.getD, h1, h1', dite_true] at h
    exact congrArg some h
  · rw [Array.getElem?_eq_none (by rw [size_copy64]; omega), Array.getElem?_eq_none (by omega)]

theorem cqBack_spec (p : Prog) {f : FnName} {c d : ArrId}
    (hp : p.lookup f = some (cqBackG c d)) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) f [k]
    ⦃fun _ s' => LocEq s' s₀ ∧ k.toNat ≤ (s₀.mem.arr64 c).size ∧ k.toNat ≤ (s₀.mem.arr64 d).size ∧
      s'.mem = s₀.mem.copy64 d 0 c 0 k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cqBackG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr]
    all_goals simp only [UInt64.toNat_zero, Locals.init, Nat.zero_add,
      List.getD_cons_zero] at *
    all_goals first | exact rfl | grind

end L.Checker
