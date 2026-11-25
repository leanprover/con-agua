module

public import ConAgua.Checker.CmpSeqEntry
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.FreezeSpec
import ConAgua.L.GrindAttr
import ConAgua.L.For
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.SlotGrow
public import ConAgua.L.Logic

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

/-- The words one row swap exchanges: `2 · CTL[ca]`. -/
def cqRowsN (m : Mem) (ca : Word) : Word := 2 * rdW (m.arr64 CTL) ca

/-- **The memory after `cqXchgLoop d s` over `[0, j)`**: `t := d[i]; d[i] := s[i]; s[i] := t` for
`i < j`, ascending. -/
def xchgM (d s : TieredArray) (m : Mem) : Nat → Mem
  | 0 => m
  | j + 1 =>
    let M := xchgM d s m j
    (M.set64 d (UInt64.ofNat j) (M.arr64 s)[j]!).set64 s (UInt64.ofNat j) (M.arr64 d)[j]!

theorem xchgM_ne (d s : TieredArray) (m : Mem) (j : Nat) {b : TieredArray} (hd : b ≠ d) (hs : b ≠ s) :
    (xchgM d s m j).arr64 b = m.arr64 b := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [xchgM, Mem.arr64_set64_ne _ _ _ _ _ hd, Mem.arr64_set64_ne _ _ _ _ _ hs, ih]

theorem xchgM_size (d s : TieredArray) (m : Mem) (j : Nat) (b : TieredArray) :
    ((xchgM d s m j).arr64 b).size = (m.arr64 b).size := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [xchgM, L.Mem.size64_set64, ih]

theorem xchgM_bytes (d s : TieredArray) (m : Mem) (j : Nat) : (xchgM d s m j).bytes = m.bytes := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [xchgM]; exact ih

theorem xchgM_glob (d s : TieredArray) (m : Mem) (j : Nat) : (xchgM d s m j).glob = m.glob := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [xchgM]; exact ih

/-- **The exchange's words**: below `j` each array holds the other's, past it its own. -/
theorem xchgM_get {d s : TieredArray} (hds : d ≠ s) (m : Mem) {j : Nat} (hj : j < 2 ^ 64)
    (hd : j ≤ (m.arr64 d).size) (hs : j ≤ (m.arr64 s).size) (k : Nat) :
    ((xchgM d s m j).arr64 d)[k]? = (if k < j then (m.arr64 s)[k]? else (m.arr64 d)[k]?) ∧
    ((xchgM d s m j).arr64 s)[k]? = (if k < j then (m.arr64 d)[k]? else (m.arr64 s)[k]?) := by
  induction j generalizing k with
  | zero => simp [xchgM]
  | succ j ih =>
    have ih' := fun k => ih (by omega) (by omega) (by omega) k
    have e : (UInt64.ofNat j).toNat = j := by simp; omega
    have hdj := (ih' j).1
    have hsj := (ih' j).2
    simp only [Nat.lt_irrefl, ite_false] at hdj hsj
    have zd : j < ((xchgM d s m j).arr64 d).size := by rw [xchgM_size]; omega
    have zs : j < ((xchgM d s m j).arr64 s).size := by rw [xchgM_size]; omega
    have gd : ((xchgM d s m j).arr64 d)[j]! = (m.arr64 d)[j]! := by
      rw [getElem!_def, getElem!_def, hdj]
    have gs : ((xchgM d s m j).arr64 s)[j]! = (m.arr64 s)[j]! := by
      rw [getElem!_def, getElem!_def, hsj]
    simp only [xchgM]
    rw [Mem.arr64_set64_ne _ _ _ _ _ hds, Mem.arr64_set64_same, Mem.arr64_set64_same,
      Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hds), e, gd, gs]
    simp only [Array.set!, Array.getElem?_setIfInBounds]
    refine ⟨?_, ?_⟩
    · by_cases hk : k = j
      · subst hk; simp [zd, getElem!_def, Array.getElem?_eq_getElem (show k < (m.arr64 s).size by omega)]
      · simp only [show ¬ j = k from Ne.symm hk, ite_false]; rw [(ih' k).1]
        by_cases hk' : k < j
        · simp [hk', show k < j + 1 by omega]
        · simp [hk', show ¬ k < j + 1 by omega]
    · by_cases hk : k = j
      · subst hk; simp [zs, getElem!_def, Array.getElem?_eq_getElem (show k < (m.arr64 d).size by omega)]
      · simp only [show ¬ j = k from Ne.symm hk, ite_false]; rw [(ih' k).2]
        by_cases hk' : k < j
        · simp [hk', show k < j + 1 by omega]
        · simp [hk', show ¬ k < j + 1 by omega]

/-- **Exchanging twice restores both arrays**: from a memory whose `d` and `s` are an exchange's of
`m`, the same exchange gives back `m`'s. -/
theorem xchgM_back {d s : TieredArray} (hds : d ≠ s) (m M : Mem) {j : Nat} (hj : j < 2 ^ 64)
    (hd : j ≤ (m.arr64 d).size) (hs : j ≤ (m.arr64 s).size)
    (eD : M.arr64 d = (xchgM d s m j).arr64 d) (eS : M.arr64 s = (xchgM d s m j).arr64 s) :
    (xchgM d s M j).arr64 d = m.arr64 d ∧ (xchgM d s M j).arr64 s = m.arr64 s := by
  have hd' : j ≤ (M.arr64 d).size := by rw [eD, xchgM_size]; exact hd
  have hs' : j ≤ (M.arr64 s).size := by rw [eS, xchgM_size]; exact hs
  have g1 := xchgM_get hds m hj hd hs
  have g2 := xchgM_get hds M hj hd' hs'
  refine ⟨Array.ext_getElem? fun k => ?_, Array.ext_getElem? fun k => ?_⟩
  · rw [(g2 k).1, eS, eD, (g1 k).2, (g1 k).1]; split <;> rfl
  · rw [(g2 k).2, eS, eD, (g1 k).1, (g1 k).2]; split <;> rfl

/-- **The memory after `cq_swap_rows(d, s, ca)`**. -/
def cqRowsM (d s : ArrId) (ca : Word) (m : Mem) : Mem := xchgM d s m (cqRowsN m ca).toNat

/-- What a returning row swap has checked: the count and both rows in bounds. -/
def CqRowsOK (d s : ArrId) (ca : Word) (m : Mem) : Prop :=
  (rdW (m.arr64 CTL) ca).toNat < 2 ^ 62 ∧
    (cqRowsN m ca).toNat ≤ (m.arr64 d).size ∧ (cqRowsN m ca).toNat ≤ (m.arr64 s).size

theorem cqXchgLoop_spec (p : Prog) (d s : ArrId) (m₀ : Mem) (k : Nat) (s₀ : St) :
    ⦃fun st => st = s₀ ∧ (st.loc 1 = 0 ∧ st.mem = m₀)⦄
    exec p k (cqXchgLoop d s)
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ (s₀.loc 0).toNat ≤ (m₀.arr64 d).size ∧
      (s₀.loc 0).toNat ≤ (m₀.arr64 s).size ∧ s'.mem = xchgM d s m₀ (s₀.loc 0).toNat; ⊤⦄ := by
  refine L.Triple.forUp_pre (w := cqXchgLoop d s) (s₀ := s₀) (P := fun st => st.loc 1 = 0 ∧ st.mem = m₀)
    (j := 1) (n := 0) (by unfold cqXchgLoop; exact rfl) (fun st => st.loc 0 = s₀.loc 0 ∧
      (st.loc 1).toNat ≤ (s₀.loc 0).toNat ∧ (st.loc 1).toNat ≤ (m₀.arr64 d).size ∧
      (st.loc 1).toNat ≤ (m₀.arr64 s).size ∧ st.mem = xchgM d s m₀ (st.loc 1).toNat) ?_ ?_ ?_ k
  · intro h
    exact ⟨rfl, by simp [h.1], by simp [h.1], by simp [h.1], by simp [h.1, h.2, xchgM]⟩
  · intro st ⟨h0, h1, h2, h3, h4⟩ hn
    have : (st.loc 1).toNat = (s₀.loc 0).toNat := by
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp (by rw [h0] at hn; exact hn)); omega
    rw [this] at h2 h3 h4
    exact ⟨rfl, h0, h2, h3, h4⟩
  · intro k s₁
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, warr]
    all_goals simp only [St.setLoc_loc, L.St.setLoc_mem, LoopPost_normal, Mem.size64_set64, Nat.reduceEqDiff,
      ite_true, ite_false, BinOp.eval] at *
    all_goals rename_i hs1 hI _ _ _ _
    all_goals obtain rfl := hs1
    all_goals obtain ⟨⟨h0, h1, h2, h3, h4⟩, hlt⟩ := hI
    all_goals have hj1 := L.toNat_add_one_of_word_lt _ _ hlt
    all_goals have hj := UInt64.lt_iff_toNat_lt.mp hlt
    all_goals rw [h0] at hj
    all_goals rename_i hd hs
    all_goals have zd := hd
    all_goals have zs := hs
    all_goals rw [h4, xchgM_size] at zd zs
    all_goals refine ⟨h0, by omega, by omega, by omega, ?_⟩
    all_goals rw [hj1]
    all_goals simp only [xchgM, UInt64.ofNat_toNat]
    all_goals rw [← h4]
    all_goals simp only [getElem!_def, Array.getElem?_eq_getElem hd, Array.getElem?_eq_getElem hs]

theorem cqXchgLoop_step_spec (p : Prog) (d s : ArrId) (m₀ : Mem) (k : Nat) (s₀ : St) :
    ⦃fun st => st = s₀ ∧ (st.loc 1 = 0 ∧ st.mem = m₀)⦄
    step p (exec p k) (cqXchgLoop d s)
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ (s₀.loc 0).toNat ≤ (m₀.arr64 d).size ∧
      (s₀.loc 0).toNat ≤ (m₀.arr64 s).size ∧ s'.mem = xchgM d s m₀ (s₀.loc 0).toNat; ⊤⦄ :=
  Triple.step_exec (cqXchgLoop_spec p d s m₀ (k + 1) s₀)

theorem cqXchg_spec (p : Prog) {f : FnName} {d s : ArrId}
    (hp : p.lookup f = some (cqXchgG d s)) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) f [k]
    ⦃fun _ s' => LocEq s' s₀ ∧ k.toNat ≤ (s₀.mem.arr64 d).size ∧ k.toNat ≤ (s₀.mem.arr64 s).size ∧
      s'.mem = xchgM d s s₀.mem k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cqXchgG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, cqXchgLoop_step_spec p d s _ n]
    all_goals rename_i h
    all_goals obtain ⟨-, h1, h2, h3⟩ := h
    all_goals first | exact rfl | exact h1 | exact h2 | exact h3

theorem cqSwapRows_spec (p : Prog) {f : FnName} {d s : ArrId} {ca : Word}
    (hp : p.lookup f = some (cqSwapRowsG d s ca)) (n : Nat) (s₀ : St) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) f []
    ⦃fun r s' => LocEq s' s₀ ∧ CqRowsOK d s ca s₀.mem ∧ s'.mem = cqRowsM d s ca s₀.mem ∧
      r.headD 0 = cqRowsN s₀.mem ca; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cqSwapRowsG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, cqXchgLoop_step_spec p d s _ n]
    all_goals simp only [L.St.setLoc_mem, St.setLoc_loc, Cmp.eval, BinOp.eval,
      Locals.init, ite_true, Nat.reduceEqDiff, ite_false, decide_eq_true_eq] at *
    case vc1 => rfl
    all_goals rename_i hc _ _ hlt h
    all_goals obtain ⟨h0, h1, h2, h3⟩ := h
    all_goals have e : rdW (s₀.mem.arr64 CTL) ca = (s₀.mem.arr64 CTL)[ca.toNat] := rdW_eq _ _ _ rfl hc
    case vc2 => exact rfl
    case vc3 =>
      refine ⟨by rw [e]; exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt), ?_, ?_⟩ <;>
        simp only [cqRowsN, e] <;> assumption
    case vc4 => simp only [cqRowsM, cqRowsN, e, h3]
    case vc5 => simp only [Sig.retVal, cqRowsN, e, h0]; rfl

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

end L.Checker
