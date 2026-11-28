module

public import ConAgua.Arena.NatCmp
public import ConAguaX86.AsmEsc.DivSubmulL
import all ConAgua.Arena.NatCmp

@[expose] public section

/-!
# `nat_cmp` as a function

The L code of `nat_cmp(oa, la, ob, lb)` (`L.Arena.natCmp`, `ConAgua/Arena/NatCmp.lean`) run at
fuel `F > la`: different lengths decide; for equal lengths, when both windows lie in their tiers
below `2^40` (or `la = 0`), the comparison from the top limb down, `ncRes` (`natCmp_run`). The
machine-level proof of the hand-written body (`NatCmpAsm.lean`) is against it.

Locals: `0 oa, 1 la, 2 ob, 3 lb, 4 k, 5 x, 6 y`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- The comparison of the limbs below `k`, from the top: `0`, `1` or `2`. -/
def ncRes (TA TB : TieredArray) (qa qb : Word) (m : Mem) : Nat → Word
  | 0 => 1
  | k + 1 =>
    let x := (m.arr64 TA)[(qa + UInt64.ofNat k).toNat]!
    let y := (m.arr64 TB)[(qb + UInt64.ofNat k).toNat]!
    if x < y then 0 else if y < x then 2 else ncRes TA TB qa qb m k

/-- Equal limbs `j` pass the comparison down. -/
theorem ncRes_eq (TA TB : TieredArray) (qa qb : Word) (M : Mem) (j : Nat)
    (h : (M.arr64 TA)[(qa + UInt64.ofNat j).toNat]! = (M.arr64 TB)[(qb + UInt64.ofNat j).toNat]!) :
    ncRes TA TB qa qb M (j + 1) = ncRes TA TB qa qb M j := by
  simp only [ncRes, h, UInt64.lt_irrefl, reduceIte]

/-- The loop's signal for the result `w`: it returns `0` or `2`, and ends normally for `1`. -/
def ncSig (w : Word) : Sig := if w = 1 then .normal else .ret [w]

/-- The loop's body. -/
def ncB : Stmt :=
  .seq (.set 5 (.ld64t 0 (.bin .shr (.bin .sub (.bin .add (.var 0) (.var 4)) (.const 1)) (.const 40))
      (.bin .and (.bin .sub (.bin .add (.var 0) (.var 4)) (.const 1)) (.const 1099511627775))))
    (.seq (.set 6 (.ld64t 0 (.bin .shr (.bin .sub (.bin .add (.var 2) (.var 4)) (.const 1)) (.const 40))
        (.bin .and (.bin .sub (.bin .add (.var 2) (.var 4)) (.const 1)) (.const 1099511627775))))
      (.seq (.ite (.cmp .ult (.var 5) (.var 6)) (.ret [.const 0]) .skip)
        (.seq (.ite (.cmp .ult (.var 6) (.var 5)) (.ret [.const 2]) .skip)
          (.set 4 (.bin .sub (.var 4) (.const 1))))))

/-- The loop. -/
def ncW : Stmt := .while (.cmp .ult (.const 0) (.var 4)) ncB

theorem natCmp_body : natCmp.body =
    .seq (.ite (.cmp .ult (.var 1) (.var 3)) (.ret [.const 0]) .skip)
      (.seq (.ite (.cmp .ult (.var 3) (.var 1)) (.ret [.const 2]) .skip)
        (.seq (.set 4 (.var 1)) (.seq ncW (.ret [.const 1])))) := by
  rfl

theorem natCmp_nparams : natCmp.nparams = 4 := by rfl

theorem sub_one_add (a k : Word) : a + k - 1 = a + (k - 1) := by
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add]
  bv_omega

theorem ncB_run (p : Prog) (K : Stmt → M Sig) (σ : St) (j : Nat) (hk : (σ.loc 4).toNat = j + 1)
    (ha : (σ.loc 0 &&& idxMask).toNat + (j + 1) ≤ 2 ^ 40) (hb : (σ.loc 2 &&& idxMask).toNat + (j + 1) ≤ 2 ^ 40)
    (hA : (σ.loc 0 &&& idxMask).toNat + (j + 1) ≤ (σ.mem.arr64 (tierA 0 (σ.loc 0 >>> 40))).size)
    (hB : (σ.loc 2 &&& idxMask).toNat + (j + 1) ≤ (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40))).size) :
    ∃ s σ', stepRun p K ncB σ = .ok (s, σ') ∧ σ'.mem = σ.mem ∧ (∀ v, v < 4 → σ'.loc v = σ.loc v) ∧
      (s = .normal → σ'.loc 4 = σ.loc 4 - 1) ∧
      s = (let x := (σ.mem.arr64 (tierA 0 (σ.loc 0 >>> 40)))[((σ.loc 0 &&& idxMask) + UInt64.ofNat j).toNat]!
           let y := (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40)))[((σ.loc 2 &&& idxMask) + UInt64.ofNat j).toNat]!
           if x < y then .ret [0] else if y < x then .ret [2] else .normal) := by
  have hj : (σ.loc 4 - 1) = UInt64.ofNat j := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), hk]
    simp only [Nat.add_sub_cancel, UInt64.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := (σ.loc 4).toNat_lt; omega)).symm
  have hjn : (UInt64.ofNat j).toNat = j := by rw [← hj]; rw [UInt64.toNat_sub_of_le _ _
    (UInt64.le_iff_toNat_le.mpr (by simp; omega)), hk]; simp
  obtain ⟨ta, ia⟩ := tag_add (σ.loc 0) (UInt64.ofNat j) (by omega)
  obtain ⟨tb, ib⟩ := tag_add (σ.loc 2) (UInt64.ofNat j) (by omega)
  have ia' : σ.loc 0 + UInt64.ofNat j &&& 1099511627775 = (σ.loc 0 &&& idxMask) + UInt64.ofNat j := ia
  have ib' : σ.loc 2 + UInt64.ofNat j &&& 1099511627775 = (σ.loc 2 &&& idxMask) + UInt64.ofNat j := ib
  have hA' : ((σ.loc 0 &&& idxMask) + UInt64.ofNat j).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 0 >>> 40))).size := by
    rw [L.toNat_add_of_lt _ _ (by omega)]; omega
  have hB' : ((σ.loc 2 &&& idxMask) + UInt64.ofNat j).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40))).size := by
    rw [L.toNat_add_of_lt _ _ (by omega)]; omega
  simp only [ncB, step_seq_run, step_set_run, step_ite_run, evalP, evalCP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    sub_one_add, hj, ta, tb, ia', ib', hA', hB', ↓reduceDIte, Cmp.eval]
  simp only [getElem!_pos, hA', hB']
  have hsk : ∀ τ : St, StateT.run (step p K Stmt.skip) τ = .ok (.normal, τ) := fun τ => step_skip_run p K τ
  by_cases h1 : (σ.mem.arr64 (tierA 0 (σ.loc 0 >>> 40)))[((σ.loc 0 &&& idxMask) + UInt64.ofNat j).toNat] <
      (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40)))[((σ.loc 2 &&& idxMask) + UInt64.ofNat j).toNat]
  · simp only [h1, decide_true, reduceIte, step_ret_run, evalArgsP, evalP, Except.map, bind, Except.bind,
      pure, Except.pure]
    refine ⟨_, _, rfl, rfl, fun v hv => ?_, fun h => (by cases h), rfl⟩
    have h5 : ¬ v = 5 := fun e => by subst e; exact absurd hv (by decide)
    have h6 : ¬ v = 6 := fun e => by subst e; exact absurd hv (by decide)
    simp only [St.setLoc_loc, h5, h6, reduceIte]
  by_cases h2 : (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40)))[((σ.loc 2 &&& idxMask) + UInt64.ofNat j).toNat] <
      (σ.mem.arr64 (tierA 0 (σ.loc 0 >>> 40)))[((σ.loc 0 &&& idxMask) + UInt64.ofNat j).toNat]
  · simp only [h1, h2, decide_true, decide_false, reduceIte, hsk, step_ret_run, evalArgsP, evalP, Except.map,
      bind, Except.bind, pure, Except.pure, St.setLoc_loc, Nat.reduceEqDiff]
    refine ⟨_, _, rfl, rfl, fun v hv => ?_, fun h => (by cases h), rfl⟩
    have h5 : ¬ v = 5 := fun e => by subst e; exact absurd hv (by decide)
    have h6 : ¬ v = 6 := fun e => by subst e; exact absurd hv (by decide)
    simp only [St.setLoc_loc, h5, h6, reduceIte]
  · simp only [h1, h2, decide_false, reduceIte, hsk, St.setLoc_loc, Nat.reduceEqDiff]
    refine ⟨_, _, rfl, rfl, fun v hv => ?_, fun _ => ?_, rfl⟩
    · have h4 : ¬ v = 4 := fun e => by subst e; exact absurd hv (by decide)
      have h5 : ¬ v = 5 := fun e => by subst e; exact absurd hv (by decide)
      have h6 : ¬ v = 6 := fun e => by subst e; exact absurd hv (by decide)
      simp only [St.setLoc_loc, h4, h5, h6, reduceIte]
    · simp only [St.setLoc_loc, reduceIte, Nat.reduceEqDiff, hj]

/-- The loop at fuel `K ≥ k` with `k` limbs to compare: the signal of `ncRes`, nothing written. -/
theorem ncW_run (p : Prog) (oa ob : Word) :
    ∀ (k K : Nat) (σ : St), σ.loc 0 = oa → σ.loc 2 = ob → (σ.loc 4).toNat = k → k ≤ K →
      (k = 0 ∨ ((oa &&& idxMask).toNat + k ≤ 2 ^ 40 ∧ (ob &&& idxMask).toNat + k ≤ 2 ^ 40 ∧
        (oa &&& idxMask).toNat + k ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size ∧
        (ob &&& idxMask).toNat + k ≤ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size)) →
      ∃ σ', stepRun p (exec p K) ncW σ =
          .ok (ncSig (ncRes (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40)) (oa &&& idxMask) (ob &&& idxMask)
            σ.mem k), σ') ∧
        σ'.mem = σ.mem ∧ ∀ v, v < 4 → σ'.loc v = σ.loc v := by
  intro k
  induction k with
  | zero =>
    intro K σ _ _ hk _ _
    have h0 : σ.loc 4 = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    refine ⟨σ, ?_, rfl, fun _ _ => rfl⟩
    rw [ncW, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h0, UInt64.lt_irrefl,
      decide_false, ncRes, ncSig, reduceIte]
  | succ j ih =>
    intro K σ h0 h2 hk hK hw
    obtain ⟨ha, hb, hA, hB⟩ := hw.resolve_left (by omega)
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hpos : (0 : Word) < σ.loc 4 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
    obtain ⟨s, σ1, e1, hm1, hv1, h41, hs⟩ := ncB_run p (exec p (K + 1)) σ j hk (by rw [h0]; exact ha)
      (by rw [h2]; exact hb) (by rw [h0]; exact hA) (by rw [h2]; exact hB)
    rw [h0, h2] at hs
    rw [ncW, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hpos, decide_true]
    rw [e1]
    have hR : ncRes (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40)) (oa &&& idxMask) (ob &&& idxMask) σ.mem (j + 1) =
        (let x := (σ.mem.arr64 (tierA 0 (oa >>> 40)))[((oa &&& idxMask) + UInt64.ofNat j).toNat]!
         let y := (σ.mem.arr64 (tierA 0 (ob >>> 40)))[((ob &&& idxMask) + UInt64.ofNat j).toNat]!
         if x < y then 0 else if y < x then 2 else
           ncRes (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40)) (oa &&& idxMask) (ob &&& idxMask) σ.mem j) := rfl
    rw [hR]
    simp only at hs ⊢
    split at hs
    · rename_i hxy
      subst hs
      refine ⟨σ1, ?_, hm1, hv1⟩
      simp only [hxy, reduceIte, ncSig]
      rfl
    split at hs
    · rename_i hxy hyx
      subst hs
      refine ⟨σ1, ?_, hm1, hv1⟩
      simp only [hxy, hyx, reduceIte, ncSig]
      rfl
    · rename_i hxy hyx
      simp only [hxy, hyx, reduceIte]
      subst hs
      have h4 := h41 rfl
      obtain ⟨σ2, e2, hm2, hv2⟩ := ih K σ1 (by rw [hv1 0 (by decide), h0]) (by rw [hv1 2 (by decide), h2])
        (by rw [h4, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), hk]; simp)
        (by omega) (Or.inr ⟨by omega, by omega, by rw [hm1]; omega, by rw [hm1]; omega⟩)
      refine ⟨σ2, ?_, by rw [hm2, hm1], fun v hv => (hv2 v hv).trans (hv1 v hv)⟩
      rw [hm1] at e2
      exact e2

/-- **`nat_cmp` at fuel `F > 0`** (`F > la` for equal lengths): by the lengths, or for equal lengths, with both windows in
their tiers below `2^40` (or `la = 0`), `ncRes` over the `la` limbs. -/
theorem natCmp_run (p : Prog) (hp : p.lookup "nat_cmp" = some natCmp) (σ : St) (oa la ob lb : Word)
    (F : Nat) (hF0 : 0 < F) (hF : la = lb → la.toNat < F)
    (hw : la = lb → la = 0 ∨ ((oa &&& idxMask).toNat + la.toNat ≤ 2 ^ 40 ∧
      (ob &&& idxMask).toNat + la.toNat ≤ 2 ^ 40 ∧
      (oa &&& idxMask).toNat + la.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size ∧
      (ob &&& idxMask).toNat + la.toNat ≤ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size)) :
    (invoke p (exec p F) "nat_cmp" [oa, la, ob, lb]).run σ =
      .ok ([if la < lb then 0 else if lb < la then 2 else
        ncRes (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40)) (oa &&& idxMask) (ob &&& idxMask) σ.mem la.toNat], σ) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure natCmp : M FunDecl); callFn (exec p (F + 1)) fd [oa, la, ob, lb]) =
    callFn (exec p (F + 1)) natCmp [oa, la, ob, lb] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) natCmp.body).run = L.Compiler.stepRun p (exec p F) natCmp.body from rfl,
    natCmp_body]
  have hsk : ∀ τ : St, StateT.run (step p (exec p F) Stmt.skip) τ = .ok (.normal, τ) :=
    fun τ => step_skip_run p (exec p F) τ
  by_cases h1 : la < lb
  · simp only [step_seq_run, step_ite_run, evalCP, evalP, Cmp.eval, Locals.init, List.getD_cons_zero, List.getD_cons_succ,
      bind, Except.bind, pure, Except.pure, h1, decide_true, step_ret_run, evalArgsP, Except.map, Sig.retVal,
      Sig.retOr, reduceIte]
  by_cases h2 : lb < la
  · simp only [step_seq_run, step_ite_run, evalCP, evalP, Cmp.eval, Locals.init, List.getD_cons_zero, List.getD_cons_succ,
      bind, Except.bind, pure, Except.pure, h1, h2, decide_true, decide_false, hsk, step_ret_run, evalArgsP,
      Except.map, Sig.retVal, Sig.retOr, reduceIte]
  have heq : la = lb := by
    apply UInt64.toNat_inj.mp
    have := mt UInt64.lt_iff_toNat_lt.mpr h1
    have := mt UInt64.lt_iff_toNat_lt.mpr h2
    omega
  simp only [step_seq_run, step_ite_run, evalCP, evalP, Cmp.eval, Locals.init, List.getD_cons_zero, List.getD_cons_succ,
    bind, Except.bind, pure, Except.pure, h1, h2, decide_false, hsk, step_set_run, Except.map, reduceIte]
  generalize hS : ({ mem := σ.mem, loc := Locals.init [oa, la, ob, lb] } : St).setLoc 4 _ = S
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g0 : S.loc 0 = oa := by subst hS; rfl
  have g2 : S.loc 2 = ob := by subst hS; rfl
  have g4 : S.loc 4 = la := by subst hS; rfl
  have hF' := hF heq
  obtain ⟨S1, e1, hm1, _⟩ := ncW_run p oa ob la.toNat F S g0 g2 (by rw [g4]) (by omega)
    (by rw [hM]; rcases hw heq with h | h
        · left; rw [h]; rfl
        · exact Or.inr h)
  rw [e1]
  by_cases hr : ncRes (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40)) (oa &&& idxMask) (ob &&& idxMask) S.mem
      la.toNat = 1
  · simp only [ncSig, hr, reduceIte, step_ret_run, evalArgsP, evalP, Except.map, bind, Except.bind, pure,
      Except.pure, Sig.retVal, Sig.retOr]
    rw [hm1, hM] at *
    rw [hr]
  · simp only [ncSig, hr, reduceIte, Sig.retVal, Sig.retOr]
    rw [hm1, hM]

end L.AsmEsc
