module

public import ConAguaX86.AsmEsc.MulRowL
import all ConAgua.Arena.NatMul

@[expose] public section

/-!
# `sub_row` as a function

The L code of `sub_row` (`L.Arena.subRow`, `ConAgua/Arena/NatMul.lean`) run at fuel `F`, when its
windows lie in their tiers and the fuel covers the row: the row loop is `srRows` (one subtract with
borrow step `srStep` per limb), the borrow ripple is `scLoop` (`subRow_run`); and `n < la` aborts
(`subRow_run_abort`). As `MulRowL.lean` for `mul_row`.

Locals: `0 o, 1 n, 2 oa, 3 la, 4 i, 5 c, 6 x, 7 t, 8 d, 9 ot, 10 ob, 11 qt, 12 qb`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- The row loop's body. -/
def srB1 : Stmt :=
  .seq (.set 6 (.ld64t 0 (.var 11) (.bin .add (.var 12) (.var 4))))
    (.seq (.set 7 (.ld64t 0 (.var 9) (.bin .add (.var 10) (.var 4))))
      (.seq (.set 8 (.bin .sub (.var 7) (.var 6)))
        (.seq (.st64t 0 (.var 9) (.bin .add (.var 10) (.var 4)) (.bin .sub (.var 8) (.var 5)))
          (.seq (.set 5 (.bin .add (.cmpw .ult (.var 7) (.var 6)) (.cmpw .ult (.var 8) (.var 5))))
            (.set 4 (.bin .add (.var 4) (.const 1)))))))

/-- The row loop. -/
def srW1 : Stmt := .while (.cmp .ult (.var 4) (.var 3)) srB1

/-- The borrow ripple's body. -/
def srB2 : Stmt :=
  .seq (.ite (.cmp .ule (.var 1) (.var 4)) (.abort (.const 0)) .skip)
    (.seq (.set 7 (.ld64t 0 (.var 9) (.bin .add (.var 10) (.var 4))))
      (.seq (.st64t 0 (.var 9) (.bin .add (.var 10) (.var 4)) (.bin .sub (.var 7) (.const 1)))
        (.seq (.set 5 (.cmpw .eq (.var 7) (.const 0)))
          (.set 4 (.bin .add (.var 4) (.const 1))))))

/-- The borrow ripple. -/
def srW2 : Stmt := .while (.cmp .ne (.var 5) (.const 0)) srB2

theorem subRow_body : subRow.body =
    .seq (.ite (.cmp .ult (.var 1) (.var 3)) (.abort (.const 0)) .skip)
      (.seq (.set 9 (.bin .shr (.var 0) (.const 40)))
        (.seq (.set 10 (.bin .and (.var 0) (.const 1099511627775)))
          (.seq (.set 11 (.bin .shr (.var 2) (.const 40)))
            (.seq (.set 12 (.bin .and (.var 2) (.const 1099511627775)))
              (.seq srW1 (.seq srW2 (.ret [.const 0]))))))) := by
  rfl

theorem subRow_nparams : subRow.nparams = 4 := by rfl

/-- One subtract-with-borrow step at index `i` with borrow `c`: the new memory and borrow. -/
def srStep (TA TO : TieredArray) (qb ob : Word) (m : Mem) (i c : Word) : Mem × Word :=
  let x := (m.arr64 TA)[(qb + i).toNat]!
  let t := (m.arr64 TO)[(ob + i).toNat]!
  (m.set64 TO (ob + i) (t - x - c), Cmp.evalW .ult t x + Cmp.evalW .ult (t - x) c)

/-- `r` steps of the row from index `i` with borrow `c`. -/
def srRows (TA TO : TieredArray) (qb ob : Word) : Nat → Mem → Word → Word → Mem × Word
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c =>
    srRows TA TO qb ob r (srStep TA TO qb ob m i c).1 (i + 1) (srStep TA TO qb ob m i c).2

/-- The borrow ripple at fuel `k` from index `i` with borrow `c`. -/
def scLoop (TO : TieredArray) (ob n : Word) : Nat → Mem → Word → Word → Except Err Mem
  | k, m, i, c =>
    if c = 0 then .ok m
    else if n ≤ i then .error (.abort 0)
    else if h : (ob + i).toNat < (m.arr64 TO).size then
      match k with
      | 0 => .error .outOfFuel
      | k + 1 =>
        scLoop TO ob n k (m.set64 TO (ob + i) ((m.arr64 TO)[(ob + i).toNat] - 1)) (i + 1)
          (Cmp.evalW .eq (m.arr64 TO)[(ob + i).toNat] 0)
    else .error .oob

theorem srB1_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hA : (σ.loc 12 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size)
    (hO : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size) :
    ∃ σ', stepRun p K srB1 σ = .ok (.normal, σ') ∧
      σ'.mem = (srStep (tierA 0 (σ.loc 11)) (tierA 0 (σ.loc 9)) (σ.loc 12) (σ.loc 10) σ.mem
        (σ.loc 4) (σ.loc 5)).1 ∧
      σ'.loc 5 = (srStep (tierA 0 (σ.loc 11)) (tierA 0 (σ.loc 9)) (σ.loc 12) (σ.loc 10) σ.mem
        (σ.loc 4) (σ.loc 5)).2 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 8 < v) → σ'.loc v = σ.loc v := by
  simp only [srB1, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, srStep, getElem!_pos, hA, hO]
  · simp only [St.setLoc_loc, srStep, getElem!_pos, hA, hO, Nat.reduceEqDiff, reduceIte]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    have h7 : ¬ v = 7 := by omega
    have h8 : ¬ v = 8 := by omega
    simp only [St.setLoc_loc, h4, h5, h6, h7, h8, reduceIte]

theorem srRows_succ (TA TO : TieredArray) (qb ob : Word) :
    ∀ (r : Nat) (m : Mem) (i c : Word), srRows TA TO qb ob (r + 1) m i c =
      srStep TA TO qb ob (srRows TA TO qb ob r m i c).1 (i + UInt64.ofNat r) (srRows TA TO qb ob r m i c).2
  | 0, m, i, c => by simp [srRows]
  | r + 1, m, i, c => by
    rw [srRows, srRows_succ TA TO qb ob r, srRows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    rw [e]

/-- The row loop at fuel `k ≥ r` with `r` steps to go, its windows in their tiers: `srRows`. -/
theorem srW1_run (p : Prog) (TA TO : TieredArray) (qb ob la : Word) :
    ∀ (r k : Nat) (σ : St), tierA 0 (σ.loc 11) = TA → tierA 0 (σ.loc 9) = TO → σ.loc 12 = qb →
      σ.loc 10 = ob → σ.loc 3 = la → (σ.loc 4).toNat + r = la.toNat → r ≤ k →
      qb.toNat + la.toNat ≤ (σ.mem.arr64 TA).size → ob.toNat + la.toNat ≤ (σ.mem.arr64 TO).size →
      (σ.mem.arr64 TA).size < 2 ^ 64 → (σ.mem.arr64 TO).size < 2 ^ 64 →
      ∃ σ', stepRun p (exec p k) srW1 σ = .ok (.normal, σ') ∧
        σ'.mem = (srRows TA TO qb ob r σ.mem (σ.loc 4) (σ.loc 5)).1 ∧
        σ'.loc 5 = (srRows TA TO qb ob r σ.mem (σ.loc 4) (σ.loc 5)).2 ∧
        σ'.loc 4 = la ∧ ∀ v : Nat, (v < 4 ∨ 8 < v) → σ'.loc v = σ.loc v := by
  intro r
  induction r with
  | zero =>
    intro k σ h11 h9 h12 h10 h3 hi _ _ _ _ _
    have hil : σ.loc 4 = la := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, rfl, hil, fun _ _ => rfl⟩
    rw [srW1, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h3, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ h11 h9 h12 h10 h3 hi hk hA hO hsA hsO
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc 4 < la := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hA' : (σ.loc 12 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size := by
      rw [h12, h11, L.toNat_add_of_lt _ _ (by omega)]; omega
    have hO' : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size := by
      rw [h10, h9, L.toNat_add_of_lt _ _ (by omega)]; omega
    obtain ⟨σ1, h1, hm1, hc1, hi1, hv1⟩ := srB1_run p (exec p (k + 1)) σ hA' hO'
    rw [h11, h9, h12, h10] at hm1 hc1
    have e11 := hv1 11 (by omega)
    have e9 := hv1 9 (by omega)
    have e12 := hv1 12 (by omega)
    have e10 := hv1 10 (by omega)
    have e3 := hv1 3 (by omega)
    have hi1' : (σ1.loc 4).toNat + r = la.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, h2, hm2, hc2, hi2, hv2⟩ := ih k σ1 (by rw [e11, h11]) (by rw [e9, h9]) (by rw [e12, h12])
      (by rw [e10, h10]) (by rw [e3, h3]) hi1' (by omega)
      (by rw [hm1, srStep, size_set64]; exact hA) (by rw [hm1, srStep, size_set64]; exact hO)
      (by rw [hm1, srStep, size_set64]; exact hsA) (by rw [hm1, srStep, size_set64]; exact hsO)
    refine ⟨σ2, ?_, ?_, ?_, hi2, fun v hv => (hv2 v hv).trans (hv1 v hv)⟩
    · rw [srW1, step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h3, hlt, decide_true]
      rw [← srW1, h1]
      exact h2
    · rw [hm2, hm1, hc1, hi1, srRows]
    · rw [hc2, hm1, hc1, hi1, srRows]

theorem srB2_run (p : Prog) (K : Stmt → M Sig) (σ : St) (hn : ¬ σ.loc 1 ≤ σ.loc 4)
    (hO : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size) :
    ∃ σ', stepRun p K srB2 σ = .ok (.normal, σ') ∧
      σ'.mem = σ.mem.set64 (tierA 0 (σ.loc 9)) (σ.loc 10 + σ.loc 4)
        ((σ.mem.arr64 (tierA 0 (σ.loc 9)))[(σ.loc 10 + σ.loc 4).toNat] - 1) ∧
      σ'.loc 5 = Cmp.evalW .eq (σ.mem.arr64 (tierA 0 (σ.loc 9)))[(σ.loc 10 + σ.loc 4).toNat] 0 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, v ≠ 4 → v ≠ 5 → v ≠ 7 → σ'.loc v = σ.loc v := by
  simp only [srB2, step_seq_run, step_ite_run, step_set_run, step_st64t_run, evalCP, evalP, bind,
    Except.bind, pure, Except.pure, Except.map, St.setLoc_loc, BinOp.eval, Cmp.eval,
    Nat.reduceEqDiff, reduceIte, hn, decide_false]
  rw [show StateT.run (step p K Stmt.skip) σ = .ok (.normal, σ) from rfl]
  simp only [St.setLoc_loc, St.setLoc_mem, Nat.reduceEqDiff, reduceIte, hO, ↓reduceDIte]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v h4 h5 h7
    simp only [St.setLoc_loc, h4, h5, h7, reduceIte]

theorem srB2_abort (p : Prog) (K : Stmt → M Sig) (σ : St) (hn : σ.loc 1 ≤ σ.loc 4) :
    stepRun p K srB2 σ = .error (.abort 0) := by
  simp only [srB2, step_seq_run, step_ite_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    Cmp.eval, hn, decide_true, step_abort_run]

theorem srB2_oob (p : Prog) (K : Stmt → M Sig) (σ : St) (hn : ¬ σ.loc 1 ≤ σ.loc 4)
    (hO : ¬ (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size) :
    stepRun p K srB2 σ = .error .oob := by
  simp only [srB2, step_seq_run, step_ite_run, step_set_run, evalCP, evalP, bind,
    Except.bind, pure, Except.pure, Except.map, Cmp.eval, hn, decide_false, BinOp.eval]
  rw [show StateT.run (step p K Stmt.skip) σ = .ok (.normal, σ) from rfl]
  simp only [hO, ↓reduceDIte]

/-- The borrow ripple at fuel `k` is `scLoop`. -/
theorem srW2_run (p : Prog) (TO : TieredArray) (ob n : Word) :
    ∀ (k : Nat) (σ : St), tierA 0 (σ.loc 9) = TO → σ.loc 10 = ob → σ.loc 1 = n →
      LoopRel (stepRun p (exec p k) srW2 σ) (scLoop TO ob n k σ.mem (σ.loc 4) (σ.loc 5)) := by
  intro k
  induction k with
  | zero =>
    intro σ h9 h10 h1
    rw [srW2, step_while_run]
    by_cases hc : σ.loc 5 = 0
    · simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval]
      rw [scLoop]; simp only [hc, reduceIte, LoopRel]; exact ⟨σ, rfl, rfl⟩
    have hc' : (σ.loc 5 != 0) = true := by simpa using hc
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hc']
    by_cases hn : σ.loc 1 ≤ σ.loc 4
    · rw [srB2_abort p (exec p 0) σ hn, scLoop]
      simp only [hc, h1 ▸ hn, reduceIte, LoopRel]
    by_cases hO : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size
    · obtain ⟨σ1, e1, -⟩ := srB2_run p (exec p 0) σ hn hO
      rw [e1, scLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h10, ← h9, hO, ↓reduceDIte, LoopRel]
      rfl
    · rw [srB2_oob p (exec p 0) σ hn hO, scLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h10, ← h9, hO, ↓reduceDIte, LoopRel]
  | succ k ih =>
    intro σ h9 h10 h1
    rw [srW2, step_while_run]
    by_cases hc : σ.loc 5 = 0
    · simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval]
      rw [scLoop]; simp only [hc, reduceIte, LoopRel]; exact ⟨σ, rfl, rfl⟩
    have hc' : (σ.loc 5 != 0) = true := by simpa using hc
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hc']
    by_cases hn : σ.loc 1 ≤ σ.loc 4
    · rw [srB2_abort p (exec p (k + 1)) σ hn, scLoop]
      simp only [hc, h1 ▸ hn, reduceIte, LoopRel]
    by_cases hO : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size
    · obtain ⟨σ1, e1, hm1, hc1, hi1, hv1⟩ := srB2_run p (exec p (k + 1)) σ hn hO
      rw [e1, scLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h10, ← h9, hO, ↓reduceDIte]
      subst h9 h10 h1
      have := ih σ1 (by rw [hv1 9 (by decide) (by decide) (by decide)])
        (by rw [hv1 10 (by decide) (by decide) (by decide)]) (by rw [hv1 1 (by decide) (by decide) (by decide)])
      rw [hm1, hc1, hi1] at this
      exact this
    · rw [srB2_oob p (exec p (k + 1)) σ hn hO, scLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h10, ← h9, hO, ↓reduceDIte, LoopRel]

/-- `sub_row` with `n < la` aborts. -/
theorem subRow_run_abort (p : Prog) (hp : p.lookup "sub_row" = some subRow) (σ : St) (o n oa la : Word)
    (F : Nat) (hF : 0 < F) (hn : n < la) :
    (invoke p (exec p F) "sub_row" [o, n, oa, la]).run σ = .error (.abort 0) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure subRow : M FunDecl); callFn (exec p (F + 1)) fd [o, n, oa, la]) =
    callFn (exec p (F + 1)) subRow [o, n, oa, la] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) subRow.body).run = L.Compiler.stepRun p (exec p F) subRow.body from rfl,
    subRow_body]
  simp only [step_seq_run, step_ite_run, evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval,
    step_abort_run, Locals.init, List.getD_cons_succ, List.getD_cons_zero, hn, decide_true]

/-- **`sub_row` at fuel `F`**, its windows in their tiers and `la < F`: the row (`srRows`), then the
borrow ripple (`scLoop`). -/
theorem subRow_run (p : Prog) (hp : p.lookup "sub_row" = some subRow) (σ : St) (o n oa la : Word)
    (F : Nat) (hn : ¬ n < la) (hF : la.toNat < F)
    (hA : (oa &&& idxMask).toNat + la.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size)
    (hO : (o &&& idxMask).toNat + la.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size)
    (hsA : (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64)
    (hsO : (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64) :
    (invoke p (exec p F) "sub_row" [o, n, oa, la]).run σ =
      (scLoop (tierA 0 (o >>> 40)) (o &&& idxMask) n (F - 1)
        (srRows (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) la.toNat σ.mem 0 0).1
        la
        (srRows (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) la.toNat σ.mem 0 0).2
        ).map fun m => ([0], { σ with mem := m }) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure subRow : M FunDecl); callFn (exec p (F + 1)) fd [o, n, oa, la]) =
    callFn (exec p (F + 1)) subRow [o, n, oa, la] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) subRow.body).run = L.Compiler.stepRun p (exec p F) subRow.body from rfl,
    subRow_body]
  simp only [step_seq_run, step_ite_run, step_set_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, Cmp.eval, BinOp.eval, Locals.init, List.getD_cons_succ, List.getD_cons_zero, hn, decide_false]
  rw [show StateT.run (step p (exec p F) Stmt.skip) _ = .ok (.normal, _) from rfl]
  simp only []
  generalize hS : (((({ mem := σ.mem, loc := Locals.init [o, n, oa, la] } : St).setLoc 9 _).setLoc 10 _).setLoc
    11 _).setLoc 12 _ = S
  have hL : ∀ v, S.loc v = if v = 12 then oa &&& idxMask else if v = 11 then oa >>> 40 else
      if v = 10 then o &&& idxMask else if v = 9 then o >>> 40 else Locals.init [o, n, oa, la] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceEqDiff, reduceIte]
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g1 : S.loc 1 = n := by rw [hL]; rfl
  have g3 : S.loc 3 = la := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  have g5 : S.loc 5 = 0 := by rw [hL]; rfl
  have g9 : S.loc 9 = o >>> 40 := by rw [hL]; rfl
  have g10 : S.loc 10 = o &&& idxMask := by rw [hL]; rfl
  have g11 : S.loc 11 = oa >>> 40 := by rw [hL]; rfl
  have g12 : S.loc 12 = oa &&& idxMask := by rw [hL]; rfl
  obtain ⟨S1, e1, hm1, hc1, hi1, hv1⟩ := srW1_run p _ _ _ _ la la.toNat F S (by rw [g11]) (by rw [g9])
    g12 g10 g3 (by rw [g4]; simp) (by omega) (by rw [hM]; exact hA) (by rw [hM]; exact hO)
    (by rw [hM]; exact hsA) (by rw [hM]; exact hsO)
  rw [e1]
  simp only []
  have hW := srW2_run p (tierA 0 (o >>> 40)) (o &&& idxMask) n F S1 (by rw [hv1 9 (by omega), g9])
    (by rw [hv1 10 (by omega), g10]) (by rw [hv1 1 (by omega), g1])
  rw [hm1, hc1, hi1, hM, g4, g5] at hW
  simp only [Nat.add_sub_cancel]
  revert hW
  generalize stepRun p (exec p F) srW2 S1 = R
  generalize scLoop _ _ _ _ _ _ _ = res
  intro hW
  rcases res with e | m
  · simp only [LoopRel] at hW; subst hW; simp only []
  · obtain ⟨σ2, h2, hm2⟩ := hW
    subst h2
    simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, Sig.retVal,
      Sig.retOr, hm2]

/-- `sub_row` with `la = 0` returns `0` and changes nothing. -/
theorem subRow_run_zero (p : Prog) (hp : p.lookup "sub_row" = some subRow) (σ : St) (o n oa : Word)
    (F : Nat) (hF : 0 < F) :
    (invoke p (exec p F) "sub_row" [o, n, oa, 0]).run σ = .ok ([0], σ) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure subRow : M FunDecl); callFn (exec p (F + 1)) fd [o, n, oa, 0]) =
    callFn (exec p (F + 1)) subRow [o, n, oa, 0] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) subRow.body).run = L.Compiler.stepRun p (exec p F) subRow.body from rfl,
    subRow_body]
  simp only [step_seq_run, step_ite_run, step_set_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, Cmp.eval, BinOp.eval, Locals.init, List.getD_cons_succ, List.getD_cons_zero,
    UInt64.not_lt_zero, decide_false]
  rw [show StateT.run (step p (exec p F) Stmt.skip) _ = .ok (.normal, _) from rfl]
  simp only [srW1, srW2, step_while_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    St.setLoc_loc, Nat.reduceEqDiff, reduceIte, Locals.init, List.getD_cons_succ, List.getD_cons_zero,
    Cmp.eval, UInt64.not_lt_zero, decide_false, bne_self_eq_false, step_ret_run, evalArgsP, Except.map,
    Sig.retVal, Sig.retOr, List.getD_nil]
  rfl

end L.AsmEsc
