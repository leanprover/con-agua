module

public import ConAgua.Arena.NatMul
public import ConAguaX86.Compiler.RunEq
public import ConAguaX86.Compiler.SimCall
public import ConAguaX86.Compiler.SimStore
import all ConAgua.Arena.NatMul

@[expose] public section

/-!
# `mul_row` as a function

The L code of `mul_row` (`L.Arena.mulRow`, `ConAgua/Arena/NatMul.lean`) run at fuel `F`, when its
windows lie in their tiers and the fuel covers the row: the row loop is `mrRows` (one
multiply-accumulate step `mrStep` per limb), the carry ripple is `mcLoop` (`mulRow_run`); and
`n < la` aborts (`mulRow_run_abort`). The machine-level proof of the hand-written body
(`MulRowAsm.lean`) is against these functions; the L code stays the source of truth for every
L-level proof.

Locals: `0 o, 1 n, 2 oa, 3 la, 4 y, 5 i, 6 c, 7 x, 8 t, 9 lo, 10 hi, 11 ot, 12 ob, 13 qt, 14 qb`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- The row loop's body. -/
def mrB1 : Stmt :=
  .seq (.set 7 (.ld64t 0 (.var 13) (.bin .add (.var 14) (.var 5))))
    (.seq (.set 8 (.ld64t 0 (.var 11) (.bin .add (.var 12) (.var 5))))
      (.seq (.set 9 (.bin .add (.bin .mul (.var 7) (.var 4)) (.var 8)))
        (.seq (.set 10 (.bin .add (.bin .mulhi (.var 7) (.var 4)) (.cmpw .ult (.var 9) (.var 8))))
          (.seq (.set 9 (.bin .add (.var 9) (.var 6)))
            (.seq (.st64t 0 (.var 11) (.bin .add (.var 12) (.var 5)) (.var 9))
              (.seq (.set 6 (.bin .add (.var 10) (.cmpw .ult (.var 9) (.var 6))))
                (.set 5 (.bin .add (.var 5) (.const 1)))))))))

/-- The row loop. -/
def mrW1 : Stmt := .while (.cmp .ult (.var 5) (.var 3)) mrB1

/-- The carry ripple's body. -/
def mrB2 : Stmt :=
  .seq (.ite (.cmp .ule (.var 1) (.var 5)) (.abort (.const 0)) .skip)
    (.seq (.set 8 (.bin .add (.ld64t 0 (.var 11) (.bin .add (.var 12) (.var 5))) (.var 6)))
      (.seq (.st64t 0 (.var 11) (.bin .add (.var 12) (.var 5)) (.var 8))
        (.seq (.set 6 (.cmpw .ult (.var 8) (.var 6)))
          (.set 5 (.bin .add (.var 5) (.const 1))))))

/-- The carry ripple. -/
def mrW2 : Stmt := .while (.cmp .ne (.var 6) (.const 0)) mrB2

theorem mulRow_body : mulRow.body =
    .seq (.ite (.cmp .ult (.var 1) (.var 3)) (.abort (.const 0)) .skip)
      (.seq (.set 11 (.bin .shr (.var 0) (.const 40)))
        (.seq (.set 12 (.bin .and (.var 0) (.const 1099511627775)))
          (.seq (.set 13 (.bin .shr (.var 2) (.const 40)))
            (.seq (.set 14 (.bin .and (.var 2) (.const 1099511627775)))
              (.seq mrW1 (.seq mrW2 (.ret [.const 0]))))))) := by
  rfl

theorem mulRow_nparams : mulRow.nparams = 5 := by rfl

/-- One multiply-accumulate step at index `i` with carry `c`: the new memory and carry. -/
def mrStep (TA TO : TieredArray) (qb ob y : Word) (m : Mem) (i c : Word) : Mem × Word :=
  let x := (m.arr64 TA)[(qb + i).toNat]!
  let t := (m.arr64 TO)[(ob + i).toNat]!
  let lo := x * y + t
  let hi := BinOp.mulhi.eval x y + Cmp.evalW .ult lo t
  let lo2 := lo + c
  (m.set64 TO (ob + i) lo2, hi + Cmp.evalW .ult lo2 c)

/-- `r` steps of the row from index `i` with carry `c`. -/
def mrRows (TA TO : TieredArray) (qb ob y : Word) : Nat → Mem → Word → Word → Mem × Word
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c =>
    mrRows TA TO qb ob y r (mrStep TA TO qb ob y m i c).1 (i + 1) (mrStep TA TO qb ob y m i c).2

/-- The carry ripple at fuel `k` from index `i` with carry `c`. -/
def mcLoop (TO : TieredArray) (ob n : Word) : Nat → Mem → Word → Word → Except Err Mem
  | k, m, i, c =>
    if c = 0 then .ok m
    else if n ≤ i then .error (.abort 0)
    else if h : (ob + i).toNat < (m.arr64 TO).size then
      match k with
      | 0 => .error .outOfFuel
      | k + 1 =>
        mcLoop TO ob n k (m.set64 TO (ob + i) ((m.arr64 TO)[(ob + i).toNat] + c)) (i + 1)
          (Cmp.evalW .ult ((m.arr64 TO)[(ob + i).toNat] + c) c)
    else .error .oob

theorem size_set64 (m : Mem) (a b : TieredArray) (i v : Word) :
    ((m.set64 a i v).arr64 b).size = (m.arr64 b).size := by
  rw [L.Compiler.Mem.arr64_set64]; split <;> simp_all

theorem mrB1_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hA : (σ.loc 14 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 13))).size)
    (hO : (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size) :
    ∃ σ', stepRun p K mrB1 σ = .ok (.normal, σ') ∧
      σ'.mem = (mrStep (tierA 0 (σ.loc 13)) (tierA 0 (σ.loc 11)) (σ.loc 14) (σ.loc 12) (σ.loc 4) σ.mem
        (σ.loc 5) (σ.loc 6)).1 ∧
      σ'.loc 6 = (mrStep (tierA 0 (σ.loc 13)) (tierA 0 (σ.loc 11)) (σ.loc 14) (σ.loc 12) (σ.loc 4) σ.mem
        (σ.loc 5) (σ.loc 6)).2 ∧
      σ'.loc 5 = σ.loc 5 + 1 ∧ ∀ v : Nat, (v < 5 ∨ 10 < v) → σ'.loc v = σ.loc v := by
  simp only [mrB1, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, mrStep, getElem!_pos, hA, hO]
  · simp only [St.setLoc_loc, mrStep, getElem!_pos, hA, hO, BinOp.eval, Nat.reduceEqDiff, reduceIte]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    have h7 : ¬ v = 7 := by omega
    have h8 : ¬ v = 8 := by omega
    have h9 : ¬ v = 9 := by omega
    have h10 : ¬ v = 10 := by omega
    simp only [St.setLoc_loc, h5, h6, h7, h8, h9, h10, reduceIte]

theorem mrRows_size (TA TO : TieredArray) (qb ob y : Word) (b : TieredArray) :
    ∀ (r : Nat) (m : Mem) (i c : Word), ((mrRows TA TO qb ob y r m i c).1.arr64 b).size = (m.arr64 b).size
  | 0, _, _, _ => rfl
  | r + 1, m, i, c => by
    rw [mrRows, mrRows_size TA TO qb ob y b r]; simp only [mrStep, size_set64]

/-- The row's last step: `r + 1` steps are `r` steps, then one at index `i + r`. -/
theorem mrRows_succ (TA TO : TieredArray) (qb ob y : Word) :
    ∀ (r : Nat) (m : Mem) (i c : Word), mrRows TA TO qb ob y (r + 1) m i c =
      mrStep TA TO qb ob y (mrRows TA TO qb ob y r m i c).1 (i + UInt64.ofNat r) (mrRows TA TO qb ob y r m i c).2
  | 0, m, i, c => by simp [mrRows]
  | r + 1, m, i, c => by
    rw [mrRows, mrRows_succ TA TO qb ob y r, mrRows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    rw [e]

/-- The row loop at fuel `k ≥ r` with `r` steps to go, its windows in their tiers: `mrRows`. -/
theorem mrW1_run (p : Prog) (TA TO : TieredArray) (qb ob y la : Word) :
    ∀ (r k : Nat) (σ : St), tierA 0 (σ.loc 13) = TA → tierA 0 (σ.loc 11) = TO → σ.loc 14 = qb →
      σ.loc 12 = ob → σ.loc 4 = y → σ.loc 3 = la → (σ.loc 5).toNat + r = la.toNat → r ≤ k →
      qb.toNat + la.toNat ≤ (σ.mem.arr64 TA).size → ob.toNat + la.toNat ≤ (σ.mem.arr64 TO).size →
      (σ.mem.arr64 TA).size < 2 ^ 64 → (σ.mem.arr64 TO).size < 2 ^ 64 →
      ∃ σ', stepRun p (exec p k) mrW1 σ = .ok (.normal, σ') ∧
        σ'.mem = (mrRows TA TO qb ob y r σ.mem (σ.loc 5) (σ.loc 6)).1 ∧
        σ'.loc 6 = (mrRows TA TO qb ob y r σ.mem (σ.loc 5) (σ.loc 6)).2 ∧
        σ'.loc 5 = la ∧ ∀ v : Nat, (v < 5 ∨ 10 < v) → σ'.loc v = σ.loc v := by
  intro r
  induction r with
  | zero =>
    intro k σ h13 h11 h14 h12 h4 h3 hi _ _ _ _ _
    have hil : σ.loc 5 = la := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, rfl, hil, fun _ _ => rfl⟩
    rw [mrW1, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h3, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ h13 h11 h14 h12 h4 h3 hi hk hA hO hsA hsO
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc 5 < la := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hA' : (σ.loc 14 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 13))).size := by
      rw [h14, h13, L.toNat_add_of_lt _ _ (by omega)]; omega
    have hO' : (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size := by
      rw [h12, h11, L.toNat_add_of_lt _ _ (by omega)]; omega
    obtain ⟨σ1, h1, hm1, hc1, hi1, hv1⟩ := mrB1_run p (exec p (k + 1)) σ hA' hO'
    rw [h13, h11, h14, h12, h4] at hm1 hc1
    have e13 := hv1 13 (by omega)
    have e11 := hv1 11 (by omega)
    have e14 := hv1 14 (by omega)
    have e12 := hv1 12 (by omega)
    have e4 := hv1 4 (by omega)
    have e3 := hv1 3 (by omega)
    have hi1' : (σ1.loc 5).toNat + r = la.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, h2, hm2, hc2, hi2, hv2⟩ := ih k σ1 (by rw [e13, h13]) (by rw [e11, h11]) (by rw [e14, h14])
      (by rw [e12, h12]) (by rw [e4, h4]) (by rw [e3, h3]) hi1' (by omega)
      (by rw [hm1, mrStep, size_set64]; exact hA) (by rw [hm1, mrStep, size_set64]; exact hO)
      (by rw [hm1, mrStep, size_set64]; exact hsA) (by rw [hm1, mrStep, size_set64]; exact hsO)
    refine ⟨σ2, ?_, ?_, ?_, hi2, fun v hv => (hv2 v hv).trans (hv1 v hv)⟩
    · rw [mrW1, step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h3, hlt, decide_true]
      rw [← mrW1, h1]
      exact h2
    · rw [hm2, hm1, hc1, hi1, mrRows]
    · rw [hc2, hm1, hc1, hi1, mrRows]

/-- A loop's run against a function of the memory: a normal end with that memory, or the same
error. -/
def LoopRel (r : Except Err (Sig × St)) : Except Err Mem → Prop
  | .ok m => ∃ σ', r = .ok (.normal, σ') ∧ σ'.mem = m
  | .error e => r = .error e

theorem mrB2_run (p : Prog) (K : Stmt → M Sig) (σ : St) (hn : ¬ σ.loc 1 ≤ σ.loc 5)
    (hO : (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size) :
    ∃ σ', stepRun p K mrB2 σ = .ok (.normal, σ') ∧
      σ'.mem = σ.mem.set64 (tierA 0 (σ.loc 11)) (σ.loc 12 + σ.loc 5)
        ((σ.mem.arr64 (tierA 0 (σ.loc 11)))[(σ.loc 12 + σ.loc 5).toNat] + σ.loc 6) ∧
      σ'.loc 6 = Cmp.evalW .ult ((σ.mem.arr64 (tierA 0 (σ.loc 11)))[(σ.loc 12 + σ.loc 5).toNat] + σ.loc 6)
        (σ.loc 6) ∧
      σ'.loc 5 = σ.loc 5 + 1 ∧ ∀ v : Nat, v ≠ 5 → v ≠ 6 → v ≠ 8 → σ'.loc v = σ.loc v := by
  simp only [mrB2, step_seq_run, step_ite_run, step_set_run, step_st64t_run, evalCP, evalP, bind,
    Except.bind, pure, Except.pure, Except.map, St.setLoc_loc, BinOp.eval, Cmp.eval,
    Nat.reduceEqDiff, reduceIte, hn, decide_false]
  rw [show StateT.run (step p K Stmt.skip) σ = .ok (.normal, σ) from rfl]
  simp only [St.setLoc_loc, St.setLoc_mem, Nat.reduceEqDiff, reduceIte, hO, ↓reduceDIte]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v h5 h6 h8
    simp only [St.setLoc_loc, h5, h6, h8, reduceIte]

theorem mrB2_abort (p : Prog) (K : Stmt → M Sig) (σ : St) (hn : σ.loc 1 ≤ σ.loc 5) :
    stepRun p K mrB2 σ = .error (.abort 0) := by
  simp only [mrB2, step_seq_run, step_ite_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    Cmp.eval, hn, decide_true, step_abort_run]

theorem mrB2_oob (p : Prog) (K : Stmt → M Sig) (σ : St) (hn : ¬ σ.loc 1 ≤ σ.loc 5)
    (hO : ¬ (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size) :
    stepRun p K mrB2 σ = .error .oob := by
  simp only [mrB2, step_seq_run, step_ite_run, step_set_run, evalCP, evalP, bind,
    Except.bind, pure, Except.pure, Except.map, Cmp.eval, hn, decide_false, BinOp.eval]
  rw [show StateT.run (step p K Stmt.skip) σ = .ok (.normal, σ) from rfl]
  simp only [hO, ↓reduceDIte]

/-- The carry ripple at fuel `k` is `mcLoop`. -/
theorem mrW2_run (p : Prog) (TO : TieredArray) (ob n : Word) :
    ∀ (k : Nat) (σ : St), tierA 0 (σ.loc 11) = TO → σ.loc 12 = ob → σ.loc 1 = n →
      LoopRel (stepRun p (exec p k) mrW2 σ) (mcLoop TO ob n k σ.mem (σ.loc 5) (σ.loc 6)) := by
  intro k
  induction k with
  | zero =>
    intro σ h11 h12 h1
    rw [mrW2, step_while_run]
    by_cases hc : σ.loc 6 = 0
    · simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval]
      rw [mcLoop]; simp only [hc, reduceIte, LoopRel]; exact ⟨σ, rfl, rfl⟩
    have hc' : (σ.loc 6 != 0) = true := by simpa using hc
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hc']
    by_cases hn : σ.loc 1 ≤ σ.loc 5
    · rw [mrB2_abort p (exec p 0) σ hn, mcLoop]
      simp only [hc, h1 ▸ hn, reduceIte, LoopRel]
    by_cases hO : (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size
    · obtain ⟨σ1, e1, -⟩ := mrB2_run p (exec p 0) σ hn hO
      rw [e1, mcLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h12, ← h11, hO, ↓reduceDIte, LoopRel]
      rfl
    · rw [mrB2_oob p (exec p 0) σ hn hO, mcLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h12, ← h11, hO, ↓reduceDIte, LoopRel]
  | succ k ih =>
    intro σ h11 h12 h1
    rw [mrW2, step_while_run]
    by_cases hc : σ.loc 6 = 0
    · simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval]
      rw [mcLoop]; simp only [hc, reduceIte, LoopRel]; exact ⟨σ, rfl, rfl⟩
    have hc' : (σ.loc 6 != 0) = true := by simpa using hc
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hc']
    by_cases hn : σ.loc 1 ≤ σ.loc 5
    · rw [mrB2_abort p (exec p (k + 1)) σ hn, mcLoop]
      simp only [hc, h1 ▸ hn, reduceIte, LoopRel]
    by_cases hO : (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size
    · obtain ⟨σ1, e1, hm1, hc1, hi1, hv1⟩ := mrB2_run p (exec p (k + 1)) σ hn hO
      rw [e1, mcLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h12, ← h11, hO, ↓reduceDIte]
      subst h11 h12 h1
      have := ih σ1 (by rw [hv1 11 (by decide) (by decide) (by decide)])
        (by rw [hv1 12 (by decide) (by decide) (by decide)]) (by rw [hv1 1 (by decide) (by decide) (by decide)])
      rw [hm1, hc1, hi1] at this
      exact this
    · rw [mrB2_oob p (exec p (k + 1)) σ hn hO, mcLoop]
      simp only [hc, ← h1, hn, reduceIte, ← h12, ← h11, hO, ↓reduceDIte, LoopRel]

/-- `mul_row` with `n < la` aborts. -/
theorem mulRow_run_abort (p : Prog) (hp : p.lookup "mul_row" = some mulRow) (σ : St) (o n oa la y : Word)
    (F : Nat) (hF : 0 < F) (hn : n < la) :
    (invoke p (exec p F) "mul_row" [o, n, oa, la, y]).run σ = .error (.abort 0) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure mulRow : M FunDecl); callFn (exec p (F + 1)) fd [o, n, oa, la, y]) =
    callFn (exec p (F + 1)) mulRow [o, n, oa, la, y] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) mulRow.body).run = L.Compiler.stepRun p (exec p F) mulRow.body from rfl,
    mulRow_body]
  simp only [step_seq_run, step_ite_run, evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval,
    step_abort_run, Locals.init, List.getD_cons_succ, List.getD_cons_zero, hn, decide_true]

/-- The 40-bit index mask of a pool reference. -/
abbrev idxMask : Word := 1099511627775

/-- **`mul_row` at fuel `F`**, its windows in their tiers and `la < F`: the row (`mrRows`), then the
carry ripple (`mcLoop`). -/
theorem mulRow_run (p : Prog) (hp : p.lookup "mul_row" = some mulRow) (σ : St) (o n oa la y : Word)
    (F : Nat) (hn : ¬ n < la) (hF : la.toNat < F)
    (hA : (oa &&& idxMask).toNat + la.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size)
    (hO : (o &&& idxMask).toNat + la.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size)
    (hsA : (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64)
    (hsO : (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64) :
    (invoke p (exec p F) "mul_row" [o, n, oa, la, y]).run σ =
      (mcLoop (tierA 0 (o >>> 40)) (o &&& idxMask) n (F - 1)
        (mrRows (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) y la.toNat σ.mem 0 0).1
        la
        (mrRows (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) y la.toNat σ.mem 0 0).2
        ).map fun m => ([0], { σ with mem := m }) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure mulRow : M FunDecl); callFn (exec p (F + 1)) fd [o, n, oa, la, y]) =
    callFn (exec p (F + 1)) mulRow [o, n, oa, la, y] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) mulRow.body).run = L.Compiler.stepRun p (exec p F) mulRow.body from rfl,
    mulRow_body]
  simp only [step_seq_run, step_ite_run, step_set_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, Cmp.eval, BinOp.eval, Locals.init, List.getD_cons_succ, List.getD_cons_zero, hn, decide_false]
  rw [show StateT.run (step p (exec p F) Stmt.skip) _ = .ok (.normal, _) from rfl]
  simp only []
  generalize hS : (((({ mem := σ.mem, loc := Locals.init [o, n, oa, la, y] } : St).setLoc 11 _).setLoc 12 _).setLoc
    13 _).setLoc 14 _ = S
  have hL : ∀ v, S.loc v = if v = 14 then oa &&& idxMask else if v = 13 then oa >>> 40 else
      if v = 12 then o &&& idxMask else if v = 11 then o >>> 40 else Locals.init [o, n, oa, la, y] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceEqDiff, reduceIte]
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g1 : S.loc 1 = n := by rw [hL]; rfl
  have g3 : S.loc 3 = la := by rw [hL]; rfl
  have g4 : S.loc 4 = y := by rw [hL]; rfl
  have g5 : S.loc 5 = 0 := by rw [hL]; rfl
  have g6 : S.loc 6 = 0 := by rw [hL]; rfl
  have g11 : S.loc 11 = o >>> 40 := by rw [hL]; rfl
  have g12 : S.loc 12 = o &&& idxMask := by rw [hL]; rfl
  have g13 : S.loc 13 = oa >>> 40 := by rw [hL]; rfl
  have g14 : S.loc 14 = oa &&& idxMask := by rw [hL]; rfl
  obtain ⟨S1, e1, hm1, hc1, hi1, hv1⟩ := mrW1_run p _ _ _ _ y la la.toNat F S (by rw [g13]) (by rw [g11])
    g14 g12 g4 g3 (by rw [g5]; simp) (by omega) (by rw [hM]; exact hA) (by rw [hM]; exact hO)
    (by rw [hM]; exact hsA) (by rw [hM]; exact hsO)
  rw [e1]
  simp only []
  have hW := mrW2_run p (tierA 0 (o >>> 40)) (o &&& idxMask) n F S1 (by rw [hv1 11 (by omega), g11])
    (by rw [hv1 12 (by omega), g12]) (by rw [hv1 1 (by omega), g1])
  rw [hm1, hc1, hi1, hM, g5, g6] at hW
  simp only [Nat.add_sub_cancel]
  revert hW
  generalize stepRun p (exec p F) mrW2 S1 = R
  generalize mcLoop _ _ _ _ _ _ _ = res
  intro hW
  rcases res with e | m
  · simp only [LoopRel] at hW; subst hW; simp only []
  · obtain ⟨σ2, h2, hm2⟩ := hW
    subst h2
    simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, Sig.retVal,
      Sig.retOr, hm2]

/-- `mul_row` with `la = 0` returns `0` and changes nothing. -/
theorem mulRow_run_zero (p : Prog) (hp : p.lookup "mul_row" = some mulRow) (σ : St) (o n oa y : Word)
    (F : Nat) (hF : 0 < F) :
    (invoke p (exec p F) "mul_row" [o, n, oa, 0, y]).run σ = .ok ([0], σ) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure mulRow : M FunDecl); callFn (exec p (F + 1)) fd [o, n, oa, 0, y]) =
    callFn (exec p (F + 1)) mulRow [o, n, oa, 0, y] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) mulRow.body).run = L.Compiler.stepRun p (exec p F) mulRow.body from rfl,
    mulRow_body]
  simp only [step_seq_run, step_ite_run, step_set_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, Cmp.eval, BinOp.eval, Locals.init, List.getD_cons_succ, List.getD_cons_zero,
    UInt64.not_lt_zero, decide_false]
  rw [show StateT.run (step p (exec p F) Stmt.skip) _ = .ok (.normal, _) from rfl]
  simp only [mrW1, mrW2, step_while_run, evalCP, evalP, bind, Except.bind, pure, Except.pure,
    St.setLoc_loc, Nat.reduceEqDiff, reduceIte, Locals.init, List.getD_cons_succ, List.getD_cons_zero,
    Cmp.eval, UInt64.not_lt_zero, decide_false, bne_self_eq_false, step_ret_run, evalArgsP, Except.map,
    Sig.retVal, Sig.retOr, List.getD_nil]
  rfl

end L.AsmEsc
