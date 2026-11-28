module

public import ConAguaX86.AsmEsc.MulRowL
import all ConAgua.Arena.NatLeaf

@[expose] public section

/-!
# The bitwise leaves and `copy_n` as functions

linleaf's `bitNG op` (`and_n`, `or_n`, `xor_n`) and `copy_n` (`ConAgua/Arena/NatLeaf.lean`), run
at fuel `F > n`, when their windows lie in their tiers (or `n = 0`), are the pure models
`g0Rows (bitStep op …)` and `g0Rows (copyStep …)` (`bitN_run`, `copyN_run`). One loop lemma
without a carry (`g0Loop_run`) serves both. The machine-level proofs of the templates
(`BitAsm.lean`) are against these (`BitSpec`, `CopySpec`).
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- `r` steps of `step` from index `i`. -/
def g0Rows (step : Mem → Word → Mem) : Nat → Mem → Word → Mem
  | 0, m, _ => m
  | r + 1, m, i => g0Rows step r (step m i) (i + 1)

/-- The step of the bitwise leaf: `P[ob + i] := A[qa + i] op B[qb + i]`. -/
def bitStep (op : BinOp) (TA TB TO : TieredArray) (qa qb ob : Word) (m : Mem) (i : Word) : Mem :=
  m.set64 TO (ob + i) (op.eval (m.arr64 TA)[(qa + i).toNat]! (m.arr64 TB)[(qb + i).toNat]!)

/-- The step of the copy: `P[ob + i] := A[qa + i]`. -/
def copyStep (TA TO : TieredArray) (qa ob : Word) (m : Mem) (i : Word) : Mem :=
  m.set64 TO (ob + i) (m.arr64 TA)[(qa + i).toNat]!

theorem g0Rows_succ (step : Mem → Word → Mem) :
    ∀ (r : Nat) (m : Mem) (i : Word), g0Rows step (r + 1) m i =
      step (g0Rows step r m i) (i + UInt64.ofNat r)
  | 0, m, i => by simp [g0Rows]
  | r + 1, m, i => by
    rw [g0Rows, g0Rows_succ step r, g0Rows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    rw [e]

/-- **A counted loop `while i < n { B }` whose body is one step** (index `I`, bound `N`), with
`r` steps to go and fuel `k ≥ r`: `g0Rows`. -/
theorem g0Loop_run (p : Prog) (B : Stmt) (I N : Nat) (n : Word) (Fr : St → Prop) (Inv : Mem → Prop)
    (step : Mem → Word → Mem)
    (hB : ∀ (k : Nat) (σ : St), Fr σ → Inv σ.mem → σ.loc N = n → σ.loc I < n →
      ∃ σ', stepRun p (exec p k) B σ = .ok (.normal, σ') ∧ σ'.mem = step σ.mem (σ.loc I) ∧
        σ'.loc I = σ.loc I + 1 ∧ σ'.loc N = n ∧ Fr σ')
    (hInv : ∀ m i, Inv m → Inv (step m i)) :
    ∀ (r k : Nat) (σ : St), Fr σ → Inv σ.mem → σ.loc N = n → (σ.loc I).toNat + r = n.toNat → r ≤ k →
      ∃ σ', stepRun p (exec p k) (.while (.cmp .ult (.var I) (.var N)) B) σ = .ok (.normal, σ') ∧
        σ'.mem = g0Rows step r σ.mem (σ.loc I) ∧ Fr σ' := by
  intro r
  induction r with
  | zero =>
    intro k σ hF _ hN hi _
    have hil : σ.loc I = n := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, hF⟩
    rw [step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hN, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ hF hI hN hi hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc I < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    obtain ⟨σ1, e1, hm1, hi1, hn1, hF1⟩ := hB (k + 1) σ hF hI hN hlt
    have hi1' : (σ1.loc I).toNat + r = n.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, f2, hm2, hF2⟩ := ih k σ1 hF1 (by rw [hm1]; exact hInv _ _ hI) hn1 hi1' (by omega)
    refine ⟨σ2, ?_, ?_, hF2⟩
    · rw [step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hN, hlt, decide_true]
      rw [e1]
      exact f2
    · rw [hm2, hm1, hi1, g0Rows]

/-- The run of a bitwise leaf `f` with operator `op`: the model `bitStep`, result `0`. -/
def BitSpec (p : Prog) (f : FnName) (op : BinOp) : Prop :=
  ∀ (σ : St) (o oa ob n : Word) (F : Nat), n.toNat < F →
    (n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size ∧
      (ob &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size ∧
      (o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧
      (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64 ∧ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size < 2 ^ 64 ∧
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64)) →
    (invoke p (exec p F) f [o, oa, ob, n]).run σ =
      .ok ([0], { σ with mem := g0Rows (bitStep op (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40))
        (tierA 0 (o >>> 40)) (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask)) n.toNat σ.mem 0 })

/-- The run of a copy leaf `f`: the model `copyStep`, result `0`. -/
def CopySpec (p : Prog) (f : FnName) : Prop :=
  ∀ (σ : St) (o oa n : Word) (F : Nat), n.toNat < F →
    (n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size ∧
      (o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧
      (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64 ∧
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64)) →
    (invoke p (exec p F) f [o, oa, n]).run σ =
      .ok ([0], { σ with mem := g0Rows (copyStep (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40))
        (oa &&& idxMask) (o &&& idxMask)) n.toNat σ.mem 0 })

/-! ## `bitNG op` -/

/-- The bitwise loop's body (locals `o, oa, ob, n, i, x, pt, pb, ta, qa, tb, qb`). -/
def bitB (op : BinOp) : Stmt :=
  .seq (.set 5 (.bin op (.ld64t 0 (.var 8) (.bin .add (.var 9) (.var 4)))
      (.ld64t 0 (.var 10) (.bin .add (.var 11) (.var 4)))))
    (.seq (.st64t 0 (.var 6) (.bin .add (.var 7) (.var 4)) (.var 5))
      (.set 4 (.bin .add (.var 4) (.const 1))))

theorem bitNG_body (op : BinOp) : (bitNG op).body =
    .seq (.set 6 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 7 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 8 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 9 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.set 10 (.bin .shr (.var 2) (.const 40)))
              (.seq (.set 11 (.bin .and (.var 2) (.const 1099511627775)))
                (.seq (.while (.cmp .ult (.var 4) (.var 3)) (bitB op)) (.ret [.const 0]))))))) := by
  rfl

theorem bitNG_nparams (op : BinOp) : (bitNG op).nparams = 4 := by rfl

theorem bitB_run (op : BinOp) (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hA : (σ.loc 9 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 8))).size)
    (hB : (σ.loc 11 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 10))).size)
    (hO : (σ.loc 7 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 6))).size) :
    ∃ σ', stepRun p K (bitB op) σ = .ok (.normal, σ') ∧
      σ'.mem = bitStep op (tierA 0 (σ.loc 8)) (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 6)) (σ.loc 9)
        (σ.loc 11) (σ.loc 7) σ.mem (σ.loc 4) ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 5 < v) → σ'.loc v = σ.loc v := by
  simp only [bitB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hB, hO, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, bitStep, getElem!_pos, hA, hB]
    rfl
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    simp only [St.setLoc_loc, h4, h5, reduceIte]

/-- **A bitwise leaf is its model.** -/
theorem bitN_spec (op : BinOp) (p : Prog) (f : FnName) (hp : p.lookup f = some (bitNG op)) :
    BitSpec p f op := by
  intro σ o oa ob n F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure (bitNG op) : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, ob, n]) =
    callFn (exec p (F + 1)) (bitNG op) [o, oa, ob, n] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) (bitNG op).body).run = L.Compiler.stepRun p (exec p F) (bitNG op).body from rfl,
    bitNG_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : ((((((({ mem := σ.mem, loc := Locals.init [o, oa, ob, n] } : St).setLoc 6 _).setLoc 7 _).setLoc
    8 _).setLoc 9 _).setLoc 10 _).setLoc 11 _) = S
  have hL : ∀ v, S.loc v = if v = 11 then ob &&& idxMask else if v = 10 then ob >>> 40 else
      if v = 9 then oa &&& idxMask else if v = 8 then oa >>> 40 else if v = 7 then o &&& idxMask else
      if v = 6 then o >>> 40 else Locals.init [o, oa, ob, n] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g3 : S.loc 3 = n := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTB : tierA 0 (ob >>> 40) = TB at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 6 = o >>> 40 ∧ s.loc 7 = o &&& idxMask ∧ s.loc 8 = oa >>> 40 ∧
    s.loc 9 = oa &&& idxMask ∧ s.loc 10 = ob >>> 40 ∧ s.loc 11 = ob &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (ob &&& idxMask).toNat + n.toNat ≤ (m.arr64 TB).size ∧ (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧
    (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TB).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    by rw [hL]; rfl⟩
  have hInv : ∀ m i, Inv m → Inv (bitStep op TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) m i) := by
    intro m i h
    simp only [Inv, bitStep, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St), Fr s → Inv s.mem → s.loc 3 = n → s.loc 4 < n →
      ∃ s', stepRun p (exec p k) (bitB op) s = .ok (.normal, s') ∧
        s'.mem = bitStep op TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) s.mem (s.loc 4) ∧
        s'.loc 4 = s.loc 4 + 1 ∧ s'.loc 3 = n ∧ Fr s' := by
    intro k s ⟨f6, f7, f8, f9, f10, f11⟩ hI hN hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hi, hv⟩ := bitB_run op p (exec p k) s
      (by rw [f8, f9, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f10, f11, hTB, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f6, f7, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f6, f7, f8, f9, f10, f11, hTA, hTB, hTO] at hm
    refine ⟨s', e, hm, hi, by rw [hv 3 (by omega), hN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv 6 (by omega), f6]
    · rw [hv 7 (by omega), f7]
    · rw [hv 8 (by omega), f8]
    · rw [hv 9 (by omega), f9]
    · rw [hv 10 (by omega), f10]
    · rw [hv 11 (by omega), f11]
  obtain ⟨S1, e1, hm1, _⟩ := g0Loop_run p (bitB op) 4 3 n Fr Inv _ hBody hInv n.toNat F S hFr
    (by rw [hM]; exact hw) g3 (by rw [g4]; simp) (by omega)
  rw [e1]
  rw [hM, g4] at hm1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map,
    Sig.retVal, Sig.retOr]
  rw [hm1]

/-! ## `copy_n` -/

/-- The copy loop's body (locals `o, oa, n, i, x, pt, pb, ta, qa`). -/
def copyB : Stmt :=
  .seq (.set 4 (.ld64t 0 (.var 7) (.bin .add (.var 8) (.var 3))))
    (.seq (.st64t 0 (.var 5) (.bin .add (.var 6) (.var 3)) (.var 4))
      (.set 3 (.bin .add (.var 3) (.const 1))))

theorem copyN_body : copyN.body =
    .seq (.set 5 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 6 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 7 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 8 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.while (.cmp .ult (.var 3) (.var 2)) copyB) (.ret [.const 0]))))) := by
  rfl

theorem copyN_nparams : copyN.nparams = 3 := by rfl

theorem copyB_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hA : (σ.loc 8 + σ.loc 3).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 7))).size)
    (hO : (σ.loc 6 + σ.loc 3).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 5))).size) :
    ∃ σ', stepRun p K copyB σ = .ok (.normal, σ') ∧
      σ'.mem = copyStep (tierA 0 (σ.loc 7)) (tierA 0 (σ.loc 5)) (σ.loc 8) (σ.loc 6) σ.mem (σ.loc 3) ∧
      σ'.loc 3 = σ.loc 3 + 1 ∧ ∀ v : Nat, (v < 3 ∨ 4 < v) → σ'.loc v = σ.loc v := by
  simp only [copyB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, copyStep, getElem!_pos, hA]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h3 : ¬ v = 3 := by omega
    have h4 : ¬ v = 4 := by omega
    simp only [St.setLoc_loc, h3, h4, reduceIte]

/-- **`copy_n` is its model.** -/
theorem copyN_spec (p : Prog) (hp : p.lookup "copy_n" = some copyN) : CopySpec p "copy_n" := by
  intro σ o oa n F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure copyN : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, n]) =
    callFn (exec p (F + 1)) copyN [o, oa, n] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) copyN.body).run = L.Compiler.stepRun p (exec p F) copyN.body from rfl, copyN_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : (((({ mem := σ.mem, loc := Locals.init [o, oa, n] } : St).setLoc 5 _).setLoc 6 _).setLoc
    7 _).setLoc 8 _ = S
  have hL : ∀ v, S.loc v = if v = 8 then oa &&& idxMask else if v = 7 then oa >>> 40 else
      if v = 6 then o &&& idxMask else if v = 5 then o >>> 40 else Locals.init [o, oa, n] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g2 : S.loc 2 = n := by rw [hL]; rfl
  have g3 : S.loc 3 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 5 = o >>> 40 ∧ s.loc 6 = o &&& idxMask ∧ s.loc 7 = oa >>> 40 ∧
    s.loc 8 = oa &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧ (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl⟩
  have hInv : ∀ m i, Inv m → Inv (copyStep TA TO (oa &&& idxMask) (o &&& idxMask) m i) := by
    intro m i h
    simp only [Inv, copyStep, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St), Fr s → Inv s.mem → s.loc 2 = n → s.loc 3 < n →
      ∃ s', stepRun p (exec p k) copyB s = .ok (.normal, s') ∧
        s'.mem = copyStep TA TO (oa &&& idxMask) (o &&& idxMask) s.mem (s.loc 3) ∧
        s'.loc 3 = s.loc 3 + 1 ∧ s'.loc 2 = n ∧ Fr s' := by
    intro k s ⟨f5, f6, f7, f8⟩ hI hN hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hi, hv⟩ := copyB_run p (exec p k) s
      (by rw [f7, f8, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f5, f6, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f5, f6, f7, f8, hTA, hTO] at hm
    refine ⟨s', e, hm, hi, by rw [hv 2 (by omega), hN], ?_, ?_, ?_, ?_⟩
    · rw [hv 5 (by omega), f5]
    · rw [hv 6 (by omega), f6]
    · rw [hv 7 (by omega), f7]
    · rw [hv 8 (by omega), f8]
  obtain ⟨S1, e1, hm1, _⟩ := g0Loop_run p copyB 3 2 n Fr Inv _ hBody hInv n.toNat F S hFr
    (by rw [hM]; exact hw) g2 (by rw [g3]; simp) (by omega)
  rw [e1]
  rw [hM, g3] at hm1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map,
    Sig.retVal, Sig.retOr]
  rw [hm1]

end L.AsmEsc
