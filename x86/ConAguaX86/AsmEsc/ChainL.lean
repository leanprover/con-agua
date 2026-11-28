module

public import ConAguaX86.AsmEsc.Chain1
import all ConAgua.Arena.NatLeaf

@[expose] public section

/-!
# The add/sub leaves meet the chain templates' specifications

linleaf's `add_n`, `sub_n` (`Chain2Spec`) and `add_1`, `sub_1` (`Chain1Spec`)
(`ConAgua/Arena/NatLeaf.lean`), run at fuel `F > n`, are the pure models `ch2Rows`/`ch1Rows` of
the hand-written bodies (`Chain2.lean`, `Chain1.lean`). One loop lemma (`chLoop_run`, over any
per-limb step) serves all four; each leaf adds its body step and its carry-word identity.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-! ## The carry words -/

theorem evalW_ult (a b : Word) : Cmp.evalW .ult a b = bw (decide (a.toNat < b.toNat)) := by
  simp only [Cmp.evalW, Cmp.eval, bw, UInt64.lt_iff_toNat_lt]

theorem add_toNat (x y : Word) : (x + y).toNat = if x.toNat + y.toNat < 2 ^ 64 then x.toNat + y.toNat
    else x.toNat + y.toNat - 2 ^ 64 := by
  have := x.toNat_lt; have := y.toNat_lt
  rw [UInt64.toNat_add]; split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem sub_toNat (x y : Word) : (x - y).toNat = if y.toNat ≤ x.toNat then x.toNat - y.toNat
    else x.toNat + 2 ^ 64 - y.toNat := by
  have := x.toNat_lt; have := y.toNat_lt
  rw [UInt64.toNat_sub]; split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem bw_toNat (c : Bool) : (bw c).toNat = if c then 1 else 0 := by cases c <;> rfl

/-- The carry words close on `toNat`: case on the conditions, then linear arithmetic. -/
macro "cw_tac" : tactic => `(tactic| (
  apply UInt64.toNat_inj.mp
  simp only [evalW_ult, add_toNat, sub_toNat, bw_toNat, Nat.reducePow, Nat.add_zero, UInt64.toNat_zero,
    Bool.false_eq_true, reduceIte, decide_eq_true_eq]
  repeat' split
  all_goals simp only [bw_toNat, add_toNat, Nat.reducePow, Nat.add_zero, UInt64.toNat_zero, reduceIte,
    Bool.false_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals (repeat' split) <;> omega))

theorem add_word (x y : Word) (c : Bool) :
    (x + bw c) + y = x + y + bw c ∧
      Cmp.evalW .ult (x + bw c) (bw c) + Cmp.evalW .ult (x + bw c + y) y =
        bw (decide (2 ^ 64 ≤ x.toNat + y.toNat + (bw c).toNat)) := by
  refine ⟨by ac_rfl, ?_⟩
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  cases c <;> cw_tac

theorem add1_word (x : Word) (c : Bool) :
    x + bw c = x + 0 + bw c ∧
      Cmp.evalW .ult (x + bw c) (bw c) = bw (decide (2 ^ 64 ≤ x.toNat + (0 : Word).toNat + (bw c).toNat)) := by
  refine ⟨by simp, ?_⟩
  have hx := x.toNat_lt
  cases c <;> cw_tac

theorem sub_word (x y : Word) (c : Bool) :
    x - y - bw c = x - y - bw c ∧
      Cmp.evalW .ult x y + Cmp.evalW .ult (x - y) (bw c) = bw (decide (x.toNat < y.toNat + (bw c).toNat)) := by
  refine ⟨rfl, ?_⟩
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  cases c <;> cw_tac

theorem sub1_word (x : Word) (c : Bool) :
    x - bw c = x - 0 - bw c ∧ Cmp.evalW .ult x (bw c) = bw (decide (x.toNat < (0 : Word).toNat + (bw c).toNat)) := by
  refine ⟨by simp, ?_⟩
  rw [evalW_ult]; simp

/-! ## The loop, over any per-limb step -/

/-- `r` steps of `step` from index `i` with carry `c`. -/
def gRows (step : Mem → Word → Bool → Mem × Bool) : Nat → Mem → Word → Bool → Mem × Bool
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c => gRows step r (step m i c).1 (i + 1) (step m i c).2

/-- The step of `ch2Rows`. -/
def ch2Step (sub : Bool) (TA TB TO : TieredArray) (qa qb ob : Word) (m : Mem) (i : Word) (c : Bool) :
    Mem × Bool :=
  let s := chStep sub (m.arr64 TA)[(qa + i).toNat]! (m.arr64 TB)[(qb + i).toNat]! c
  (m.set64 TO (ob + i) s.1, s.2)

/-- The step of `ch1Rows`. -/
def ch1Step (sub : Bool) (TA TO : TieredArray) (qa ob : Word) (m : Mem) (i : Word) (c : Bool) : Mem × Bool :=
  let s := chStep sub (m.arr64 TA)[(qa + i).toNat]! 0 c
  (m.set64 TO (ob + i) s.1, s.2)

theorem ch2Rows_eq (sub : Bool) (TA TB TO : TieredArray) (qa qb ob : Word) :
    ∀ (r : Nat) (m : Mem) (i : Word) (c : Bool),
      ch2Rows sub TA TB TO qa qb ob r m i c = gRows (ch2Step sub TA TB TO qa qb ob) r m i c
  | 0, _, _, _ => rfl
  | r + 1, m, i, c => by rw [ch2Rows, gRows, ch2Rows_eq sub TA TB TO qa qb ob r]; rfl

theorem ch1Rows_eq (sub : Bool) (TA TO : TieredArray) (qa ob : Word) :
    ∀ (r : Nat) (m : Mem) (i : Word) (c : Bool),
      ch1Rows sub TA TO qa ob r m i c = gRows (ch1Step sub TA TO qa ob) r m i c
  | 0, _, _, _ => rfl
  | r + 1, m, i, c => by rw [ch1Rows, gRows, ch1Rows_eq sub TA TO qa ob r]; rfl

/-- **A counted loop `while i < n { B }` whose body is one step** (index local `I`, bound `N`,
carry `C`): with `r` steps to go and fuel `k ≥ r`, `gRows`. `Fr` holds the locals the body keeps,
`Inv` the memory facts (the windows' sizes) the steps keep. -/
theorem chLoop_run (p : Prog) (B : Stmt) (I N C : Nat) (n : Word) (Fr : St → Prop) (Inv : Mem → Prop)
    (step : Mem → Word → Bool → Mem × Bool)
    (hB : ∀ (k : Nat) (σ : St) (c : Bool), Fr σ → Inv σ.mem → σ.loc N = n → σ.loc I < n → σ.loc C = bw c →
      ∃ σ', stepRun p (exec p k) B σ = .ok (.normal, σ') ∧ σ'.mem = (step σ.mem (σ.loc I) c).1 ∧
        σ'.loc C = bw (step σ.mem (σ.loc I) c).2 ∧ σ'.loc I = σ.loc I + 1 ∧ σ'.loc N = n ∧ Fr σ')
    (hInv : ∀ m i c, Inv m → Inv (step m i c).1) :
    ∀ (r k : Nat) (σ : St) (c : Bool), Fr σ → Inv σ.mem → σ.loc N = n → σ.loc C = bw c →
      (σ.loc I).toNat + r = n.toNat → r ≤ k →
      ∃ σ', stepRun p (exec p k) (.while (.cmp .ult (.var I) (.var N)) B) σ = .ok (.normal, σ') ∧
        σ'.mem = (gRows step r σ.mem (σ.loc I) c).1 ∧ σ'.loc C = bw (gRows step r σ.mem (σ.loc I) c).2 ∧
        Fr σ' := by
  intro r
  induction r with
  | zero =>
    intro k σ c hF _ hN hC hi _
    have hil : σ.loc I = n := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, hC, hF⟩
    rw [step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hN, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ c hF hI hN hC hi hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc I < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    obtain ⟨σ1, e1, hm1, hc1, hi1, hn1, hF1⟩ := hB (k + 1) σ c hF hI hN hlt hC
    have hi1' : (σ1.loc I).toNat + r = n.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, f2, hm2, hc2, hF2⟩ := ih k σ1 _ hF1 (by rw [hm1]; exact hInv _ _ _ hI)
      hn1 hc1 hi1' (by omega)
    refine ⟨σ2, ?_, ?_, ?_, hF2⟩
    · rw [step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hN, hlt, decide_true]
      rw [e1]
      exact f2
    · rw [hm2, hm1, hi1, gRows]
    · rw [hc2, hm1, hi1, gRows]

/-! ## `add_n` -/

/-- `add_n`'s loop body (locals `o, oa, ob, n, c, i, x, y, pt, pb, ta, qa, tb, qb`). -/
def addNB : Stmt :=
  .seq (.set 6 (.ld64t 0 (.var 10) (.bin .add (.var 11) (.var 5))))
    (.seq (.set 7 (.ld64t 0 (.var 12) (.bin .add (.var 13) (.var 5))))
      (.seq (.set 6 (.bin .add (.var 6) (.var 4)))
        (.seq (.set 4 (.cmpw .ult (.var 6) (.var 4)))
          (.seq (.set 6 (.bin .add (.var 6) (.var 7)))
            (.seq (.set 4 (.bin .add (.var 4) (.cmpw .ult (.var 6) (.var 7))))
              (.seq (.st64t 0 (.var 8) (.bin .add (.var 9) (.var 5)) (.var 6))
                (.set 5 (.bin .add (.var 5) (.const 1)))))))))

theorem addN_body : addN.body =
    .seq (.set 8 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 9 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 10 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 11 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.set 12 (.bin .shr (.var 2) (.const 40)))
              (.seq (.set 13 (.bin .and (.var 2) (.const 1099511627775)))
                (.seq (.while (.cmp .ult (.var 5) (.var 3)) addNB) (.ret [.var 4]))))))) := by
  rfl

theorem addNB_run (p : Prog) (K : Stmt → M Sig) (σ : St) (c : Bool) (hc : σ.loc 4 = bw c)
    (hA : (σ.loc 11 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 10))).size)
    (hB : (σ.loc 13 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 12))).size)
    (hO : (σ.loc 9 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 8))).size) :
    ∃ σ', stepRun p K addNB σ = .ok (.normal, σ') ∧
      σ'.mem = (ch2Step false (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 12)) (tierA 0 (σ.loc 8)) (σ.loc 11)
        (σ.loc 13) (σ.loc 9) σ.mem (σ.loc 5) c).1 ∧
      σ'.loc 4 = bw (ch2Step false (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 12)) (tierA 0 (σ.loc 8)) (σ.loc 11)
        (σ.loc 13) (σ.loc 9) σ.mem (σ.loc 5) c).2 ∧
      σ'.loc 5 = σ.loc 5 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 7 < v) → σ'.loc v = σ.loc v := by
  have hw := add_word (σ.mem.arr64 (tierA 0 (σ.loc 10)))[(σ.loc 11 + σ.loc 5).toNat]
    (σ.mem.arr64 (tierA 0 (σ.loc 12)))[(σ.loc 13 + σ.loc 5).toNat] c
  simp only [addNB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hB, hO, ↓reduceDIte, hc]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, ch2Step, chStep, getElem!_pos, hA, hB, Bool.false_eq_true, reduceIte, hw.1]
  · simp only [St.setLoc_loc, ch2Step, chStep, getElem!_pos, hA, hB, Bool.false_eq_true, reduceIte,
      Nat.reduceEqDiff, hw.2]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    have h7 : ¬ v = 7 := by omega
    simp only [St.setLoc_loc, h4, h5, h6, h7, reduceIte]

/-- **`add_n` is the model of the two-window carry chain.** -/
theorem addN_spec (p : Prog) (hp : p.lookup "add_n" = some addN) : Chain2Spec p "add_n" false := by
  intro σ o oa ob n c F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure addN : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, ob, n, bw c]) =
    callFn (exec p (F + 1)) addN [o, oa, ob, n, bw c] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) addN.body).run = L.Compiler.stepRun p (exec p F) addN.body from rfl, addN_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : ((((((({ mem := σ.mem, loc := Locals.init [o, oa, ob, n, bw c] } : St).setLoc 8 _).setLoc 9 _).setLoc
    10 _).setLoc 11 _).setLoc 12 _).setLoc 13 _) = S
  have hL : ∀ v, S.loc v = if v = 13 then ob &&& idxMask else if v = 12 then ob >>> 40 else
      if v = 11 then oa &&& idxMask else if v = 10 then oa >>> 40 else if v = 9 then o &&& idxMask else
      if v = 8 then o >>> 40 else Locals.init [o, oa, ob, n, bw c] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g3 : S.loc 3 = n := by rw [hL]; rfl
  have g4 : S.loc 4 = bw c := by rw [hL]; rfl
  have g5 : S.loc 5 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTB : tierA 0 (ob >>> 40) = TB at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 8 = o >>> 40 ∧ s.loc 9 = o &&& idxMask ∧ s.loc 10 = oa >>> 40 ∧
    s.loc 11 = oa &&& idxMask ∧ s.loc 12 = ob >>> 40 ∧ s.loc 13 = ob &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (ob &&& idxMask).toNat + n.toNat ≤ (m.arr64 TB).size ∧ (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧
    (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TB).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    by rw [hL]; rfl⟩
  have hInv : ∀ m i c, Inv m → Inv (ch2Step false TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) m i c).1 := by
    intro m i c h
    simp only [Inv, ch2Step, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St) (c : Bool), Fr s → Inv s.mem → s.loc 3 = n → s.loc 5 < n → s.loc 4 = bw c →
      ∃ s', stepRun p (exec p k) addNB s = .ok (.normal, s') ∧
        s'.mem = (ch2Step false TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) s.mem (s.loc 5) c).1 ∧
        s'.loc 4 = bw (ch2Step false TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) s.mem (s.loc 5) c).2 ∧
        s'.loc 5 = s.loc 5 + 1 ∧ s'.loc 3 = n ∧ Fr s' := by
    intro k s c ⟨f8, f9, f10, f11, f12, f13⟩ hI hN hlt hC
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hc, hi, hv⟩ := addNB_run p (exec p k) s c hC
      (by rw [f10, f11, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f12, f13, hTB, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f8, f9, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f8, f9, f10, f11, f12, f13, hTA, hTB, hTO] at hm hc
    refine ⟨s', e, hm, hc, hi, by rw [hv 3 (by omega), hN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv 8 (by omega), f8]
    · rw [hv 9 (by omega), f9]
    · rw [hv 10 (by omega), f10]
    · rw [hv 11 (by omega), f11]
    · rw [hv 12 (by omega), f12]
    · rw [hv 13 (by omega), f13]
  obtain ⟨S1, e1, hm1, hc1, hF1⟩ := chLoop_run p addNB 5 3 4 n Fr Inv _ hBody hInv n.toNat F S c hFr
    (by rw [hM]; exact hw) g3 g4 (by rw [g5]; simp) (by omega)
  rw [e1]
  rw [hM, g5] at hm1 hc1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, hc1,
    Sig.retVal, Sig.retOr, ch2Rows_eq]
  rw [hm1]

/-! ## `sub_n` -/

/-- `sub_n`'s loop body (locals `o, oa, ob, n, c, i, x, y, d, pt, pb, ta, qa, tb, qb`). -/
def subNB : Stmt :=
  .seq (.set 6 (.ld64t 0 (.var 11) (.bin .add (.var 12) (.var 5))))
    (.seq (.set 7 (.ld64t 0 (.var 13) (.bin .add (.var 14) (.var 5))))
      (.seq (.set 8 (.bin .sub (.var 6) (.var 7)))
        (.seq (.st64t 0 (.var 9) (.bin .add (.var 10) (.var 5)) (.bin .sub (.var 8) (.var 4)))
          (.seq (.set 4 (.bin .add (.cmpw .ult (.var 6) (.var 7)) (.cmpw .ult (.var 8) (.var 4))))
            (.set 5 (.bin .add (.var 5) (.const 1)))))))

theorem subN_body : subN.body =
    .seq (.set 9 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 10 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 11 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 12 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.set 13 (.bin .shr (.var 2) (.const 40)))
              (.seq (.set 14 (.bin .and (.var 2) (.const 1099511627775)))
                (.seq (.while (.cmp .ult (.var 5) (.var 3)) subNB) (.ret [.var 4]))))))) := by
  rfl

theorem subNB_run (p : Prog) (K : Stmt → M Sig) (σ : St) (c : Bool) (hc : σ.loc 4 = bw c)
    (hA : (σ.loc 12 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 11))).size)
    (hB : (σ.loc 14 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 13))).size)
    (hO : (σ.loc 10 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size) :
    ∃ σ', stepRun p K subNB σ = .ok (.normal, σ') ∧
      σ'.mem = (ch2Step true (tierA 0 (σ.loc 11)) (tierA 0 (σ.loc 13)) (tierA 0 (σ.loc 9)) (σ.loc 12)
        (σ.loc 14) (σ.loc 10) σ.mem (σ.loc 5) c).1 ∧
      σ'.loc 4 = bw (ch2Step true (tierA 0 (σ.loc 11)) (tierA 0 (σ.loc 13)) (tierA 0 (σ.loc 9)) (σ.loc 12)
        (σ.loc 14) (σ.loc 10) σ.mem (σ.loc 5) c).2 ∧
      σ'.loc 5 = σ.loc 5 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 8 < v) → σ'.loc v = σ.loc v := by
  have hw := sub_word (σ.mem.arr64 (tierA 0 (σ.loc 11)))[(σ.loc 12 + σ.loc 5).toNat]
    (σ.mem.arr64 (tierA 0 (σ.loc 13)))[(σ.loc 14 + σ.loc 5).toNat] c
  simp only [subNB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hB, hO, ↓reduceDIte, hc]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, ch2Step, chStep, getElem!_pos, hA, hB, reduceIte, hw.1]
  · simp only [St.setLoc_loc, ch2Step, chStep, getElem!_pos, hA, hB, reduceIte,
      Nat.reduceEqDiff, hw.2]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    have h7 : ¬ v = 7 := by omega
    have h8 : ¬ v = 8 := by omega
    simp only [St.setLoc_loc, h4, h5, h6, h7, h8, reduceIte]

/-- **`sub_n` is the model of the two-window carry chain.** -/
theorem subN_spec (p : Prog) (hp : p.lookup "sub_n" = some subN) : Chain2Spec p "sub_n" true := by
  intro σ o oa ob n c F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure subN : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, ob, n, bw c]) =
    callFn (exec p (F + 1)) subN [o, oa, ob, n, bw c] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) subN.body).run = L.Compiler.stepRun p (exec p F) subN.body from rfl, subN_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : ((((((({ mem := σ.mem, loc := Locals.init [o, oa, ob, n, bw c] } : St).setLoc 9 _).setLoc 10 _).setLoc
    11 _).setLoc 12 _).setLoc 13 _).setLoc 14 _) = S
  have hL : ∀ v, S.loc v = if v = 14 then ob &&& idxMask else if v = 13 then ob >>> 40 else
      if v = 12 then oa &&& idxMask else if v = 11 then oa >>> 40 else if v = 10 then o &&& idxMask else
      if v = 9 then o >>> 40 else Locals.init [o, oa, ob, n, bw c] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g3 : S.loc 3 = n := by rw [hL]; rfl
  have g4 : S.loc 4 = bw c := by rw [hL]; rfl
  have g5 : S.loc 5 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTB : tierA 0 (ob >>> 40) = TB at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 9 = o >>> 40 ∧ s.loc 10 = o &&& idxMask ∧ s.loc 11 = oa >>> 40 ∧
    s.loc 12 = oa &&& idxMask ∧ s.loc 13 = ob >>> 40 ∧ s.loc 14 = ob &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (ob &&& idxMask).toNat + n.toNat ≤ (m.arr64 TB).size ∧ (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧
    (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TB).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    by rw [hL]; rfl⟩
  have hInv : ∀ m i c, Inv m → Inv (ch2Step true TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) m i c).1 := by
    intro m i c h
    simp only [Inv, ch2Step, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St) (c : Bool), Fr s → Inv s.mem → s.loc 3 = n → s.loc 5 < n → s.loc 4 = bw c →
      ∃ s', stepRun p (exec p k) subNB s = .ok (.normal, s') ∧
        s'.mem = (ch2Step true TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) s.mem (s.loc 5) c).1 ∧
        s'.loc 4 = bw (ch2Step true TA TB TO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) s.mem (s.loc 5) c).2 ∧
        s'.loc 5 = s.loc 5 + 1 ∧ s'.loc 3 = n ∧ Fr s' := by
    intro k s c ⟨f9, f10, f11, f12, f13, f14⟩ hI hN hlt hC
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hc, hi, hv⟩ := subNB_run p (exec p k) s c hC
      (by rw [f11, f12, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f13, f14, hTB, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f9, f10, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f9, f10, f11, f12, f13, f14, hTA, hTB, hTO] at hm hc
    refine ⟨s', e, hm, hc, hi, by rw [hv 3 (by omega), hN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv 9 (by omega), f9]
    · rw [hv 10 (by omega), f10]
    · rw [hv 11 (by omega), f11]
    · rw [hv 12 (by omega), f12]
    · rw [hv 13 (by omega), f13]
    · rw [hv 14 (by omega), f14]
  obtain ⟨S1, e1, hm1, hc1, hF1⟩ := chLoop_run p subNB 5 3 4 n Fr Inv _ hBody hInv n.toNat F S c hFr
    (by rw [hM]; exact hw) g3 g4 (by rw [g5]; simp) (by omega)
  rw [e1]
  rw [hM, g5] at hm1 hc1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, hc1,
    Sig.retVal, Sig.retOr, ch2Rows_eq]
  rw [hm1]

/-! ## `add_1` -/

/-- `add_1`'s loop body (locals `o, oa, n, c, i, x, pt, pb, ta, qa`). -/
def add1B : Stmt :=
  .seq (.set 5 (.ld64t 0 (.var 8) (.bin .add (.var 9) (.var 4))))
    (.seq (.set 5 (.bin .add (.var 5) (.var 3)))
      (.seq (.set 3 (.cmpw .ult (.var 5) (.var 3)))
        (.seq (.st64t 0 (.var 6) (.bin .add (.var 7) (.var 4)) (.var 5))
          (.set 4 (.bin .add (.var 4) (.const 1))))))

theorem add1_body : add1.body =
    .seq (.set 6 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 7 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 8 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 9 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.while (.cmp .ult (.var 4) (.var 2)) add1B) (.ret [.var 3]))))) := by
  rfl

theorem add1B_run (p : Prog) (K : Stmt → M Sig) (σ : St) (c : Bool) (hc : σ.loc 3 = bw c)
    (hA : (σ.loc 9 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 8))).size)
    (hO : (σ.loc 7 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 6))).size) :
    ∃ σ', stepRun p K add1B σ = .ok (.normal, σ') ∧
      σ'.mem = (ch1Step false (tierA 0 (σ.loc 8)) (tierA 0 (σ.loc 6)) (σ.loc 9) (σ.loc 7) σ.mem (σ.loc 4) c).1 ∧
      σ'.loc 3 = bw (ch1Step false (tierA 0 (σ.loc 8)) (tierA 0 (σ.loc 6)) (σ.loc 9) (σ.loc 7) σ.mem (σ.loc 4) c).2 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 3 ∨ 5 < v) → σ'.loc v = σ.loc v := by
  have hw := add1_word (σ.mem.arr64 (tierA 0 (σ.loc 8)))[(σ.loc 9 + σ.loc 4).toNat] c
  simp only [add1B, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte, hc]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, ch1Step, chStep, getElem!_pos, hA, Bool.false_eq_true, reduceIte, hw.1]
  · simp only [St.setLoc_loc, ch1Step, chStep, getElem!_pos, hA, Bool.false_eq_true, reduceIte,
      Nat.reduceEqDiff, hw.2]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h3 : ¬ v = 3 := by omega
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    simp only [St.setLoc_loc, h3, h4, h5, reduceIte]

/-- **`add_1` is the model of the one-window carry chain.** -/
theorem add1_spec (p : Prog) (hp : p.lookup "add_1" = some add1) : Chain1Spec p "add_1" false := by
  intro σ o oa n c F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure add1 : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, n, bw c]) =
    callFn (exec p (F + 1)) add1 [o, oa, n, bw c] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) add1.body).run = L.Compiler.stepRun p (exec p F) add1.body from rfl, add1_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : (((({ mem := σ.mem, loc := Locals.init [o, oa, n, bw c] } : St).setLoc 6 _).setLoc 7 _).setLoc
    8 _).setLoc 9 _ = S
  have hL : ∀ v, S.loc v = if v = 9 then oa &&& idxMask else if v = 8 then oa >>> 40 else
      if v = 7 then o &&& idxMask else if v = 6 then o >>> 40 else Locals.init [o, oa, n, bw c] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g2 : S.loc 2 = n := by rw [hL]; rfl
  have g3 : S.loc 3 = bw c := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 6 = o >>> 40 ∧ s.loc 7 = o &&& idxMask ∧ s.loc 8 = oa >>> 40 ∧
    s.loc 9 = oa &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧ (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl⟩
  have hInv : ∀ m i c, Inv m → Inv (ch1Step false TA TO (oa &&& idxMask) (o &&& idxMask) m i c).1 := by
    intro m i c h
    simp only [Inv, ch1Step, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St) (c : Bool), Fr s → Inv s.mem → s.loc 2 = n → s.loc 4 < n → s.loc 3 = bw c →
      ∃ s', stepRun p (exec p k) add1B s = .ok (.normal, s') ∧
        s'.mem = (ch1Step false TA TO (oa &&& idxMask) (o &&& idxMask) s.mem (s.loc 4) c).1 ∧
        s'.loc 3 = bw (ch1Step false TA TO (oa &&& idxMask) (o &&& idxMask) s.mem (s.loc 4) c).2 ∧
        s'.loc 4 = s.loc 4 + 1 ∧ s'.loc 2 = n ∧ Fr s' := by
    intro k s c ⟨f6, f7, f8, f9⟩ hI hN hlt hC
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hc, hi, hv⟩ := add1B_run p (exec p k) s c hC
      (by rw [f8, f9, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f6, f7, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f6, f7, f8, f9, hTA, hTO] at hm hc
    refine ⟨s', e, hm, hc, hi, by rw [hv 2 (by omega), hN], ?_, ?_, ?_, ?_⟩
    · rw [hv 6 (by omega), f6]
    · rw [hv 7 (by omega), f7]
    · rw [hv 8 (by omega), f8]
    · rw [hv 9 (by omega), f9]
  obtain ⟨S1, e1, hm1, hc1, hF1⟩ := chLoop_run p add1B 4 2 3 n Fr Inv _ hBody hInv n.toNat F S c hFr
    (by rw [hM]; exact hw) g2 g3 (by rw [g4]; simp) (by omega)
  rw [e1]
  rw [hM, g4] at hm1 hc1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, hc1,
    Sig.retVal, Sig.retOr, ch1Rows_eq]
  rw [hm1]

/-! ## `sub_1` -/

/-- `sub_1`'s loop body (locals `o, oa, n, c, i, x, pt, pb, ta, qa`). -/
def sub1B : Stmt :=
  .seq (.set 5 (.ld64t 0 (.var 8) (.bin .add (.var 9) (.var 4))))
    (.seq (.st64t 0 (.var 6) (.bin .add (.var 7) (.var 4)) (.bin .sub (.var 5) (.var 3)))
      (.seq (.set 3 (.cmpw .ult (.var 5) (.var 3)))
        (.set 4 (.bin .add (.var 4) (.const 1)))))

theorem sub1_body : sub1.body =
    .seq (.set 6 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 7 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 8 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 9 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.while (.cmp .ult (.var 4) (.var 2)) sub1B) (.ret [.var 3]))))) := by
  rfl

theorem sub1B_run (p : Prog) (K : Stmt → M Sig) (σ : St) (c : Bool) (hc : σ.loc 3 = bw c)
    (hA : (σ.loc 9 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 8))).size)
    (hO : (σ.loc 7 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 6))).size) :
    ∃ σ', stepRun p K sub1B σ = .ok (.normal, σ') ∧
      σ'.mem = (ch1Step true (tierA 0 (σ.loc 8)) (tierA 0 (σ.loc 6)) (σ.loc 9) (σ.loc 7) σ.mem (σ.loc 4) c).1 ∧
      σ'.loc 3 = bw (ch1Step true (tierA 0 (σ.loc 8)) (tierA 0 (σ.loc 6)) (σ.loc 9) (σ.loc 7) σ.mem (σ.loc 4) c).2 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 3 ∨ 5 < v) → σ'.loc v = σ.loc v := by
  have hw := sub1_word (σ.mem.arr64 (tierA 0 (σ.loc 8)))[(σ.loc 9 + σ.loc 4).toNat] c
  simp only [sub1B, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte, hc]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, ch1Step, chStep, getElem!_pos, hA, reduceIte, hw.1]
  · simp only [St.setLoc_loc, ch1Step, chStep, getElem!_pos, hA, reduceIte,
      Nat.reduceEqDiff, hw.2]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h3 : ¬ v = 3 := by omega
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    simp only [St.setLoc_loc, h3, h4, h5, reduceIte]

/-- **`sub_1` is the model of the one-window carry chain.** -/
theorem sub1_spec (p : Prog) (hp : p.lookup "sub_1" = some sub1) : Chain1Spec p "sub_1" true := by
  intro σ o oa n c F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure sub1 : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, n, bw c]) =
    callFn (exec p (F + 1)) sub1 [o, oa, n, bw c] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) sub1.body).run = L.Compiler.stepRun p (exec p F) sub1.body from rfl, sub1_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : (((({ mem := σ.mem, loc := Locals.init [o, oa, n, bw c] } : St).setLoc 6 _).setLoc 7 _).setLoc
    8 _).setLoc 9 _ = S
  have hL : ∀ v, S.loc v = if v = 9 then oa &&& idxMask else if v = 8 then oa >>> 40 else
      if v = 7 then o &&& idxMask else if v = 6 then o >>> 40 else Locals.init [o, oa, n, bw c] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g2 : S.loc 2 = n := by rw [hL]; rfl
  have g3 : S.loc 3 = bw c := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 6 = o >>> 40 ∧ s.loc 7 = o &&& idxMask ∧ s.loc 8 = oa >>> 40 ∧
    s.loc 9 = oa &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧ (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl⟩
  have hInv : ∀ m i c, Inv m → Inv (ch1Step true TA TO (oa &&& idxMask) (o &&& idxMask) m i c).1 := by
    intro m i c h
    simp only [Inv, ch1Step, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St) (c : Bool), Fr s → Inv s.mem → s.loc 2 = n → s.loc 4 < n → s.loc 3 = bw c →
      ∃ s', stepRun p (exec p k) sub1B s = .ok (.normal, s') ∧
        s'.mem = (ch1Step true TA TO (oa &&& idxMask) (o &&& idxMask) s.mem (s.loc 4) c).1 ∧
        s'.loc 3 = bw (ch1Step true TA TO (oa &&& idxMask) (o &&& idxMask) s.mem (s.loc 4) c).2 ∧
        s'.loc 4 = s.loc 4 + 1 ∧ s'.loc 2 = n ∧ Fr s' := by
    intro k s c ⟨f6, f7, f8, f9⟩ hI hN hlt hC
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hc, hi, hv⟩ := sub1B_run p (exec p k) s c hC
      (by rw [f8, f9, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f6, f7, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f6, f7, f8, f9, hTA, hTO] at hm hc
    refine ⟨s', e, hm, hc, hi, by rw [hv 2 (by omega), hN], ?_, ?_, ?_, ?_⟩
    · rw [hv 6 (by omega), f6]
    · rw [hv 7 (by omega), f7]
    · rw [hv 8 (by omega), f8]
    · rw [hv 9 (by omega), f9]
  obtain ⟨S1, e1, hm1, hc1, hF1⟩ := chLoop_run p sub1B 4 2 3 n Fr Inv _ hBody hInv n.toNat F S c hFr
    (by rw [hM]; exact hw) g2 g3 (by rw [g4]; simp) (by omega)
  rw [e1]
  rw [hM, g4] at hm1 hc1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, hc1,
    Sig.retVal, Sig.retOr, ch1Rows_eq]
  rw [hm1]

end L.AsmEsc
