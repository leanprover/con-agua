module

public import ConAguaX86.AsmEsc.BitL
import all ConAgua.Arena.NatLeaf

@[expose] public section

/-!
# The shift leaves and `zero_n` as functions

linleaf's `shl_n`, `shr_n` and `zero_n` (`ConAgua/Arena/NatLeaf.lean`), run at fuel `F > n`, when
their windows lie in their tiers (`shr_n` reads `n + 1` limbs), are pure models: `wRows` of
`shlStep` (the carry word) and of `shrStep` (the previous limb), and `g0Rows` of `zeroStep`
(`shlN_spec`, `shrN_spec`, `zeroN_spec`). The machine-level proofs (`ShiftAsmSim.lean`) are
against these.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- `r` steps of `step` from index `i` with the word `c` carried along. -/
def wRows (step : Mem → Word → Word → Mem × Word) : Nat → Mem → Word → Word → Mem × Word
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c => wRows step r (step m i c).1 (i + 1) (step m i c).2

theorem wRows_succ (step : Mem → Word → Word → Mem × Word) :
    ∀ (r : Nat) (m : Mem) (i c : Word), wRows step (r + 1) m i c =
      step (wRows step r m i c).1 (i + UInt64.ofNat r) (wRows step r m i c).2
  | 0, m, i, c => by simp [wRows]
  | r + 1, m, i, c => by
    rw [wRows, wRows_succ step r, wRows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    rw [e]

/-- **A counted loop `while i < n { B }` whose body is one step with a carried word** (index `I`,
bound `N`, word `C`), with `r` steps to go and fuel `k ≥ r`: `wRows`. -/
theorem wLoop_run (p : Prog) (B : Stmt) (I N C : Nat) (n : Word) (Fr : St → Prop) (Inv : Mem → Prop)
    (step : Mem → Word → Word → Mem × Word)
    (hB : ∀ (k : Nat) (σ : St), Fr σ → Inv σ.mem → σ.loc N = n → σ.loc I < n →
      ∃ σ', stepRun p (exec p k) B σ = .ok (.normal, σ') ∧ σ'.mem = (step σ.mem (σ.loc I) (σ.loc C)).1 ∧
        σ'.loc C = (step σ.mem (σ.loc I) (σ.loc C)).2 ∧ σ'.loc I = σ.loc I + 1 ∧ σ'.loc N = n ∧ Fr σ')
    (hInv : ∀ m i c, Inv m → Inv (step m i c).1) :
    ∀ (r k : Nat) (σ : St), Fr σ → Inv σ.mem → σ.loc N = n → (σ.loc I).toNat + r = n.toNat → r ≤ k →
      ∃ σ', stepRun p (exec p k) (.while (.cmp .ult (.var I) (.var N)) B) σ = .ok (.normal, σ') ∧
        σ'.mem = (wRows step r σ.mem (σ.loc I) (σ.loc C)).1 ∧
        σ'.loc C = (wRows step r σ.mem (σ.loc I) (σ.loc C)).2 ∧ Fr σ' := by
  intro r
  induction r with
  | zero =>
    intro k σ hF _ hN hi _
    have hil : σ.loc I = n := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, rfl, hF⟩
    rw [step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hN, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ hF hI hN hi hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc I < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    obtain ⟨σ1, e1, hm1, hc1, hi1, hn1, hF1⟩ := hB (k + 1) σ hF hI hN hlt
    have hi1' : (σ1.loc I).toNat + r = n.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, f2, hm2, hc2, hF2⟩ := ih k σ1 hF1 (by rw [hm1]; exact hInv _ _ _ hI) hn1 hi1' (by omega)
    refine ⟨σ2, ?_, ?_, ?_, hF2⟩
    · rw [step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hN, hlt, decide_true]
      rw [e1]
      exact f2
    · rw [hm2, hm1, hc1, hi1, wRows]
    · rw [hc2, hm1, hc1, hi1, wRows]

/-! ## `shl_n` -/

/-- One step of `shl_n`: `P[ob + i] := (A[qa + i] << s) | c`, the carry `(A[qa + i] >> 1) >> rs`. -/
def shlStep (TA TO : TieredArray) (qa ob s rs : Word) (m : Mem) (i c : Word) : Mem × Word :=
  let x := (m.arr64 TA)[(qa + i).toNat]!
  (m.set64 TO (ob + i) ((x <<< s) ||| c), (x >>> 1) >>> rs)

/-- `shl_n`'s loop body (locals `o, oa, n, s, c, i, x, rs, pt, pb, ta, qa`). -/
def shlB : Stmt :=
  .seq (.set 6 (.ld64t 0 (.var 10) (.bin .add (.var 11) (.var 5))))
    (.seq (.st64t 0 (.var 8) (.bin .add (.var 9) (.var 5)) (.bin .or (.bin .shl (.var 6) (.var 3)) (.var 4)))
      (.seq (.set 4 (.bin .shr (.bin .shr (.var 6) (.const 1)) (.var 7)))
        (.set 5 (.bin .add (.var 5) (.const 1)))))

theorem shlN_body : shlN.body =
    .seq (.set 8 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 9 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 10 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 11 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.set 7 (.bin .sub (.const 63) (.var 3)))
              (.seq (.while (.cmp .ult (.var 5) (.var 2)) shlB) (.ret [.var 4])))))) := by
  rfl

theorem shlN_nparams : shlN.nparams = 5 := by rfl

theorem shlB_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hA : (σ.loc 11 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 10))).size)
    (hO : (σ.loc 9 + σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 8))).size) :
    ∃ σ', stepRun p K shlB σ = .ok (.normal, σ') ∧
      σ'.mem = (shlStep (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 8)) (σ.loc 11) (σ.loc 9) (σ.loc 3) (σ.loc 7)
        σ.mem (σ.loc 5) (σ.loc 4)).1 ∧
      σ'.loc 4 = (shlStep (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 8)) (σ.loc 11) (σ.loc 9) (σ.loc 3) (σ.loc 7)
        σ.mem (σ.loc 5) (σ.loc 4)).2 ∧
      σ'.loc 5 = σ.loc 5 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 6 < v) → σ'.loc v = σ.loc v := by
  simp only [shlB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, shlStep, getElem!_pos, hA]
  · simp only [St.setLoc_loc, shlStep, getElem!_pos, hA, reduceIte, Nat.reduceEqDiff]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    simp only [St.setLoc_loc, h4, h5, h6, reduceIte]

/-- The run of `shl_n`: the model `shlStep` over the window, the carry out. -/
def ShlSpec (p : Prog) : Prop :=
  ∀ (σ : St) (o oa n s c : Word) (F : Nat), n.toNat < F →
    (n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size ∧
      (o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧
      (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64 ∧
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64)) →
    (invoke p (exec p F) "shl_n" [o, oa, n, s, c]).run σ =
      let R := wRows (shlStep (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) s
        (63 - s)) n.toNat σ.mem 0 c
      .ok ([R.2], { σ with mem := R.1 })

/-- **`shl_n` is its model.** -/
theorem shlN_spec (p : Prog) (hp : p.lookup "shl_n" = some shlN) : ShlSpec p := by
  intro σ o oa n sh c F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure shlN : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, n, sh, c]) =
    callFn (exec p (F + 1)) shlN [o, oa, n, sh, c] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) shlN.body).run = L.Compiler.stepRun p (exec p F) shlN.body from rfl, shlN_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : ((((({ mem := σ.mem, loc := Locals.init [o, oa, n, sh, c] } : St).setLoc 8 _).setLoc 9 _).setLoc
    10 _).setLoc 11 _).setLoc 7 _ = S
  have hL : ∀ v, S.loc v = if v = 7 then 63 - sh else if v = 11 then oa &&& idxMask else
      if v = 10 then oa >>> 40 else if v = 9 then o &&& idxMask else
      if v = 8 then o >>> 40 else Locals.init [o, oa, n, sh, c] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
    rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g2 : S.loc 2 = n := by rw [hL]; rfl
  have g4 : S.loc 4 = c := by rw [hL]; rfl
  have g5 : S.loc 5 = 0 := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hw ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 3 = sh ∧ s.loc 7 = 63 - sh ∧ s.loc 8 = o >>> 40 ∧
    s.loc 9 = o &&& idxMask ∧ s.loc 10 = oa >>> 40 ∧ s.loc 11 = oa &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (m.arr64 TA).size ∧
    (o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧ (m.arr64 TA).size < 2 ^ 64 ∧ (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    by rw [hL]; rfl⟩
  have hInv : ∀ m i c, Inv m →
      Inv (shlStep TA TO (oa &&& idxMask) (o &&& idxMask) sh (63 - sh) m i c).1 := by
    intro m i c h
    simp only [Inv, shlStep, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St), Fr s → Inv s.mem → s.loc 2 = n → s.loc 5 < n →
      ∃ s', stepRun p (exec p k) shlB s = .ok (.normal, s') ∧
        s'.mem = (shlStep TA TO (oa &&& idxMask) (o &&& idxMask) sh (63 - sh) s.mem (s.loc 5) (s.loc 4)).1 ∧
        s'.loc 4 = (shlStep TA TO (oa &&& idxMask) (o &&& idxMask) sh (63 - sh) s.mem (s.loc 5) (s.loc 4)).2 ∧
        s'.loc 5 = s.loc 5 + 1 ∧ s'.loc 2 = n ∧ Fr s' := by
    intro k s ⟨f3, f7, f8, f9, f10, f11⟩ hI hN hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2, i3, i4⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hc, hi, hv⟩ := shlB_run p (exec p k) s
      (by rw [f10, f11, hTA, L.toNat_add_of_lt _ _ (by omega)]; omega)
      (by rw [f8, f9, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f3, f7, f8, f9, f10, f11, hTA, hTO] at hm hc
    refine ⟨s', e, hm, hc, hi, by rw [hv 2 (by omega), hN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv 3 (by omega), f3]
    · rw [hv 7 (by omega), f7]
    · rw [hv 8 (by omega), f8]
    · rw [hv 9 (by omega), f9]
    · rw [hv 10 (by omega), f10]
    · rw [hv 11 (by omega), f11]
  obtain ⟨S1, e1, hm1, hc1, _⟩ := wLoop_run p shlB 5 2 4 n Fr Inv _ hBody hInv n.toNat F S hFr
    (by rw [hM]; exact hw) g2 (by rw [g5]; simp) (by omega)
  rw [e1]
  rw [hM, g5, g4] at hm1 hc1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, hc1,
    Sig.retVal, Sig.retOr]
  rw [hm1]

/-! ## `shr_n` -/

/-- One step of `shr_n` with the previous limb `x`: `y := A[qa + i + 1]`,
`P[ob + i] := (x >> s) | ((y << 1) << rs)`, and `y` carried on. -/
def shrStep (TA TO : TieredArray) (qa ob s rs : Word) (m : Mem) (i x : Word) : Mem × Word :=
  let y := (m.arr64 TA)[(qa + (i + 1)).toNat]!
  (m.set64 TO (ob + i) ((x >>> s) ||| ((y <<< 1) <<< rs)), y)

/-- `shr_n`'s loop body (locals `o, oa, n, s, i, x, y, rs, pt, pb, ta, qa`). -/
def shrB : Stmt :=
  .seq (.set 6 (.ld64t 0 (.var 10) (.bin .add (.var 11) (.bin .add (.var 4) (.const 1)))))
    (.seq (.st64t 0 (.var 8) (.bin .add (.var 9) (.var 4))
        (.bin .or (.bin .shr (.var 5) (.var 3)) (.bin .shl (.bin .shl (.var 6) (.const 1)) (.var 7))))
      (.seq (.set 5 (.var 6))
        (.set 4 (.bin .add (.var 4) (.const 1)))))

theorem shrN_body : shrN.body =
    .seq (.set 8 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 9 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.set 10 (.bin .shr (.var 1) (.const 40)))
          (.seq (.set 11 (.bin .and (.var 1) (.const 1099511627775)))
            (.seq (.set 7 (.bin .sub (.const 63) (.var 3)))
              (.seq (.set 5 (.ld64t 0 (.var 10) (.var 11)))
                (.seq (.while (.cmp .ult (.var 4) (.var 2)) shrB) (.ret [.const 0]))))))) := by
  rfl

theorem shrN_nparams : shrN.nparams = 4 := by rfl

theorem shrB_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hA : (σ.loc 11 + (σ.loc 4 + 1)).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 10))).size)
    (hO : (σ.loc 9 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 8))).size) :
    ∃ σ', stepRun p K shrB σ = .ok (.normal, σ') ∧
      σ'.mem = (shrStep (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 8)) (σ.loc 11) (σ.loc 9) (σ.loc 3) (σ.loc 7)
        σ.mem (σ.loc 4) (σ.loc 5)).1 ∧
      σ'.loc 5 = (shrStep (tierA 0 (σ.loc 10)) (tierA 0 (σ.loc 8)) (σ.loc 11) (σ.loc 9) (σ.loc 3) (σ.loc 7)
        σ.mem (σ.loc 4) (σ.loc 5)).2 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 6 < v) → σ'.loc v = σ.loc v := by
  simp only [shrB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    hA, hO, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, shrStep, getElem!_pos, hA]
  · simp only [St.setLoc_loc, shrStep, getElem!_pos, hA, reduceIte, Nat.reduceEqDiff]
  · simp only [St.setLoc_loc, reduceIte, Nat.reduceEqDiff]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    simp only [St.setLoc_loc, h4, h5, h6, reduceIte]

/-- The run of `shr_n`: the model `shrStep` from the first limb, result `0`. -/
def ShrSpec (p : Prog) : Prop :=
  ∀ (σ : St) (o oa n s : Word) (F : Nat), n.toNat < F →
    (oa &&& idxMask).toNat + n.toNat + 1 ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size →
    (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64 →
    (n = 0 ∨ ((o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64)) →
    (invoke p (exec p F) "shr_n" [o, oa, n, s]).run σ =
      .ok ([0], { σ with mem := (wRows (shrStep (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask)
        (o &&& idxMask) s (63 - s)) n.toNat σ.mem 0
        (σ.mem.arr64 (tierA 0 (oa >>> 40)))[(oa &&& idxMask).toNat]!).1 })

/-- **`shr_n` is its model.** -/
theorem shrN_spec (p : Prog) (hp : p.lookup "shr_n" = some shrN) : ShrSpec p := by
  intro σ o oa n sh F hF hA0 hAs hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure shrN : M FunDecl); callFn (exec p (F + 1)) fd [o, oa, n, sh]) =
    callFn (exec p (F + 1)) shrN [o, oa, n, sh] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) shrN.body).run = L.Compiler.stepRun p (exec p F) shrN.body from rfl, shrN_body]
  have hq0 : (oa &&& idxMask).toNat < (σ.mem.arr64 (tierA 0 (oa >>> 40))).size := by omega
  have hq0' : (oa &&& 1099511627775).toNat < (σ.mem.arr64 (tierA 0 (oa >>> 40))).size := hq0
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero, St.setLoc_loc, St.setLoc_mem, Nat.reduceEqDiff,
    reduceIte, List.getD_cons_succ, hq0', ↓reduceDIte]
  generalize hS : (((((({ mem := σ.mem, loc := Locals.init [o, oa, n, sh] } : St).setLoc 8 _).setLoc 9 _).setLoc
    10 _).setLoc 11 _).setLoc 7 _).setLoc 5 _ = S
  have hL : ∀ v, S.loc v = if v = 5 then (σ.mem.arr64 (tierA 0 (oa >>> 40)))[(oa &&& idxMask).toNat]! else
      if v = 7 then 63 - sh else if v = 11 then oa &&& idxMask else
      if v = 10 then oa >>> 40 else if v = 9 then o &&& idxMask else
      if v = 8 then o >>> 40 else Locals.init [o, oa, n, sh] v := by
    intro v; subst hS; simp only [St.setLoc_loc]
    split
    · simp only [getElem!_pos, hq0]
    · rfl
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g2 : S.loc 2 = n := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  have g5 : S.loc 5 = (σ.mem.arr64 (tierA 0 (oa >>> 40)))[(oa &&& idxMask).toNat]! := by rw [hL]; rfl
  generalize hTA : tierA 0 (oa >>> 40) = TA at hA0 hAs hw g5 ⊢
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 3 = sh ∧ s.loc 7 = 63 - sh ∧ s.loc 8 = o >>> 40 ∧
    s.loc 9 = o &&& idxMask ∧ s.loc 10 = oa >>> 40 ∧ s.loc 11 = oa &&& idxMask
  let Inv : Mem → Prop := fun m => ((oa &&& idxMask).toNat + n.toNat + 1 ≤ (m.arr64 TA).size ∧
    (m.arr64 TA).size < 2 ^ 64) ∧ (n = 0 ∨ ((o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧
      (m.arr64 TO).size < 2 ^ 64))
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    by rw [hL]; rfl⟩
  have hInv : ∀ m i c, Inv m →
      Inv (shrStep TA TO (oa &&& idxMask) (o &&& idxMask) sh (63 - sh) m i c).1 := by
    intro m i c h
    simp only [Inv, shrStep, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St), Fr s → Inv s.mem → s.loc 2 = n → s.loc 4 < n →
      ∃ s', stepRun p (exec p k) shrB s = .ok (.normal, s') ∧
        s'.mem = (shrStep TA TO (oa &&& idxMask) (o &&& idxMask) sh (63 - sh) s.mem (s.loc 4) (s.loc 5)).1 ∧
        s'.loc 5 = (shrStep TA TO (oa &&& idxMask) (o &&& idxMask) sh (63 - sh) s.mem (s.loc 4) (s.loc 5)).2 ∧
        s'.loc 4 = s.loc 4 + 1 ∧ s'.loc 2 = n ∧ Fr s' := by
    intro k s ⟨f3, f7, f8, f9, f10, f11⟩ ⟨⟨i1, i2⟩, hI⟩ hN hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i3, i4⟩ := hI.resolve_left hn0
    have hn := n.toNat_lt
    have h41 : (s.loc 4 + 1).toNat = (s.loc 4).toNat + 1 := L.toNat_add_one_of_word_lt _ _ hlt
    obtain ⟨s', e, hm, hc, hi, hv⟩ := shrB_run p (exec p k) s
      (by rw [f10, f11, hTA, L.toNat_add_of_lt _ _ (by omega), h41]; omega)
      (by rw [f8, f9, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f3, f7, f8, f9, f10, f11, hTA, hTO] at hm hc
    refine ⟨s', e, hm, hc, hi, by rw [hv 2 (by omega), hN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv 3 (by omega), f3]
    · rw [hv 7 (by omega), f7]
    · rw [hv 8 (by omega), f8]
    · rw [hv 9 (by omega), f9]
    · rw [hv 10 (by omega), f10]
    · rw [hv 11 (by omega), f11]
  obtain ⟨S1, e1, hm1, _, _⟩ := wLoop_run p shrB 4 2 5 n Fr Inv _ hBody hInv n.toNat F S hFr
    (by rw [hM]; exact ⟨⟨hA0, hAs⟩, hw⟩) g2 (by rw [g4]; simp) (by omega)
  rw [e1]
  rw [hM, g4, g5] at hm1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map,
    Sig.retVal, Sig.retOr]
  rw [hm1]

/-! ## `zero_n` -/

/-- One step of `zero_n`: `P[ob + i] := 0`. -/
def zeroStep (TO : TieredArray) (ob : Word) (m : Mem) (i : Word) : Mem := m.set64 TO (ob + i) 0

/-- `zero_n`'s loop body (locals `o, n, i, pt, pb`). -/
def zeroB : Stmt :=
  .seq (.st64t 0 (.var 3) (.bin .add (.var 4) (.var 2)) (.const 0))
    (.set 2 (.bin .add (.var 2) (.const 1)))

theorem zeroN_body : zeroN.body =
    .seq (.set 3 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 4 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq (.while (.cmp .ult (.var 2) (.var 1)) zeroB) (.ret [.const 0]))) := by
  rfl

theorem zeroN_nparams : zeroN.nparams = 2 := by rfl

theorem zeroB_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hO : (σ.loc 4 + σ.loc 2).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 3))).size) :
    ∃ σ', stepRun p K zeroB σ = .ok (.normal, σ') ∧
      σ'.mem = zeroStep (tierA 0 (σ.loc 3)) (σ.loc 4) σ.mem (σ.loc 2) ∧
      σ'.loc 2 = σ.loc 2 + 1 ∧ ∀ v : Nat, v ≠ 2 → σ'.loc v = σ.loc v := by
  simp only [zeroB, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, BinOp.eval, reduceIte, hO]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    simp only [St.setLoc_loc, hv, reduceIte]

/-- The run of `zero_n`: zeros over the window, result `0`. -/
def ZeroSpec (p : Prog) : Prop :=
  ∀ (σ : St) (o n : Word) (F : Nat), n.toNat < F →
    (n = 0 ∨ ((o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64)) →
    (invoke p (exec p F) "zero_n" [o, n]).run σ =
      .ok ([0], { σ with mem := g0Rows (zeroStep (tierA 0 (o >>> 40)) (o &&& idxMask)) n.toNat σ.mem 0 })

/-- **`zero_n` is its model.** -/
theorem zeroN_spec (p : Prog) (hp : p.lookup "zero_n" = some zeroN) : ZeroSpec p := by
  intro σ o n F hF hw
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure zeroN : M FunDecl); callFn (exec p (F + 1)) fd [o, n]) =
    callFn (exec p (F + 1)) zeroN [o, n] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) zeroN.body).run = L.Compiler.stepRun p (exec p F) zeroN.body from rfl, zeroN_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : (({ mem := σ.mem, loc := Locals.init [o, n] } : St).setLoc 3 _).setLoc 4 _ = S
  have hL : ∀ v, S.loc v = if v = 4 then o &&& idxMask else if v = 3 then o >>> 40 else
      Locals.init [o, n] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero, Nat.reduceEqDiff, reduceIte]
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g1 : S.loc 1 = n := by rw [hL]; rfl
  have g2 : S.loc 2 = 0 := by rw [hL]; rfl
  generalize hTO : tierA 0 (o >>> 40) = TO at hw ⊢
  let Fr : St → Prop := fun s => s.loc 3 = o >>> 40 ∧ s.loc 4 = o &&& idxMask
  let Inv : Mem → Prop := fun m => n = 0 ∨ ((o &&& idxMask).toNat + n.toNat ≤ (m.arr64 TO).size ∧
    (m.arr64 TO).size < 2 ^ 64)
  have hFr : Fr S := ⟨by rw [hL]; rfl, by rw [hL]; rfl⟩
  have hInv : ∀ m i, Inv m → Inv (zeroStep TO (o &&& idxMask) m i) := by
    intro m i h
    simp only [Inv, zeroStep, size_set64] at h ⊢
    exact h
  have hBody : ∀ (k : Nat) (s : St), Fr s → Inv s.mem → s.loc 1 = n → s.loc 2 < n →
      ∃ s', stepRun p (exec p k) zeroB s = .ok (.normal, s') ∧
        s'.mem = zeroStep TO (o &&& idxMask) s.mem (s.loc 2) ∧
        s'.loc 2 = s.loc 2 + 1 ∧ s'.loc 1 = n ∧ Fr s' := by
    intro k s ⟨f3, f4⟩ hI hN hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hlt'
    obtain ⟨i1, i2⟩ := hI.resolve_left hn0
    obtain ⟨s', e, hm, hi, hv⟩ := zeroB_run p (exec p k) s
      (by rw [f3, f4, hTO, L.toNat_add_of_lt _ _ (by omega)]; omega)
    rw [f3, f4, hTO] at hm
    refine ⟨s', e, hm, hi, by rw [hv 1 (by omega), hN], ?_, ?_⟩
    · rw [hv 3 (by omega), f3]
    · rw [hv 4 (by omega), f4]
  obtain ⟨S1, e1, hm1, _⟩ := g0Loop_run p zeroB 2 1 n Fr Inv _ hBody hInv n.toNat F S hFr
    (by rw [hM]; exact hw) g1 (by rw [g2]; simp) (by omega)
  rw [e1]
  rw [hM, g2] at hm1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map,
    Sig.retVal, Sig.retOr]
  rw [hm1]

end L.AsmEsc
