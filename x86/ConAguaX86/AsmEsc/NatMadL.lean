module

public import ConAgua.Front.NatDec
public import ConAguaX86.AsmEsc.DivSubmulL
import all ConAgua.Front.NatDec

@[expose] public section

/-!
# `nat_mad` as a function

The L code of `nat_mad(o, n, w, y)` (`L.Front.natMad`, `ConAgua/Front/NatDec.lean`: `R := R · w + y`
in place on the `n` limbs at `o`, returning the carry) run at fuel `F > n`, when its window lies in
its tier below `2^40` (or `n = 0`): the row `nmRows`, one multiply-add step `nmStep` per limb
(`natMad_run`). The machine-level proof of the hand-written body (`NatMadAsm.lean`) is against it.

Locals: `0 o, 1 n, 2 w, 3 y, 4 i, 5 x, 6 lo, 7 pt, 8 pb`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler L.Front

/-- The row loop's body. -/
def nmB1 : Stmt :=
  .seq (.set 5 (.ld64t 0 (.bin .shr (.bin .add (.var 0) (.var 4)) (.const 40))
      (.bin .and (.bin .add (.var 0) (.var 4)) (.const 1099511627775))))
    (.seq (.set 6 (.bin .add (.bin .mul (.var 5) (.var 2)) (.var 3)))
      (.seq (.set 3 (.bin .add (.bin .mulhi (.var 5) (.var 2)) (.cmpw .ult (.var 6) (.var 3))))
        (.seq (.st64t 0 (.var 7) (.bin .add (.var 8) (.var 4)) (.var 6))
          (.set 4 (.bin .add (.var 4) (.const 1))))))

/-- The row loop. -/
def nmW1 : Stmt := .while (.cmp .ult (.var 4) (.var 1)) nmB1

theorem natMad_body : natMad.body =
    .seq (.set 7 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 8 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq nmW1 (.ret [.var 3]))) := by
  rfl

theorem natMad_nparams : natMad.nparams = 4 := by rfl

/-- One multiply-add step at index `i` with carry `c`: the new memory and carry. -/
def nmStep (TR : TieredArray) (rb w : Word) (m : Mem) (i c : Word) : Mem × Word :=
  let x := (m.arr64 TR)[(rb + i).toNat]!
  let lo := x * w + c
  (m.set64 TR (rb + i) lo, BinOp.mulhi.eval x w + Cmp.evalW .ult lo c)

/-- `r` steps of the row from index `i` with carry `c`. -/
def nmRows (TR : TieredArray) (rb w : Word) : Nat → Mem → Word → Word → Mem × Word
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c => nmRows TR rb w r (nmStep TR rb w m i c).1 (i + 1) (nmStep TR rb w m i c).2

theorem nmRows_succ (TR : TieredArray) (rb w : Word) :
    ∀ (r : Nat) (m : Mem) (i c : Word), nmRows TR rb w (r + 1) m i c =
      nmStep TR rb w (nmRows TR rb w r m i c).1 (i + UInt64.ofNat r) (nmRows TR rb w r m i c).2
  | 0, m, i, c => by simp [nmRows]
  | r + 1, m, i, c => by
    rw [nmRows, nmRows_succ TR rb w r, nmRows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    rw [e]

theorem nmB1_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (h7 : (σ.loc 0 + σ.loc 4) >>> 40 = σ.loc 7) (h8 : (σ.loc 0 + σ.loc 4) &&& 1099511627775 = σ.loc 8 + σ.loc 4)
    (hR : (σ.loc 8 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 7))).size) :
    ∃ σ', stepRun p K nmB1 σ = .ok (.normal, σ') ∧
      σ'.mem = (nmStep (tierA 0 (σ.loc 7)) (σ.loc 8) (σ.loc 2) σ.mem (σ.loc 4) (σ.loc 3)).1 ∧
      σ'.loc 3 = (nmStep (tierA 0 (σ.loc 7)) (σ.loc 8) (σ.loc 2) σ.mem (σ.loc 4) (σ.loc 3)).2 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 3 ∨ 6 < v) → σ'.loc v = σ.loc v := by
  simp only [nmB1, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    h7, h8, hR, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, nmStep, getElem!_pos, hR]
  · simp only [St.setLoc_loc, nmStep, getElem!_pos, hR, BinOp.eval, Nat.reduceEqDiff, reduceIte]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h3 : ¬ v = 3 := by omega
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    simp only [St.setLoc_loc, h3, h4, h5, h6, reduceIte]

/-- The row loop at fuel `k ≥ r` with `r` steps to go, its window in its tier below `2^40` (or
`n = 0`): `nmRows`. -/
theorem nmW1_run (p : Prog) (rr w n : Word) :
    ∀ (r k : Nat) (σ : St), σ.loc 0 = rr → σ.loc 7 = rr >>> 40 → σ.loc 8 = rr &&& idxMask →
      σ.loc 2 = w → σ.loc 1 = n → (σ.loc 4).toNat + r = n.toNat → r ≤ k →
      (n = 0 ∨ ((rr &&& idxMask).toNat + n.toNat < 2 ^ 40 ∧
        (rr &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (rr >>> 40))).size)) →
      ∃ σ', stepRun p (exec p k) nmW1 σ = .ok (.normal, σ') ∧
        σ'.mem = (nmRows (tierA 0 (rr >>> 40)) (rr &&& idxMask) w r σ.mem (σ.loc 4) (σ.loc 3)).1 ∧
        σ'.loc 3 = (nmRows (tierA 0 (rr >>> 40)) (rr &&& idxMask) w r σ.mem (σ.loc 4) (σ.loc 3)).2 ∧
        ∀ v : Nat, (v < 3 ∨ 6 < v) → σ'.loc v = σ.loc v := by
  intro r
  induction r with
  | zero =>
    intro k σ h0 h7 h8 h2 h1 hi _ _
    have hil : σ.loc 4 = n := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, rfl, fun _ _ => rfl⟩
    rw [nmW1, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h1, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ h0 h7 h8 h2 h1 hi hk hw
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc 4 < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hn0 : n ≠ 0 := by intro h; subst h; simp at hi
    obtain ⟨hr40, hR⟩ := hw.resolve_left hn0
    obtain ⟨ta, ia⟩ := tag_add rr (σ.loc 4) (by omega)
    have hR' : (σ.loc 8 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 7))).size := by
      rw [h8, h7, L.toNat_add_of_lt _ _ (by omega)]; omega
    obtain ⟨σ1, e1, hm1, hc1, hi1, hv1⟩ := nmB1_run p (exec p (k + 1)) σ (by rw [h0, h7, ta])
      (by rw [h0, h8]; exact ia) hR'
    rw [h7, h8, h2] at hm1 hc1
    have e0 := hv1 0 (by omega)
    have e7 := hv1 7 (by omega)
    have e8 := hv1 8 (by omega)
    have e2 := hv1 2 (by omega)
    have e1' := hv1 1 (by omega)
    have hi1' : (σ1.loc 4).toNat + r = n.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, f2, hm2, hc2, hv2⟩ := ih k σ1 (by rw [e0, h0]) (by rw [e7, h7]) (by rw [e8, h8])
      (by rw [e2, h2]) (by rw [e1', h1]) hi1' (by omega)
      (Or.inr ⟨hr40, by rw [hm1, nmStep, size_set64]; exact hR⟩)
    refine ⟨σ2, ?_, ?_, ?_, fun v hv => (hv2 v hv).trans (hv1 v hv)⟩
    · rw [nmW1, step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h1, hlt, decide_true]
      rw [← nmW1, e1]
      exact f2
    · rw [hm2, hm1, hc1, hi1, nmRows]
    · rw [hc2, hm1, hc1, hi1, nmRows]

/-- **`nat_mad` at fuel `F > n`**, its window in its tier below `2^40` (or `n = 0`): the row
`nmRows`. -/
theorem natMad_run (p : Prog) (hp : p.lookup "nat_mad" = some natMad) (σ : St) (o n w y : Word)
    (F : Nat) (hF : n.toNat < F)
    (hw : n = 0 ∨ ((o &&& idxMask).toNat + n.toNat < 2 ^ 40 ∧
      (o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size)) :
    (invoke p (exec p F) "nat_mad" [o, n, w, y]).run σ =
      let R := nmRows (tierA 0 (o >>> 40)) (o &&& idxMask) w n.toNat σ.mem 0 y
      .ok ([R.2], { σ with mem := R.1 }) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure natMad : M FunDecl); callFn (exec p (F + 1)) fd [o, n, w, y]) =
    callFn (exec p (F + 1)) natMad [o, n, w, y] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) natMad.body).run = L.Compiler.stepRun p (exec p F) natMad.body from rfl,
    natMad_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : (({ mem := σ.mem, loc := Locals.init [o, n, w, y] } : St).setLoc 7 _).setLoc 8 _ = S
  have hL : ∀ v, S.loc v = if v = 8 then o &&& idxMask else if v = 7 then o >>> 40 else
      Locals.init [o, n, w, y] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero,
      Nat.reduceEqDiff, reduceIte]
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g0 : S.loc 0 = o := by rw [hL]; rfl
  have g1 : S.loc 1 = n := by rw [hL]; rfl
  have g2 : S.loc 2 = w := by rw [hL]; rfl
  have g3 : S.loc 3 = y := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  have g7 : S.loc 7 = o >>> 40 := by rw [hL]; rfl
  have g8 : S.loc 8 = o &&& idxMask := by rw [hL]; rfl
  obtain ⟨S1, e1, hm1, hc1, _⟩ := nmW1_run p o w n n.toNat F S g0 g7 g8 g2 g1
    (by rw [g4]; simp) (by omega) (by rw [hM]; exact hw)
  rw [e1]
  rw [hM, g4, g3] at hm1 hc1
  simp only [step_ret_run, evalArgsP, evalP, bind, Except.bind, pure, Except.pure, Except.map, hc1,
    Sig.retVal, Sig.retOr]
  rw [hm1]

end L.AsmEsc
