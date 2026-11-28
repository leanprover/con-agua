module

public import ConAgua.Arena.NatDivSubmul
public import ConAguaX86.AsmEsc.MulRowL
import all ConAgua.Arena.NatDivSubmul

@[expose] public section

/-!
# `div_submul` as a function

The L code of `div_submul(r, n, ob, q)` (`L.Arena.divSubmul`, `ConAgua/Arena/NatDivSubmul.lean`) run
at fuel `F`, when both windows lie in their tiers, their indices do not reach `2^40` (so a tagged
address `r + i` keeps `r`'s tier) and `n < F`: the row is `dsRows` (one multiply-subtract step
`dsStep` per limb), then the top limb `dsEnd` (`divSubmul_run`). The machine-level proof of the
hand-written body (`DivSubmulAsm.lean`) is against these functions.

Locals: `0 r, 1 n, 2 ob, 3 q, 4 i, 5 c, 6 x, 7 y, 8 lo, 9 rt, 10 rb`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- A tagged address plus an offset that stays in the tier: the same tier, the index plus the
offset. -/
theorem tag_add (r i : Word) (h : (r &&& idxMask).toNat + i.toNat < 2 ^ 40) :
    (r + i) >>> 40 = r >>> 40 ∧ (r + i) &&& idxMask = (r &&& idxMask) + i := by
  have hi : (r &&& idxMask).toNat = r.toNat % 2 ^ 40 := tag_idx_toNat r
  have ht := tag_tier_toNat r
  have hr := r.toNat_lt
  have hlt : (r >>> 40).toNat < 2 ^ 24 := by rw [ht]; omega
  have hnw : r.toNat + i.toNat < 2 ^ 64 := by omega
  have hri : (r + i).toNat = r.toNat + i.toNat := L.toNat_add_of_lt _ _ hnw
  constructor
  · apply tag_tier_eq; rw [hri]; omega
  · apply UInt64.toNat_inj.mp
    rw [show ((r + i) &&& idxMask).toNat = (r + i).toNat % 2 ^ 40 from tag_idx_toNat _, hri,
      L.toNat_add_of_lt _ _ (by omega), hi]
    omega

/-- The row loop's body. -/
def dsB1 : Stmt :=
  .seq (.set 6 (.ld64t 0 (.bin .shr (.bin .add (.var 0) (.var 4)) (.const 40))
      (.bin .and (.bin .add (.var 0) (.var 4)) (.const 1099511627775))))
    (.seq (.set 7 (.ld64t 0 (.bin .shr (.bin .add (.var 2) (.var 4)) (.const 40))
        (.bin .and (.bin .add (.var 2) (.var 4)) (.const 1099511627775))))
      (.seq (.set 8 (.bin .add (.bin .mul (.var 3) (.var 7)) (.var 5)))
        (.seq (.set 5 (.bin .add (.bin .mulhi (.var 3) (.var 7)) (.cmpw .ult (.var 8) (.var 5))))
          (.seq (.st64t 0 (.var 9) (.bin .add (.var 10) (.var 4)) (.bin .sub (.var 6) (.var 8)))
            (.seq (.set 5 (.bin .add (.var 5) (.cmpw .ult (.var 6) (.var 8))))
              (.set 4 (.bin .add (.var 4) (.const 1))))))))

/-- The row loop. -/
def dsW1 : Stmt := .while (.cmp .ult (.var 4) (.var 1)) dsB1

theorem divSubmul_body : divSubmul.body =
    .seq (.set 9 (.bin .shr (.var 0) (.const 40)))
      (.seq (.set 10 (.bin .and (.var 0) (.const 1099511627775)))
        (.seq dsW1
          (.seq (.set 6 (.ld64t 0 (.bin .shr (.bin .add (.var 0) (.var 1)) (.const 40))
              (.bin .and (.bin .add (.var 0) (.var 1)) (.const 1099511627775))))
            (.seq (.st64t 0 (.var 9) (.bin .add (.var 10) (.var 1)) (.bin .sub (.var 6) (.var 5)))
              (.ret [.cmpw .ult (.var 6) (.var 5)]))))) := by
  rfl

theorem divSubmul_nparams : divSubmul.nparams = 4 := by rfl

/-- One multiply-subtract step at index `i` with carry `c`: the new memory and carry. -/
def dsStep (TR TB : TieredArray) (rb qb q : Word) (m : Mem) (i c : Word) : Mem × Word :=
  let x := (m.arr64 TR)[(rb + i).toNat]!
  let y := (m.arr64 TB)[(qb + i).toNat]!
  let lo := q * y + c
  (m.set64 TR (rb + i) (x - lo), BinOp.mulhi.eval q y + Cmp.evalW .ult lo c + Cmp.evalW .ult x lo)

/-- `r` steps of the row from index `i` with carry `c`. -/
def dsRows (TR TB : TieredArray) (rb qb q : Word) : Nat → Mem → Word → Word → Mem × Word
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c =>
    dsRows TR TB rb qb q r (dsStep TR TB rb qb q m i c).1 (i + 1) (dsStep TR TB rb qb q m i c).2

theorem dsRows_succ (TR TB : TieredArray) (rb qb q : Word) :
    ∀ (r : Nat) (m : Mem) (i c : Word), dsRows TR TB rb qb q (r + 1) m i c =
      dsStep TR TB rb qb q (dsRows TR TB rb qb q r m i c).1 (i + UInt64.ofNat r) (dsRows TR TB rb qb q r m i c).2
  | 0, m, i, c => by simp [dsRows]
  | r + 1, m, i, c => by
    rw [dsRows, dsRows_succ TR TB rb qb q r, dsRows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    rw [e]

/-- The top limb: `x - c` and the borrow out. -/
def dsEnd (TR : TieredArray) (rb n : Word) (m : Mem) (c : Word) : Mem × Word :=
  let x := (m.arr64 TR)[(rb + n).toNat]!
  (m.set64 TR (rb + n) (x - c), Cmp.evalW .ult x c)

theorem dsB1_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (h9 : (σ.loc 0 + σ.loc 4) >>> 40 = σ.loc 9) (h10 : (σ.loc 0 + σ.loc 4) &&& 1099511627775 = σ.loc 10 + σ.loc 4)
    (hb1 : (σ.loc 2 + σ.loc 4) >>> 40 = σ.loc 2 >>> 40)
    (hb2 : (σ.loc 2 + σ.loc 4) &&& 1099511627775 = (σ.loc 2 &&& idxMask) + σ.loc 4)
    (hR : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size)
    (hB : ((σ.loc 2 &&& idxMask) + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40))).size) :
    ∃ σ', stepRun p K dsB1 σ = .ok (.normal, σ') ∧
      σ'.mem = (dsStep (tierA 0 (σ.loc 9)) (tierA 0 (σ.loc 2 >>> 40)) (σ.loc 10) (σ.loc 2 &&& idxMask)
        (σ.loc 3) σ.mem (σ.loc 4) (σ.loc 5)).1 ∧
      σ'.loc 5 = (dsStep (tierA 0 (σ.loc 9)) (tierA 0 (σ.loc 2 >>> 40)) (σ.loc 10) (σ.loc 2 &&& idxMask)
        (σ.loc 3) σ.mem (σ.loc 4) (σ.loc 5)).2 ∧
      σ'.loc 4 = σ.loc 4 + 1 ∧ ∀ v : Nat, (v < 4 ∨ 8 < v) → σ'.loc v = σ.loc v := by
  simp only [dsB1, step_seq_run, step_set_run, step_st64t_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    h9, h10, hb1, hb2, hR, hB, ↓reduceDIte]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [St.setLoc_mem, dsStep, getElem!_pos, hR, hB]
  · simp only [St.setLoc_loc, dsStep, getElem!_pos, hR, hB, BinOp.eval, Nat.reduceEqDiff, reduceIte]
  · simp only [St.setLoc_loc, reduceIte]
  · intro v hv
    have h4 : ¬ v = 4 := by omega
    have h5 : ¬ v = 5 := by omega
    have h6 : ¬ v = 6 := by omega
    have h7 : ¬ v = 7 := by omega
    have h8 : ¬ v = 8 := by omega
    simp only [St.setLoc_loc, h4, h5, h6, h7, h8, reduceIte]

/-- The row loop at fuel `k ≥ r` with `r` steps to go, its windows in their tiers and below `2^40`:
`dsRows`. -/
theorem dsW1_run (p : Prog) (rr ob q n : Word) :
    ∀ (r k : Nat) (σ : St), σ.loc 0 = rr → σ.loc 9 = rr >>> 40 → σ.loc 10 = rr &&& idxMask → σ.loc 2 = ob →
      σ.loc 3 = q → σ.loc 1 = n → (σ.loc 4).toNat + r = n.toNat → r ≤ k →
      (rr &&& idxMask).toNat + n.toNat < 2 ^ 40 → (ob &&& idxMask).toNat + n.toNat ≤ 2 ^ 40 →
      (rr &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (rr >>> 40))).size →
      (ob &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size →
      ∃ σ', stepRun p (exec p k) dsW1 σ = .ok (.normal, σ') ∧
        σ'.mem = (dsRows (tierA 0 (rr >>> 40)) (tierA 0 (ob >>> 40)) (rr &&& idxMask) (ob &&& idxMask) q r
          σ.mem (σ.loc 4) (σ.loc 5)).1 ∧
        σ'.loc 5 = (dsRows (tierA 0 (rr >>> 40)) (tierA 0 (ob >>> 40)) (rr &&& idxMask) (ob &&& idxMask) q r
          σ.mem (σ.loc 4) (σ.loc 5)).2 ∧
        σ'.loc 4 = n ∧ ∀ v : Nat, (v < 4 ∨ 8 < v) → σ'.loc v = σ.loc v := by
  intro r
  induction r with
  | zero =>
    intro k σ h0 h9 h10 h2 h3 h1 hi _ _ _ _ _
    have hil : σ.loc 4 = n := UInt64.toNat_inj.mp (by omega)
    refine ⟨σ, ?_, rfl, rfl, hil, fun _ _ => rfl⟩
    rw [dsW1, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h1, hil, UInt64.lt_irrefl,
      decide_false]
  | succ r ih =>
    intro k σ h0 h9 h10 h2 h3 h1 hi hk hr40 hb40 hR hB
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt : σ.loc 4 < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    obtain ⟨ta, ia⟩ := tag_add rr (σ.loc 4) (by omega)
    obtain ⟨tb, ib⟩ := tag_add ob (σ.loc 4) (by omega)
    have hR' : (σ.loc 10 + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 9))).size := by
      rw [h10, h9, L.toNat_add_of_lt _ _ (by omega)]; omega
    have hB' : ((σ.loc 2 &&& idxMask) + σ.loc 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 2 >>> 40))).size := by
      rw [h2, L.toNat_add_of_lt _ _ (by omega)]; omega
    obtain ⟨σ1, e1, hm1, hc1, hi1, hv1⟩ := dsB1_run p (exec p (k + 1)) σ (by rw [h0, h9, ta])
      (by rw [h0, h10]; exact ia) (by rw [h2, tb]) (by rw [h2]; exact ib) hR' hB'
    rw [h9, h10, h2, h3] at hm1 hc1
    have e0 := hv1 0 (by omega)
    have e9 := hv1 9 (by omega)
    have e10 := hv1 10 (by omega)
    have e2 := hv1 2 (by omega)
    have e3 := hv1 3 (by omega)
    have e1' := hv1 1 (by omega)
    have hi1' : (σ1.loc 4).toNat + r = n.toNat := by
      rw [hi1, L.toNat_add_one_of_word_lt _ _ hlt]; omega
    obtain ⟨σ2, f2, hm2, hc2, hi2, hv2⟩ := ih k σ1 (by rw [e0, h0]) (by rw [e9, h9]) (by rw [e10, h10])
      (by rw [e2, h2]) (by rw [e3, h3]) (by rw [e1', h1]) hi1' (by omega) hr40 hb40
      (by rw [hm1, dsStep, size_set64]; exact hR) (by rw [hm1, dsStep, size_set64]; exact hB)
    refine ⟨σ2, ?_, ?_, ?_, hi2, fun v hv => (hv2 v hv).trans (hv1 v hv)⟩
    · rw [dsW1, step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h1, hlt, decide_true]
      rw [← dsW1, e1]
      exact f2
    · rw [hm2, hm1, hc1, hi1, dsRows]
    · rw [hc2, hm1, hc1, hi1, dsRows]

theorem dsRows_size (TR TB : TieredArray) (rb qb q : Word) (b : TieredArray) :
    ∀ (r : Nat) (m : Mem) (i c : Word), ((dsRows TR TB rb qb q r m i c).1.arr64 b).size = (m.arr64 b).size
  | 0, _, _, _ => rfl
  | r + 1, m, i, c => by
    rw [dsRows, dsRows_size TR TB rb qb q b r]; simp only [dsStep, size_set64]

/-- **`div_submul` at fuel `F`**, its windows in their tiers and below `2^40`, `n < F`: the row
(`dsRows`), then the top limb (`dsEnd`). -/
theorem divSubmul_run (p : Prog) (hp : p.lookup "div_submul" = some divSubmul) (σ : St) (r n ob q : Word)
    (F : Nat) (hF : n.toNat < F) (hr40 : (r &&& idxMask).toNat + n.toNat < 2 ^ 40)
    (hb40 : (ob &&& idxMask).toNat + n.toNat ≤ 2 ^ 40)
    (hR : (r &&& idxMask).toNat + n.toNat < (σ.mem.arr64 (tierA 0 (r >>> 40))).size)
    (hB : (ob &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size) :
    (invoke p (exec p F) "div_submul" [r, n, ob, q]).run σ =
      let R := dsRows (tierA 0 (r >>> 40)) (tierA 0 (ob >>> 40)) (r &&& idxMask) (ob &&& idxMask) q n.toNat
        σ.mem 0 0
      let E := dsEnd (tierA 0 (r >>> 40)) (r &&& idxMask) n R.1 R.2
      .ok ([E.2], { σ with mem := E.1 }) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rw [show (do let fd ← (pure divSubmul : M FunDecl); callFn (exec p (F + 1)) fd [r, n, ob, q]) =
    callFn (exec p (F + 1)) divSubmul [r, n, ob, q] from rfl, L.Compiler.callFn_run]
  rw [show (exec p (F + 1) divSubmul.body).run = L.Compiler.stepRun p (exec p F) divSubmul.body from rfl,
    divSubmul_body]
  simp only [step_seq_run, step_set_run, evalP, bind, Except.bind, pure, Except.pure,
    Except.map, BinOp.eval, Locals.init, List.getD_cons_zero]
  generalize hS : (({ mem := σ.mem, loc := Locals.init [r, n, ob, q] } : St).setLoc 9 _).setLoc 10 _ = S
  have hL : ∀ v, S.loc v = if v = 10 then r &&& idxMask else if v = 9 then r >>> 40 else
      Locals.init [r, n, ob, q] v := by
    intro v; subst hS; simp only [St.setLoc_loc, Locals.init, List.getD_cons_zero,
      Nat.reduceEqDiff, reduceIte]
  have hM : S.mem = σ.mem := by subst hS; rfl
  have g0 : S.loc 0 = r := by rw [hL]; rfl
  have g1 : S.loc 1 = n := by rw [hL]; rfl
  have g2 : S.loc 2 = ob := by rw [hL]; rfl
  have g3 : S.loc 3 = q := by rw [hL]; rfl
  have g4 : S.loc 4 = 0 := by rw [hL]; rfl
  have g5 : S.loc 5 = 0 := by rw [hL]; rfl
  have g9 : S.loc 9 = r >>> 40 := by rw [hL]; rfl
  have g10 : S.loc 10 = r &&& idxMask := by rw [hL]; rfl
  obtain ⟨S1, e1, hm1, hc1, hi1, hv1⟩ := dsW1_run p r ob q n n.toNat F S g0 g9 g10 g2 g3 g1
    (by rw [g4]; simp) (by omega) hr40 hb40 (by rw [hM]; omega) (by rw [hM]; exact hB)
  rw [e1]
  simp only []
  rw [hM, g4, g5] at hm1 hc1
  generalize hRR : dsRows (tierA 0 (r >>> 40)) (tierA 0 (ob >>> 40)) (r &&& idxMask) (ob &&& idxMask) q
    n.toNat σ.mem 0 0 = RR at hm1 hc1
  obtain ⟨M, c⟩ := RR
  simp only at hm1 hc1
  have hsz : (M.arr64 (tierA 0 (r >>> 40))).size = (σ.mem.arr64 (tierA 0 (r >>> 40))).size := by
    have := dsRows_size (tierA 0 (r >>> 40)) (tierA 0 (ob >>> 40)) (r &&& idxMask) (ob &&& idxMask) q
      (tierA 0 (r >>> 40)) n.toNat σ.mem 0 0
    rw [hRR] at this; exact this
  obtain ⟨ta, ia⟩ := tag_add r n hr40
  have h0 := hv1 0 (by omega)
  have h1 := hv1 1 (by omega)
  have h9 := hv1 9 (by omega)
  have h10 := hv1 10 (by omega)
  rw [g0] at h0; rw [g1] at h1; rw [g9] at h9; rw [g10] at h10
  have hin : ((r &&& idxMask) + n).toNat < (M.arr64 (tierA 0 (r >>> 40))).size := by
    rw [hsz, L.toNat_add_of_lt _ _ (by omega)]; exact hR
  have ia' : (r + n) &&& 1099511627775 = (r &&& idxMask) + n := ia
  simp only [step_st64t_run, step_ret_run, evalP, evalArgsP, bind, Except.bind,
    pure, Except.pure, Except.map, BinOp.eval, h0, h1, h9, h10, hm1, ta, ia', hin, ↓reduceDIte, St.setLoc_loc,
    St.setLoc_mem, Nat.reduceEqDiff, reduceIte, hc1]
  simp only [Sig.retVal, Sig.retOr, dsEnd, getElem!_pos, hin]

end L.AsmEsc
