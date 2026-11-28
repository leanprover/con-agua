module

public import ConAgua.Arena.Store
public import ConAguaX86.Compiler.RunEq
public import ConAguaX86.Compiler.SimCall
import all ConAgua.Arena.Store

@[expose] public section

/-!
# `lit_hash` as a function

The L code of `lit_hash(o, l)` (`L.Arena.litHash`, `ConAgua/Arena/Store.lean`: the FNV-1a hash of the
`l` limbs at `o`; eight limbs per round in `hashLoop8`, the rest in `hashTail`) run at fuel `F > l`,
when its window lies in its tier below `2^40` (or `l = 0`): `lhRows`, one FNV step per limb over the
tier's word array (`litHash_run`). The machine-level proof of the hand-written body
(`LitHashAsm.lean`) is against it.

Locals: `0 o, 1 l, 2 i, 3 h, 4 t, 5 x, 6 q`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- `r` limbs of the FNV hash from index `x` of the word array `A`, starting from `h`. -/
def lhRows (A : Array Word) (x h : Word) : Nat → Word
  | 0 => h
  | r + 1 => lhRows A (x + 1) ((h ^^^ A[x.toNat]!) * fnvPrime) r

theorem lhRows_add (A : Array Word) (b : Nat) :
    ∀ (a : Nat) (x h : Word), lhRows A x h (a + b) = lhRows A (x + UInt64.ofNat a) (lhRows A x h a) b
  | 0, x, h => by
    have e : x + UInt64.ofNat 0 = x := by simp
    rw [e, Nat.zero_add, lhRows]
  | a + 1, x, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega, lhRows, lhRows_add A b a, lhRows,
      UInt64.add_assoc, UInt64.ofNat_add, UInt64.ofNat_one, UInt64.add_comm 1]

/-- The body of `hashLoop8`. -/
def hB8 : Stmt := match hashLoop8 with | .while _ b => b | _ => .skip

theorem hashLoop8_eq : hashLoop8 = .while (.cmp .ule (.const 8) (.var 1)) hB8 := by rfl

theorem hB8_run (p : Prog) (K : Stmt → M Sig) (σ : St)
    (hb : (σ.loc 5).toNat + 8 ≤ (σ.mem.arr64 (tierA 0 (σ.loc 4))).size)
    (hw : (σ.loc 5).toNat + 8 < 2 ^ 64) (h6 : σ.loc 6 = fnvPrime) :
    ∃ σ', stepRun p K hB8 σ = .ok (.normal, σ') ∧ σ'.mem = σ.mem ∧
      σ'.loc 3 = lhRows (σ.mem.arr64 (tierA 0 (σ.loc 4))) (σ.loc 5) (σ.loc 3) 8 ∧
      σ'.loc 5 = σ.loc 5 + 8 ∧ σ'.loc 1 = σ.loc 1 - 8 ∧
      ∀ v : Nat, (v ≠ 1 ∧ v ≠ 3 ∧ v ≠ 5) → σ'.loc v = σ.loc v := by
  have e : ∀ k : Word, k.toNat ≤ 8 → (σ.loc 5 + k).toNat = (σ.loc 5).toNat + k.toNat := fun k hk => by
    rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have b1 : (σ.loc 5 + 1).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 1 (by decide)]; simp; omega
  have b2 : (σ.loc 5 + 2).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 2 (by decide)]; simp; omega
  have b3 : (σ.loc 5 + 3).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 3 (by decide)]; simp; omega
  have b4 : (σ.loc 5 + 4).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 4 (by decide)]; simp; omega
  have b5 : (σ.loc 5 + 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 5 (by decide)]; simp; omega
  have b6 : (σ.loc 5 + 6).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 6 (by decide)]; simp; omega
  have b7 : (σ.loc 5 + 7).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by rw [e 7 (by decide)]; simp; omega
  have b0 : (σ.loc 5).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by omega
  simp only [hB8, hashLoop8, step_seq_run, step_set_run, evalP, bind, Except.bind, pure,
    Except.pure, Except.map, St.setLoc_loc, St.setLoc_mem, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    b0, b1, b2, b3, b4, b5, b6, b7, ↓reduceDIte]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, h6, lhRows, getElem!_pos, b0, b1, b2, b3, b4, b5, b6, b7,
      UInt64.add_assoc, UInt64.reduceAdd]
  · intro v hv
    simp only [St.setLoc_loc, hv.1, hv.2.1, hv.2.2, reduceIte]

/-- `hashLoop8` at fuel `k ≥ q` with `q` rounds to go. -/
theorem hl8_run (p : Prog) (t : Word) (m : Mem) :
    ∀ (q k : Nat) (σ : St), σ.mem = m → σ.loc 4 = t → σ.loc 6 = fnvPrime → q ≤ k →
      (σ.loc 1).toNat / 8 = q →
      ((σ.loc 1).toNat = 0 ∨ ((σ.loc 5).toNat + (σ.loc 1).toNat ≤ (m.arr64 (tierA 0 t)).size ∧
        (σ.loc 5).toNat + (σ.loc 1).toNat < 2 ^ 64)) →
      ∃ σ', stepRun p (exec p k) hashLoop8 σ = .ok (.normal, σ') ∧ σ'.mem = m ∧
        σ'.loc 3 = lhRows (m.arr64 (tierA 0 t)) (σ.loc 5) (σ.loc 3) (8 * q) ∧
        σ'.loc 5 = σ.loc 5 + UInt64.ofNat (8 * q) ∧ (σ'.loc 1).toNat = (σ.loc 1).toNat % 8 ∧
        σ'.loc 1 + σ'.loc 5 = σ.loc 1 + σ.loc 5 ∧
        ∀ v : Nat, (v ≠ 1 ∧ v ≠ 3 ∧ v ≠ 5) → σ'.loc v = σ.loc v := by
  intro q
  induction q with
  | zero =>
    intro k σ hm h4 h6 _ hq _
    refine ⟨σ, ?_, hm, rfl, by simp, by omega, rfl, fun _ _ => rfl⟩
    have hl : ¬ (8 : Word) ≤ σ.loc 1 := by
      rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
    rw [hashLoop8_eq, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hl, decide_false]
  | succ q ih =>
    intro k σ hm h4 h6 hk hq hw
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hw' := hw.resolve_left (by omega)
    have h8 : (8 : Word) ≤ σ.loc 1 := by
      rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
    obtain ⟨σ1, e1, hm1, hc1, hx1, hl1, hv1⟩ := hB8_run p (exec p (k + 1)) σ
      (by rw [hm, h4]; omega) (by omega) h6
    have hl1' : (σ1.loc 1).toNat = (σ.loc 1).toNat - 8 := by
      rw [hl1, UInt64.toNat_sub_of_le _ _ h8]; rfl
    have hx1' : (σ1.loc 5).toNat = (σ.loc 5).toNat + 8 := by
      rw [hx1, UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    obtain ⟨σ2, f2, hm2, hc2, hx2, hl2, hs2, hv2⟩ := ih k σ1 (by rw [hm1, hm])
      (by rw [hv1 4 (by omega), h4]) (by rw [hv1 6 (by omega), h6]) (by omega) (by omega)
      (Or.inr ⟨by rw [hl1', hx1']; omega, by omega⟩)
    refine ⟨σ2, ?_, hm2, ?_, ?_, ?_, ?_, fun v hv => (hv2 v hv).trans (hv1 v hv)⟩
    · rw [hashLoop8_eq, step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, h8, decide_true]
      rw [e1]
      rw [← hashLoop8_eq]
      exact f2
    · rw [hc2, hc1, hx1, hm, h4, show 8 * (q + 1) = 8 + 8 * q by omega, lhRows_add]; rfl
    · rw [hx2, hx1, UInt64.add_assoc, show 8 * (q + 1) = 8 + 8 * q by omega, UInt64.ofNat_add]; rfl
    · rw [hl2, hl1']; omega
    · rw [hs2, hl1, hx1]; grind

/-- The body of `hashTail`. -/
def hBT : Stmt := match hashTail with | .while _ b => b | _ => .skip

theorem hashTail_eq : hashTail = .while (.cmp .ult (.var 2) (.var 1)) hBT := by rfl

/-- `hashTail` at fuel `k ≥ r` with `r` limbs to go. -/
theorem hT_run (p : Prog) (t : Word) (m : Mem) :
    ∀ (r k : Nat) (σ : St), σ.mem = m → σ.loc 4 = t → σ.loc 6 = fnvPrime → r ≤ k →
      (σ.loc 2).toNat + r = (σ.loc 1).toNat →
      (r = 0 ∨ ((σ.loc 5).toNat + (σ.loc 1).toNat ≤ (m.arr64 (tierA 0 t)).size ∧
        (σ.loc 5).toNat + (σ.loc 1).toNat < 2 ^ 64)) →
      ∃ σ', stepRun p (exec p k) hashTail σ = .ok (.normal, σ') ∧ σ'.mem = m ∧
        σ'.loc 3 = lhRows (m.arr64 (tierA 0 t)) (σ.loc 5 + σ.loc 2) (σ.loc 3) r := by
  intro r
  induction r with
  | zero =>
    intro k σ hm _ _ _ hi _
    refine ⟨σ, ?_, hm, rfl⟩
    have hl : ¬ σ.loc 2 < σ.loc 1 := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [hashTail_eq, step_while_run]
    simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hl, decide_false]
  | succ r ih =>
    intro k σ hm h4 h6 hk hi hw
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hw' := hw.resolve_left (by omega)
    have hlt : σ.loc 2 < σ.loc 1 := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hxi : (σ.loc 5 + σ.loc 2).toNat = (σ.loc 5).toNat + (σ.loc 2).toNat := by
      rw [UInt64.toNat_add]; omega
    have hb : (σ.loc 5 + σ.loc 2).toNat < (σ.mem.arr64 (tierA 0 (σ.loc 4))).size := by
      rw [hxi, hm, h4]; omega
    have hi1 : (σ.loc 2 + 1).toNat = (σ.loc 2).toNat + 1 := L.toNat_add_one_of_word_lt _ _ hlt
    obtain ⟨σ2, f2, hm2, hc2⟩ := ih k
      (σ.setLoc 3 ((σ.loc 3 ^^^ (σ.mem.arr64 (tierA 0 (σ.loc 4)))[(σ.loc 5 + σ.loc 2).toNat]) *
        σ.loc 6) |>.setLoc 2 (σ.loc 2 + 1))
      (by simp only [St.setLoc_mem, hm]) (by simp only [St.setLoc_loc]; exact h4)
      (by simp only [St.setLoc_loc]; exact h6) (by omega)
      (by simp only [St.setLoc_loc, reduceIte, Nat.reduceEqDiff]; omega)
      (Or.inr (by simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte]; omega))
    refine ⟨σ2, ?_, hm2, ?_⟩
    · rw [hashTail_eq, step_while_run]
      simp only [evalCP, evalP, bind, Except.bind, pure, Except.pure, Cmp.eval, hlt, decide_true]
      simp only [hBT, hashTail, step_seq_run, step_set_run, evalP, bind, Except.bind, pure,
        Except.pure, Except.map, St.setLoc_loc, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, hb, ↓reduceDIte]
      exact f2
    · rw [hc2]
      have hb' : (σ.loc 5 + σ.loc 2).toNat < (m.arr64 (tierA 0 t)).size := by rw [← hm, ← h4]; exact hb
      simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, lhRows, getElem!_pos, hb', h6, hm, h4]
      rw [UInt64.add_assoc]

theorem seq_normal {p : Prog} {K : Stmt → M Sig} {s t : Stmt} {σ σ' : St}
    (h : stepRun p K s σ = .ok (.normal, σ')) : stepRun p K (.seq s t) σ = stepRun p K t σ' := by
  rw [step_seq_run, h]

theorem set_const_run (p : Prog) (K : Stmt → M Sig) (σ : St) (x : Var) (c : Word) :
    stepRun p K (.set x (.const c)) σ = .ok (.normal, σ.setLoc x c) := rfl

theorem ret_var_run (p : Prog) (K : Stmt → M Sig) (σ : St) (x : Var) :
    stepRun p K (.ret [.var x]) σ = .ok (.ret [σ.loc x], σ) := rfl

theorem evalCP_slice (σ : St) (c : Word) :
    evalCP σ (.cmp .ult (.bin .sub (.const c) (.var 5)) (.var 1)) = .ok (decide (c - σ.loc 5 < σ.loc 1)) :=
  rfl

theorem sliceRes_run (p : Prog) (K : Stmt → M Sig) (S : St)
    (hc : ¬ (1099511627776 - (S.loc 0 &&& 1099511627775)) < S.loc 1) :
    stepRun p K (sliceRes 0 1 4 5) S =
      .ok (.normal, (S.setLoc 4 (S.loc 0 >>> 40)).setLoc 5 (S.loc 0 &&& 1099511627775)) := by
  unfold sliceRes
  simp only [step_seq_run, step_set_run, evalP, BinOp.eval, Except.map, bind, Except.bind, pure,
    Except.pure, St.setLoc_loc, Nat.reduceEqDiff, reduceIte]
  rw [step_ite_run]
  rw [evalCP_slice]
  simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte]
  rw [decide_eq_false hc]
  exact step_skip_run p K _

theorem exec_succ_run (p : Prog) (F : Nat) (s : Stmt) :
    (exec p (F + 1) s).run = L.Compiler.stepRun p (exec p F) s := rfl

theorem litHash_nparams : litHash.nparams = 2 := by rfl

theorem litHash_body : litHash.body =
    .seq (.set 3 (.const fnvBasis)) (.seq (sliceRes 0 1 4 5) (.seq (.set 6 (.const fnvPrime))
      (.seq hashLoop8 (.seq hashTail (.ret [.var 3]))))) := by
  with_unfolding_all exact Eq.refl _

/-- **`lit_hash` at fuel `F > l`**, its window in its tier below `2^40` (or `l = 0`): `lhRows`. -/
theorem litHash_run (p : Prog) (hp : p.lookup "lit_hash" = some litHash) (σ : St) (o l : Word)
    (F : Nat) (hF : l.toNat < F)
    (hw : l = 0 ∨ ((o &&& 1099511627775).toNat + l.toNat < 2 ^ 40 ∧
      (o &&& 1099511627775).toNat + l.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size)) :
    (invoke p (exec p F) "lit_hash" [o, l]).run σ =
      .ok ([lhRows (σ.mem.arr64 (tierA 0 (o >>> 40))) (o &&& 1099511627775) fnvBasis l.toNat], σ) := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [invoke, lookupFn, hp]
  rewrite [pure_bind, L.Compiler.callFn_run, exec_succ_run, litHash_body]
  have hx : (o &&& 1099511627775).toNat < 2 ^ 40 := tag_idx_lt o
  have hc : ¬ (1099511627776 - (o &&& 1099511627775)) < l := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [show (1099511627776 : Word).toNat = 2 ^ 40 from rfl]; omega))]
    rw [show (1099511627776 : Word).toNat = 2 ^ 40 from rfl]
    rcases hw with rfl | ⟨h1, _⟩
    · simp
    · omega
  rewrite [seq_normal (set_const_run _ _ _ _ _)]
  generalize hS0 : ({ mem := σ.mem, loc := Locals.init [o, l] } : St).setLoc 3 fnvBasis = S0
  have g0 : S0.loc 0 = o := by subst hS0; rfl
  have g1 : S0.loc 1 = l := by subst hS0; rfl
  have g2 : S0.loc 2 = 0 := by subst hS0; rfl
  have g3 : S0.loc 3 = fnvBasis := by subst hS0; rfl
  have gm : S0.mem = σ.mem := by subst hS0; rfl
  rewrite [seq_normal (sliceRes_run p _ S0 (by rw [g0, g1]; exact hc)), seq_normal (set_const_run _ _ _ _ _)]
  generalize hS1 : ((S0.setLoc 4 (S0.loc 0 >>> 40)).setLoc 5 (S0.loc 0 &&& 1099511627775)).setLoc 6
    fnvPrime = S1
  have k0 : S1.loc 0 = o := by subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, g0]
  have k1 : S1.loc 1 = l := by subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, g1]
  have k2 : S1.loc 2 = 0 := by subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, g2]
  have k3 : S1.loc 3 = fnvBasis := by subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, g3]
  have k4 : S1.loc 4 = o >>> 40 := by subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, g0]
  have k5 : S1.loc 5 = o &&& 1099511627775 := by
    subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte, g0]
  have k6 : S1.loc 6 = fnvPrime := by subst hS1; simp only [St.setLoc_loc, Nat.reduceEqDiff, reduceIte]
  have km : S1.mem = σ.mem := by subst hS1; simp only [St.setLoc_mem, gm]
  have hwin : l.toNat = 0 ∨ ((o &&& 1099511627775).toNat + l.toNat ≤
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧ (o &&& 1099511627775).toNat + l.toNat < 2 ^ 64) := by
    rcases hw with rfl | ⟨h1, h2⟩
    · left; rfl
    · right; omega
  obtain ⟨σ8, e8, m8, c8, x8, l8, s8, v8⟩ := hl8_run p (o >>> 40) σ.mem (l.toNat / 8) F S1 km k4 k6
    (by omega) (by rw [k1]) (by rw [k1, k5]; exact hwin)
  rewrite [seq_normal e8]
  have hx8 : (σ8.loc 5).toNat = (o &&& 1099511627775).toNat + 8 * (l.toNat / 8) := by
    rw [x8, k5, UInt64.toNat_add, L.toNat_ofNat_of_lt (by omega)]; omega
  obtain ⟨σT, eT, mT, cT⟩ := hT_run p (o >>> 40) σ.mem (l.toNat % 8) F σ8 m8
    (by rw [v8 4 (by omega), k4]) (by rw [v8 6 (by omega), k6]) (by omega)
    (by rw [v8 2 (by omega), k2, l8, k1]; simp)
    (by
      rcases hwin with h | h
      · left; omega
      · right; rw [hx8, l8, k1]; omega)
  rewrite [seq_normal eT, ret_var_run]
  simp only [Sig.retVal, Sig.retOr]
  rw [cT, c8, v8 2 (by omega), k2, k5, k3, x8, k5, UInt64.add_zero, ← lhRows_add,
    show 8 * (l.toNat / 8) + l.toNat % 8 = l.toNat by omega, mT]

end L.AsmEsc
