module

import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCanonEq
import ConAgua.L.LocNF
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.DeclNatCv
import all ConAgua.Arena.WhnfDelta

@[expose] public section

/-!
# `nat_lit_supported` under the stage relation (lane `decls3`, helper `decls3-nat`)

Lane `whnf` proves `nat_lit_supported` and its three callees under its relation `CoreS`
(`WhnfDeltaRefine.lean`), which carries the readback-cache invariants and the memo maps that the
stage relation `StageR` does not. The functions use only the pins, the environment and the
expression tables, so this file proves them again at `StageR`, in `CallRef` form.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def ciTag : IConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo .. => 1 | .thmInfo _ => 2 | .indInfo .. => 3
  | .ctorInfo .. => 4 | .recInfo .. => 5

theorem decCI_tag {a : Array Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI (aread a) p = some ci) :
    ∃ w, a[p]? = some w ∧ w.toNat = ciTag ci := by
  sorry

/-- A record's constant value reads: the level-parameter count word and the type word. -/
theorem natCvWords {m : Mem} {q : Word} {cv : IConstantVal} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : decCV (erecP m) (q.toNat + 1) = some cv) :
    ∃ wt, ((rdW (m.arr64 EREC) (q + 3) = 0) ↔ cv.levelParams.isEmpty = true) ∧
      rdW (m.arr64 EREC) (q + 4) = wt ∧ wt.toNat < 2 ^ 32 ∧ cv.type = decI wt ∧
      ∀ m', IWGrow m m' → rdW (m'.arr64 EREC) (q + 3) = rdW (m.arr64 EREC) (q + 3) ∧
        rdW (m'.arr64 EREC) (q + 4) = wt := by
  sorry

/-- A word read of the record's tag. -/
theorem tagWord {m : Mem} {q : Word} {ci : IConstantInfo}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (h : decCI (erecP m) q.toNat = some ci) :
    (rdW (m.arr64 EREC) q).toNat = ciTag ci := by
  sorry

/-- The record's constant value decodes at `q + 1`. -/
theorem ciCv_decodes {m : Mem} {q : Word} {ci : IConstantInfo} {cv : IConstantVal}
    (h : decCI (erecP m) q.toNat = some ci)
    (hcv : ci.toConstantVal = cv) : decCV (erecP m) (q.toNat + 1) = some cv := by
  sorry

structure NatLitProg (p : Prog) : Prop extends NatCvProg p where
  lNatIndOk : p.lookup "nat_ind_ok" = some natIndOkL
  lNatZeroOk : p.lookup "nat_zero_ok" = some natZeroOkL
  lNatSuccOk : p.lookup "nat_succ_ok" = some natSuccOkL
  lNatLitSupported : p.lookup "nat_lit_supported" = some natLitSupportedL

theorem callW_pinWord' {p : Prog} (hp : p.lookup "pin_word" = some pinWordL) {n : Nat} {m m' : Mem}
    {k : Word} {r : List Word} (h : callW p n "pin_word" [k] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ r = [pinW m k.toNat] := by
  obtain ⟨s', rfl, -, hmod⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinWord_specW p hp n _ k) h
  exact pinWord_model hmod

theorem natIndOk_nonind {ci : IConstantInfo} (h : ciTag ci ≠ 3) : natIndOk (some ci) = pure false := by
  cases ci <;> simp_all [natIndOk, ciTag]

section lit
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- The decoded `env_find` answer of `(found, q)`. -/
def FoundR (dn : NIdx → Option ConLeche.Name) (m : Mem) (found q : Word) (o : Option IConstantInfo) :
    Prop := decFd m [found, q] o

/-! ### `nat_ind_ok` -/

def natIndOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (List Word × Mem) :=
  if found = 0 then some ([0], m) else
  if rdW (m.arr64 EREC) q ≠ 3 then some ([0], m) else
  if rdW (m.arr64 EREC) (q + 3) ≠ 0 then some ([0], m) else
  ntBW (callW p n "pin_word" [54] m) fun r1 m1 =>
  some ([if rdW (m1.arr64 EREC) (q + 4) = r1.headD 0 then 1 else 0], m1)

theorem natIndOk_specW (p : Prog) (hp : p.lookup "nat_ind_ok" = some natIndOkL) (n : Nat)
    (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_ind_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natIndOkW p n s₀.mem found q = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem natIndOk_ref (hN : NatLitProg p) (found q : Word) (o : Option IConstantInfo) :
    CallRef p "nat_ind_ok" [found, q]
      (fun m a => StageR vis fe m a ∧ pinW m 0 ≠ 0 ∧ FoundR dn m found q o)
      (natIndOk o) (KeepPost vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, h0, hfd⟩ hc => ?_
  have hw := callW_model (M := fun mm => natIndOkW p k mm found q) (natIndOk_specW p hN.lNatIndOk k · found q) hc
  unfold natIndOkW at hw
  have hF := hS.check.pins.full h0
  have hsz := hS.iw.erSize
  cases o with
  | none =>
    simp only [FoundR, decFd] at hfd
    have hf : found = 0 := by simpa using hfd
    rw [ite_eq_left hf] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | some ci =>
    obtain ⟨hf1, hci⟩ := hfd
    simp only [List.headD_cons, List.tail_cons] at hf1 hci
    rw [ite_eq_right (by rw [hf1]; decide)] at hw
    have htag := tagWord hsz hci
    by_cases h3 : rdW (m.arr64 EREC) q = 3
    · have hci3 : ciTag ci = 3 := by rw [← htag, h3]; rfl
      cases ci with
      | indInfo cv caps =>
        rw [ite_eq_right (by simpa using h3)] at hw
        have hcvd := ciCv_decodes (cv := cv) hci rfl
        obtain ⟨wt, hiff, hrd, hlt, hty, hstay⟩ := natCvWords hsz hcvd
        by_cases hl : rdW (m.arr64 EREC) (q + 3) = 0
        · rw [ite_eq_right (by simpa using hl)] at hw
          replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
          obtain ⟨hm1, -, hr1⟩ := callW_pinWord' hN.lPinWord h1
          rw [hm1, hr1] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hp54 : (pinW m 54).toNat < 2 ^ 32 := hF.lv_lt.2.2
          have hisE : cv.levelParams.isEmpty = true := hiff.mp hl
          have hrun : (natIndOk (some (.indInfo cv caps))).run a =
              .ok (decide (rdW (m.arr64 EREC) (q + 4) = pinW m 54), a) := by
            simp only [natIndOk, sortOne, StateT.run_bind, pinSortOne_run hF, exc_ok_bind', hisE,
              Bool.true_and, hty, hrd, decI_beq _ _ hlt hp54, StateT.run_pure]
            rfl
          refine ⟨_, a, hrun, hS, IWGrow.refl _, ?_⟩
          by_cases he : rdW (m.arr64 EREC) (q + 4) = pinW m 54
          · simp [decW0B, he]
          · simp [decW0B, he]
        · rw [ite_eq_left (by simpa using hl)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : cv.levelParams.isEmpty = false := by
            cases h : cv.levelParams.isEmpty
            · rfl
            · exact absurd (hiff.mpr h) hl
          refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
          simp only [natIndOk, sortOne, StateT.run_bind, pinSortOne_run hF, exc_ok_bind', hisE,
            Bool.false_and, StateT.run_pure]
          rfl
      | _ => simp [ciTag] at hci3
    · rw [ite_eq_left h3] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hne : ciTag ci ≠ 3 := fun e => h3 (UInt64.toNat_inj.mp (by rw [htag, e]; rfl))
      exact ⟨false, a, by rw [natIndOk_nonind hne]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩

/-! ### `nat_zero_ok` -/

def natZeroOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (List Word × Mem) :=
  if found = 0 then some ([0], m) else
  if rdW (m.arr64 EREC) q ≠ 4 then some ([0], m) else
  ntBW (callW p n "pin_at" [1] m) fun r1 m1 =>
  ntBW (callW p n "const_e" [r1.headD 0] m1) fun r2 m2 =>
  if rdW (m2.arr64 EREC) (q + 3) ≠ 0 then some ([0], m2) else
  some ([if rdW (m2.arr64 EREC) (q + 4) = r2.headD 0 then 1 else 0], m2)

theorem natZeroOk_specW (p : Prog) (hp : p.lookup "nat_zero_ok" = some natZeroOkL) (n : Nat)
    (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_zero_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natZeroOkW p n s₀.mem found q = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem natZeroOk_nonctor {ci : IConstantInfo} (h : ciTag ci ≠ 4) : natZeroOk (some ci) = pure false := by
  cases ci <;> simp_all [natZeroOk, ciTag]

/-- The pin read at slot `1` (`Nat`), as a run. -/
theorem pinNat_call {p : Prog} (hN : NatLitProg p) {k : Nat} {m m1 : Mem} {r1 : List Word}
    (h : callW p k "pin_at" [1] m = some (r1, m1)) :
    m1 = m ∧ pinW m 0 ≠ 0 ∧ r1.headD 0 = pinW m 2 := by
  obtain ⟨hm, h0, -, hr⟩ := pinAt_model hN.lPinAt h (j := 2) rfl
  exact ⟨hm, h0, hr⟩

theorem natZeroOk_ref (hN : NatLitProg p) (found q : Word) (o : Option IConstantInfo) :
    CallRef p "nat_zero_ok" [found, q]
      (fun m a => StageR vis fe m a ∧ pinW m 0 ≠ 0 ∧ FoundR dn m found q o)
      (natZeroOk o) (KeepPost vis fe decW0B) := by
  sorry

/-! ### `nat_succ_ok` -/

def natSuccOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (List Word × Mem) :=
  if found = 0 then some ([0], m) else
  if rdW (m.arr64 EREC) q ≠ 4 then some ([0], m) else
  if rdW (m.arr64 EREC) (q + 3) ≠ 0 then some ([0], m) else
  ntBW (callW p n "pin_at" [1] m) fun r1 m1 =>
  ntBW (callW p n "const_e" [r1.headD 0] m1) fun r2 m2 =>
  if tagW (rdW (m2.arr64 EREC) (q + 4)) ≠ 6 then some ([0], m2) else
  if tierW (rdW (m2.arr64 EREC) (q + 4)) ≠ 0 ∧ rdW (m2.arr64 CTL) 1 = 0 then none else
  if tcnt m2 FORALL (tierW (rdW (m2.arr64 EREC) (q + 4))) ≤ idxW (rdW (m2.arr64 EREC) (q + 4))
    then none else
  some ([if tfld m2 FORALL (tierW (rdW (m2.arr64 EREC) (q + 4))) (idxW (rdW (m2.arr64 EREC) (q + 4))) 0 = r2.headD 0 ∧
        tfld m2 FORALL (tierW (rdW (m2.arr64 EREC) (q + 4))) (idxW (rdW (m2.arr64 EREC) (q + 4))) 1 = r2.headD 0 then 1 else 0], m2)

theorem natSuccOk_specW (p : Prog) (hp : p.lookup "nat_succ_ok" = some natSuccOkL) (n : Nat)
    (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_succ_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natSuccOkW p n s₀.mem found q = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem natSuccOk_nonctor {ci : IConstantInfo} (h : ciTag ci ≠ 4) : natSuccOk (some ci) = pure false := by
  cases ci <;> simp_all [natSuccOk, ciTag]

theorem natSuccOk_ref (hN : NatLitProg p) (found q : Word) (o : Option IConstantInfo) :
    CallRef p "nat_succ_ok" [found, q]
      (fun m a => StageR vis fe m a ∧ pinW m 0 ≠ 0 ∧ FoundR dn m found q o)
      (natSuccOk o) (KeepPost vis fe decW0B) := by
  sorry

/-! ### `nat_lit_supported` -/

def natLitSupportedW (p : Prog) (n : Nat) (m : Mem) (vis : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "pin_at" [1] m) fun r1 m1 =>
  ntBW (callW p n "env_find" [r1.headD 0, vis] m1) fun rf m2 =>
  ntBW (callW p n "nat_ind_ok" [rf.headD 0, rf.tail.headD 0] m2) fun ri m3 =>
  if ri.headD 0 = 0 then some ([0], m3) else
  ntBW (callW p n "pin_at" [2] m3) fun r4 m4 =>
  ntBW (callW p n "env_find" [r4.headD 0, vis] m4) fun rg m5 =>
  ntBW (callW p n "nat_zero_ok" [rg.headD 0, rg.tail.headD 0] m5) fun rz m6 =>
  if rz.headD 0 = 0 then some ([0], m6) else
  ntBW (callW p n "pin_at" [3] m6) fun r7 m7 =>
  ntBW (callW p n "env_find" [r7.headD 0, vis] m7) fun rh m8 =>
  ntBW (callW p n "nat_succ_ok" [rh.headD 0, rh.tail.headD 0] m8) fun rs m9 =>
  some ([rs.headD 0], m9)

theorem natLitSupported_specW (p : Prog) (hp : p.lookup "nat_lit_supported" = some natLitSupportedL)
    (n : Nat) (s₀ : St) (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_lit_supported" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧ natLitSupportedW p n s₀.mem vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natLitSupportedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "nat_ind_ok",
      callW_spec p n "nat_zero_ok", callW_spec p n "nat_succ_ok"] <;>
    finish (gen := 20) [natLitSupportedW, ntBW]

/-- A pin read at slot `1 + j`, as a run. -/
theorem pinAt_call {p : Prog} (hp : p.lookup "pin_at" = some pinAtL) {k : Nat} {m m1 : Mem}
    {i : Word} {j : Nat} (hj : 1 + i.toNat = j) {r1 : List Word}
    (h : callW p k "pin_at" [i] m = some (r1, m1)) :
    m1 = m ∧ pinW m 0 ≠ 0 ∧ r1.headD 0 = pinW m j := by
  obtain ⟨hm, h0, -, hr⟩ := pinAt_model hp h hj
  exact ⟨hm, h0, hr⟩

theorem natLitSupported_ref (hN : NatLitProg p) :
    CallRef p "nat_lit_supported" [vis] (StageR vis fe) (natLitSupported fe)
      (KeepPost vis fe decW0B) := by
  sorry

@[refines ConRon.Arena.natLitSupported]
theorem natLitSupported_refines (hN : NatLitProg p) :
    RefAM p "nat_lit_supported" [vis] (StageR vis fe) (natLitSupported fe)
      (KeepPost vis fe decW0B) :=
  (natLitSupported_ref hN).refAM

end lit

end L.Ind
