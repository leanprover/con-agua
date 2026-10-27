import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

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

theorem decCI_tag {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ w, a[p]? = some w ∧ w.toNat = ciTag ci := by
  unfold decCI at h
  cases hk : nat? a p with
  | none => simp [hk] at h
  | some k =>
  have hw : ∃ w, a[p]? = some w ∧ w.toNat = k := by
    simp only [nat?, Option.map_eq_some_iff] at hk
    obtain ⟨w, hw, hk⟩ := hk; exact ⟨w, hw, hk⟩
  obtain ⟨w, hw, hwk⟩ := hw
  rw [hk] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  refine ⟨w, hw, ?_⟩
  rw [hwk]
  rcases k with _ | _ | _ | _ | _ | _ | k
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h; rfl
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, _, -, _, -, rfl⟩ := h; rfl
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h; rfl
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, _, -, rfl⟩ := h; rfl
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, _, -, _, -, rfl⟩ := h; rfl
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, _, -, _, -, _, -, _, -, _, -, rfl⟩ := h; rfl
  · simp at h

/-- A record's constant value reads: the level-parameter count word and the type word. -/
theorem natCvWords {m : Mem} {q : Word} {cv : IConstantVal} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : decCV (erecP m) (q.toNat + 1) = some cv) :
    ∃ wt, ((rdW (m.arr64 EREC) (q + 3) = 0) ↔ cv.levelParams.isEmpty = true) ∧
      rdW (m.arr64 EREC) (q + 4) = wt ∧ wt.toNat < 2 ^ 32 ∧ cv.type = decI wt ∧
      ∀ m', IWGrow m m' → rdW (m'.arr64 EREC) (q + 3) = rdW (m.arr64 EREC) (q + 3) ∧
        rdW (m'.arr64 EREC) (q + 4) = wt := by
  obtain ⟨wl, hwl, hlen⟩ := decCV_lps_len h
  obtain ⟨wt, hwt, hlt, hty⟩ := decCV_typeW h
  have hwl' := erecP_get hwl
  have hwt' := erecP_get hwt
  have hb : q.toNat + 4 < (m.arr64 EREC).size := by
    have := (Array.getElem?_eq_some_iff.mp hwt').1; omega
  have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hq4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : rdW (m.arr64 EREC) (q + 3) = wl := by
    simp only [rdW, hq3]; rw [show q.toNat + 3 = q.toNat + 1 + 2 by omega, hwl']; rfl
  have e4 : rdW (m.arr64 EREC) (q + 4) = wt := by
    simp only [rdW, hq4]; rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, hwt']; rfl
  have hst : ∀ m', IWGrow m m' → rdW (m'.arr64 EREC) (q + 3) = rdW (m.arr64 EREC) (q + 3) ∧
      rdW (m'.arr64 EREC) (q + 4) = wt := by
    intro m' hg
    constructor
    · rw [e3]; simp only [rdW, hq3]
      rw [show q.toNat + 3 = q.toNat + 1 + 2 by omega, hg.erec_get hwl]; rfl
    · simp only [rdW, hq4]
      rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, hg.erec_get hwt]; rfl
  refine ⟨wt, ?_, e4, hlt, hty, hst⟩
  rw [e3]
  simp only [List.isEmpty_iff_length_eq_zero]
  constructor
  · intro hw0; rw [← hlen, hw0]; rfl
  · intro hl; exact UInt64.toNat_inj.mp (by simpa [hlen] using hl)

/-- A word read of the record's tag. -/
theorem tagWord {m : Mem} {q : Word} {ci : IConstantInfo} {dn : NIdx → Option ConLeche.Name}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (h : decCI (erecP m) dn q.toNat = some ci) :
    (rdW (m.arr64 EREC) q).toNat = ciTag ci := by
  obtain ⟨w, hw, ht⟩ := decCI_tag h
  rw [rdW_erec_of hsz hw, ht]

/-- The record's constant value decodes at `q + 1`. -/
theorem ciCv_decodes {m : Mem} {q : Word} {ci : IConstantInfo} {cv : IConstantVal}
    {dn : NIdx → Option ConLeche.Name} (h : decCI (erecP m) dn q.toNat = some ci)
    (hcv : ci.toConstantVal = cv) : decCV (erecP m) (q.toNat + 1) = some cv :=
  hcv ▸ ciD_cv h

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

theorem tagForallIff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.forallE) = decide (w >>> 28 = 6) := by
  have := decE_tag_eq w hw 6 (by decide)
  have e1 : (ETag.forallE : UInt32) = UInt32.ofNat 6 := rfl
  show ((decE w).tag == ETag.forallE) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

section lit
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- The decoded `env_find` answer of `(found, q)`. -/
def FoundR (dn : NIdx → Option ConLeche.Name) (m : Mem) (found q : Word) (o : Option IConstantInfo) :
    Prop := decFd dn m [found, q] o

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
  rw [invoke_eq _ hp]
  simp only [callFn, natIndOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word"] <;>
    finish (gen := 20) [natIndOkW, ntBW]

theorem natIndOk_ref (hN : NatLitProg p) (found q : Word) (o : Option IConstantInfo) :
    CallRef p "nat_ind_ok" [found, q]
      (fun m a => StageR dn vis fe m a ∧ pinW m 0 ≠ 0 ∧ FoundR dn m found q o)
      (natIndOk o) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, h0, hfd⟩ hc => ?_
  have hw := callW_model (M := fun mm => natIndOkW p k mm found q) (natIndOk_specW p hN.lNatIndOk k · found q) hc
  unfold natIndOkW at hw
  have hF := hS.1.pins.full h0
  have hsz := hS.2.2.2.2.1
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
              Bool.true_and, hty, hrd, decI_beq_word hlt hp54, StateT.run_pure]
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
  rw [invoke_eq _ hp]
  simp only [callFn, natZeroOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "const_e"] <;>
    finish (gen := 20) [natZeroOkW, ntBW]

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
      (fun m a => StageR dn vis fe m a ∧ pinW m 0 ≠ 0 ∧ FoundR dn m found q o)
      (natZeroOk o) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, h0, hfd⟩ hc => ?_
  have hw := callW_model (M := fun mm => natZeroOkW p k mm found q) (natZeroOk_specW p hN.lNatZeroOk k · found q) hc
  unfold natZeroOkW at hw
  have hF := hS.1.pins.full h0
  have hsz := hS.2.2.2.2.1
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
    by_cases h4 : rdW (m.arr64 EREC) q = 4
    · cases ci with
      | ctorInfo cv np nf =>
        rw [ite_eq_right (by simpa using h4)] at hw
        have hcvd := ciCv_decodes (cv := cv) hci rfl
        obtain ⟨wt, hiff, hrd, hlt, hty, hstay⟩ := natCvWords hsz hcvd
        replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
        obtain ⟨hm1, -, hr1⟩ := pinNat_call hN h1
        subst hm1
        replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
        have hp2 : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt 1 (by decide)
        obtain ⟨x2, a2, hr2, hS2, hg2, hx2l, hx2⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
          hN.toMasterProg (r1.headD 0) k m1 a r2 m2 ⟨hS, hp2⟩ h2
        obtain ⟨hst3, hst4⟩ := hstay m2 hg2
        by_cases hl : rdW (m1.arr64 EREC) (q + 3) = 0
        · have hl2 : rdW (m2.arr64 EREC) (q + 3) = 0 := by rw [hst3]; exact hl
          rw [ite_eq_right (by simpa using hl2)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : cv.levelParams.isEmpty = true := hiff.mp hl
          have e1 : (pinAt 1).run a = .ok (decI (r1.headD 0), a) := by
            have := pinAt_run hF 1 (by decide)
            rw [hr1]; exact this
          have hrun : (natZeroOk (some (.ctorInfo cv np nf))).run a =
              .ok (decide (wt = r2.headD 0), a2) := by
            simp only [natZeroOk, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hr2, hisE,
              Bool.true_and, hty, decI_beq_word hlt hx2l, ← hx2, StateT.run_pure]
            rfl
          refine ⟨_, a2, hrun, hS2, hg2, ?_⟩
          rw [hst4] at *
          simp only [decW0B, List.headD_cons]
          by_cases he : wt = r2.headD 0
          · rw [ite_eq_left he, decide_eq_true he]; decide
          · rw [ite_eq_right he, decide_eq_false he]; decide
        · have hl2 : ¬ rdW (m2.arr64 EREC) (q + 3) = 0 := by rw [hst3]; exact hl
          rw [ite_eq_left (by simpa using hl2)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : cv.levelParams.isEmpty = false := by
            cases h : cv.levelParams.isEmpty
            · rfl
            · exact absurd (hiff.mpr h) hl
          have e1 : (pinAt 1).run a = .ok (decI (r1.headD 0), a) := by
            have := pinAt_run hF 1 (by decide)
            rw [hr1]; exact this
          have hrun : (natZeroOk (some (.ctorInfo cv np nf))).run a = .ok (false, a2) := by
            simp only [natZeroOk, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hr2, hisE,
              Bool.false_and, StateT.run_pure]
            rfl
          exact ⟨false, a2, hrun, hS2, hg2, by simp [decW0B]⟩
      | _ => rw [h4] at htag; simp [ciTag] at htag
    · rw [ite_eq_left h4] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hne : ciTag ci ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp (by rw [htag, e]; rfl))
      exact ⟨false, a, by rw [natZeroOk_nonctor hne]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩


/-! ### `nat_succ_ok` -/

def natSuccOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (List Word × Mem) :=
  if found = 0 then some ([0], m) else
  if rdW (m.arr64 EREC) q ≠ 4 then some ([0], m) else
  if rdW (m.arr64 EREC) (q + 3) ≠ 0 then some ([0], m) else
  ntBW (callW p n "pin_at" [1] m) fun r1 m1 =>
  ntBW (callW p n "const_e" [r1.headD 0] m1) fun r2 m2 =>
  if rdW (m2.arr64 EREC) (q + 4) >>> 28 ≠ 6 then some ([0], m2) else
  if tierW (rdW (m2.arr64 EREC) (q + 4)) ≠ 0 ∧ rdW (m2.arr64 CTL) 1 = 0 then none else
  if tcnt m2 FORALL (tierW (rdW (m2.arr64 EREC) (q + 4))) ≤ idxW (rdW (m2.arr64 EREC) (q + 4))
    then none else
  some ([if tfld m2 FORALL (tierW (rdW (m2.arr64 EREC) (q + 4))) (idxW (rdW (m2.arr64 EREC) (q + 4))) 0 = r2.headD 0 ∧
        tfld m2 FORALL (tierW (rdW (m2.arr64 EREC) (q + 4))) (idxW (rdW (m2.arr64 EREC) (q + 4))) 1 = r2.headD 0 then 1 else 0], m2)

theorem natSuccOk_specW (p : Prog) (hp : p.lookup "nat_succ_ok" = some natSuccOkL) (n : Nat)
    (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_succ_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natSuccOkW p n s₀.mem found q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natSuccOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "pin_at", callW_spec p n "const_e"] <;>
    finish (gen := 20) [natSuccOkW, ntBW, tierW, idxW]


theorem natSuccOk_nonctor {ci : IConstantInfo} (h : ciTag ci ≠ 4) : natSuccOk (some ci) = pure false := by
  cases ci <;> simp_all [natSuccOk, ciTag]

theorem natSuccOk_ref (hN : NatLitProg p) (found q : Word) (o : Option IConstantInfo) :
    CallRef p "nat_succ_ok" [found, q]
      (fun m a => StageR dn vis fe m a ∧ pinW m 0 ≠ 0 ∧ FoundR dn m found q o)
      (natSuccOk o) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, h0, hfd⟩ hc => ?_
  have hw := callW_model (M := fun mm => natSuccOkW p k mm found q) (natSuccOk_specW p hN.lNatSuccOk k · found q) hc
  unfold natSuccOkW at hw
  have hF := hS.1.pins.full h0
  have hsz := hS.2.2.2.2.1
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
    by_cases h4 : rdW (m.arr64 EREC) q = 4
    · cases ci with
      | ctorInfo cv np nf =>
        rw [ite_eq_right (by simpa using h4)] at hw
        have hcvd := ciCv_decodes (cv := cv) hci rfl
        obtain ⟨wt, hiff, hrd, hlt, hty, hstay⟩ := natCvWords hsz hcvd
        by_cases hl : rdW (m.arr64 EREC) (q + 3) = 0
        · rw [ite_eq_right (by simpa using hl)] at hw
          have hisE : cv.levelParams.isEmpty = true := hiff.mp hl
          replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
          obtain ⟨hm1, -, hr1⟩ := pinNat_call hN h1
          subst hm1
          replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
          have hp2 : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt 1 (by decide)
          obtain ⟨x2, a2, hr2, hS2, hg2, hx2l, hx2⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
            hN.toMasterProg (r1.headD 0) k m1 a r2 m2 ⟨hS, hp2⟩ h2
          obtain ⟨-, hst4⟩ := hstay m2 hg2
          rw [hst4] at hw
          have e1 : (pinAt 1).run a = .ok (decI (r1.headD 0), a) := by
            have := pinAt_run hF 1 (by decide)
            rw [hr1]; exact this
          by_cases h6 : wt >>> 28 = 6
          · rw [ite_eq_right (by simpa using h6)] at hw
            by_cases hv1 : tierW wt ≠ 0 ∧ rdW (m2.arr64 CTL) 1 = 0
            · rw [ite_eq_left hv1] at hw; cases hw
            rw [ite_eq_right hv1] at hw
            by_cases hv2 : tcnt m2 FORALL (tierW wt) ≤ idxW wt
            · rw [ite_eq_left hv2] at hw; cases hw
            rw [ite_eq_right hv2] at hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            have hvok : viewOK m2 wt FORALL := ⟨hv1, by
              rw [UInt64.lt_iff_toNat_lt]
              exact Nat.lt_of_not_le (fun e => hv2 (UInt64.le_iff_toNat_le.mpr e))⟩
            obtain ⟨hview, hdlt, hblt⟩ := view_forall m2 a2 hS2.1.arena.1 wt hlt hvok h6
            have hrun : (natSuccOk (some (.ctorInfo cv np nf))).run a =
                .ok (decide (tfld m2 FORALL (tierW wt) (idxW wt) 0 = r2.headD 0 ∧
                  tfld m2 FORALL (tierW wt) (idxW wt) 1 = r2.headD 0), a2) := by
              simp only [natSuccOk, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hr2, hisE,
                Bool.not_true, Bool.false_eq_true, ite_false, hty]
              rw [tagForallIff wt hlt]
              simp only [h6, decide_true, ite_true, ← decE_eq]
              simp only [StateT.run_bind, view_run (decE wt) a2 _ hview]
              simp only [exc_ok_bind', decE_eq, decI_beq_word hdlt hx2l, decI_beq_word hblt hx2l,
                ← hx2, Bool.decide_and, StateT.run_pure]
              rfl
            refine ⟨_, a2, hrun, hS2, hg2, ?_⟩
            simp only [decW0B, List.headD_cons]
            by_cases he : tfld m2 FORALL (tierW wt) (idxW wt) 0 = r2.headD 0 ∧
                tfld m2 FORALL (tierW wt) (idxW wt) 1 = r2.headD 0
            · rw [ite_eq_left he, decide_eq_true he]; decide
            · rw [ite_eq_right he, decide_eq_false he]; decide
          · rw [ite_eq_left (by simpa using h6)] at hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            have hrun : (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (false, a2) := by
              simp only [natSuccOk, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hr2, hisE,
                Bool.not_true, Bool.false_eq_true, ite_false, hty]
              rw [tagForallIff wt hlt]
              simp only [h6, decide_false, Bool.false_eq_true, ite_false, StateT.run_pure]
              rfl
            exact ⟨false, a2, hrun, hS2, hg2, by simp [decW0B]⟩
        · rw [ite_eq_left (by simpa using hl)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : cv.levelParams.isEmpty = false := by
            cases h : cv.levelParams.isEmpty
            · rfl
            · exact absurd (hiff.mpr h) hl
          refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
          simp only [natSuccOk, hisE]
          rfl
      | _ => rw [h4] at htag; simp [ciTag] at htag
    · rw [ite_eq_left h4] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hne : ciTag ci ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp (by rw [htag, e]; rfl))
      exact ⟨false, a, by rw [natSuccOk_nonctor hne]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩


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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
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
    CallRef p "nat_lit_supported" [vis] (StageR dn vis fe) (natLitSupported fe)
      (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' hS hc => ?_
  have hw := callW_model (M := fun mm => natLitSupportedW p k mm vis) (natLitSupported_specW p hN.lNatLitSupported k · vis) hc
  unfold natLitSupportedW at hw
  -- the first lookup
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  obtain ⟨hm1, h0, hr1⟩ := pinNat_call hN h1
  rw [hm1] at hw
  have hF := hS.1.pins.full h0
  have hp1 : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt 1 (by decide)
  replace hw := ntBW_some hw; obtain ⟨rf, m2, h2, hw⟩ := hw
  obtain ⟨hm2, hfd⟩ := envFind_call hN.toMasterProg (r1.headD 0) hp1 hS.1.env h2
  rw [hm2] at hw
  replace hw := ntBW_some hw; obtain ⟨ri, m3, h3, hw⟩ := hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := natIndOk_ref (dn := dn) (vis := vis) (fe := fe) hN
    (rf.headD 0) (rf.tail.headD 0) (fe.find? (decI (r1.headD 0))) k m a ri m3 ⟨hS, h0, hfd⟩ h3
  have e1 : (pinAt 1).run a = .ok (decI (r1.headD 0), a) := by
    have := pinAt_run hF 1 (by decide)
    rw [hr1]; exact this
  by_cases hi : ri.headD 0 = 0
  · rw [ite_eq_left hi] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx : x1 = false := by
      have := hx1.1
      simp only [hi] at this
      simpa using this.symm
    refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [natLitSupported, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hrun1, hx]
    rfl
  · rw [ite_eq_right hi] at hw
    have hx : x1 = true := by
      have := hx1.1
      have hne : (ri.headD 0 != 0) = true := by simpa using hi
      rw [hne] at this; exact this.symm
    -- the second lookup
    replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
    obtain ⟨hm4, h0', hr4⟩ := pinAt_call hN.lPinAt (j := 3) rfl h4
    rw [hm4] at hw
    have hF3 := hS1.1.pins.full h0'
    have hp4 : H (r4.headD 0) := by rw [hr4]; exact hF3.names_lt 2 (by decide)
    replace hw := ntBW_some hw; obtain ⟨rg, m5, h5, hw⟩ := hw
    obtain ⟨hm5, hfd2⟩ := envFind_call hN.toMasterProg (r4.headD 0) hp4 hS1.1.env h5
    rw [hm5] at hw
    replace hw := ntBW_some hw; obtain ⟨rz, m6, h6, hw⟩ := hw
    obtain ⟨x2, a2, hrun2, hS2, hg2, hx2⟩ := natZeroOk_ref (dn := dn) (vis := vis) (fe := fe) hN
      (rg.headD 0) (rg.tail.headD 0) (fe.find? (decI (r4.headD 0))) k m3 a1 rz m6 ⟨hS1, h0', hfd2⟩ h6
    have e2 : (pinAt 2).run a1 = .ok (decI (r4.headD 0), a1) := by
      have := pinAt_run hF3 2 (by decide)
      rw [hr4]; exact this
    by_cases hz : rz.headD 0 = 0
    · rw [ite_eq_left hz] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx' : x2 = false := by
        have := hx2.1
        simp only [hz] at this
        simpa using this.symm
      refine ⟨false, a2, ?_, hS2, hg1.trans hg2, by simp [decW0B]⟩
      simp only [natLitSupported, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hrun1, hx,
        Bool.not_true, Bool.false_eq_true, ite_false, pinNatZero_eq, e2, hrun2, hx']
      rfl
    · rw [ite_eq_right hz] at hw
      have hx' : x2 = true := by
        have := hx2.1
        have hne : (rz.headD 0 != 0) = true := by simpa using hz
        rw [hne] at this; exact this.symm
      -- the third lookup
      replace hw := ntBW_some hw; obtain ⟨r7, m7, h7, hw⟩ := hw
      obtain ⟨hm7, h0'', hr7⟩ := pinAt_call hN.lPinAt (j := 4) rfl h7
      rw [hm7] at hw
      have hF6 := hS2.1.pins.full h0''
      have hp7 : H (r7.headD 0) := by rw [hr7]; exact hF6.names_lt 3 (by decide)
      replace hw := ntBW_some hw; obtain ⟨rh, m8, h8, hw⟩ := hw
      obtain ⟨hm8, hfd3⟩ := envFind_call hN.toMasterProg (r7.headD 0) hp7 hS2.1.env h8
      rw [hm8] at hw
      replace hw := ntBW_some hw; obtain ⟨rs, m9, h9, hw⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := natSuccOk_ref (dn := dn) (vis := vis) (fe := fe) hN
        (rh.headD 0) (rh.tail.headD 0) (fe.find? (decI (r7.headD 0))) k m6 a2 rs m9
        ⟨hS2, h0'', hfd3⟩ h9
      have e3 : (pinAt 3).run a2 = .ok (decI (r7.headD 0), a2) := by
        have := pinAt_run hF6 3 (by decide)
        rw [hr7]; exact this
      refine ⟨x3, a3, ?_, hS3, hg1.trans (hg2.trans hg3), ?_⟩
      · simp only [natLitSupported, pinNat_eq, StateT.run_bind, e1, exc_ok_bind', hrun1, hx,
          Bool.not_true, Bool.false_eq_true, ite_false, pinNatZero_eq, e2, hrun2, hx', pinNatSucc_eq,
          e3, hrun3]
      · simpa [decW0B] using hx3

@[refines ConRon.Arena.natLitSupported]
theorem natLitSupported_refines (hN : NatLitProg p) :
    RefAM p "nat_lit_supported" [vis] (StageR dn vis fe) (natLitSupported fe)
      (KeepPost dn vis fe decW0B) :=
  (natLitSupported_ref hN).refAM

end lit

end L.Ind
