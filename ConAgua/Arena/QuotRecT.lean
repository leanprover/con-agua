module

public import ConAgua.Arena.QuotRecW
public import ConAgua.Arena.IndPosSpec.EnvFindWHit
import all ConAgua.Arena.BasisL

@[expose] public section

/-!
# The quotient records' refinements (lane `ronsync2`, stage 3)

Against the models of `QuotRecW.lean`: `quot_preds_ok(vis, k)` refines `quotPredsOk fe k` (the three
pins read, each looked up in the view, the slot's conjunction).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem exb {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
theorem exm {ε α β : Type} (x : α) (f : α → β) : (f <$> (Except.ok x : Except ε α)) = Except.ok (f x) := rfl

/-- A `pin_at` call through its model. -/
theorem callW_pinAtW {p : Prog} (hp : p.lookup "pin_at" = some pinAtL) {n : Nat} {m m' : Mem}
    {i : Word} {r : List Word} (h : callW p n "pin_at" [i] m = some (r, m')) :
    pinAtW m i = some (r, m') := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinAt_specW p hp n _ i) h
  exact hW

/-- **`env_find`'s hit flag is the view's `find?`**. -/
theorem findRes_isSome {vis : Word} {fe : IFEnv} {m : Mem} {w : Word} (hE : EnvR m vis fe)
    (hw : w.toNat < 2 ^ 32) : (fe.find? (decI w)).isSome = ((findRes m vis w).headD 0 != 0) := by
  by_cases h0 : (findRes m vis w).headD 0 = 0
  · rw [findRes_miss hE hw h0, h0]; rfl
  · obtain ⟨e, ci, hci⟩ := findRes_hit hE hw h0
    rw [e, hci]; simpa [List.headD] using h0

/-- One pin's lookup: the pin read (the memory unchanged), `env_find` at it. -/
theorem pinFind_ok {p : Prog} (hB : BasisProg p) (hpa : p.lookup "pin_at" = some pinAtL)
    {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a : AState} {i : Word} {n : Nat}
    {r1 r2 : List Word} (hS : StageR vis fe m a)
    (h1 : callW p n "pin_at" [i] m = some (r1, m1))
    (h2 : callW p n "env_find" [r1.headD 0, vis] m1 = some (r2, m2)) :
    m = m1 ∧ m = m2 ∧ ∃ w : Word, w.toNat < 2 ^ 32 ∧ r1.headD 0 = w ∧
      (if i = 51 then (pinAt 51).run a = .ok (decI w, a)
        else (pinAt i.toNat).run a = .ok (decI w, a)) ∧
      (fe.find? (decI w)).isSome = (r2.headD 0 != 0) := by
  have hW := callW_pinAtW hpa h1
  by_cases h51 : i = 51
  · subst h51
    obtain ⟨rfl, rfl, hl, hrun⟩ := pinAtW_ok51 hW hS.check.pins
    obtain ⟨rfl, rfl⟩ := envFind_callB hB hl hS.check.env h2
    exact ⟨rfl, rfl, _, hl, rfl, by simpa using hrun, findRes_isSome hS.check.env hl⟩
  · obtain ⟨rfl, rfl, hl, hrun⟩ := pinAtW_ok hW hS.check.pins h51
    obtain ⟨rfl, rfl⟩ := envFind_callB hB hl hS.check.env h2
    exact ⟨rfl, rfl, _, hl, rfl, by simpa [h51] using hrun, findRes_isSome hS.check.env hl⟩

/-- **`quot_preds_ok(vis, k.slot)` refines `quotPredsOk fe k`** (the memory and the twin state
unchanged). -/
theorem quotPredsOkW_ok {p : Prog} (hB : BasisProg p) (hpa : p.lookup "pin_at" = some pinAtL)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {n : Nat} {r : List Word}
    (k : ConLeche.QuotKind) (hS : StageR vis fe m a)
    (h : quotPredsOkW p n m vis (UInt64.ofNat k.slot) = some (r, m')) :
    m' = m ∧ (ConRon.Arena.quotPredsOk fe k).run a = .ok ((r.headD 0 != 0), a) := by
  cases n with
  | zero => simp [quotPredsOkW] at h
  | succ n =>
  simp only [quotPredsOkW] at h
  cases h1 : callW p n "pin_at" [0] m with
  | none => rw [h1] at h; simp [quotPredsOkW.k_pin_at] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h; simp only [quotPredsOkW.k_pin_at] at h
  cases h2 : callW p n "env_find" [r1.headD 0, vis] m1 with
  | none => rw [h2] at h; simp [quotPredsOkW.k_env_find] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at h; simp only [quotPredsOkW.k_env_find] at h
  obtain ⟨rfl, rfl, w1, -, -, hp1, hf1⟩ := pinFind_ok hB hpa hS h1 h2
  cases h3 : callW p n "pin_at" [47] m with
  | none => rw [h3] at h; simp [quotPredsOkW.k_pin_at_2] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at h; simp only [quotPredsOkW.k_pin_at_2] at h
  cases h4 : callW p n "env_find" [r3.headD 0, vis] m3 with
  | none => rw [h4] at h; simp [quotPredsOkW.k_env_find_2] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4] at h; simp only [quotPredsOkW.k_env_find_2] at h
  obtain ⟨rfl, rfl, w3, -, -, hp3, hf3⟩ := pinFind_ok hB hpa hS h3 h4
  cases h5 : callW p n "pin_at" [51] m with
  | none => rw [h5] at h; simp [quotPredsOkW.k_pin_at_3] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at h; simp only [quotPredsOkW.k_pin_at_3] at h
  cases h6 : callW p n "env_find" [r5.headD 0, vis] m5 with
  | none => rw [h6] at h; simp [quotPredsOkW.k_env_find_3] at h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6] at h
  obtain ⟨rfl, rfl, w5, -, -, hp5, hf5⟩ := pinFind_ok hB hpa hS h5 h6
  simp only [show (0 : Word) ≠ 51 by decide, show (47 : Word) ≠ 51 by decide, ite_true,
    ite_false] at hp1 hp3 hp5
  have e0 : (pinEq).run a = .ok (decI w1, a) := hp1
  have e47 : (pinQuot).run a = .ok (decI w3, a) := hp3
  have e51 : (pinQuotMk).run a = .ok (decI w5, a) := hp5
  simp only [ConRon.Arena.quotPredsOk, StateT.run_bind, e0, exb, e47, e51, exm, StateT.run_pure]
  cases k <;> simp [ConLeche.QuotKind.slot, quotPredsOkW.k_env_find_3, Except.bind, StateT.run_pure,
      hf1, hf3, hf5] at h ⊢ <;>
    first
    | (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    | (split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; refine ⟨rfl, ?_⟩; show Except.ok _ = Except.ok _; simp_all))
    | skip

end L.Ind
