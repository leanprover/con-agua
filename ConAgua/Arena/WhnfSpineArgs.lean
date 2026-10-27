import ConAgua.Arena.WhnfSpineRefine
import ConAgua.Arena.SimLib
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The argument walks: `app_count`, `app_fill`, `app_fill2`

`get_app_args`/`get_app_spine` walk a spine twice: once to count (and check) the `.app` nodes,
once to write the arguments (and nodes) into a new stack slice. Each walk is its own L function,
so each spec is one loop: `app_count` is `get_app_fn`'s loop (the count is the fuel spent),
`app_fill`/`app_fill2` write without checks (the count walk checked every node).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `app_count(e)`: the number of `.app` nodes on the spine -/

/-- `app_count(e)`: `get_app_fn`'s loop; the count is the fuel spent.
con-ron: ConRon/Arena/ExprOps.lean:1292-1303 ConRon.Arena.getAppArgs -/
def appCountL : FunDecl := lfn (e) locals (f, t, x) {
  f := 4000000000;
  ⟪getAppFnLoop⟫;
  if f == 0 { abort };
  return (4000000000 - f, e)
}

/-- The model of `app_count`. -/
def appCntW (m : Mem) (e : Word) : Option (Word × Word) :=
  match gafLoopW m e 4000000000 with
  | none => none
  | some (e', f') => if f' = 0 then none else some (4000000000 - f', e')

theorem appCount_spec (p : Prog) (hp : p.lookup "app_count" = some appCountL) (n : Nat)
    (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "app_count" [e]
    ⦃fun r s' => s' = s₀ ∧ appCntW s₀.mem e = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appCountL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, getAppFnLoop_step_spec p n] <;>
      finish [appCntW]

/-! ## `app_fill(e, o, n)`: the arguments into `SPN[o ‥ o + n)`, last first -/

def appFillLoop : Stmt := lblk (e, o, n, t, x) {
  while n != 0 {
    n -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    SPN.u64[o + n] := APP⟨t, x⟩.a;
    e := APP⟨t, x⟩.f
  }
}

/-- `app_fill(e, o, n)`.
con-ron: ConRon/Arena/ExprOps.lean:1292-1303 ConRon.Arena.getAppArgs -/
def appFillL : FunDecl := lfn (e, o, n) locals (t, x) {
  ⟪appFillLoop⟫;
  return 0
}

/-- The function child and the argument child of an `.app` handle word. -/
def fnW (m : Mem) (e : Word) : Word := tfld m APP (tierW e) (idxW e) 0
def argW (m : Mem) (e : Word) : Word := tfld m APP (tierW e) (idxW e) 1

/-- The fills' stack writes do not touch the `app` records (either tier). -/
theorem tfld_set64_SPN_app (m : Mem) (k v t i f : Word) :
    tfld (m.set64 SPN k v) APP t i f = tfld m APP t i f :=
  tfld_set64_ne m APP SPN k v t i f (by decide) (by decide)

/-- The model of the fill loop, by L fuel. -/
def fillW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | k + 1, m, e, o, n =>
    if n = 0 then some m
    else fillW k (m.set64 SPN (o + (n - 1)) (argW m e)) (fnW m e) o (n - 1)

theorem fillW_zero (k : Nat) (m : Mem) (e o : Word) : fillW (k + 1) m e o 0 = some m := by
  simp [fillW]

theorem fillW_succ (k : Nat) (m : Mem) (e o n : Word) (hn : n ≠ 0) :
    fillW (k + 1) m e o n =
      fillW k (m.set64 SPN (o + (n - 1)) (argW m e)) (fnW m e) o (n - 1) := by
  simp [fillW, hn]

theorem appFillLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k appFillLoop
    ⦃fun r s' => r = .normal ∧
      fillW k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := appFillLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE, st64, ih] <;>
      finish [fillW_zero, fillW_succ, fnW, argW, tierW, idxW, tfld_set64_SPN_app, tcnt]


theorem appFill_spec (p : Prog) (hp : p.lookup "app_fill" = some appFillL) (k : Nat)
    (s₀ : St) (e o c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "app_fill" [e, o, c]
    ⦃fun _ s' => fillW (k + 1) s₀.mem e o c = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appFillL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, fun s₀ => Triple.step_exec (appFillLoop_spec p (k + 1) s₀)] <;>
    finish

theorem toUInt64_succ_sub_one (j : Nat) : ((j + 1).toUInt64 - 1) = j.toUInt64 := by
  simp [Nat.toUInt64]

theorem toUInt64_ne_zero (j : Nat) (hj : j + 1 < 2 ^ 64) : (j + 1).toUInt64 ≠ 0 := by
  intro h
  have := congrArg UInt64.toNat h
  simp at this
  rw [Nat.mod_eq_of_lt hj] at this; omega

/-- A fill that succeeds had fuel for every node. -/
theorem fillW_fuel (o : Word) : ∀ (j k : Nat) (m m' : Mem) (e : Word), j < 2 ^ 64 →
    fillW k m e o j.toUInt64 = some m' → j < k := by
  intro j
  induction j with
  | zero => intro k m m' e _ h; cases k with
    | zero => simp [fillW] at h
    | succ k => omega
  | succ j ih =>
    intro k m m' e hj h
    cases k with
    | zero => simp [fillW] at h
    | succ k =>
      rw [fillW_succ k m e o _ (toUInt64_ne_zero j hj), toUInt64_succ_sub_one] at h
      have := ih k _ m' _ (by omega) h
      omega

/-! ## What the fill writes -/

/-- The argument words of the spine at `e`, `c` nodes deep, outermost last. -/
def argsW (m : Mem) : Word → Nat → List Word
  | _, 0 => []
  | e, c + 1 => argsW m (fnW m e) c ++ [argW m e]

theorem argsW_length (m : Mem) : ∀ (c : Nat) (e : Word), (argsW m e c).length = c
  | 0, _ => rfl
  | c + 1, e => by simp [argsW, argsW_length m c]

/-- The reads of a fill step do not see the stack. -/
theorem argsW_set (m : Mem) (k v : Word) : ∀ (c : Nat) (e : Word),
    argsW (m.set64 SPN k v) e c = argsW m e c
  | 0, _ => rfl
  | c + 1, e => by
    have h1 : fnW (m.set64 SPN k v) e = fnW m e := by
      simp only [fnW, tfld_set64_ne (R := APP) (a := SPN) (h := by decide) (h' := by decide)]
    have h2 : argW (m.set64 SPN k v) e = argW m e := by
      simp only [argW, tfld_set64_ne (R := APP) (a := SPN) (h := by decide) (h' := by decide)]
    simp only [argsW, h1, h2, argsW_set m k v c]

/-- **The fill writes the spine's arguments into `SPN[o ‥ o + j)`**, nothing else. -/
theorem fillW_ok (o : Word) : ∀ (j k : Nat) (m : Mem) (e : Word), j < k →
    o.toNat + j ≤ (m.arr64 SPN).size → (m.arr64 SPN).size < 2 ^ 63 →
    ∃ m', fillW k m e o j.toUInt64 = some m' ∧ MemFrame [SPN] [] m m' ∧
      (∀ i, i < j → spW m' (o + i.toUInt64) = (argsW m e j).getD i 0) ∧
      (∀ w : Word, (w.toNat < o.toNat ∨ o.toNat + j ≤ w.toNat) → spW m' w = spW m w) := by
  intro j
  induction j with
  | zero =>
    intro k m e hk _ _
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨m, by simpa using fillW_zero k' m e o, MemFrame.refl _ _ _, fun i hi => absurd hi (by omega),
      fun _ _ => rfl⟩
  | succ j ih =>
    intro k m e hk hb hsz
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hne := toUInt64_ne_zero j (by omega)
    rw [fillW_succ k' m e o _ hne, toUInt64_succ_sub_one]
    have hoj : (o + j.toUInt64).toNat = o.toNat + j := by
      have hs : UInt64.size = 2 ^ 64 := rfl
      rw [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega)]
      try rw [hs]
      omega
    obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = m.set64 SPN (o + j.toUInt64) (argW m e) := ⟨_, rfl⟩
    rw [← hm₁]
    have hsz₁ : (m₁.arr64 SPN).size = (m.arr64 SPN).size := by rw [hm₁]; exact size_set64 _ _ _ _ _
    obtain ⟨m', hf, hfr, hget, hout⟩ := ih k' m₁ (fnW m e) (by omega) (by rw [hsz₁]; omega)
      (by rw [hsz₁]; exact hsz)
    have hset : spW m₁ (o + j.toUInt64) = argW m e := by
      simp only [spW, hm₁, rdW_set64]; simp [hoj]; omega
    have hoth : ∀ w : Word, w ≠ o + j.toUInt64 → spW m₁ w = spW m w := by
      intro w hw; simp only [spW, hm₁, rdW_set64]; simp [Ne.symm hw]
    refine ⟨m', hf, (hm₁ ▸ MemFrame.set64 m SPN (by decide) _ _).trans hfr, ?_, ?_⟩
    · intro i hi
      have ha : argsW m₁ (fnW m e) j = argsW m (fnW m e) j := by rw [hm₁, argsW_set]
      rw [ha] at hget
      rw [argsW]
      rcases Nat.lt_or_ge i j with h | h
      · rw [hget i h]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [argsW_length]; exact h : i < (argsW m (fnW m e) j).length)]
      · have hij : i = j := by omega
        subst hij
        rw [hout _ (Or.inr (by rw [hoj]; exact Nat.le_refl _)), hset]
        simp [List.getD_eq_getElem?_getD, argsW_length]
    · intro w hw
      rw [hout w (by omega)]
      apply hoth
      intro h; subst h; rw [hoj] at hw; omega

/-! ## `app_fill_n(e, o, n)`: the `.app` nodes into `SPN[o ‥ o + n)` -/

def appFillNLoop : Stmt := lblk (e, o, n, t, x) {
  while n != 0 {
    n -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    SPN.u64[o + n] := e;
    e := APP⟨t, x⟩.f
  }
}

/-- `app_fill_n(e, o, n)`.
con-ron: ConRon/Arena/Core.lean:2110-2124 ConRon.Arena.getAppSpineGo -/
def appFillNL : FunDecl := lfn (e, o, n) locals (t, x) {
  ⟪appFillNLoop⟫;
  return 0
}

/-- The model of the fill loop, by L fuel. -/
def fillNW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | k + 1, m, e, o, n =>
    if n = 0 then some m
    else fillNW k (m.set64 SPN (o + (n - 1)) e) (fnW m e) o (n - 1)

theorem fillNW_zero (k : Nat) (m : Mem) (e o : Word) : fillNW (k + 1) m e o 0 = some m := by
  simp [fillNW]

theorem fillNW_succ (k : Nat) (m : Mem) (e o n : Word) (hn : n ≠ 0) :
    fillNW (k + 1) m e o n =
      fillNW k (m.set64 SPN (o + (n - 1)) e) (fnW m e) o (n - 1) := by
  simp [fillNW, hn]

theorem appFillNLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k appFillNLoop
    ⦃fun r s' => r = .normal ∧
      fillNW k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := appFillNLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE, st64, ih] <;>
      finish [fillNW_zero, fillNW_succ, fnW, tierW, idxW, tfld_set64_SPN_app, tcnt]


theorem appFillN_spec (p : Prog) (hp : p.lookup "app_fill_n" = some appFillNL) (k : Nat)
    (s₀ : St) (e o c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "app_fill_n" [e, o, c]
    ⦃fun _ s' => fillNW (k + 1) s₀.mem e o c = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appFillNL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, fun s₀ => Triple.step_exec (appFillNLoop_spec p (k + 1) s₀)] <;>
    finish

/-- A fill that succeeds had fuel for every node. -/
theorem fillNW_fuel (o : Word) : ∀ (j k : Nat) (m m' : Mem) (e : Word), j < 2 ^ 64 →
    fillNW k m e o j.toUInt64 = some m' → j < k := by
  intro j
  induction j with
  | zero => intro k m m' e _ h; cases k with
    | zero => simp [fillNW] at h
    | succ k => omega
  | succ j ih =>
    intro k m m' e hj h
    cases k with
    | zero => simp [fillNW] at h
    | succ k =>
      rw [fillNW_succ k m e o _ (toUInt64_ne_zero j hj), toUInt64_succ_sub_one] at h
      have := ih k _ m' _ (by omega) h
      omega

/-- The `.app` nodes of the spine at `e`, `c` nodes deep, outermost last. -/
def nodesW (m : Mem) : Word → Nat → List Word
  | _, 0 => []
  | e, c + 1 => nodesW m (fnW m e) c ++ [e]

theorem nodesW_length (m : Mem) : ∀ (c : Nat) (e : Word), (nodesW m e c).length = c
  | 0, _ => rfl
  | c + 1, e => by simp [nodesW, nodesW_length m c]

/-- The reads of a fill step do not see the stack. -/
theorem nodesW_set (m : Mem) (k v : Word) : ∀ (c : Nat) (e : Word),
    nodesW (m.set64 SPN k v) e c = nodesW m e c
  | 0, _ => rfl
  | c + 1, e => by
    have h1 : fnW (m.set64 SPN k v) e = fnW m e := by
      simp only [fnW, tfld_set64_ne (R := APP) (a := SPN) (h := by decide) (h' := by decide)]
    simp only [nodesW, h1, nodesW_set m k v c]

/-- **The fill writes the spine's arguments into `SPN[o ‥ o + j)`**, nothing else. -/
theorem fillNW_ok (o : Word) : ∀ (j k : Nat) (m : Mem) (e : Word), j < k →
    o.toNat + j ≤ (m.arr64 SPN).size → (m.arr64 SPN).size < 2 ^ 63 →
    ∃ m', fillNW k m e o j.toUInt64 = some m' ∧ MemFrame [SPN] [] m m' ∧
      (∀ i, i < j → spW m' (o + i.toUInt64) = (nodesW m e j).getD i 0) ∧
      (∀ w : Word, (w.toNat < o.toNat ∨ o.toNat + j ≤ w.toNat) → spW m' w = spW m w) := by
  intro j
  induction j with
  | zero =>
    intro k m e hk _ _
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨m, by simpa using fillNW_zero k' m e o, MemFrame.refl _ _ _, fun i hi => absurd hi (by omega),
      fun _ _ => rfl⟩
  | succ j ih =>
    intro k m e hk hb hsz
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hne := toUInt64_ne_zero j (by omega)
    rw [fillNW_succ k' m e o _ hne, toUInt64_succ_sub_one]
    have hoj : (o + j.toUInt64).toNat = o.toNat + j := by
      have hs : UInt64.size = 2 ^ 64 := rfl
      rw [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega)]
      try rw [hs]
      omega
    obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = m.set64 SPN (o + j.toUInt64) e := ⟨_, rfl⟩
    rw [← hm₁]
    have hsz₁ : (m₁.arr64 SPN).size = (m.arr64 SPN).size := by rw [hm₁]; exact size_set64 _ _ _ _ _
    obtain ⟨m', hf, hfr, hget, hout⟩ := ih k' m₁ (fnW m e) (by omega) (by rw [hsz₁]; omega)
      (by rw [hsz₁]; exact hsz)
    have hset : spW m₁ (o + j.toUInt64) = e := by
      simp only [spW, hm₁, rdW_set64]; simp [hoj]; omega
    have hoth : ∀ w : Word, w ≠ o + j.toUInt64 → spW m₁ w = spW m w := by
      intro w hw; simp only [spW, hm₁, rdW_set64]; simp [Ne.symm hw]
    refine ⟨m', hf, (hm₁ ▸ MemFrame.set64 m SPN (by decide) _ _).trans hfr, ?_, ?_⟩
    · intro i hi
      have ha : nodesW m₁ (fnW m e) j = nodesW m (fnW m e) j := by rw [hm₁, nodesW_set]
      rw [ha] at hget
      rw [nodesW]
      rcases Nat.lt_or_ge i j with h | h
      · rw [hget i h]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [nodesW_length]; exact h : i < (nodesW m (fnW m e) j).length)]
      · have hij : i = j := by omega
        subst hij
        rw [hout _ (Or.inr (by rw [hoj]; exact Nat.le_refl _)), hset]
        simp [List.getD_eq_getElem?_getD, nodesW_length]
    · intro w hw
      rw [hout w (by omega)]
      apply hoth
      intro h; subst h; rw [hoj] at hw; omega

/-! ## The count walk refines `getAppArgs` -/

/-- A count loop at fuel zero ends with fuel zero. -/
theorem gafLoopW_f0 {m : Mem} {e e' f' : Word} (hL : gafLoopW m e 0 = some (e', f')) : f' = 0 := by
  by_cases hc : e >>> 28 = 4
  · rw [gafLoopW] at hL; simp [hc] at hL
  · rw [gafLoopW_done m e 0 hc] at hL
    exact (Prod.mk.inj (Option.some.inj hL)).2.symm

/-- **One step of the count loop at an `app` node**: the guards pass and the loop goes on at the
function. -/
theorem gafLoopW_app {m : Mem} {e f e' f' : Word} (hL : gafLoopW m e f = some (e', f'))
    (hc : e >>> 28 = 4) :
    f.toNat ≠ 0 ∧ ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧
      idxW e < tcnt m APP (tierW e) ∧ gafLoopW m (fnW m e) (f - 1) = some (e', f') ∧
      (f - 1).toNat = f.toNat - 1 := by
  have hf0 : f ≠ 0 := by
    intro hf0; rw [hf0, gafLoopW] at hL; simp [hc] at hL
  have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
    rw [gafLoopW] at hL
    simp only [hc, ↓reduceIte, hf0] at hL
    by_cases hv : (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)
    · simp [hv] at hL
    · exact hv
  have hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e := by
    rw [gafLoopW] at hL
    simp only [hc, ↓reduceIte, hf0, hv1] at hL
    by_cases hv : tcnt m APP (tierW e) ≤ idxW e
    · simp [hv] at hL
    · exact hv
  have hf0' : f.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h))
  refine ⟨hf0', hv1, UInt64.not_le.mp hv2, ?_, ?_⟩
  · rw [fnW, ← gafLoopW_step m e f _ hc hf0 hv1 hv2 rfl]; exact hL
  · rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp

/-- **The count loop's run refines `getAppArgs`**: when `gafLoopW` from `(e, f)` ends at
`(e', f')` with `f' ≠ 0`, the twin's walk at fuel `f` returns the `f - f'` argument words. -/
theorem gaaTwin (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (e f e' f' : Word), f.toNat ≤ N → e.toNat < 2 ^ 32 →
      gafLoopW m e f = some (e', f') → f' ≠ 0 →
      (getAppArgs f.toNat (decE e)).run a =
        .ok ((argsW m e (f.toNat - f'.toNat)).map decE, a) ∧
      (∀ w ∈ argsW m e (f.toNat - f'.toNat), w.toNat < 2 ^ 32) ∧ f'.toNat ≤ f.toNat := by
  intro N
  induction N with
  | zero =>
    intro e f e' f' hfN he hL hf'
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    exact absurd (gafLoopW_f0 hL) hf'
  | succ N ih =>
    intro e f e' f' hfN he hL hf'
    by_cases hc : e >>> 28 = 4
    · obtain ⟨hf0', hv1, hcnt, hL', hfm1⟩ := gafLoopW_app hL hc
      have hfm1N : (f - 1).toNat ≤ N := by rw [hfm1]; omega
      have hva := viewApp_ok m a hR e he ⟨hv1, hcnt⟩
      have hb := view_app m a hR e he ⟨hv1, hcnt⟩ hc
      obtain ⟨ihr, ihw, ihle⟩ := ih _ (f - 1) e' f' hfm1N hb.2.1 hL' hf'
      rw [hfm1] at ihr ihw ihle
      have hc' : f.toNat - f'.toNat = (f.toNat - 1 - f'.toNat) + 1 := by omega
      have heq : getAppArgs f.toNat (decE e) = getAppArgs ((f.toNat - 1) + 1) (decE e) := by
        congr 1; omega
      refine ⟨?_, ?_, by omega⟩
      · rw [heq, getAppArgs, (decE_tag_app e he).mpr hc, hc', argsW]
        try simp only [fnW] at ihr
        simp only [fnW]
        simp [StateT.run_bind, viewApp_run' _ a, hva, except_ok_bind, ihr, argW]
        rfl
      · rw [hc', argsW]
        intro w hw
        rcases List.mem_append.mp hw with h | h
        · exact ihw w (by simpa [fnW] using h)
        · simp at h; subst h; exact hb.2.2
    · rw [gafLoopW_done m e f hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hf' (UInt64.toNat_inj.mp (by simpa using h)))
      refine ⟨?_, by simp [argsW], Nat.le_refl _⟩
      rw [Nat.sub_self, hk, getAppArgs]
      have htag : (decE e).tag ≠ ETag.app := fun h => hc ((decE_tag_app e he).mp h)
      simp [htag, argsW]
      rfl

/-- **The count loop's run refines `getAppSpineGo`**: the head `e'`, the `f - f'` argument words
and the `.app` nodes. -/
theorem gasTwin (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (e f e' f' : Word), f.toNat ≤ N → e.toNat < 2 ^ 32 →
      gafLoopW m e f = some (e', f') → f' ≠ 0 →
      (getAppSpineGo f.toNat (decE e)).run a =
        .ok ((decE e', ((argsW m e (f.toNat - f'.toNat)).map decE).toArray,
          ((nodesW m e (f.toNat - f'.toNat)).map decE).toArray), a) ∧
      (∀ w ∈ nodesW m e (f.toNat - f'.toNat), w.toNat < 2 ^ 32) ∧ e'.toNat < 2 ^ 32 := by
  intro N
  induction N with
  | zero =>
    intro e f e' f' hfN he hL hf'
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    exact absurd (gafLoopW_f0 hL) hf'
  | succ N ih =>
    intro e f e' f' hfN he hL hf'
    by_cases hc : e >>> 28 = 4
    · obtain ⟨hf0', hv1, hcnt, hL', hfm1⟩ := gafLoopW_app hL hc
      have hfm1N : (f - 1).toNat ≤ N := by rw [hfm1]; omega
      have hva := viewApp_ok m a hR e he ⟨hv1, hcnt⟩
      have hb := view_app m a hR e he ⟨hv1, hcnt⟩ hc
      obtain ⟨ihr, ihw, ihe⟩ := ih _ (f - 1) e' f' hfm1N hb.2.1 hL' hf'
      rw [hfm1] at ihr ihw
      have hle : f'.toNat ≤ f.toNat - 1 := by
        have := (gaaTwin m a hR _ _ (f - 1) e' f' (Nat.le_refl _) hb.2.1 hL' hf').2.2
        rw [hfm1] at this; exact this
      have hc' : f.toNat - f'.toNat = (f.toNat - 1 - f'.toNat) + 1 := by omega
      have heq : getAppSpineGo f.toNat (decE e) = getAppSpineGo ((f.toNat - 1) + 1) (decE e) := by
        congr 1; omega
      refine ⟨?_, ?_, ihe⟩
      · rw [heq, getAppSpineGo, (decE_tag_app e he).mpr hc, hc', argsW, nodesW]
        try simp only [fnW] at ihr
        simp only [fnW]
        simp [StateT.run_bind, viewApp_run' _ a, hva, except_ok_bind, ihr, argW]
        simp [Functor.map, Except.map]
      · rw [hc', nodesW]
        intro w hw
        rcases List.mem_append.mp hw with h | h
        · exact ihw w (by simpa [fnW] using h)
        · simp at h; subst h; exact he
    · rw [gafLoopW_done m e f hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hf' (UInt64.toNat_inj.mp (by simpa using h)))
      refine ⟨?_, by simp [nodesW], he⟩
      rw [Nat.sub_self, hk, getAppSpineGo]
      have htag : (decE e).tag ≠ ETag.app := fun h => hc ((decE_tag_app e he).mp h)
      simp [htag, argsW, nodesW]
      rfl

/-! ## `get_app_args(e)`: count, check room, fill, push -/

/-- con-ron: ConRon/Arena/ExprOps.lean:1292-1303 ConRon.Arena.getAppArgs -/
@[l_impl ConRon.Arena.getAppArgs]
def getAppArgsL : FunDecl := lfn (e) locals (n, o, z) {
  n := call app_count(e);
  o := CTL.u64[136];
  if len(SPN.u64) < o { abort };
  if len(SPN.u64) - o < n { abort };
  z := call app_fill(e, o, n);
  CTL.u64[136] := o + n;
  return (o, n)
}

/-- The model of `get_app_args`. -/
def gaaW (p : Prog) (n : Nat) (m : Mem) (e : Word) : Option (Word × Word × Mem) :=
  match callW p n "app_count" [e] m with
  | none => none
  | some (r₁, m₁) =>
    if m₁.len64 SPN < rdW (m₁.arr64 CTL) 136 then none
    else if m₁.len64 SPN - rdW (m₁.arr64 CTL) 136 < r₁.headD 0 then none
    else match callW p n "app_fill" [e, rdW (m₁.arr64 CTL) 136, r₁.headD 0] m₁ with
    | none => none
    | some (_, m₂) =>
      some (rdW (m₁.arr64 CTL) 136, r₁.headD 0,
        m₂.set64 CTL 136 (rdW (m₁.arr64 CTL) 136 + r₁.headD 0))

theorem gaa_spec (p : Prog) (hp : p.lookup "get_app_args" = some getAppArgsL) (n : Nat)
    (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "get_app_args" [e]
    ⦃fun r s' => LocEq s' s₀ ∧
      gaaW p n s₀.mem e = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppArgsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "app_count", callW_spec p n "app_fill"] <;>
    finish [gaaW]

/-- **`get_app_args` refines `getAppArgs coreWalkFuel`**: the arguments are a new slice at the
old top. The helper behind `WhnfSpine.lean`'s `getAppArgs_refines`. -/
theorem getAppArgs_refines' (p : Prog) (hg : p.lookup "get_app_args" = some getAppArgsL)
    (hc : p.lookup "app_count" = some appCountL) (hf : p.lookup "app_fill" = some appFillL)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word) (he : HW e)
    (hspn : (s₀.mem.arr64 SPN).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_args" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      r.headD 0 = spTop s₀.mem ∧ spTop s'.mem = spTop s₀.mem + r.tail.headD 0 ∧
      ∃ xs, (getAppArgs coreWalkFuel (decE e)).run a₀ = .ok (xs, a₀) ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  obtain ⟨hloc, hcall⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec p n "get_app_args" [e] s)
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨t, ht, -, hW, h136⟩ := triple_of_callW (gaa_spec p hg n s e) hcall
  rw [ht] at hW h136
  refine ⟨hloc, ?_⟩
  simp only [gaaW] at hW
  rcases h1 : callW p n "app_count" [e] s.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [h1, reduceCtorEq] at hW
  cases n with
  | zero => rw [callW_zero] at h1; cases h1
  | succ n' =>
  obtain ⟨t₁, ht₁, ht₁s, hcnt⟩ := triple_of_callW (appCount_spec p hc (n' + 1) s e) h1
  have hm₁ : m₁ = s.mem := by rw [← ht₁, ht₁s]
  subst hm₁
  try rw [ht₁s] at hcnt
  -- the count
  simp only [appCntW] at hcnt
  rcases hL : gafLoopW s.mem e 4000000000 with _ | ⟨e', f'⟩ <;> simp only [hL, reduceCtorEq] at hcnt
  by_cases hf0 : f' = 0
  · simp [hf0] at hcnt
  simp only [hf0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hcnt
  obtain ⟨hcnt, -⟩ := hcnt
  obtain ⟨hrun', hlt, hle⟩ := gaaTwin s.mem a₀ hR _ e 4000000000 e' f' (Nat.le_refl _) he hL hf0
  have hfuel : (4000000000 : Word).toNat = coreWalkFuel := by simp [UInt64.toNat_ofNat, coreWalkFuel]
  rw [hfuel] at hrun' hlt hle
  -- the count word is the number of arguments
  have hcw : (r₁.headD 0).toNat = coreWalkFuel - f'.toNat := by
    have hle' : f' ≤ 4000000000 := by
      rw [UInt64.le_iff_toNat_le, hfuel]; exact hle
    rw [← hcnt, UInt64.toNat_sub_of_le _ _ hle', hfuel]
  -- the room checks
  have hlen : s.mem.len64 SPN = ((s.mem.arr64 SPN).size : Nat).toUInt64 := rfl
  obtain ⟨hk1, hW⟩ := of_ite_none hW
  obtain ⟨hk2, hW⟩ := of_ite_none hW
  have hszl : ((s.mem.arr64 SPN).size : Nat).toUInt64.toNat = (s.mem.arr64 SPN).size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega : (s.mem.arr64 SPN).size < 2 ^ 64)]
  have hroom : (rdW (s.mem.arr64 CTL) 136).toNat + (r₁.headD 0).toNat ≤ (s.mem.arr64 SPN).size := by
    rw [hlen] at hk1 hk2
    have a1 := UInt64.not_lt.mp hk1
    have a2 := UInt64.not_lt.mp hk2
    rw [UInt64.le_iff_toNat_le, hszl] at a1
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hk1), hszl] at a2
    omega
  rcases h2 : callW p (n' + 1) "app_fill" [e, rdW (s.mem.arr64 CTL) 136, r₁.headD 0] s.mem with _ | ⟨r₂, m₂⟩ <;>
    simp only [h2, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  obtain ⟨t₂, ht₂, hfill⟩ := triple_of_callW (appFill_spec p hf n' s e _ _) h2
  rw [ht₂] at hfill
  -- the fill, at the count as a `Nat`
  have hcN : r₁.headD 0 = (coreWalkFuel - f'.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp; rw [hcw]; simp [Nat.toUInt64]
    exact (Nat.mod_eq_of_lt (by simp [coreWalkFuel]; omega)).symm
  rw [hcN] at hfill
  have hfu := fillW_fuel _ _ _ _ _ _ (by simp [coreWalkFuel]; omega) hfill
  obtain ⟨m', hf', hfr, hget, hout⟩ := fillW_ok (rdW (s.mem.arr64 CTL) 136) (coreWalkFuel - f'.toNat)
    (n' + 1) s.mem e hfu (by rw [← hcw]; exact hroom) hspn
  rw [hf'] at hfill
  cases hfill
  -- the post
  have hsp : ∀ w : Word, spW s'.mem w = spW m₂ w := by
    intro w; rw [← hm]; simp only [spW]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hszs : (s'.mem.arr64 SPN).size = (s.mem.arr64 SPN).size := by
    rw [← hm, size_set64]; exact hfr.2.2.1 SPN
  have hctl136 : (136 : Word).toNat < (m₂.arr64 CTL).size := by
    rw [← hm, size_set64] at h136; exact h136
  have htop' : spTop s'.mem = rdW (s.mem.arr64 CTL) 136 + r₁.headD 0 := by
    rw [← hm]; simp only [spTop]; rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hctl136⟩]
  have hcN' : (r₁.headD 0).toNat = coreWalkFuel - f'.toNat := hcw
  have hadd : (rdW (s.mem.arr64 CTL) 136 + r₁.headD 0).toNat =
      (rdW (s.mem.arr64 CTL) 136).toNat + (r₁.headD 0).toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?hf, StackGrew.of_spnFrame ?hf ?_ ?_, ?_, ?_, ?_⟩
  · rw [← hm]
    exact (hfr.mono (fun b hb => hb) (fun x hx => by simp at hx)).trans
      ((MemFrame.setCtl m₂ 136 _).mono (fun b hb => by simp at hb) (fun x hx => hx))
  · rw [htop', UInt64.le_iff_toNat_le, hadd]; simp only [spTop]; omega
  · intro i hi
    rw [hsp, hout i (Or.inl (by simpa [spTop, UInt64.lt_iff_toNat_lt] using hi))]
  · rw [← hr0]; rfl
  · rw [htop', ← hr1]; rfl
  · refine ⟨_, hrun', ?_⟩
    rw [← hr0, ← hr1]
    refine ⟨by simp only [List.size_toArray, List.length_map, argsW_length]; exact hcN'.symm,
      by rw [hszs]; exact hroom, ?_, ?_⟩
    · intro i hi
      rw [hcN'] at hi
      rw [hsp, hget i hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [argsW_length]; exact hi)]
      exact hlt _ (List.getElem_mem _)
    · intro i hi
      simp only [List.size_toArray, List.length_map, argsW_length] at hi
      have hi' : i < (argsW s.mem e (coreWalkFuel - f'.toNat)).length := by rw [argsW_length]; exact hi
      rw [hsp, hget i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      simp

/-! ## `get_app_spine(e)`: count (and head), check room, two fills, push -/

theorem nodesW_congr {m m' : Mem} (h : m'.arr64 AREC = m.arr64 AREC)
    (h' : m'.arr64 (tier1 AREC) = m.arr64 (tier1 AREC)) :
    ∀ (c : Nat) (e : Word), nodesW m' e c = nodesW m e c
  | 0, _ => rfl
  | c + 1, e => by simp only [nodesW, fnW, nodesW_congr h h' c, tfld_arr_eq (R := APP) h h']

/-- con-ron: ConRon/Arena/Core.lean:2126-2129 ConRon.Arena.getAppSpine
con-ron: ConRon/Arena/Core.lean:2110-2124 ConRon.Arena.getAppSpineGo -/
@[l_impl ConRon.Arena.getAppSpine ConRon.Arena.getAppSpineGo]
def getAppSpineL : FunDecl := lfn (e) locals (n, h, o, z) {
  (n, h) := call app_count(e);
  o := CTL.u64[136];
  if len(SPN.u64) < o { abort };
  if (len(SPN.u64) - o) >> 1 < n { abort };
  z := call app_fill(e, o, n);
  z := call app_fill_n(e, o + n, n);
  CTL.u64[136] := o + n + n;
  return (h, o, n)
}

/-- The model of `get_app_spine`. -/
def gasW (p : Prog) (n : Nat) (m : Mem) (e : Word) : Option (Word × Word × Word × Mem) :=
  match callW p n "app_count" [e] m with
  | none => none
  | some (r₁, m₁) =>
    if m₁.len64 SPN < rdW (m₁.arr64 CTL) 136 then none
    else if (m₁.len64 SPN - rdW (m₁.arr64 CTL) 136) >>> 1 < r₁.headD 0 then none
    else match callW p n "app_fill" [e, rdW (m₁.arr64 CTL) 136, r₁.headD 0] m₁ with
    | none => none
    | some (_, m₂) =>
      match callW p n "app_fill_n" [e, rdW (m₁.arr64 CTL) 136 + r₁.headD 0, r₁.headD 0] m₂ with
      | none => none
      | some (_, m₃) =>
        some (r₁.tail.headD 0, rdW (m₁.arr64 CTL) 136, r₁.headD 0,
          m₃.set64 CTL 136 (rdW (m₁.arr64 CTL) 136 + r₁.headD 0 + r₁.headD 0))

theorem gas_spec (p : Prog) (hp : p.lookup "get_app_spine" = some getAppSpineL) (n : Nat)
    (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "get_app_spine" [e]
    ⦃fun r s' => LocEq s' s₀ ∧
      gasW p n s₀.mem e = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppSpineL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "app_count", callW_spec p n "app_fill", callW_spec p n "app_fill_n"] <;>
    finish [gasW]

/-- **`get_app_spine` refines `getAppSpine coreWalkFuel`**: the head, then the arguments and the
`.app` nodes as two slices of the same length at the old top. -/
theorem getAppSpine_refines' (p : Prog) (hg : p.lookup "get_app_spine" = some getAppSpineL)
    (hc : p.lookup "app_count" = some appCountL) (hf : p.lookup "app_fill" = some appFillL)
    (hfn : p.lookup "app_fill_n" = some appFillNL)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word) (he : HW e)
    (hspn : (s₀.mem.arr64 SPN).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_spine" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      HW (r.headD 0) ∧ r.tail.headD 0 = spTop s₀.mem ∧
      spTop s'.mem = spTop s₀.mem + r.tail.tail.headD 0 + r.tail.tail.headD 0 ∧
      ∃ xs ns, (getAppSpine coreWalkFuel (decE e)).run a₀ = .ok ((decE (r.headD 0), xs, ns), a₀) ∧
        SpineR s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) xs ∧
        SpineR s'.mem (r.tail.headD 0 + r.tail.tail.headD 0) (r.tail.tail.headD 0) ns; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  obtain ⟨hloc, hcall⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec p n "get_app_spine" [e] s)
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨t, ht, -, hW, h136⟩ := triple_of_callW (gas_spec p hg n s e) hcall
  rw [ht] at hW h136
  refine ⟨hloc, ?_⟩
  simp only [gasW] at hW
  rcases h1 : callW p n "app_count" [e] s.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [h1, reduceCtorEq] at hW
  cases n with
  | zero => rw [callW_zero] at h1; cases h1
  | succ n' =>
  obtain ⟨t₁, ht₁, ht₁s, hcnt⟩ := triple_of_callW (appCount_spec p hc (n' + 1) s e) h1
  have hm₁ : m₁ = s.mem := by rw [← ht₁, ht₁s]
  subst hm₁
  try rw [ht₁s] at hcnt
  simp only [appCntW] at hcnt
  rcases hL : gafLoopW s.mem e 4000000000 with _ | ⟨e', f'⟩ <;> simp only [hL, reduceCtorEq] at hcnt
  by_cases hf0 : f' = 0
  · simp [hf0] at hcnt
  simp only [hf0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hcnt
  obtain ⟨hcnt, hhd⟩ := hcnt
  obtain ⟨-, hlt, hle⟩ := gaaTwin s.mem a₀ hR _ e 4000000000 e' f' (Nat.le_refl _) he hL hf0
  obtain ⟨hrun', hltn, he'⟩ := gasTwin s.mem a₀ hR _ e 4000000000 e' f' (Nat.le_refl _) he hL hf0
  have hfuel : (4000000000 : Word).toNat = coreWalkFuel := by simp [UInt64.toNat_ofNat, coreWalkFuel]
  rw [hfuel] at hrun' hlt hle hltn
  have hcw : (r₁.headD 0).toNat = coreWalkFuel - f'.toNat := by
    have hle' : f' ≤ 4000000000 := by
      rw [UInt64.le_iff_toNat_le, hfuel]; exact hle
    rw [← hcnt, UInt64.toNat_sub_of_le _ _ hle', hfuel]
  -- the room checks
  have hlen : s.mem.len64 SPN = ((s.mem.arr64 SPN).size : Nat).toUInt64 := rfl
  obtain ⟨hk1, hW⟩ := of_ite_none hW
  obtain ⟨hk2, hW⟩ := of_ite_none hW
  have hszl : ((s.mem.arr64 SPN).size : Nat).toUInt64.toNat = (s.mem.arr64 SPN).size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega : (s.mem.arr64 SPN).size < 2 ^ 64)]
  have hroom : (rdW (s.mem.arr64 CTL) 136).toNat + (r₁.headD 0).toNat + (r₁.headD 0).toNat ≤
      (s.mem.arr64 SPN).size := by
    rw [hlen] at hk1 hk2
    have a1 := UInt64.not_lt.mp hk1
    have a2 := UInt64.not_lt.mp hk2
    rw [UInt64.le_iff_toNat_le, hszl] at a1
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_shiftRight, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hk1),
      hszl, Nat.shiftRight_eq_div_pow] at a2
    simp only [show (UInt64.toNat 1 % 64) = 1 from rfl, Nat.pow_one] at a2
    omega
  rcases h2 : callW p (n' + 1) "app_fill" [e, rdW (s.mem.arr64 CTL) 136, r₁.headD 0] s.mem with _ | ⟨r₂, m₂⟩ <;>
    simp only [h2, reduceCtorEq] at hW
  rcases h3 : callW p (n' + 1) "app_fill_n" [e, rdW (s.mem.arr64 CTL) 136 + r₁.headD 0, r₁.headD 0] m₂ with _ | ⟨r₃, m₃⟩ <;>
    simp only [h3, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hr2, hm⟩ := hW
  obtain ⟨t₂, ht₂, hfill⟩ := triple_of_callW (appFill_spec p hf n' s e _ _) h2
  rw [ht₂] at hfill
  obtain ⟨t₃, ht₃, hfill3⟩ := triple_of_callW (appFillN_spec p hfn n' ⟨m₂, Locals.init []⟩ e _ _) h3
  rw [ht₃] at hfill3
  have hcN : r₁.headD 0 = (coreWalkFuel - f'.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp; rw [hcw]; simp [Nat.toUInt64]
    exact (Nat.mod_eq_of_lt (by simp [coreWalkFuel]; omega)).symm
  rw [hcN] at hfill hfill3
  have hfu := fillW_fuel _ _ _ _ _ _ (by simp [coreWalkFuel]; omega) hfill
  obtain ⟨m', hf', hfr, hget, hout⟩ := fillW_ok (rdW (s.mem.arr64 CTL) 136) (coreWalkFuel - f'.toNat)
    (n' + 1) s.mem e hfu (by rw [← hcw]; omega) hspn
  rw [hf'] at hfill
  cases hfill
  have hadd : (rdW (s.mem.arr64 CTL) 136 + r₁.headD 0).toNat =
      (rdW (s.mem.arr64 CTL) 136).toNat + (r₁.headD 0).toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hsz2 : (m₂.arr64 SPN).size = (s.mem.arr64 SPN).size := hfr.2.2.1 SPN
  have hfu3 := fillNW_fuel _ _ _ _ _ _ (by simp [coreWalkFuel]; omega) hfill3
  rw [← hcN] at hfill3
  obtain ⟨m'', hf'', hfr3, hget3, hout3⟩ := fillNW_ok (rdW (s.mem.arr64 CTL) 136 + r₁.headD 0)
    (coreWalkFuel - f'.toNat) (n' + 1) m₂ e hfu3 (by rw [hsz2, hadd, ← hcw]; omega) (by rw [hsz2]; exact hspn)
  rw [hcN] at hf''
  rw [hcN] at hfill3
  rw [hf''] at hfill3
  cases hfill3
  have harec : m₂.arr64 AREC = s.mem.arr64 AREC := hfr.1 AREC (by decide) (by decide)
  have harec' : m₂.arr64 (tier1 AREC) = s.mem.arr64 (tier1 AREC) :=
    hfr.1 (tier1 AREC) (by decide) (by decide)
  -- the post
  have hsp : ∀ w : Word, spW s'.mem w = spW m₃ w := by
    intro w; rw [← hm]; simp only [spW]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hszs : (s'.mem.arr64 SPN).size = (s.mem.arr64 SPN).size := by
    rw [← hm, size_set64]; rw [hfr3.2.2.1 SPN]; exact hsz2
  have hctl136 : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    rw [← hm, size_set64] at h136; exact h136
  have htop' : spTop s'.mem = rdW (s.mem.arr64 CTL) 136 + r₁.headD 0 + r₁.headD 0 := by
    rw [← hm]; simp only [spTop]; rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hctl136⟩]
  have hadd2 : (rdW (s.mem.arr64 CTL) 136 + r₁.headD 0 + r₁.headD 0).toNat =
      (rdW (s.mem.arr64 CTL) 136).toNat + (r₁.headD 0).toNat + (r₁.headD 0).toNat := by
    rw [UInt64.toNat_add, hadd]; exact Nat.mod_eq_of_lt (by omega)
  have hcN' : (r₁.headD 0).toNat = coreWalkFuel - f'.toNat := hcw
  -- the argument slice survives the node fill
  have hargs : ∀ i, i < coreWalkFuel - f'.toNat →
      spW s'.mem (rdW (s.mem.arr64 CTL) 136 + i.toUInt64) =
        (argsW s.mem e (coreWalkFuel - f'.toNat)).getD i 0 := by
    intro i hi
    have hcwf : coreWalkFuel = 4000000000 := rfl
    have h64 : UInt64.size = 2 ^ 64 := rfl
    have hoi : (rdW (s.mem.arr64 CTL) 136 + i.toUInt64).toNat = (rdW (s.mem.arr64 CTL) 136).toNat + i := by
      rw [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsp, hout3 _ (Or.inl (by rw [hoi, hadd]; omega)), hget i hi]
  have hnodes : ∀ i, i < coreWalkFuel - f'.toNat →
      spW s'.mem (rdW (s.mem.arr64 CTL) 136 + r₁.headD 0 + i.toUInt64) =
        (nodesW s.mem e (coreWalkFuel - f'.toNat)).getD i 0 := by
    intro i hi
    rw [hsp, hget3 i hi, nodesW_congr harec harec']
  refine ⟨?hf, StackGrew.of_spnFrame ?hf ?_ ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hm]
    exact ((hfr.mono (fun b hb => hb) (fun x hx => by simp at hx)).trans
      (hfr3.mono (fun b hb => hb) (fun x hx => by simp at hx))).trans
      ((MemFrame.setCtl m₃ 136 _).mono (fun b hb => by simp at hb) (fun x hx => hx))
  · rw [htop', UInt64.le_iff_toNat_le, hadd2]; simp only [spTop]; omega
  · intro i hi
    have hi' : i.toNat < (rdW (s.mem.arr64 CTL) 136).toNat := by
      simpa [spTop, UInt64.lt_iff_toNat_lt] using hi
    have hlt3 : i.toNat < (rdW (s.mem.arr64 CTL) 136 + r₁.headD 0).toNat := by
      rw [hadd]; exact Nat.lt_of_lt_of_le hi' (Nat.le_add_right _ _)
    rw [hsp, hout3 i (Or.inl hlt3), hout i (Or.inl hi')]
  · rw [← hr0, ← hhd]; exact he'
  · rw [← hr1]; rfl
  · rw [htop', ← hr2]; rfl
  · refine ⟨((argsW s.mem e (coreWalkFuel - f'.toNat)).map decE).toArray,
      ((nodesW s.mem e (coreWalkFuel - f'.toNat)).map decE).toArray, ?_, ?_, ?_⟩
    · rw [← hr0, ← hhd]; exact hrun'
    · rw [← hr1, ← hr2]
      refine ⟨by simp only [List.size_toArray, List.length_map, argsW_length]; exact hcN'.symm,
        by rw [hszs]; omega, ?_, ?_⟩
      · intro i hi
        rw [hcN'] at hi
        rw [hargs i hi, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [argsW_length]; exact hi)]
        exact hlt _ (List.getElem_mem _)
      · intro i hi
        simp only [List.size_toArray, List.length_map, argsW_length] at hi
        have hi' : i < (argsW s.mem e (coreWalkFuel - f'.toNat)).length := by rw [argsW_length]; exact hi
        rw [hargs i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
        simp
    · rw [← hr1, ← hr2]
      refine ⟨by simp only [List.size_toArray, List.length_map, nodesW_length]; exact hcN'.symm,
        by rw [hszs, hadd]; omega, ?_, ?_⟩
      · intro i hi
        rw [hcN'] at hi
        rw [hnodes i hi, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [nodesW_length]; exact hi)]
        exact hltn _ (List.getElem_mem _)
      · intro i hi
        simp only [List.size_toArray, List.length_map, nodesW_length] at hi
        have hi' : i < (nodesW s.mem e (coreWalkFuel - f'.toNat)).length := by
          rw [nodesW_length]; exact hi
        rw [hnodes i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
        simp

/-! ## `head_and_args(v)` -/

/-- con-ron: ConRon/Arena/Core.lean:2131-2139 ConRon.Arena.headAndArgs -/
@[l_impl ConRon.Arena.headAndArgs]
def headAndArgsL : FunDecl := lfn (v) locals (h, o, n) {
  if v >> 28 == 4 {
    h := call get_app_fn(v);
    (o, n) := call get_app_args(v);
    return (h, o, n)
  };
  return (v, CTL.u64[136], 0)
}

/-- The model of `head_and_args`. -/
def haaW (p : Prog) (n : Nat) (m : Mem) (v : Word) : Option (Word × Word × Word × Mem) :=
  if v >>> 28 = 4 then
    match callW p n "get_app_fn" [v] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "get_app_args" [v] m₁ with
      | none => none
      | some (r₂, m₂) => some (r₁.headD 0, r₂.headD 0, r₂.tail.headD 0, m₂)
  else some (v, rdW (m.arr64 CTL) 136, 0, m)

theorem haa_spec (p : Prog) (hp : p.lookup "head_and_args" = some headAndArgsL) (n : Nat)
    (s₀ : St) (v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "head_and_args" [v]
    ⦃fun r s' => LocEq s' s₀ ∧
      haaW p n s₀.mem v = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, headAndArgsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_fn", callW_spec p n "get_app_args"] <;>
    finish [haaW]

/-- **`head_and_args` refines `headAndArgs`.** -/
theorem headAndArgs_refines' (p : Prog) (hh : p.lookup "head_and_args" = some headAndArgsL)
    (hfn : p.lookup "get_app_fn" = some getAppFnL) (hg : p.lookup "get_app_args" = some getAppArgsL)
    (hc : p.lookup "app_count" = some appCountL) (hf : p.lookup "app_fill" = some appFillL)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (v : Word) (hv : HW v)
    (hspn : (s₀.mem.arr64 SPN).size < 2 ^ 63) (htop : (spTop s₀.mem).toNat ≤ (s₀.mem.arr64 SPN).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "head_and_args" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      HW (r.headD 0) ∧ r.tail.headD 0 = spTop s₀.mem ∧
      spTop s'.mem = spTop s₀.mem + r.tail.tail.headD 0 ∧
      ∃ xs, (headAndArgs (decE v)).run a₀ = .ok ((decE (r.headD 0), xs), a₀) ∧
        SpineR s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) xs; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  obtain ⟨hloc, hcall⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec p n "head_and_args" [v] s)
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (haa_spec p hh n s v) hcall
  rw [ht] at hW
  refine ⟨hloc, ?_⟩
  simp only [haaW] at hW
  by_cases h4 : v >>> 28 = 4
  · rw [ite_eq_left h4] at hW
    rcases h1 : callW p n "get_app_fn" [v] s.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [h1, reduceCtorEq] at hW
    rcases h2 : callW p n "get_app_args" [v] m₁ with _ | ⟨r₂, m₂⟩ <;>
      simp only [h2, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hr2, hm⟩ := hW
    obtain ⟨t₁, ht₁, hm₁, -, hhw, hfnrun⟩ := triple_of_callW (getAppFn_refines' p hfn n s a₀ hR v hv) h1
    rw [ht₁] at hm₁
    subst hm₁
    obtain ⟨t₂, ht₂, -, hfr, hgrow, ho, htop, xs, hxs, hsr⟩ :=
      triple_of_callW (getAppArgs_refines' p hg hc hf n s a₀ hR v hv hspn) h2
    rw [ht₂] at hfr hgrow htop hsr
    subst hm
    refine ⟨hfr, hgrow, by rw [← hr0]; exact hhw, by rw [← hr1]; exact ho,
      by rw [← hr2]; exact htop, xs.toArray, ?_, by rw [← hr1, ← hr2]; exact hsr⟩
    have htag : (decE v).tag = ETag.app := (decE_tag_app v hv).mpr h4
    rw [← hr0]
    simp [headAndArgs, htag, StateT.run_bind, hfnrun, except_ok_bind]
    simp only [StateT.run] at hxs ⊢
    simp only [hxs]
    rfl
  · rw [ite_eq_right h4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hr2, hm⟩ := hW
    rw [← hm]
    refine ⟨MemFrame.refl _ _ _, StackGrew.refl _,
      by rw [← hr0]; exact hv, by rw [← hr1]; rfl, by rw [← hr2]; simp, #[], ?_, ?_⟩
    · have htag : (decE v).tag ≠ ETag.app := fun h => h4 ((decE_tag_app v hv).mp h)
      rw [← hr0]; simp [headAndArgs, htag]; rfl
    · rw [← hr2]
      exact ⟨rfl, by rw [← hr1]; simpa [spTop] using htop, fun i hi => absurd hi (by simp),
        fun i hi => absurd hi (by simp)⟩

end L.Arena
