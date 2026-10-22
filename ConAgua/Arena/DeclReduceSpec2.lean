import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.DeclCanonEq

/-!
# `matchesPin`, `reduceStoredOk`, `reduceElemOk` (lane `decls3`)

The comparisons with the pins: `matches_pin` is `cv_eq` (helper `decls3-canon`'s word-level
comparison, `cvEqB_ok`), and the two environment shapes of the reduce operations read the
environment (`env_find`: `envFindW_miss`/`envFindW_hit`) and compare with a ROM value. Through the
ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

theorem matchesPin_eq (cv pin : IConstantVal) : cv.matchesPin pin = pure (decide (cv = pin)) := by
  cases cv; cases pin
  simp only [IConstantVal.matchesPin, IConstantVal.mk.injEq]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

/-! ## `matches_pin(q, pin)` -/

/-- **The model of `matches_pin`**: `cv_eq`'s word-level comparison; the memory unchanged. -/
def mpW (m : Mem) (q pin : Word) : Option (List Word × Mem) :=
  some ([if cvEqB (m.arr64 EREC) q pin then 1 else 0], m)

theorem mp_specW (p : Prog) (hC : CanonProg p) (hp : p.lookup "matches_pin" = some matchesPinL)
    (n : Nat) (s₀ : St) (q pin : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "matches_pin" [q, pin]
    ⦃fun r s' => LocEq s' s₀ ∧ mpW s₀.mem q pin = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, matchesPinL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, cvEq_spec' p hC n] <;>
      finish [mpW]

theorem mpW_ok {m m' : Mem} {a : AState} {q pin : Word} {r : List Word} {cv cv' : IConstantVal}
    (h : mpW m q pin = some (r, m')) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h1 : decCV (erA m) q.toNat = some cv) (h2 : decCV (erA m) pin.toNat = some cv') :
    m' = m ∧ (cv.matchesPin cv').run a = .ok (decide (cv = cv'), a) ∧
      decW0B m' r (decide (cv = cv')) := by
  simp only [mpW, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [cvEqB_ok hsz h1 h2, matchesPin_eq]
  refine ⟨rfl, rfl, ?_⟩
  by_cases e : cv = cv' <;> simp [e, decW0B]

/-- **`matches_pin(q, pin)` refines `IConstantVal.matchesPin`** (sorry-free). -/
@[refines ConRon.Arena.IConstantVal.matchesPin]
theorem matchesPin_refines (p : Prog) (hC : CanonProg p)
    (hp : p.lookup "matches_pin" = some matchesPinL) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q pin : Word) (cv cv' : IConstantVal) :
    RefAM p "matches_pin" [q, pin]
      (fun m a => StageR dn vis fe m a ∧ decCV (erA m) q.toNat = some cv ∧
        decCV (erA m) pin.toNat = some cv')
      (cv.matchesPin cv') (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, h1, h2⟩
  refine triple_post (mp_specW p hC hp n s₀ q pin) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, hrun, hd⟩ := mpW_ok (a := a₀) hm hS.2.2.2.2.1 h1 h2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres, hmem]
  exact ⟨hS, IWGrow.refl _, by rw [← hmem]; exact hd⟩

/-! ## The kind word of a decoded constant record -/

/-- A record of kind word `0` is an `axiomInfo`, any other kind word is not. -/
theorem decCI_kind0 {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI a dn p = some ci) (hw : a[p]? = some w) :
    (w = 0 → ∃ cv, decCV a (p + 1) = some cv ∧ ci = .axiomInfo cv) ∧
      (w ≠ 0 → ∀ cv, ci ≠ .axiomInfo cv) := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rw [hw] at e; cases e
  constructor
  · intro h0
    subst h0
    rcases hk with ⟨-, cv, hcv, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨cv, hcv, rfl⟩
    all_goals simp at h1
  · intro h0 cv hc
    subst hc
    rcases hk with ⟨h1, -⟩ | ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, -, h2⟩ | ⟨-, _, _, -, -, h2⟩ |
      ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, _, _, _, _, _, -, -, -, -, -, -, h2⟩ | ⟨-, _, -, h2⟩
    · exact h0 (UInt64.toNat_inj.mp (by simpa using h1))
    all_goals cases h2

/-- A record of kind word `3` is an `indInfo`, any other kind word is not. -/
theorem decCI_kind3 {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI a dn p = some ci) (hw : a[p]? = some w) :
    (w = 3 → ∃ cv caps, decCV a (p + 1) = some cv ∧ ci = .indInfo cv caps) ∧
      (w ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rw [hw] at e; cases e
  constructor
  · intro h0
    subst h0
    rcases hk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, cv, caps, hcv, -, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩
    · simp at h1
    · simp at h1
    · simp at h1
    · exact ⟨cv, caps, hcv, rfl⟩
    all_goals simp at h1
  · intro h0 cv caps hc
    subst hc
    rcases hk with ⟨-, _, -, h2⟩ | ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, -, h2⟩ | ⟨h1, -⟩ |
      ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, _, _, _, _, _, -, -, -, -, -, -, h2⟩ | ⟨-, _, -, h2⟩
    · cases h2
    · cases h2
    · cases h2
    · exact h0 (UInt64.toNat_inj.mp (by simpa using h1))
    all_goals cases h2

/-! ## `reduce_stored_ok(vis, c)` -/

section rso
variable (p : Prog)

/-- After `reduce_op_cv_a`: the comparison. -/
def rsoK2 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => mpW m2 (q + 1) (r2.headD 0)

/-- After the lookup: a miss or another kind answers `0`. -/
def rsoK1 (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 0 then some ([0], m1)
    else rsoK2 (r1.tail.headD 0) (callW p n "reduce_op_cv_a" [c] m1)

/-- **The model of `reduce_stored_ok(vis, c)`.** -/
def rsoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => rsoK1 p n c (envFindW m c vis)

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis c q : Word) (r1 r2 : List Word)
theorem rsoW_step : rsoW p (n + 1) m vis c = rsoK1 p n c (envFindW m c vis) := rfl
theorem rsoK1_some : rsoK1 p n c (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 0 then some ([0], m1)
    else rsoK2 (r1.tail.headD 0) (callW p n "reduce_op_cv_a" [c] m1) := rfl
theorem rsoK2_some : rsoK2 q (some (r2, m2)) = mpW m2 (q + 1) (r2.headD 0) := rfl
end arms

grind_pattern [ind_grind] rsoW_step => rsoW p (n + 1) m vis c
grind_pattern [ind_grind] rsoK1_some => rsoK1 p n c (some (r1, m1))
grind_pattern [ind_grind] rsoK2_some => rsoK2 q (some (r2, m2))

/-- The lookups of the reduce operations' environment shapes. -/
structure RedProg (p : Prog) : Prop where
  canon : CanonProg p
  mp : p.lookup "matches_pin" = some matchesPinL
  rso : p.lookup "reduce_stored_ok" = some reduceStoredOkL
  reo : p.lookup "reduce_elem_ok" = some reduceElemOkL
  ocv : p.lookup "reduce_op_cv_a" = some reduceOpCvAL
  pa : p.lookup "pin_at" = some pinAtL
  ih : IhProg p

theorem rso_specW (h : RedProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_stored_ok" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rsoW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rso]
  simp only [callFn, reduceStoredOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.ih.ix h.ih.rowGet h.ih.find n, callW_spec p n "reduce_op_cv_a",
        mp_specW p h.canon h.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end rso

/-- **`reduce_stored_ok(vis, c)` refines `reduceStoredOk`** at the model level. -/
theorem rsoW_ok {p : Prog} (h : RedProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    (hW : rsoW p n m vis c = some (r, m')) (hS : StageR dn vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ b a', (reduceStoredOk fe (decI c)).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [rsoW] at hW
  | succ n =>
  rw [rsoW_step] at hW
  cases h1 : envFindW m c vis with
  | none => rw [h1] at hW; cases hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, rsoK1_some] at hW
  by_cases hf : r1.headD 0 = 0
  · -- a miss
    rw [if_pos hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hc hf
    refine ⟨false, a, by simp [reduceStoredOk, hfind]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  rw [if_neg hf] at hW
  obtain ⟨rfl, hptr, hfind, htag, hrc⟩ := envFindW_hit h1 hS.1.env hc hf
  obtain ⟨ci, hci⟩ := envR_row_dec hS.1.env c hc htag hrc
  rw [hptr] at hW
  generalize hq : rowP m1 c = q at hW hci hfind
  have hsz := hS.2.2.2.2.1
  obtain ⟨wk, hwk⟩ : ∃ wk, (erecP m1)[q.toNat]? = some wk := by
    obtain ⟨wk, e, -⟩ := ciD hci; exact ⟨wk, e⟩
  have ek : rdW (m1.arr64 EREC) q = wk := rdW_of_get? rfl (erecP_get hwk)
  rw [ek] at hW
  obtain ⟨hk0, hkn⟩ := decCI_kind0 hci hwk
  by_cases hk : wk ≠ 0
  · -- another kind
    rw [if_pos hk] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
    have hne := hkn hk
    simp only [reduceStoredOk, hfind, hci]
    cases ci with
    | axiomInfo cv => exact absurd rfl (hne cv)
    | _ => rfl
  rw [if_neg hk] at hW
  obtain ⟨cvR, hcvR, rfl⟩ := hk0 (by simpa using hk)
  -- the pinned type
  cases h2 : callW p n "reduce_op_cv_a" [c] m1 with
  | none => rw [h2] at hW; cases hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, rsoK2_some] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hd2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (reduceOpCvA_refines p h.pa n ⟨m1, Locals.init []⟩ a dn fe vis c hS hc h.ocv) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  have hpin := DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ hd2
  have hq1b : q.toNat + 1 < 2 ^ 64 := by
    obtain ⟨w, hw, -, -⟩ := decCV_typeW hcvR
    have := erecP_bound hw hS.2; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 hq1b
  have hcvR2 : decCV (erA s2.mem) (q + 1).toNat = some cvR := by
    rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt hg2) hcvR
  obtain ⟨hm3, hrun3, hd3⟩ := mpW_ok (a := AM.st (reduceOpCvA (decI c)) a) hW hS2.2.2.2.2.1 hcvR2 hpin
  subst hm3
  refine ⟨_, _, ?_, hS2, hg2, hd3⟩
  simp only [reduceStoredOk, hfind, hci, StateT.run_bind, hrun2, exc_ok_bind']
  exact hrun3

/-- **`reduce_stored_ok(vis, c)` refines `reduceStoredOk`** (through `rom_cv`'s stub). -/
@[refines ConRon.Arena.reduceStoredOk]
theorem reduceStoredOk_refines (p : Prog) (h : RedProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (c : Word) (hc : c.toNat < 2 ^ 32) :
    RefAM p "reduce_stored_ok" [vis, c] (StageR dn vis fe) (reduceStoredOk fe (decI c))
      (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ hS
  refine triple_post (rso_specW p h n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := rsoW_ok h hm hS hc
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
