import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclBasisSpec2

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
    rcases hk with ⟨-, cv, hcv, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨cv, hcv, rfl⟩
    all_goals simp at h1
  · intro h0 cv hc
    subst hc
    rcases hk with ⟨h1, -⟩ | ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, -, h2⟩ | ⟨-, _, _, -, -, h2⟩ |
      ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, _, _, _, _, _, -, -, -, -, -, -, h2⟩
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
    rcases hk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, cv, caps, hcv, -, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · simp at h1
    · simp at h1
    · simp at h1
    · exact ⟨cv, caps, hcv, rfl⟩
    all_goals simp at h1
  · intro h0 cv caps hc
    subst hc
    rcases hk with ⟨-, _, -, h2⟩ | ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, -, h2⟩ | ⟨h1, -⟩ |
      ⟨-, _, _, _, -, -, -, h2⟩ | ⟨-, _, _, _, _, _, _, -, -, -, -, -, -, h2⟩
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
  rom : L.Rom.RomRefs p

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
  rcases h1 : envFindW m c vis with _ | ⟨r1, m1⟩ <;> simp only [h1, rsoK1, reduceCtorEq] at hW
  by_cases hf : r1.headD 0 = 0
  · -- a miss
    rw [if_pos hf] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
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
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
    have hne := hkn hk
    simp only [reduceStoredOk, hfind, hci]
    cases ci with
    | axiomInfo cv => exact absurd rfl (hne cv)
    | _ => rfl
  rw [if_neg hk] at hW
  obtain ⟨cvR, hcvR, rfl⟩ := hk0 (by simpa using hk)
  -- the pinned type
  rcases h2 : callW p n "reduce_op_cv_a" [c] m1 with _ | ⟨r2, m2⟩ <;> simp only [h2, rsoK2, reduceCtorEq] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hd2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (reduceOpCvA_refines p h.pa n ⟨m1, Locals.init []⟩ a dn fe vis c hS hc h.rom h.ocv) h2
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

/-! ## `reduce_elem_ok(vis, c)` -/

section reo
variable (p : Prog)

/-- `Bool`: after `rom_cv(5)`, the comparison. -/
def reoB3 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => mpW m4 (q + 1) (r4.headD 0)

/-- `Bool`: after the lookup. -/
def reoB2 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0], m3)
    else if rdW (m3.arr64 EREC) (r3.tail.headD 0) ≠ 3 then some ([0], m3)
    else reoB3 (r3.tail.headD 0) (callW p n "rom_cv" [5] m3)

/-- `Bool`: after the pin. -/
def reoB1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => reoB2 p n (envFindW m2 (r2.headD 0) vis)

/-- `Nat`: after `rom_ci(1)`, the comparison (a miss answers `0`). -/
def reoN3 (r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r3.headD 0 = 0 then some ([0], m4)
    else some ([if ciEqB (m4.arr64 EREC) (r3.tail.headD 0) (r4.headD 0) then 1 else 0], m4)

/-- `Nat`: after the lookup. -/
def reoN2 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => reoN3 r3 (callW p n "rom_ci" [1] m3)

/-- `Nat`: after the pin. -/
def reoN1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => reoN2 p n (envFindW m2 (r2.headD 0) vis)

/-- After the `reduceNat` pin. -/
def reoK1 (n : Nat) (vis c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if c = r1.headD 0 then reoN1 p n vis (pinAtW m1 1) else reoB1 p n vis (pinAtW m1 29)

/-- **The model of `reduce_elem_ok(vis, c)`.** -/
def reoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => reoK1 p n vis c (pinAtW m 43)

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (vis c q : Word) (r1 r2 r3 r4 : List Word)
theorem reoW_step : reoW p (n + 1) m vis c = reoK1 p n vis c (pinAtW m 43) := rfl
theorem reoK1_some : reoK1 p n vis c (some (r1, m1)) =
    if c = r1.headD 0 then reoN1 p n vis (pinAtW m1 1) else reoB1 p n vis (pinAtW m1 29) := rfl
theorem reoN1_some : reoN1 p n vis (some (r2, m2)) = reoN2 p n (envFindW m2 (r2.headD 0) vis) := rfl
theorem reoN2_some : reoN2 p n (some (r3, m3)) = reoN3 r3 (callW p n "rom_ci" [1] m3) := rfl
theorem reoN3_some : reoN3 r3 (some (r4, m4)) =
    if r3.headD 0 = 0 then some ([0], m4)
    else some ([if ciEqB (m4.arr64 EREC) (r3.tail.headD 0) (r4.headD 0) then 1 else 0], m4) := rfl
theorem reoB1_some : reoB1 p n vis (some (r2, m2)) = reoB2 p n (envFindW m2 (r2.headD 0) vis) := rfl
theorem reoB2_some : reoB2 p n (some (r3, m3)) =
    if r3.headD 0 = 0 then some ([0], m3)
    else if rdW (m3.arr64 EREC) (r3.tail.headD 0) ≠ 3 then some ([0], m3)
    else reoB3 (r3.tail.headD 0) (callW p n "rom_cv" [5] m3) := rfl
theorem reoB3_some : reoB3 q (some (r4, m4)) = mpW m4 (q + 1) (r4.headD 0) := rfl
end arms

grind_pattern [ind_grind] reoW_step => reoW p (n + 1) m vis c
grind_pattern [ind_grind] reoK1_some => reoK1 p n vis c (some (r1, m1))
grind_pattern [ind_grind] reoN1_some => reoN1 p n vis (some (r2, m2))
grind_pattern [ind_grind] reoN2_some => reoN2 p n (some (r3, m3))
grind_pattern [ind_grind] reoN3_some => reoN3 r3 (some (r4, m4))
grind_pattern [ind_grind] reoB1_some => reoB1 p n vis (some (r2, m2))
grind_pattern [ind_grind] reoB2_some => reoB2 p n (some (r3, m3))
grind_pattern [ind_grind] reoB3_some => reoB3 q (some (r4, m4))

set_option maxHeartbeats 1600000 in
theorem reo_specW (h : RedProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_elem_ok" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ reoW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.reo]
  simp only [callFn, reduceElemOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pinAt_specW p h.pa n,
        envFind_specW p h.ih.ix h.ih.rowGet h.ih.find n, callW_spec p n "rom_ci",
        callW_spec p n "rom_cv", ciEq_spec' p h.canon n, mp_specW p h.canon h.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end reo

/-- **`reduce_elem_ok(vis, c)` refines `reduceElemOk`** at the model level. -/
theorem reoW_ok {p : Prog} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) (hR : L.Rom.RomRefs p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    (hW : reoW p n m vis c = some (r, m')) (hS : StageR dn vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ b a', (reduceElemOk fe (decI c)).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [reoW] at hW
  | succ n =>
  rw [reoW_step] at hW
  rcases h1 : pinAtW m 43 with _ | ⟨r1, m1⟩ <;> simp only [h1, reoK1, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.1.pins
  have e1 : r1.headD 0 = pinW m (1 + (43 : Word).toNat) := by rw [hr1]; rfl
  have hbeq : ((decI c : NIdx) == decI (pinW m (1 + (43 : Word).toNat))) =
      decide (c = pinW m (1 + (43 : Word).toNat)) := decI_beq c _ hc hl1
  have hsz := hS.2.2.2.2.1
  by_cases he : c = r1.headD 0
  · -- `reduceNat`: the pinned `Nat` basis
    rw [if_pos he, hm1] at hW
    rw [e1] at he
    rcases h2 : pinAtW m 1 with _ | ⟨r2, m2⟩ <;> simp only [h2, reoN1, reduceCtorEq] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok h2 hS.1.pins
    rw [hm2, hr2] at hW
    simp only [List.headD_cons] at hW
    rcases h3 : envFindW m (pinW m (1 + (1 : Word).toNat)) vis with _ | ⟨r3, m3⟩ <;> simp only [h3, reoN2, reduceCtorEq] at hW
    rcases h4 : callW p n "rom_ci" [1] m3 with _ | ⟨r4, m4⟩ <;> simp only [h4, reoN3, reduceCtorEq] at hW
    have hfm3 : m3 = m := by
      unfold envFindW at h3; split at h3 <;> (try split at h3) <;> (try split at h3) <;>
        simp_all
    subst hfm3
    obtain ⟨na, a4, hrun4, hS4, hg4, hna⟩ := hR.ci dn vis fe 1 (by decide) n _ a r4 m4 hS h4
    have hrun4' : ConRon.Arena.natA.run a = .ok (na, a4) := hrun4
    have htwin : (reduceElemOk fe (decI c)).run a =
        .ok (fe.find? (decI (pinW m3 (1 + (1 : Word).toNat))) == some na, a4) := by
      simp only [reduceElemOk, reduceNatName, pinReduceNat, StateT.run_bind,
        show PIN_REDUCE_NAT = (43 : Word).toNat from rfl, hrun1, exc_ok_bind', hbeq, he,
        decide_true, if_true, pinNat, show PIN_NAT = (1 : Word).toNat from rfl, hrun2, hrun4',
        beq_self_eq_true]
      rfl
    by_cases hf : r3.headD 0 = 0
    · rw [if_pos hf] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨-, hfind⟩ := envFindW_miss h3 hS.1.env hl2 hf
      refine ⟨false, a4, by rw [htwin, hfind]; rfl, hS4, hg4, by simp [decW0B]⟩
    rw [if_neg hf] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨-, hptr, hfind, htag, hrc⟩ := envFindW_hit h3 hS.1.env hl2 hf
    obtain ⟨ci, hci⟩ := envR_row_dec hS.1.env _ hl2 htag hrc
    have hci4 : decCI (erA m4) dn (r3.tail.headD 0).toNat = some ci := by
      rw [hptr]; exact ArrExt.decCI (IWGrow.erecExt hg4) hci
    have hq := ciEqB_ok hdn hS4.2.2.2.2.1 hci4 (decRCI_get hna)
    rw [hq]
    refine ⟨decide (ci = na), a4, ?_, hS4, hg4, ?_⟩
    · rw [htwin, hfind, hci]
      by_cases e : ci = na <;> simp [e]
    · by_cases e : ci = na <;> simp [e, decW0B]
  · -- `reduceBool`: a standard `Bool`
    rw [if_neg he, hm1] at hW
    rw [e1] at he
    rcases h2 : pinAtW m 29 with _ | ⟨r2, m2⟩ <;> simp only [h2, reoB1, reduceCtorEq] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok h2 hS.1.pins
    rw [hm2, hr2] at hW
    simp only [List.headD_cons] at hW
    have hpre : (reduceElemOk fe (decI c)).run a =
        (match fe.find? (decI (pinW m (1 + (29 : Word).toNat))) with
          | some (.indInfo cvB _) => do cvB.matchesPin (← boolCvA)
          | _ => pure false : AM Bool).run a := by
      simp only [reduceElemOk, reduceNatName, pinReduceNat, StateT.run_bind,
        show PIN_REDUCE_NAT = (43 : Word).toNat from rfl, hrun1, exc_ok_bind', hbeq, he,
        decide_false, Bool.false_eq_true, if_false, boolName, pinBool,
        show PIN_BOOL = (29 : Word).toNat from rfl, hrun2]
      rfl
    rcases h3 : envFindW m (pinW m (1 + (29 : Word).toNat)) vis with _ | ⟨r3, m3⟩ <;> simp only [h3, reoB2, reduceCtorEq] at hW
    by_cases hf : r3.headD 0 = 0
    · rw [if_pos hf] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨rfl, hfind⟩ := envFindW_miss h3 hS.1.env hl2 hf
      refine ⟨false, a, by rw [hpre, hfind]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    rw [if_neg hf] at hW
    obtain ⟨rfl, hptr, hfind, htag, hrc⟩ := envFindW_hit h3 hS.1.env hl2 hf
    obtain ⟨ci, hci⟩ := envR_row_dec hS.1.env _ hl2 htag hrc
    rw [hptr] at hW
    generalize hq : rowP m3 (pinW m3 (1 + (29 : Word).toNat)) = q at hW hci hfind
    obtain ⟨wk, hwk⟩ : ∃ wk, (erecP m3)[q.toNat]? = some wk := by
      obtain ⟨wk, e, -⟩ := ciD hci; exact ⟨wk, e⟩
    have ek : rdW (m3.arr64 EREC) q = wk := rdW_of_get? rfl (erecP_get hwk)
    rw [ek] at hW
    obtain ⟨hk3, hkn⟩ := decCI_kind3 hci hwk
    by_cases hk : wk ≠ 3
    · rw [if_pos hk] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
      rw [hpre, hfind, hci]
      have hne := hkn hk
      cases ci with
      | indInfo cv caps => exact absurd rfl (hne cv caps)
      | _ => rfl
    rw [if_neg hk] at hW
    obtain ⟨cvB, caps, hcvB, rfl⟩ := hk3 (by simpa using hk)
    rcases h4 : callW p n "rom_cv" [5] m3 with _ | ⟨r4, m4⟩ <;> simp only [h4, reoB3, reduceCtorEq] at hW
    obtain ⟨pin, a4, hrun4, hS4, hg4, hpin⟩ := hR.cv dn vis fe 5 (by decide) n _ a r4 m4 hS h4
    have hrun4' : boolCvA.run a = .ok (pin, a4) := hrun4
    have hq1b : q.toNat + 1 < 2 ^ 64 := by
      obtain ⟨w, hw, -, -⟩ := decCV_typeW hcvB
      have := erecP_bound hw hS.2; omega
    have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 hq1b
    have hcvB4 : decCV (erA m4) (q + 1).toNat = some cvB := by
      rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt hg4) hcvB
    obtain ⟨hm5, hrun5, hd5⟩ := mpW_ok (a := a4) hW hS4.2.2.2.2.1 hcvB4
      (DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ hpin)
    subst hm5
    refine ⟨_, _, ?_, hS4, hg4, hd5⟩
    rw [hpre, hfind, hci]
    simp only [StateT.run_bind, hrun4', exc_ok_bind']
    exact hrun5

/-- **`reduce_elem_ok(vis, c)` refines `reduceElemOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.reduceElemOk]
theorem reduceElemOk_refines (p : Prog) (h : RedProg p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis : Word) (fe : IFEnv) (c : Word) (hc : c.toNat < 2 ^ 32) :
    RefAM p "reduce_elem_ok" [vis, c] (StageR dn vis fe) (reduceElemOk fe (decI c))
      (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ hS
  refine triple_post (reo_specW p h n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := reoW_ok hdn h.rom hm hS hc
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
