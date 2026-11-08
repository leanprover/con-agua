module

import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclValRef
public import ConAgua.Arena.DeclCanonEq
public import ConAgua.Rom.CIReadSpec
import all ConAgua.Arena.DeclArms

@[expose] public section

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
  sorry

/-- **`matches_pin(q, pin)` refines `IConstantVal.matchesPin`** (sorry-free). -/
@[refines ConRon.Arena.IConstantVal.matchesPin]
theorem matchesPin_refines (p : Prog) (hC : CanonProg p)
    (hp : p.lookup "matches_pin" = some matchesPinL) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q pin : Word) (cv cv' : IConstantVal) :
    RefAM p "matches_pin" [q, pin]
      (fun m a => StageR vis fe m a ∧ decCV (erA m) q.toNat = some cv ∧
        decCV (erA m) pin.toNat = some cv')
      (cv.matchesPin cv') (KeepPost vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, h1, h2⟩
  refine triple_post (mp_specW p hC hp n s₀ q pin) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, hrun, hd⟩ := mpW_ok (a := a₀) hm hS.iw.erSize h1 h2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres, hmem]
  exact ⟨hS, IWGrow.refl _, by rw [← hmem]; exact hd⟩

/-! ## The kind word of a decoded constant record -/

/-- A record of kind word `0` is an `axiomInfo`, any other kind word is not. -/
theorem decCI_kind0 {a : Array Word} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI (aread a) p = some ci) (hw : a[p]? = some w) :
    (w = 0 → ∃ cv, decCV (aread a) (p + 1) = some cv ∧ ci = .axiomInfo cv) ∧
      (w ≠ 0 → ∀ cv, ci ≠ .axiomInfo cv) := by
  sorry

/-- A record of kind word `3` is an `indInfo`, any other kind word is not. -/
theorem decCI_kind3 {a : Array Word} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI (aread a) p = some ci) (hw : a[p]? = some w) :
    (w = 3 → ∃ cv caps, decCV (aread a) (p + 1) = some cv ∧ ci = .indInfo cv caps) ∧
      (w ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  sorry

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `reduce_stored_ok(vis, c)`.** -/
def rsoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => rsoK1 p n c (envFindW m c vis)
-/

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis c q : Word) (r1 r2 : List Word)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem rsoW_step : rsoW p (n + 1) m vis c = rsoK1 p n c (envFindW m c vis) := by
  sorry

-/
theorem rsoK1_some : rsoK1 p n c (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 0 then some ([0], m1)
    else rsoK2 (r1.tail.headD 0) (callW p n "reduce_op_cv_a" [c] m1) := rfl
theorem rsoK2_some : rsoK2 q (some (r2, m2)) = mpW m2 (q + 1) (r2.headD 0) := rfl
end arms

-- ronsync2 stage 2: grind_pattern [ind_grind] rsoW_step => rsoW p (n + 1) m vis c
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
  rom : L.Rom.RomRefs p

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem rso_specW (h : RedProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_stored_ok" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rsoW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  sorry

-/

end rso

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`reduce_stored_ok(vis, c)` refines `reduceStoredOk`** at the model level. -/
theorem rsoW_ok {p : Prog} (h : RedProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    (hW : rsoW p n m vis c = some (r, m')) (hS : StageR vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ b a', (reduceStoredOk fe (decI c)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  sorry

-/

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`reduce_stored_ok(vis, c)` refines `reduceStoredOk`** (through `rom_cv`'s stub). -/
@[refines ConRon.Arena.reduceStoredOk]
theorem reduceStoredOk_refines (p : Prog) (h : RedProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (c : Word) (hc : c.toNat < 2 ^ 32) :
    RefAM p "reduce_stored_ok" [vis, c] (StageR vis fe) (reduceStoredOk fe (decI c))
      (KeepPost vis fe decW0B) := by
  sorry

-- RS2E

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `Bool`: after the pin. -/
def reoB1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => reoB2 p n (envFindW m2 (r2.headD 0) vis)
-/

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `Nat`: after the pin. -/
def reoN1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => reoN2 p n (envFindW m2 (r2.headD 0) vis)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- After the `reduceNat` pin. -/
def reoK1 (n : Nat) (vis c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if c = r1.headD 0 then reoN1 p n vis (pinAtW m1 1) else reoB1 p n vis (pinAtW m1 29)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `reduce_elem_ok(vis, c)`.** -/
def reoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => reoK1 p n vis c (pinAtW m 43)
-/

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (vis c q : Word) (r1 r2 r3 r4 : List Word)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem reoW_step : reoW p (n + 1) m vis c = reoK1 p n vis c (pinAtW m 43) := by
  sorry

-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem reoK1_some : reoK1 p n vis c (some (r1, m1)) =
    if c = r1.headD 0 then reoN1 p n vis (pinAtW m1 1) else reoB1 p n vis (pinAtW m1 29) := by
  sorry

-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem reoN1_some : reoN1 p n vis (some (r2, m2)) = reoN2 p n (envFindW m2 (r2.headD 0) vis) := by
  sorry

-/
theorem reoN2_some : reoN2 p n (some (r3, m3)) = reoN3 r3 (callW p n "rom_ci" [1] m3) := rfl
theorem reoN3_some : reoN3 r3 (some (r4, m4)) =
    if r3.headD 0 = 0 then some ([0], m4)
    else some ([if ciEqB (m4.arr64 EREC) (r3.tail.headD 0) (r4.headD 0) then 1 else 0], m4) := rfl
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem reoB1_some : reoB1 p n vis (some (r2, m2)) = reoB2 p n (envFindW m2 (r2.headD 0) vis) := by
  sorry

-/
theorem reoB2_some : reoB2 p n (some (r3, m3)) =
    if r3.headD 0 = 0 then some ([0], m3)
    else if rdW (m3.arr64 EREC) (r3.tail.headD 0) ≠ 3 then some ([0], m3)
    else reoB3 (r3.tail.headD 0) (callW p n "rom_cv" [5] m3) := rfl
theorem reoB3_some : reoB3 q (some (r4, m4)) = mpW m4 (q + 1) (r4.headD 0) := rfl
end arms

-- ronsync2 stage 2: grind_pattern [ind_grind] reoW_step => reoW p (n + 1) m vis c
-- ronsync2 stage 2: grind_pattern [ind_grind] reoK1_some => reoK1 p n vis c (some (r1, m1))
-- ronsync2 stage 2: grind_pattern [ind_grind] reoN1_some => reoN1 p n vis (some (r2, m2))
grind_pattern [ind_grind] reoN2_some => reoN2 p n (some (r3, m3))
grind_pattern [ind_grind] reoN3_some => reoN3 r3 (some (r4, m4))
-- ronsync2 stage 2: grind_pattern [ind_grind] reoB1_some => reoB1 p n vis (some (r2, m2))
grind_pattern [ind_grind] reoB2_some => reoB2 p n (some (r3, m3))
grind_pattern [ind_grind] reoB3_some => reoB3 q (some (r4, m4))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
set_option maxHeartbeats 1600000 in
theorem reo_specW (h : RedProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_elem_ok" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ reoW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  sorry

-/

end reo

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`reduce_elem_ok(vis, c)` refines `reduceElemOk`** at the model level. -/
theorem reoW_ok {p : Prog} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) (hR : L.Rom.RomRefs p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    (hW : reoW p n m vis c = some (r, m')) (hS : StageR vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ b a', (reduceElemOk fe (decI c)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  sorry

-/

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`reduce_elem_ok(vis, c)` refines `reduceElemOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.reduceElemOk]
theorem reduceElemOk_refines (p : Prog) (h : RedProg p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis : Word) (fe : IFEnv) (c : Word) (hc : c.toNat < 2 ^ 32) :
    RefAM p "reduce_elem_ok" [vis, c] (StageR vis fe) (reduceElemOk fe (decI c))
      (KeepPost vis fe decW0B) := by
  sorry

-- RS2E

end L.Arena
