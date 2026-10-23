import ConAgua.Arena.DeclValSpec

/-!
# `checkDecl`'s value checks: the relational lemmas (lane `decls3`)

A model run of `check_constant_val`/`check_defn_val`/`check_thm_val`/`check_opaque_val` from the
stage relation is a successful twin run (`ccvW_ok`, `dvW_ok`, `tvW_ok`), and the census theorems
(`checkConstantVal_refines`, …) assemble them with the `vcgen` specs of `DeclValSpec.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- The value checks' common tail: the value's guards, its type against the declared one, the
push of `ci` (`msg` the twin's error text, never reached on a successful run). -/
def dvT (fe : IFEnv) (cv : IConstantVal) (v : EIdx) (ci : IConstantInfo) (msg : String) :
    AM IFEnv := do
  installValueGuards fe cv v
  let vtype ← inferTypeCore V fe checkFuel 0 v
  unless ← isDefEqCore V fe checkFuel 0 vtype cv.type do
    fail (.invalid msg)
  pure (fe.push ci)

theorem checkDefnVal_dvT (fe : IFEnv) (cv : IConstantVal) (v : EIdx)
    (h : ConLeche.ReducibilityHint) :
    checkDefnVal V fe cv v h = dvT fe cv v (.defnInfo cv v h) "type mismatch in definition" := rfl

theorem checkOpaqueVal_dvT (fe : IFEnv) (cv : IConstantVal) (v : EIdx) :
    checkOpaqueVal V fe cv v = dvT fe cv v (.axiomInfo cv) "type mismatch in opaque" := rfl

theorem checkThmVal_eq (fe : IFEnv) (cv : IConstantVal) (v : EIdx) :
    checkThmVal V fe cv v = (do
      let stype ← inferTypeCore V fe checkFuel 0 cv.type
      let u ← ensureSortCore V fe checkFuel 0 stype
      let z ← zeroLevel
      unless ← liftFueled "level comparison" (← lvlEq? u z) do
        fail (.invalid "type of theorem is not a proposition")
      dvT fe cv v (.thmInfo cv) "type mismatch in theorem") := by
  simp only [checkThmVal, dvT, bind_assoc]

theorem toNat_add_small (c : Word) (k : Nat) (h : c.toNat + k < 2 ^ 64) :
    (c + UInt64.ofNat k).toNat = c.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega

/-- A decoding in `erecP` is below the record pool's size, so offsets from it do not wrap. -/
theorem erecP_bound {m : Mem} {i : Nat} {w : Word} (h : (erecP m)[i]? = some w) (hS : IWOK m) :
    i < 2 ^ 64 := by
  have := (Array.getElem?_eq_some_iff.mp (erecP_get h)).1
  have := hS.2.2.2.1
  omega

/-! ## `check_constant_val` -/

/-- **`check_constant_val` refines `checkConstantVal .verified`** at the model level. -/
theorem ccvW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : ccvW stubCall n m vis q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    ∃ a', (checkConstantVal V fe cv).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (k := q.toNat + 3) (toNat_add_small q 3 hqb).symm (erecP_get hwt)
  cases n with
  | zero => simp [ccvW] at h
  | succ n =>
  rw [ccvW_step, et] at h
  cases h1 : ihW stubCall n m vis q with
  | none => rw [h1] at h; simp [ccvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ccvK1_some] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ := ihW_ok h1 hS hq hqb
  cases h2 : stubCall n "infer_type_core" [vis, 0, wt] m1 with
  | none => rw [h2] at h; simp [ccvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ccvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    inferTypeCore_spec dn vis fe 0 wt hwtl m1 m2 a1 r2 h2 hS1
  cases h3 : stubCall n "ensure_sort_core" [vis, 0, r2.headD 0] m2 with
  | none => rw [h3] at h; simp [ccvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ccvK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, -⟩ :=
    ensureSortCore_spec dn vis fe 0 (r2.headD 0) hx2l m2 m3 a2 r3 h3 hS2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00, ← hty] at hrun2
  rw [h00, hx2] at hrun3
  refine ⟨a3, ?_, hS3, hg1.trans (hg2.trans hg3)⟩
  rw [checkConstantVal_eq]
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, hrun3, StateT.run_pure]
  rfl

/-! ## `check_defn_val`, `check_opaque_val` -/

/-- **The value checks' common tail** at the model level, from the memory after the guards' start:
a `dvK1` run (after `install_value_guards`, from the twin's run of it) is the rest of `dvT`. -/
theorem dvK1_ok {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} {m1 m' : Mem} {c wv wt : Word} {r : List Word} {cv : IConstantVal}
    {ci : IConstantInfo} {a1 : AState} {r1 : List Word} (msg : String)
    (h : dvK1 p stubCall n vis c wv wt (some (r1, m1)) = some (r, m')) (hS1 : StageR dn vis fe m1 a1)
    (hci : decCI (erecP m1) dn c.toNat = some ci) (hcb : c.toNat + 5 < 2 ^ 64)
    (hwv : wv.toNat < 2 ^ 32) (hwt : wt.toNat < 2 ^ 32) (hty : cv.type = decI wt) :
    ∃ a', (do
        let vtype ← inferTypeCore V fe checkFuel 0 (decI wv)
        unless ← isDefEqCore V fe checkFuel 0 vtype cv.type do
          fail (.invalid msg)
        pure (fe.push ci) : AM IFEnv).run a1 = .ok (fe.push ci, a') ∧
      StageR dn (r.headD 0) (fe.push ci) m' a' ∧ IWGrow m1 m' := by
  rw [dvK1_some] at h
  cases h2 : stubCall n "infer_type_core" [vis, 0, wv] m1 with
  | none => rw [h2] at h; simp [dvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, dvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    inferTypeCore_spec dn vis fe 0 wv hwv m1 m2 a1 r2 h2 hS1
  cases h3 : stubCall n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with
  | none => rw [h3] at h; simp [dvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, dvK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    isDefEqCore_spec dn vis fe 0 (r2.headD 0) wt hx2l hwt m2 m3 a2 r3 h3 hS2
  by_cases hb3 : r3.headD 0 = 0
  · rw [if_pos hb3] at h; simp at h
  rw [if_neg hb3] at h
  have ex3 : x3 = true := by rw [← hx3]; simpa using hb3
  -- the push
  have hx13 : ArrExt (erecP m1) (erecP m3) := IWGrow.erecPExt (hg2.trans hg3)
  have hci3 := ArrExt.decCI hx13 hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have hw : (rdW (m3.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  cases h4 : callW p n "env_push" [vis, c] m3 with
  | none => rw [h4] at h; simp [dvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, dvK4_some] at h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPush_specW p hRp n ⟨m3, Locals.init []⟩ vis c hw) h4
  subst hs4
  obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3 hci3
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun2
  rw [h00, hx2, ← hty] at hrun3
  refine ⟨a3, ?_, by simpa using hS4, hg2.trans (hg3.trans hg4)⟩
  simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, ex3, if_true, StateT.run_pure]
  rfl

/-- **`check_defn_val`/`check_opaque_val` refine `dvT`** at the model level (the record `c`
decodes to the constant `ci` the twin pushes, with constant value `cv` at `c + 1` and value `v` at
`c + 5`). -/
theorem dvW_ok {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx} {ci : IConstantInfo} (msg : String)
    (h : dvW p stubCall n m vis c = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v) :
    ∃ a', (dvT fe cv v ci msg).run a = .ok (fe.push ci, a') ∧
      StageR dn (r.headD 0) (fe.push ci) m' a' ∧ IWGrow m m' := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  cases n with
  | zero => simp [dvW] at h
  | succ n =>
  rw [dvW_step, ev, et] at h
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases h1 : ivgW stubCall n m vis (c + 1) wv with
  | none => rw [h1] at h; simp [dvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ :=
    ivgW_ok h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv) (by rw [hc1]; omega) hwvl
  obtain ⟨a', hrun', hS', hg'⟩ := dvK1_ok hRp msg h hS1
    (ArrExt.decCI (IWGrow.erecPExt hg1) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hg1.trans hg'⟩
  simp only [dvT, StateT.run_bind, hrun1, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

end L.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_thm_val` -/

/-- **`check_thm_val` refines `checkThmVal .verified`** at the model level. -/
theorem tvW_ok {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx}
    (h : tvW p stubCall n m vis c = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some (.thmInfo cv))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v) :
    ∃ a', (checkThmVal V fe cv v).run a = .ok (fe.push (.thmInfo cv), a') ∧
      StageR dn (r.headD 0) (fe.push (.thmInfo cv)) m' a' ∧ IWGrow m m' := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have h00 : (0 : Word).toNat = 0 := rfl
  cases n with
  | zero => simp [tvW] at h
  | succ n =>
  rw [tvW_step, ev, et] at h
  -- the type's type and sort
  cases h1 : stubCall n "infer_type_core" [vis, 0, wt] m with
  | none => rw [h1] at h; simp [tvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, tvK1_some] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ :=
    inferTypeCore_spec dn vis fe 0 wt hwtl m m1 a r1 h1 hS
  cases h2 : stubCall n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | none => rw [h2] at h; simp [tvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, tvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    ensureSortCore_spec dn vis fe 0 (r1.headD 0) hx1l m1 m2 a1 r2 h2 hS1
  -- the zero level
  cases h3 : pinWordW m2 53 with
  | none => rw [h3] at h; simp [tvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, tvK3_some] at h
  have hflag : pinW m2 0 ≠ 0 := by
    intro h0; simp [pinWordW, h0] at h3
  simp only [pinWordW, hflag, if_false, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hF := hS2.1.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  simp only [List.headD_cons, hz] at h
  -- the comparison
  cases h4 : lfW stubCall n m2 (r2.headD 0) (pinW m2 53) with
  | none => rw [h4] at h; simp [tvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, tvK4_some] at h
  have h4' : lveW m2 (r2.headD 0) (pinW m2 53) = some (r4, m4) := by
    cases n with
    | zero => simp [lfW] at h4
    | succ k => exact h4
  obtain ⟨b, a4, hrun4, hS4, hg4, hr4⟩ :=
    lveW_ok dn vis fe m2 m4 a2 (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 r4 h4' hS2
  by_cases hb4 : r4.headD 0 = 0
  · rw [if_pos hb4] at h; simp at h
  rw [if_neg hb4] at h
  have hb : b = true := by
    cases b
    · exfalso; apply hb4; simpa using hr4
    · rfl
  subst hb
  -- the value's guards, then the common tail
  cases h5 : ivgW stubCall n m4 vis (c + 1) wv with
  | none => rw [h5] at h; simp [dvK1] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5] at h
  have hg14 := hg1.trans (hg2.trans hg4)
  obtain ⟨a5, hrun5, hS5, hg5⟩ :=
    ivgW_ok h5 hS4 (by rw [hc1]; exact ArrExt.decCV (IWGrow.erecExt hg14) hcv)
      (by rw [hc1]; omega) hwvl
  obtain ⟨a', hrun', hS', hg'⟩ := dvK1_ok hRp "type mismatch in theorem" h hS5
    (ArrExt.decCI (IWGrow.erecPExt (hg14.trans hg5)) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hg14.trans (hg5.trans hg')⟩
  rw [h00, ← hty] at hrun1
  rw [h00, hx1] at hrun2
  rw [hx2] at hrun4
  rw [checkThmVal_eq]
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, zeroLevel, pinZeroLevel_run hF, hrun4,
    liftFueled, StateT.run_pure, if_true, pure_bind]
  simp only [dvT, StateT.run_bind, hrun5, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

/-! ## The census theorems -/

theorem decls_decCI_defn {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {cv : IConstantVal}
    {v : EIdx} {hh : ConLeche.ReducibilityHint} (h : decCI a dn q = some (.defnInfo cv v hh)) :
    decCV a (q + 1) = some cv ∧ hd? a (q + 5) = some v := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  split at h
  all_goals (try simp only [Option.bind_eq_some_iff, Option.some.injEq] at h)
  all_goals grind

theorem decCI_cv {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {ci : IConstantInfo} {cv : IConstantVal}
    (h : decCI a dn q = some ci) (hk : ci = .thmInfo cv ∨ ci = .axiomInfo cv) :
    decCV a (q + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases hk with rfl | rfl <;> split at h
  all_goals (try simp only [Option.bind_eq_some_iff, Option.some.injEq] at h)
  all_goals grind

/-- **`check_constant_val` refines `checkConstantVal .verified`** (through the core's stubs; the census link is `checkConstantVal_refinesT`, `DeclArmT.lean`). -/
theorem checkConstantVal_refines (p : Prog) (hp : ValProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q : Word) (cv : IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀) (hq : decCV (erecP s₀.mem) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_constant_val" [vis, q]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (checkConstantVal V fe cv) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (checkConstantVal V fe cv) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ccv_specW p hp stubCall (stubCall_spec p) n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := ccvW_ok hm hS hq hqb
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩

/-- **`check_defn_val` refines `checkDefnVal .verified`** at the arm's record (through the core's
stubs). -/
theorem checkDefnVal_refines (p : Prog) (hp : ValProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (cv : IConstantVal) (v : EIdx)
    (hh : ConLeche.ReducibilityHint) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.defnInfo cv v hh)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_defn_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDefnVal V fe cv v hh) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkDefnVal V fe cv v hh) a₀) s'.mem
        (AM.st (checkDefnVal V fe cv v hh) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (dv_specW p hp stubCall (stubCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hcv, hv⟩ := decls_decCI_defn hc
  obtain ⟨a', hrun, hS', hg⟩ := dvW_ok hp.rcp "type mismatch in definition" hm hS hc hcv hv
  rw [← checkDefnVal_dvT] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hg⟩

/-- **`check_opaque_val` refines `checkOpaqueVal .verified`** at the arm's record (an `axiomInfo`,
its value word at `c + 5`; through the core's stubs). -/
theorem checkOpaqueVal_refines (p : Prog) (hp : ValProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (cv : IConstantVal) (v : EIdx)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.axiomInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_opaque_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkOpaqueVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkOpaqueVal V fe cv v) a₀) s'.mem
        (AM.st (checkOpaqueVal V fe cv v) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ov_specW p hp stubCall (stubCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  have hcv := decCI_cv hc (.inr rfl)
  obtain ⟨a', hrun, hS', hg⟩ := dvW_ok hp.rcp "type mismatch in opaque" hm hS hc hcv hv
  rw [← checkOpaqueVal_dvT] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hg⟩

/-- **`check_thm_val` refines `checkThmVal .verified`** at the arm's record (a `thmInfo`, its value
word at `c + 5`; through the core's stubs and `lvl_eq_c`'s). -/
theorem checkThmVal_refines (p : Prog) (hp : ValProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (cv : IConstantVal) (v : EIdx)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.thmInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkThmVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkThmVal V fe cv v) a₀) s'.mem
        (AM.st (checkThmVal V fe cv v) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (tv_specW p hp stubCall (stubCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  have hcv := decCI_cv hc (.inl rfl)
  obtain ⟨a', hrun, hS', hg⟩ := tvW_ok hp.rcp hm hS hc hcv hv
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hg⟩

end L.Arena
