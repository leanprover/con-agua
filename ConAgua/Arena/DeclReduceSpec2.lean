module

import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.DeclCanonEq
public import ConAgua.Rom.CIReadSpec
public import ConAgua.Arena.LeafFns
import all ConAgua.Arena.DeclArms
import ConAgua.L.WordOff

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
  some ([if cvEqB (erRd m) q pin then 1 else 0], m)

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
    (h : mpW m q pin = some (r, m')) (_hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h1 : decCV (erA m) q.toNat = some cv) (h2 : decCV (erA m) pin.toNat = some cv') :
    m' = m ∧ (cv.matchesPin cv').run a = .ok (decide (cv = cv'), a) ∧
      decW0B m' r (decide (cv = cv')) := by
  simp only [mpW, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [cvEqB_ok (erRdOK m) h1 h2, matchesPin_eq]
  refine ⟨rfl, rfl, ?_⟩
  by_cases e : cv = cv' <;> simp [e, decW0B]

/-- **`matches_pin(q, pin)` refines `IConstantVal.matchesPin`**. -/
@[refines ConRon.Arena.IConstantVal.matchesPin]
theorem matchesPin_refines (p : Prog) (hC : CanonProg p)
    (hp : p.lookup "matches_pin" = some matchesPinL) (_dn : NIdx → Option ConLeche.Name)
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
theorem decCI_kind0 {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI a p = some ci) (hw : a p = some w) :
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
    rcases hk with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h0 (UInt64.toNat_inj.mp (by simpa using h1))
    all_goals simp_all

/-- A record of kind word `3` is an `indInfo`, any other kind word is not. -/
theorem decCI_kind3 {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI a p = some ci) (hw : a p = some w) :
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
    rcases hk with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · simp_all
    · simp_all
    · simp_all
    · exact h0 (UInt64.toNat_inj.mp (by simpa using h1))
    all_goals simp_all

/-- A record of kind word `4` is a `ctorInfo` with its counts at `+5`, `+6`; any other kind word
is not. -/
theorem decCI_kind4 {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI a p = some ci) (hw : a p = some w) :
    (w = 4 → ∃ cv np nf, decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some np ∧
      nat? a (p + 6) = some nf ∧ ci = .ctorInfo cv np nf) ∧
      (w ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rw [hw] at e; cases e
  constructor
  · intro h0
    subst h0
    rcases hk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, cv, np, nf, hcv, h5, h6, rfl⟩ | ⟨h1, -⟩
    · simp at h1
    · simp at h1
    · simp at h1
    · simp at h1
    · exact ⟨cv, np, nf, hcv, h5, h6, rfl⟩
    · simp at h1
  · intro h0 cv np nf hc
    subst hc
    rcases hk with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · exact h0 (UInt64.toNat_inj.mp (by simpa using h1))
    · simp_all

/-- A record of kind word `5` is a `recInfo` with its counts at `+5`, `+6`; any other kind word
is not. -/
theorem decCI_kind5 {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} {w : Word} (h : decCI a p = some ci) (hw : a p = some w) :
    (w = 5 → ∃ cv mi rp k rules, decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some mi ∧
      nat? a (p + 6) = some rp ∧ ci = .recInfo cv mi rp k rules) ∧
      (w ≠ 5 → ∀ cv mi rp k rules, ci ≠ .recInfo cv mi rp k rules) := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rw [hw] at e; cases e
  constructor
  · intro h0
    subst h0
    rcases hk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨-, cv, mi, rp, o, c, k, rules, hcv, h5, h6, -, -, -, -, rfl⟩
    · simp at h1
    · simp at h1
    · simp at h1
    · simp at h1
    · simp at h1
    · exact ⟨cv, mi, rp, k, rules, hcv, h5, h6, rfl⟩
  · intro h0 cv mi rp k rules hc
    subst hc
    rcases hk with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · exact h0 (UInt64.toNat_inj.mp (by simpa using h1))

/-! ## `reduce_stored_ok(vis, c)`, `reduce_elem_ok(vis, c)` -/

/-- The lookups of the reduce operations' environment shapes. -/
structure RedProg (p : Prog) : Prop where
  canon : CanonProg p
  mp : p.lookup "matches_pin" = some matchesPinL
  rso : p.lookup "reduce_stored_ok" = some reduceStoredOkL
  reo : p.lookup "reduce_elem_ok" = some reduceElemOkL
  ocv : p.lookup "reduce_op_cv_a" = some reduceOpCvAL
  pa : p.lookup "pin_at" = some pinAtL
  rom : L.Rom.RomRefs p
  erg : p.lookup "env_row_get" = some envRowGetL
  brg : p.lookup "base_row_get" = some baseRowGetL
  ef : p.lookup "env_find" = some envFindL

/-- **The model of `reduce_stored_ok(vis, c)`.** -/
l_model rso_specW (p : Prog) (hp : p.lookup "reduce_stored_ok" = some reduceStoredOkL)
  fns [hp ↦ rsoW list]
  specs [callW_spec p n "env_find", callW_spec p n "reduce_op_cv_a", callW_spec p n "matches_pin"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `reduce_elem_ok(vis, c)`.** -/
l_model reo_specW (p : Prog) (hp : p.lookup "reduce_elem_ok" = some reduceElemOkL)
  fns [hp ↦ reoW list]
  specs [callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "rom_ci",
    callW_spec p n "rom_cv", callW_spec p n "matches_pin"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- An `env_find` call: the memory unchanged, the result `findRes`. -/
theorem envFind_callR {p : Prog} (h : RedProg p) {n : Nat} {m m' : Mem} {vis w : Word}
    {r : List Word} (hc : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ r = findRes m vis w := by
  obtain ⟨s', rfl, h1, -, h3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_spec p h.erg h.brg h.ef n _ vis w) hc
  exact ⟨h1, h3⟩

/-- A `pin_at` call through its model. -/
theorem pinAt_callR {p : Prog} (h : RedProg p) {n : Nat} {m m' : Mem} {i : Word}
    {r : List Word} (hc : callW p n "pin_at" [i] m = some (r, m')) : pinAtW m i = some (r, m') := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinAt_specW p h.pa n _ i) hc
  exact hW

/-- A `matches_pin` call through its model. -/
theorem mp_callR {p : Prog} (h : RedProg p) {n : Nat} {m m' : Mem} {q pin : Word}
    {r : List Word} (hc : callW p n "matches_pin" [q, pin] m = some (r, m')) :
    mpW m q pin = some (r, m') := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mp_specW p h.canon h.mp n _ q pin) hc
  exact hW

/-- The kind word of a record at the tagged `EREC` read. -/
theorem erecKind {m : Mem} {q w : Word} (hw : erecP m q.toNat = some w) :
    rdW (m.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775) = w := by
  rw [erRd_congr rfl rfl]; exact erRd_of _ _ hw

/-- A pinned constant value read back from `rom_cv`'s result. -/
theorem decRCV_get {m : Mem} {r : List Word} {cv : IConstantVal} (h : decRCV m r cv) :
    decCV (erA m) (r.headD 0).toNat = some cv :=
  DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ h

/-- **`reduce_stored_ok(vis, c)` refines `reduceStoredOk`** at the model level. -/
theorem rsoW_ok {p : Prog} (h : RedProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    (hW : rsoW p n m vis c = some (r, m')) (hS : StageR vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ b a', (reduceStoredOk fe (decI c)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [rsoW.eq_1] at hW
  | succ n =>
  rw [rsoW.arm1] at hW
  rcases h1 : callW p n "env_find" [c, vis] m with _ | ⟨r1, m1⟩
  · rw [h1, rsoW.k_env_find.none] at hW; cases hW
  rw [h1] at hW
  obtain ⟨hm1, hr1⟩ := envFind_callR h h1
  subst m1 r1
  by_cases hf : (findRes m vis c).headD 0 = 0
  · rw [rsoW.k_env_find.arm1 p n c _ _ hf] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hfind := findRes_miss hS.check.env hc hf
    exact ⟨false, a, by simp only [reduceStoredOk, hfind]; rfl, hS, IWGrow.refl _,
      by simp [decW0B]⟩
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hS.check.env hc hf
  generalize hq : (findRes m vis c).tail.headD 0 = q at hW hci hfind
  obtain ⟨wk, hwk⟩ := decCI_rd hci
  obtain ⟨hk0, hkn⟩ := decCI_kind0 hci hwk
  by_cases hk : wk ≠ 0
  · rw [rsoW.k_env_find.arm2 p n c _ _ hf (by rw [hq, erecKind hwk]; exact hk)] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
    have hne := hkn hk
    simp only [reduceStoredOk, hfind, hci]
    cases ci with
    | axiomInfo cv => exact absurd rfl (hne cv)
    | _ => rfl
  have hk' : wk = 0 := by simpa using hk
  rw [rsoW.k_env_find.arm3 p n c _ _ hf (by rw [hq, erecKind hwk]; exact hk'), hq] at hW
  obtain ⟨cvR, hcvR, rfl⟩ := hk0 hk'
  -- the pinned type
  rcases h2 : callW p n "reduce_op_cv_a" [c] m with _ | ⟨r2, m2⟩
  · rw [h2, rsoW.k_reduce_op_cv_a.none] at hW; cases hW
  rw [h2, rsoW.k_reduce_op_cv_a.arm1] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hd2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceOpCvA_refines (p := p) (hpa := h.pa) (n := n) (s₀ := ⟨m, Locals.init []⟩) (a₀ := a)
      (hS := hS) (hc := hc) (hR := h.rom) (hp := h.ocv)) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  have hpin := decRCV_get hd2
  obtain ⟨wn, hwn, -⟩ := decCV_name hcvR
  have hq1 : (q + 1).toNat = q.toNat + 1 := L.toNat_add_ofNat_of_lt q 1 (erecP_lt64 hwn)
  have hcvR2 : decCV (erA s2.mem) (q + 1).toNat = some cvR := by
    rw [hq1]; exact ArrExt.decCV (L.Ind.IWGrow.ext hg2) hcvR
  rcases h3 : callW p n "matches_pin" [q + 1, r2.headD 0] s2.mem with _ | ⟨r3, m3⟩
  · rw [h3, rsoW.k_matches_pin.none] at hW; cases hW
  rw [h3, rsoW.k_matches_pin.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨rfl, hrun3, hd3⟩ := mpW_ok (a := AM.st (reduceOpCvA (decI c)) a) (mp_callR h h3)
    hS2.iw.erSize hcvR2 hpin
  refine ⟨_, _, ?_, hS2, hg2, by simpa [decW0B] using hd3⟩
  simp only [reduceStoredOk, hfind, hci, StateT.run_bind, hrun2, L.Arena.except_ok_bind]
  exact hrun3

/-- **`reduce_stored_ok(vis, c)` refines `reduceStoredOk`** (through `rom_cv`'s refinement). -/
@[refines ConRon.Arena.reduceStoredOk]
theorem reduceStoredOk_refines (p : Prog) (h : RedProg p)
    (vis : Word) (fe : IFEnv) (c : Word) (hc : c.toNat < 2 ^ 32) :
    RefAM p "reduce_stored_ok" [vis, c] (StageR vis fe) (reduceStoredOk fe (decI c))
      (KeepPost vis fe decW0B) := by
  intro n s₀ a₀ hS
  refine triple_post (rso_specW p h.rso n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := rsoW_ok h hm hS hc
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

/-- **`reduce_elem_ok(vis, c)` refines `reduceElemOk`** at the model level. -/
theorem reoW_ok {p : Prog} (h : RedProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    (hW : reoW p n m vis c = some (r, m')) (hS : StageR vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ b a', (reduceElemOk fe (decI c)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [reoW.eq_1] at hW
  | succ n =>
  rw [reoW.arm1] at hW
  rcases h1 : callW p n "pin_at" [43] m with _ | ⟨r1, m1⟩
  · rw [h1, reoW.k_pin_at.none] at hW; cases hW
  rw [h1, reoW.k_pin_at.eq_2] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok (pinAt_callR h h1) hS.check.pins
  subst m1
  have e1 : r1.headD 0 = pinW m (1 + (43 : Word).toNat) := by rw [hr1]; rfl
  have hbeq : ((decI c : NIdx) == decI (pinW m (1 + (43 : Word).toNat))) =
      decide (c = pinW m (1 + (43 : Word).toNat)) := decI_beq c _ hc hl1
  by_cases he : c = r1.headD 0
  · -- `reduceNat`: a stored `Nat` inductive at the pin's constant value
    rw [ite_eq_left he] at hW
    rw [e1] at he
    rcases h2 : callW p n "pin_at" [1] m with _ | ⟨r2, m2⟩
    · rw [h2, reoW.k_pin_at_2.none] at hW; cases hW
    rw [h2, reoW.k_pin_at_2.arm1] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok (pinAt_callR h h2) hS.check.pins
    subst m2 hr2
    simp only [List.headD_cons] at hW
    have hpre : (reduceElemOk fe (decI c)).run a =
        (match fe.find? (decI (pinW m (1 + (1 : Word).toNat))) with
          | some (.indInfo cvN _) => do cvN.matchesPin (← natA).toConstantVal
          | _ => pure false : AM Bool).run a := by
      simp only [reduceElemOk, reduceNatName, pinReduceNat, StateT.run_bind,
        show PIN_REDUCE_NAT = (43 : Word).toNat from rfl, hrun1, L.Arena.except_ok_bind, he,
        beq_self_eq_true, ite_true, pinNat, show PIN_NAT = (1 : Word).toNat from rfl, hrun2]
      rfl
    rcases h3 : callW p n "env_find" [pinW m (1 + (1 : Word).toNat), vis] m with _ | ⟨r3, m3⟩
    · rw [h3, reoW.k_env_find.none] at hW; cases hW
    rw [h3] at hW
    obtain ⟨hm3, hr3⟩ := envFind_callR h h3
    subst m3 r3
    by_cases hf : (findRes m vis (pinW m (1 + (1 : Word).toNat))).headD 0 = 0
    · rw [reoW.k_env_find.arm1 p n _ _ hf] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hfind := findRes_miss hS.check.env hl2 hf
      exact ⟨false, a, by rw [hpre, hfind]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    obtain ⟨hfind, ci, hci⟩ := findRes_hit hS.check.env hl2 hf
    generalize hq : (findRes m vis (pinW m (1 + (1 : Word).toNat))).tail.headD 0 = q at hW hci hfind
    obtain ⟨wk, hwk⟩ := decCI_rd hci
    obtain ⟨hk3, hkn⟩ := decCI_kind3 hci hwk
    by_cases hk : wk ≠ 3
    · rw [reoW.k_env_find.arm2 p n _ _ hf (by rw [hq, erecKind hwk]; exact hk)] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
      rw [hpre, hfind, hci]
      have hne := hkn hk
      cases ci with
      | indInfo cv caps => exact absurd rfl (hne cv caps)
      | _ => rfl
    have hk' : wk = 3 := by simpa using hk
    rw [reoW.k_env_find.arm3 p n _ _ hf (by rw [hq, erecKind hwk]; exact hk'), hq] at hW
    obtain ⟨cvN, caps, hcvN, rfl⟩ := hk3 hk'
    rcases h4 : callW p n "rom_ci" [0] m with _ | ⟨r4, m4⟩
    · rw [h4, reoW.k_rom_ci.none] at hW; cases hW
    rw [h4, reoW.k_rom_ci.arm1] at hW
    obtain ⟨na, a4, hrun4, hS4, hg4, hna⟩ :=
      h.rom.ci (fun _ => none) vis fe 0 (by decide) n _ a r4 m4 hS h4
    have hrun4' : ConRon.Arena.natA.run a = .ok (na, a4) := hrun4
    obtain ⟨wn, hwn, -⟩ := decCV_name hcvN
    have hq1 : (q + 1).toNat = q.toNat + 1 := L.toNat_add_ofNat_of_lt q 1 (erecP_lt64 hwn)
    have hcvN4 : decCV (erA m4) (q + 1).toNat = some cvN := by
      rw [hq1]; exact ArrExt.decCV (L.Ind.IWGrow.ext hg4) hcvN
    have hna4 : decCI (erecP m4) (r4.headD 0).toNat = some na :=
      DecB.get ⟨fun _ _ _ he h => he.2.decCI h⟩ hna
    have hnacv := ciD_cv hna4
    obtain ⟨wn', hwn', -⟩ := decCV_name hnacv
    have hp1 : (r4.headD 0 + 1).toNat = (r4.headD 0).toNat + 1 :=
      L.toNat_add_ofNat_of_lt _ 1 (erecP_lt64 hwn')
    have hnacv' : decCV (erA m4) (r4.headD 0 + 1).toNat = some na.toConstantVal := by
      rw [hp1]; exact hnacv
    rcases h5 : callW p n "matches_pin" [q + 1, r4.headD 0 + 1] m4 with _ | ⟨r5, m5⟩
    · rw [h5, reoW.k_matches_pin.none] at hW; cases hW
    rw [h5, reoW.k_matches_pin.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨rfl, hrun5, hd5⟩ := mpW_ok (a := a4) (mp_callR h h5) hS4.iw.erSize hcvN4 hnacv'
    refine ⟨_, _, ?_, hS4, hg4, by simpa [decW0B] using hd5⟩
    rw [hpre, hfind, hci]
    simp only [StateT.run_bind, hrun4', L.Arena.except_ok_bind]
    exact hrun5
  · -- `reduceBool`: a standard `Bool`
    rw [ite_eq_right he] at hW
    rw [e1] at he
    rcases h2 : callW p n "pin_at" [29] m with _ | ⟨r2, m2⟩
    · rw [h2, reoW.k_pin_at_3.none] at hW; cases hW
    rw [h2, reoW.k_pin_at_3.arm1] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok (pinAt_callR h h2) hS.check.pins
    subst m2 hr2
    simp only [List.headD_cons] at hW
    have hpre : (reduceElemOk fe (decI c)).run a =
        (match fe.find? (decI (pinW m (1 + (29 : Word).toNat))) with
          | some (.indInfo cvB _) => do cvB.matchesPin (← boolCvA)
          | _ => pure false : AM Bool).run a := by
      simp only [reduceElemOk, reduceNatName, pinReduceNat, StateT.run_bind,
        show PIN_REDUCE_NAT = (43 : Word).toNat from rfl, hrun1, L.Arena.except_ok_bind, hbeq, he,
        decide_false, Bool.false_eq_true, ite_false, boolName, pinBool,
        show PIN_BOOL = (29 : Word).toNat from rfl, hrun2]
      rfl
    rcases h3 : callW p n "env_find" [pinW m (1 + (29 : Word).toNat), vis] m with _ | ⟨r3, m3⟩
    · rw [h3, reoW.k_env_find_2.none] at hW; cases hW
    rw [h3] at hW
    obtain ⟨hm3, hr3⟩ := envFind_callR h h3
    subst m3 r3
    by_cases hf : (findRes m vis (pinW m (1 + (29 : Word).toNat))).headD 0 = 0
    · rw [reoW.k_env_find_2.arm1 p n _ _ hf] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hfind := findRes_miss hS.check.env hl2 hf
      exact ⟨false, a, by rw [hpre, hfind]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    obtain ⟨hfind, ci, hci⟩ := findRes_hit hS.check.env hl2 hf
    generalize hq : (findRes m vis (pinW m (1 + (29 : Word).toNat))).tail.headD 0 = q at hW hci hfind
    obtain ⟨wk, hwk⟩ := decCI_rd hci
    obtain ⟨hk3, hkn⟩ := decCI_kind3 hci hwk
    by_cases hk : wk ≠ 3
    · rw [reoW.k_env_find_2.arm2 p n _ _ hf (by rw [hq, erecKind hwk]; exact hk)] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
      rw [hpre, hfind, hci]
      have hne := hkn hk
      cases ci with
      | indInfo cv caps => exact absurd rfl (hne cv caps)
      | _ => rfl
    have hk' : wk = 3 := by simpa using hk
    rw [reoW.k_env_find_2.arm3 p n _ _ hf (by rw [hq, erecKind hwk]; exact hk'), hq] at hW
    obtain ⟨cvB, caps, hcvB, rfl⟩ := hk3 hk'
    rcases h4 : callW p n "rom_cv" [5] m with _ | ⟨r4, m4⟩
    · rw [h4, reoW.k_rom_cv.none] at hW; cases hW
    rw [h4, reoW.k_rom_cv.arm1] at hW
    obtain ⟨pin, a4, hrun4, hS4, hg4, hpin⟩ := h.rom.cv vis fe 5 (by decide) n _ a r4 m4 hS h4
    have hrun4' : boolCvA.run a = .ok (pin, a4) := hrun4
    obtain ⟨wn, hwn, -⟩ := decCV_name hcvB
    have hq1 : (q + 1).toNat = q.toNat + 1 := L.toNat_add_ofNat_of_lt q 1 (erecP_lt64 hwn)
    have hcvB4 : decCV (erA m4) (q + 1).toNat = some cvB := by
      rw [hq1]; exact ArrExt.decCV (L.Ind.IWGrow.ext hg4) hcvB
    rcases h5 : callW p n "matches_pin" [q + 1, r4.headD 0] m4 with _ | ⟨r5, m5⟩
    · rw [h5, reoW.k_matches_pin.none] at hW; cases hW
    rw [h5, reoW.k_matches_pin.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨rfl, hrun5, hd5⟩ := mpW_ok (a := a4) (mp_callR h h5) hS4.iw.erSize hcvB4
      (decRCV_get hpin)
    refine ⟨_, _, ?_, hS4, hg4, by simpa [decW0B] using hd5⟩
    rw [hpre, hfind, hci]
    simp only [StateT.run_bind, hrun4', L.Arena.except_ok_bind]
    exact hrun5

/-- **`reduce_elem_ok(vis, c)` refines `reduceElemOk`** (through the ROM readers' refinements). -/
@[refines ConRon.Arena.reduceElemOk]
theorem reduceElemOk_refines (p : Prog) (h : RedProg p)
    (vis : Word) (fe : IFEnv) (c : Word) (hc : c.toNat < 2 ^ 32) :
    RefAM p "reduce_elem_ok" [vis, c] (StageR vis fe) (reduceElemOk fe (decI c))
      (KeepPost vis fe decW0B) := by
  intro n s₀ a₀ hS
  refine triple_post (reo_specW p h.reo n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := reoW_ok h hm hS hc
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

/-! ## `reduce_stored_ok`'s write set

At the pushed view of the reduce-pin gate the own rows must stand for `env_pop_temp`: the
callee `reduce_op_cv_a` interns the pinned type (the pools, the stores) but leaves the own layer's
rows and their stamp alone (`RcvaClosed`, checked at the program). -/

/-- The call closure of `reduce_op_cv_a`. -/
def rcvaFns : List FnName :=
  ["app_find", "app_push", "bvar_find", "bvar_push", "const_find", "const_push", "der_b",
   "erec_alloc", "erec_put", "forall_find", "forall_push", "fvar_find", "fvar_push", "imax_find",
   "imax_push", "intern_app", "intern_bvar", "intern_const", "intern_forall", "intern_fvar",
   "intern_imax", "intern_lam", "intern_letE", "intern_lit", "intern_ls", "intern_max",
   "intern_nanon", "intern_nnum", "intern_nstr", "intern_param", "intern_proj", "intern_sort",
   "intern_succ", "intern_zero", "lam_find", "lam_push", "letE_find", "letE_push", "limbs_eq",
   "lit_find", "lit_hash", "lit_match", "lit_push", "ls_find", "ls_match", "ls_push", "max_find",
   "max_push", "memo_get", "memo_push", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj",
   "nanon_find", "nanon_push", "nnum_find", "nnum_push", "nstr_find", "nstr_match", "nstr_push",
   "param_find", "param_push", "pin_at", "proj_find", "proj_push", "rci_cv", "rci_fresh",
   "rci_name_sl", "rci_names_to", "rci_slot", "reduce_op_cv_a", "rom_cv", "rom_ex_leaf_c",
   "rom_ex_one_c", "rom_ex_ref_c", "rom_ex_two_c", "rom_expr_c", "rom_level_c", "rom_levels_c",
   "rom_lit", "rom_lvls_go_c", "rom_name_c", "rom_put_c", "rom_u64_c", "rset_clear", "rset_find",
   "rset_put", "sort_find", "sort_push", "stk_pool", "stk_push", "succ_find", "succ_push",
   "zero_find", "zero_push"]

/-- What `reduce_op_cv_a` may write: a leaf's arrays but the own layer's rows. -/
def rcvaA : List TieredArray := leafA.filter fun b => b ≠ OIXA ∧ b ≠ OIXS ∧ b ≠ OIXN ∧
  b ≠ tier1 OIXA ∧ b ≠ tier1 OIXS ∧ b ≠ tier1 OIXN

/-- What `reduce_op_cv_a` may write of `CTL`: a leaf's words but the own layer's stamp. -/
def rcvaC : List Word := leafC.filter fun x => x ≠ 133

/-- **`reduce_op_cv_a`'s closure writes only `rcvaA`/`rcvaC`.** -/
def RcvaClosed (p : Prog) : Prop := closedA p rcvaA rcvaC rcvaFns = true

/-- **`reduce_stored_ok`'s frame**: `env_find` and `matches_pin` leave the memory alone, the
pinned type's interning is `reduce_op_cv_a`'s. -/
theorem rsoW_frame {p : Prog} (h : RedProg p) (hcl : RcvaClosed p) {vis : Word} {n : Nat}
    {m m' : Mem} {c : Word} {r : List Word} (hW : rsoW p n m vis c = some (r, m')) :
    MemFrame rcvaA rcvaC m m' := by
  cases n with
  | zero => simp [rsoW.eq_1] at hW
  | succ n =>
  rw [rsoW.arm1] at hW
  rcases h1 : callW p n "env_find" [c, vis] m with _ | ⟨r1, m1⟩
  · rw [h1, rsoW.k_env_find.none] at hW; cases hW
  rw [h1] at hW
  obtain ⟨hm1, hr1⟩ := envFind_callR h h1
  subst m1 r1
  by_cases hf : (findRes m vis c).headD 0 = 0
  · rw [rsoW.k_env_find.arm1 p n c _ _ hf] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact MemFrame.refl _ _ _
  generalize hq : (findRes m vis c).tail.headD 0 = q at hW
  by_cases hk : rdW (m.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775) ≠ 0
  · rw [rsoW.k_env_find.arm2 p n c _ _ hf (by rw [hq]; exact hk)] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact MemFrame.refl _ _ _
  rw [rsoW.k_env_find.arm3 p n c _ _ hf (by rw [hq]; simpa using hk), hq] at hW
  rcases h2 : callW p n "reduce_op_cv_a" [c] m with _ | ⟨r2, m2⟩
  · rw [h2, rsoW.k_reduce_op_cv_a.none] at hW; cases hW
  rw [h2, rsoW.k_reduce_op_cv_a.arm1] at hW
  have hf2 := (run_memFrame hcl (by simp [rcvaFns]) (run_of_callW h2)).1
  rcases h3 : callW p n "matches_pin" [q + 1, r2.headD 0] m2 with _ | ⟨r3, m3⟩
  · rw [h3, rsoW.k_matches_pin.none] at hW; cases hW
  rw [h3, rsoW.k_matches_pin.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hm3 := mp_callR h h3
  simp only [mpW, Option.some.injEq, Prod.mk.injEq] at hm3
  rw [← hm3.2]
  exact hf2

end L.Arena
