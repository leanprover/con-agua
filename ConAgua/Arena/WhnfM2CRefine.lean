import ConAgua.Arena.WhnfM2C
import ConAgua.Arena.WhnfIotaRefine
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import ConAgua.L.Examples

/-!
# `major_to_ctor`: the twin split along the L pieces, and the leaf specs

The twin `majorToCtor` (`Core.lean:1705-1820`) is one function; its pieces are named here
(`m2cHeadT` … `m2cCheckT`), each the twin's own code with the values decoded so far as
parameters, and `majorToCtor` unfolds into them by `rfl` (`majorToCtor_eq`). Each L piece of
`WhnfM2C.lean` has a unified model (`Verdict/WhnfModels6E.lean`); `major_to_ctor` itself and the
leaves outside the verdict closure (`m2c_const_view`, `m2c_eta2`) get a word-level model through
`callW` and an L spec by `vcgen` + `finish` here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin, split -/

/-- The major's type in whnf and its head; `k` at a constant head, `major` otherwise. -/
def m2cPreT (r : CoreFnsA) (depth : Nat) (major : EIdx) (k : EIdx → NIdx → LsIdx → AM EIdx) :
    AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => k tmaj T' ust
    | _ => pure major
  else pure major

/-- The scope guard, the type check and proof irrelevance of a fabricated `fab` (K, `And`). -/
def m2cCheckT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (tmaj fab major : EIdx) : AM EIdx := do
  if ← fabScopeOk depth fab major then do
    if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
      let irK ←
        if mode.verifiedChecks then proofIrrel r fe depth fab major
        else pure true
      if irK then pure fab else pure major
    else pure major
  else pure major

/-- The K arm's fabrication. -/
def m2cK2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor : NIdx)
    (cnP : Nat) (tmaj : EIdx) (ust : LsIdx) (major : EIdx) : AM EIdx := do
  let targs ← getAppArgs coreWalkFuel tmaj
  if cnP ≤ targs.length then do
    let hd ← internE (.const ctor ust)
    let fab ← mkAppN hd (targs.take cnP)
    m2cCheckT mode r fe depth tmaj fab major
  else pure major

/-- The K arm. -/
def m2cKT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor : NIdx)
    (lpl cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx :=
  m2cPreT r depth major fun tmaj T' ust => do
    let ustl ← viewLs ust
    if T' = T ∧ lpl = ustl.length then m2cK2T mode r fe depth ctor cnP tmaj ust major
    else pure major

/-- The η arm's fabrication. -/
def m2cEta2T (fe : IFEnv) (depth : Nat) (T etaCtor : NIdx) (etaFields : Nat) (targs : List EIdx)
    (ust : LsIdx) (major : EIdx) : AM EIdx := do
  let reserved ← reservedBasisNames
  if reserved.contains T = false ∧ reserved.contains etaCtor = false then do
    if ← (pure (towerSlotsAll fe T etaFields) : AM Bool) then do
      let fabArgs ← etaFabArgsE T targs major etaFields
      let hd ← internE (.const etaCtor ust)
      let fab ← mkAppN hd fabArgs
      if ← fabScopeOk depth fab major then pure fab
      else pure major
    else pure major
  else pure major

/-- The η arm. -/
def m2cEtaT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (T : NIdx) (cvT : IConstantVal)
    (caps : IIndCaps) (major : EIdx) : AM EIdx :=
  m2cPreT r depth major fun tmaj T' ust => do
    let ustl ← viewLs ust
    let targs ← getAppArgs coreWalkFuel tmaj
    let nz ← capsNeverZero cvT.levelParams ust caps
    if T' = T ∧ targs.length = caps.etaParams ∧
        ustl.length = cvT.levelParams.length ∧ nz = true then
      m2cEta2T fe depth T caps.etaCtor caps.etaFields targs ust major
    else pure major

/-- The `And` arm's fabrication. -/
def m2cAnd2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor T : NIdx)
    (tmaj : EIdx) (targs : List EIdx) (ust : LsIdx) (major : EIdx) : AM EIdx := do
  let p0 ← internE (.proj T 0 major)
  let p1 ← internE (.proj T 1 major)
  let fabArgs := targs ++ [p0, p1]
  let hd ← internE (.const ctor ust)
  let fab ← mkAppN hd fabArgs
  m2cCheckT mode r fe depth tmaj fab major

/-- The `And` arm. -/
def m2cAndT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor : NIdx)
    (lpl cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx := do
  let an ← pinAnd
  if T = an then
    m2cPreT r depth major fun tmaj T' ust => do
      match ← viewLsLen ust with
      | none => failDanglingLs
      | some ustl =>
      let targs ← getAppArgs coreWalkFuel tmaj
      let ars ← andRescueSlots fe ctor cnP ust
      if T' = T ∧ targs.length = cnP ∧ lpl = ustl ∧ ars = true then
        m2cAnd2T mode r fe depth ctor T tmaj targs ust major
      else pure major
  else pure major

/-- The dispatch on the rule's bits. -/
def m2cArmsT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule)
    (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (major : EIdx) : AM EIdx :=
  if rl.k = true then m2cKT mode r fe depth rl.ctor cvj.levelParams.length cnP T major
  else if rl.eta = true then m2cEtaT r fe depth T cvT caps major
  else m2cAndT mode r fe depth rl.ctor cvj.levelParams.length cnP T major

/-- The family of the constructor. -/
def m2cCtorT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule)
    (cvj : IConstantVal) (cnP : Nat) (major : EIdx) : AM EIdx := do
  let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T _ =>
      match fe.find? T with
      | some (.indInfo cvT caps) => m2cArmsT mode r fe depth rl cvj cnP T cvT caps major
      | _ => pure major
    | _ => pure major
  else pure major

/-- The constructor test, the single rule, its constructor. -/
def m2cHeadT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (rules : List IRecRule) (major : EIdx) : AM EIdx := do
  if ← isCtorApp fe major then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) => m2cCtorT mode r fe depth rl cvj cnP major
    | _ => pure major
  | _ => pure major

/-- **The twin is its pieces.** -/
theorem majorToCtor_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (recName : NIdx) (rules : List IRecRule) (major : EIdx) :
    majorToCtor mode r fe depth recName rules major = m2cHeadT mode r fe depth rules major := rfl

/-! ## Word models and L specs

Each piece's run as a function of the memory, its callees through `callW` (`WhnfBase.lean`). -/

/-- Model of `m2c_const_view`. -/
def cvwW (m : Mem) (hh : Word) : Option (List Word) :=
  if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW hh) ≤ idxW hh then none
  else some [tfld m CONST (tierW hh) (idxW hh) 0,
    tfld m CONST (tierW hh) (idxW hh) 1]

theorem m2cConstView_spec (p : Prog) (hp : p.lookup "m2c_const_view" = some m2cConstViewL)
    (n : Nat) (s₀ : St) (hh : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "m2c_const_view" [hh]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ cvwW s₀.mem hh = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cConstViewL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE] <;>
      finish [cvwW, tierW, idxW]

/-- Model of `m2c_eta2`. -/
def m2cEta2W (p : Prog) (n : Nat) (m : Mem) (vis d T ec ef to tn ust major : Word) :
    Option (Word × Mem) :=
  match callW p n "reserved_contains_w" [T] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 ≠ 0 then some (major, m₁) else
  match callW p n "reserved_contains_w" [ec] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 ≠ 0 then some (major, m₂) else
  match callW p n "tower_slots_all" [vis, T, ef] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₃.headD 0 = 0 then some (major, m₃) else
  match callW p n "eta_fab_args" [T, to, tn, major, ef] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "intern_const" [ec, ust] m₄ with
  | none => none
  | some (r₅, m₅) =>
  match callW p n "mk_app_n" [r₅.headD 0, r₄.headD 0, r₄.tail.headD 0] m₅ with
  | none => none
  | some (r₆, m₆) =>
  match callW p n "fab_scope_ok" [d, r₆.headD 0, major] m₆ with
  | none => none
  | some (r₇, m₇) => if r₇.headD 0 = 0 then some (major, m₇) else some (r₆.headD 0, m₇)

theorem m2cEta2_spec (p : Prog) (hp : p.lookup "m2c_eta2" = some m2cEta2L) (n : Nat) (s₀ : St)
    (vis d T ec ef to tn ust major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_eta2" [vis, d, T, ec, ef, to, tn, ust, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cEta2W p n s₀.mem vis d T ec ef to tn ust major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cEta2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "reserved_contains_w", callW_spec p n "tower_slots_all",
    callW_spec p n "eta_fab_args", callW_spec p n "intern_const", callW_spec p n "mk_app_n",
    callW_spec p n "fab_scope_ok"] <;>
  simp_all [-UInt64.toNat_add, m2cEta2W, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- The stack writes of `m2c_and2`: the two projections at `to + tn`, `to + tn + 1`, the top
raised past them. -/
def and2Push (m : Mem) (to tn p0 p1 : Word) : Option Mem :=
  if to + tn < UInt64.ofNat (m.arr64 SPN).size ∧ (to + tn).toNat < (m.arr64 SPN).size ∧
      to + tn + 1 < UInt64.ofNat ((m.set64 SPN (to + tn) p0).arr64 SPN).size ∧
      (to + tn + 1).toNat < ((m.set64 SPN (to + tn) p0).arr64 SPN).size ∧
      136 < (((m.set64 SPN (to + tn) p0).set64 SPN (to + tn + 1) p1).arr64 CTL).size then
    some (((m.set64 SPN (to + tn) p0).set64 SPN (to + tn + 1) p1).set64 CTL 136 (to + tn + 2))
  else none

/-! ## `reserved_contains(x)` (`WhnfIota.lean`'s `reservedContainsL`, the η arm's two tests) -/

/-- The loop of `reservedContainsL`, as a named block (`reservedContainsL` writes the same
statement inline: `reservedContainsL_eq`). -/
def resContLoop : Stmt := lblk (x, j) {
  while j < 16 {
    if PINS.u64[55 + j] == x { return 1 };
    j += 1
  }
}

theorem reservedContainsL_eq : reservedContainsL = lfn (x) locals (j) {
  if PINS.u64[0] == 0 { abort };
  j := 0;
  ⟪resContLoop⟫;
  return 0
} := rfl

/-- Model of the loop at L fuel `k`. -/
def rcLoopW (m : Mem) (x : Word) : Nat → Word → Option (List Word × Mem)
  | 0, _ => none
  | k + 1, j =>
    if j < 16 then
      if rdW (m.arr64 PINS) (55 + j) = x then some ([1], m) else rcLoopW m x k (j + 1)
    else some ([0], m)

theorem rcLoopW_end (m : Mem) (x : Word) (k : Nat) (j : Word) (h : ¬ j < 16) :
    rcLoopW m x (k + 1) j = some ([0], m) := by
  simp only [rcLoopW, h, ↓reduceIte]

theorem rcLoopW_hit (m : Mem) (x : Word) (k : Nat) (j : Word) (h : j < 16)
    (he : rdW (m.arr64 PINS) (55 + j) = x) : rcLoopW m x (k + 1) j = some ([1], m) := by
  simp only [rcLoopW, h, he, ↓reduceIte]

theorem rcLoopW_cont (m : Mem) (x : Word) (k : Nat) (j : Word) (h : j < 16)
    (he : ¬ rdW (m.arr64 PINS) (55 + j) = x) : rcLoopW m x (k + 1) j = rcLoopW m x k (j + 1) := by
  simp only [rcLoopW, h, he, ↓reduceIte]

theorem resContLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k resContLoop
    ⦃fun r s' => r ≠ .brk ∧ rcLoopW s₀.mem (s₀.loc 0) k (s₀.loc 1) = some (r.retOr [0], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := resContLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish [rcLoopW_end, rcLoopW_hit, rcLoopW_cont, rdW]

/-- Model of `reserved_contains`. -/
def rcW_m2c (k : Nat) (m : Mem) (x : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 PINS) 0 = 0 then none else rcLoopW m x (k + 1) 0

theorem reservedContains_spec (p : Prog) (hp : p.lookup "reserved_contains_w" = some reservedContainsL)
    (k : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "reserved_contains_w" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ rcW_m2c k s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, reservedContainsL_eq]
  simp only [callFn]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, fun s₀ => Triple.step_exec (resContLoop_spec p (k + 1) s₀)] <;>
    finish [rcW_m2c, rdW]

/-- The loop's answer: a hit from `j` on, or none. -/
theorem rcLoopW_ok (m : Mem) (x : Word) :
    ∀ (K k : Nat) (j : Word) (L : List Word) (m' : Mem), 16 - j.toNat = K → j.toNat ≤ 16 →
      rcLoopW m x k j = some (L, m') →
      m' = m ∧ (L = [0] ∨ L = [1]) ∧ (L.headD 0 ≠ 0 ↔ ∃ i : Nat, j.toNat ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x) := by
  intro K
  induction K with
  | zero =>
    intro k j L m' hK hj h
    cases k with
    | zero => simp [rcLoopW] at h
    | succ k =>
    have hn : ¬ j < 16 := fun h => by
      have : j.toNat < 16 := h
      omega
    rw [rcLoopW_end m x k j hn] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨rfl, .inl rfl, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
    intro i h1 h2; omega
  | succ K ih =>
    intro k j L m' hK hj h
    cases k with
    | zero => simp [rcLoopW] at h
    | succ k =>
    have hlt : j < 16 := by
      have : j.toNat < 16 := by omega
      exact this
    have hjt : j.toNat < 16 := hlt
    have e55 : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hpw : rdW (m.arr64 PINS) (55 + j) = pinW m (55 + j.toNat) := by
      simp only [rdW, pinW, e55]
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · rw [rcLoopW_hit m x k j hlt he] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨rfl, .inr rfl, ?_⟩
      simp only [List.headD_cons, ne_eq]
      exact ⟨fun _ => ⟨j.toNat, Nat.le_refl _, hjt, hpw ▸ he⟩, fun _ => by decide⟩
    · rw [rcLoopW_cont m x k j hlt he] at h
      have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat 16 j hlt
      obtain ⟨hm, hl, hiff⟩ := ih k (j + 1) L m' (by omega) (by omega) h
      refine ⟨hm, hl, hiff.trans ?_⟩
      rw [h1]
      constructor
      · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, by omega, h2, h3⟩
      · rintro ⟨i, h1, h2, h3⟩
        rcases Nat.lt_or_ge j.toNat i with hl' | hl'
        · exact ⟨i, by omega, h2, h3⟩
        · have : i = j.toNat := by omega
          subst this; exact absurd (hpw ▸ h3) he

/-- **`reserved_contains` as a run**: memory unchanged, and the answer is `reservedBasisNames`'
membership test. -/
theorem callW_reservedContains (p : Prog) (hp : p.lookup "reserved_contains_w" = some reservedContainsL)
    (n : Nat) (m : Mem) (a : AState) (hP : PinsFull m a.pins) (x : Word) (hx : HW x) (r : List Word)
    (m' : Mem) (h : callW p n "reserved_contains_w" [x] m = some (r, m')) :
    m' = m ∧ ∃ l, reservedBasisNames.run a = .ok (l, a) ∧ l.contains (decI x) = (r.headD 0 != 0) ∧
      ResH r := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reservedContains_spec p hp k _ x) h
  simp only [rcW_m2c] at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  obtain ⟨hm, hl, hiff⟩ := rcLoopW_ok m x _ (k + 1) 0 r s'.mem rfl (by simp) hW
  refine ⟨hs' ▸ hm, _, pinReserved_run hP, ?_, ?_⟩
  · have hc : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) =
        true ↔ ∃ i : Nat, 0 ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := by
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, e⟩
        exact ⟨i, Nat.zero_le _, hi,
          ((decI_eq_iff _ (hP.reserved_lt i hi) _).mp e).trans (decI_word_self x hx)⟩
      · rintro ⟨i, -, hi, e⟩; exact ⟨i, hi, by rw [e]⟩
    have hiff' : r.headD 0 ≠ 0 ↔ ∃ i : Nat, 0 ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := by
      simpa using hiff
    by_cases hr : r.headD 0 = 0
    · have : ¬ ∃ i : Nat, 0 ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := fun e => hiff'.mpr e hr
      rw [hr]
      exact Bool.eq_false_iff.mpr (fun h' => this (hc.mp h'))
    · rw [show (r.headD 0 != 0) = true by simpa using hr]; exact hc.mpr (hiff'.mp hr)
  · unfold ResH HW
    rcases hl with rfl | rfl <;> decide

end L.Arena
