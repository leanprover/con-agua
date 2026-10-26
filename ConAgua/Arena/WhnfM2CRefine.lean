import ConAgua.Arena.WhnfM2C
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.ConstRefine

/-!
# `major_to_ctor`: the twin split along the L pieces, and the leaf specs

The twin `majorToCtor` (`Core.lean:1705-1820`) is one function; its pieces are named here
(`m2cHeadT` … `m2cCheckT`), each the twin's own code with the values decoded so far as
parameters, and `majorToCtor` unfolds into them by `rfl` (`majorToCtor_eq`). Each L piece of
`WhnfM2C.lean` gets a word-level model through `callW` and an L spec by `vcgen` + `finish`.
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

/-- Model of `major_to_ctor`. -/
def mtcW (p : Prog) (n : Nat) (m : Mem) (mode vis d ro rc major : Word) : Option (Word × Mem) :=
  match callW p n "m2c_head" [mode, vis, d, ro, rc, major] m with
  | none => none
  | some (r, m₁) =>
    if 136 < (m₁.arr64 CTL).size then some (r.headD 0, m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136))
    else none

theorem majorToCtor_spec (p : Prog) (hp : p.lookup "major_to_ctor" = some majorToCtorL) (n : Nat)
    (s₀ : St) (mode vis d rec ro rc major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "major_to_ctor" [mode, vis, d, rec, ro, rc, major]
    ⦃fun r s' => LocEq s' s₀ ∧ mtcW p n s₀.mem mode vis d ro rc major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, majorToCtorL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "m2c_head"] <;>
  simp_all [mtcW, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL] <;>
  (congr 1; rw [Array.getElem?_eq_getElem]; rfl)

/-- Model of `m2c_head`. -/
def m2cHeadW (p : Prog) (n : Nat) (m : Mem) (mode vis d ro rc major : Word) :
    Option (Word × Mem) :=
  match callW p n "is_ctor_app" [vis, major] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 ≠ 0 then some (major, m₁) else
  if rc ≠ 1 then some (major, m₁) else
  match callW p n "env_find" [rdW (m₁.arr64 EREC) ro, vis] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 = 0 then some (major, m₂) else
  if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 4 then some (major, m₂) else
  match callW p n "m2c_ctor" [mode, vis, d, ro, r₂.tail.headD 0, major] m₂ with
  | none => none
  | some (r₃, m₃) => some (r₃.headD 0, m₃)

theorem m2cHead_spec (p : Prog) (hp : p.lookup "m2c_head" = some m2cHeadL) (n : Nat) (s₀ : St)
    (mode vis d ro rc major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_head" [mode, vis, d, ro, rc, major]
    ⦃fun r s' => LocEq s' s₀ ∧ m2cHeadW p n s₀.mem mode vis d ro rc major = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cHeadL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "is_ctor_app", callW_spec p n "env_find", callW_spec p n "m2c_ctor"] <;>
    finish [m2cHeadW]

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
        tcntM, evalE_tierE, evalE_idxE] <;>
      finish [cvwW, tierW, idxW]

/-- Model of `m2c_ctor`. -/
def m2cCtorW (p : Prog) (n : Nat) (m : Mem) (mode vis d ro cvjP major : Word) :
    Option (Word × Mem) :=
  match callW p n "pi_result" [rdW (m.arr64 EREC) (cvjP + 4)] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "get_app_fn" [r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 >>> 28 ≠ 3 then some (major, m₂) else
  match callW p n "m2c_const_view" [r₂.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "env_find" [r₃.headD 0, vis] m₃ with
  | none => none
  | some (r₄, m₄) =>
  if r₄.headD 0 = 0 then some (major, m₄) else
  if rdW (m₄.arr64 EREC) (r₄.tail.headD 0) ≠ 3 then some (major, m₄) else
  match callW p n "m2c_arms" [mode, vis, d, ro, cvjP, r₃.headD 0, r₄.tail.headD 0, major] m₄ with
  | none => none
  | some (r₅, m₅) => some (r₅.headD 0, m₅)

theorem m2cCtor_spec (p : Prog) (hp : p.lookup "m2c_ctor" = some m2cCtorL) (n : Nat) (s₀ : St)
    (mode vis d ro cvjP major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_ctor" [mode, vis, d, ro, cvjP, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cCtorW p n s₀.mem mode vis d ro cvjP major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cCtorL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "pi_result", callW_spec p n "get_app_fn", callW_spec p n "m2c_const_view",
    callW_spec p n "env_find", callW_spec p n "m2c_arms"] <;>
  simp_all [-UInt64.toNat_add, m2cCtorW, EREC, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- Model of `m2c_arms`. -/
def m2cArmsW (p : Prog) (n : Nat) (m : Mem) (mode vis d ro cvjP T indP major : Word) :
    Option (Word × Mem) :=
  if rdW (m.arr64 EREC) (ro + 9) ≠ 0 then
    match callW p n "m2c_k" [mode, vis, d, T, major, rdW (m.arr64 EREC) ro,
        rdW (m.arr64 EREC) (cvjP + 3), rdW (m.arr64 EREC) (cvjP + 5)] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)
  else if rdW (m.arr64 EREC) (ro + 10) ≠ 0 then
    match callW p n "m2c_eta" [mode, vis, d, T, indP, major] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)
  else
    match callW p n "m2c_and" [mode, vis, d, T, major, rdW (m.arr64 EREC) ro,
        rdW (m.arr64 EREC) (cvjP + 3), rdW (m.arr64 EREC) (cvjP + 5)] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)

theorem m2cArms_spec (p : Prog) (hp : p.lookup "m2c_arms" = some m2cArmsL) (n : Nat) (s₀ : St)
    (mode vis d ro cvjP T indP major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_arms" [mode, vis, d, ro, cvjP, T, indP, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cArmsW p n s₀.mem mode vis d ro cvjP T indP major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cArmsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "m2c_k", callW_spec p n "m2c_eta", callW_spec p n "m2c_and"] <;>
    finish [m2cArmsW]

/-- Model of `m2c_pre`: the five result words. -/
def m2cPreW (p : Prog) (n : Nat) (m : Mem) (mode vis d major : Word) :
    Option (List Word × Mem) :=
  match callW p n "infer_io" [mode, vis, d, major] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  match callW p n "get_app_fn" [r₂.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₃.headD 0 >>> 28 ≠ 3 then some ([0, 0, 0, 0, 0], m₃) else
  match callW p n "m2c_const_view" [r₃.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "ls_node" [r₄.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some ([1, r₂.headD 0, r₄.headD 0, r₄.tail.headD 0, r₅.tail.headD 0], m₅)

theorem m2cPre_spec (p : Prog) (hp : p.lookup "m2c_pre" = some m2cPreL) (n : Nat) (s₀ : St)
    (mode vis d major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_pre" [mode, vis, d, major]
    ⦃fun r s' => LocEq s' s₀ ∧ m2cPreW p n s₀.mem mode vis d major = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cPreL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "infer_io", callW_spec p n "whnf", callW_spec p n "get_app_fn",
    callW_spec p n "m2c_const_view", callW_spec p n "ls_node"] <;>
  simp_all [-UInt64.toNat_add, m2cPreW, BinOp.eval, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- Model of `m2c_check`. -/
def m2cCheckW (p : Prog) (n : Nat) (m : Mem) (mode vis d tmaj fab major : Word) :
    Option (Word × Mem) :=
  match callW p n "fab_scope_ok" [d, fab, major] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 = 0 then some (major, m₁) else
  match callW p n "infer_io" [mode, vis, d, fab] m₁ with
  | none => none
  | some (r₂, m₂) =>
  match callW p n "defeq" [mode, vis, d, tmaj, r₂.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₃.headD 0 = 0 then some (major, m₃) else
  if mode &&& 1 = 0 then
    match callW p n "proof_irrel" [mode, vis, d, fab, major] m₃ with
    | none => none
    | some (r₄, m₄) => if r₄.headD 0 ≠ 0 then some (fab, m₄) else some (major, m₄)
  else some (fab, m₃)

theorem m2cCheck_spec (p : Prog) (hp : p.lookup "m2c_check" = some m2cCheckL) (n : Nat) (s₀ : St)
    (mode vis d tmaj fab major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_check" [mode, vis, d, tmaj, fab, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cCheckW p n s₀.mem mode vis d tmaj fab major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cCheckL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "fab_scope_ok", callW_spec p n "infer_io", callW_spec p n "defeq",
      callW_spec p n "proof_irrel"] <;>
    finish [m2cCheckW]

/-- Model of `m2c_k`. -/
def m2cKW (p : Prog) (n : Nat) (m : Mem) (mode vis d T major ctor lpl cnP : Word) :
    Option (Word × Mem) :=
  match callW p n "m2c_pre" [mode, vis, d, major] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 = 0 then some (major, m₁) else
  if r₁.tail.tail.headD 0 ≠ T then some (major, m₁) else
  if lpl ≠ r₁.tail.tail.tail.tail.headD 0 then some (major, m₁) else
  match callW p n "m2c_k2" [mode, vis, d, ctor, cnP, r₁.tail.headD 0, r₁.tail.tail.tail.headD 0,
      major] m₁ with
  | none => none
  | some (r₂, m₂) => some (r₂.headD 0, m₂)

theorem m2cK_spec (p : Prog) (hp : p.lookup "m2c_k" = some m2cKL) (n : Nat) (s₀ : St)
    (mode vis d T major ctor lpl cnP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_k" [mode, vis, d, T, major, ctor, lpl, cnP]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cKW p n s₀.mem mode vis d T major ctor lpl cnP = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cKL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "m2c_pre", callW_spec p n "m2c_k2"] <;>
  simp_all [-UInt64.toNat_add, m2cKW, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- Model of `m2c_k2`. -/
def m2cK2W (p : Prog) (n : Nat) (m : Mem) (mode vis d ctor cnP tmaj ust major : Word) :
    Option (Word × Mem) :=
  match callW p n "get_app_args" [tmaj] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.tail.headD 0 < cnP then some (major, m₁) else
  match callW p n "intern_const" [ctor, ust] m₁ with
  | none => none
  | some (r₂, m₂) =>
  match callW p n "mk_app_n" [r₂.headD 0, r₁.headD 0, cnP] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "m2c_check" [mode, vis, d, tmaj, r₃.headD 0, major] m₃ with
  | none => none
  | some (r₄, m₄) => some (r₄.headD 0, m₄)

theorem m2cK2_spec (p : Prog) (hp : p.lookup "m2c_k2" = some m2cK2L) (n : Nat) (s₀ : St)
    (mode vis d ctor cnP tmaj ust major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_k2" [mode, vis, d, ctor, cnP, tmaj, ust, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cK2W p n s₀.mem mode vis d ctor cnP tmaj ust major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cK2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "get_app_args", callW_spec p n "intern_const", callW_spec p n "mk_app_n",
    callW_spec p n "m2c_check"] <;>
  simp_all [-UInt64.toNat_add, m2cK2W, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr] <;>
  (intro h1; exact absurd h1 (UInt64.not_lt.mpr ‹_›))

/-- Model of `m2c_eta` (the record words read at entry). -/
def m2cEtaW (p : Prog) (n : Nat) (m : Mem) (mode vis d T indP major : Word) :
    Option (Word × Mem) :=
  match callW p n "m2c_pre" [mode, vis, d, major] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 = 0 then some (major, m₁) else
  match callW p n "get_app_args" [r₁.tail.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  match callW p n "caps_never_zero" [rdW (m.arr64 EREC) (indP + 2), rdW (m.arr64 EREC) (indP + 3),
      r₁.tail.tail.tail.headD 0, rdW (m.arr64 EREC) (indP + 12), rdW (m.arr64 EREC) (indP + 13),
      rdW (m.arr64 EREC) (indP + 14)] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₁.tail.tail.headD 0 ≠ T then some (major, m₃) else
  if r₂.tail.headD 0 ≠ rdW (m.arr64 EREC) (indP + 7) then some (major, m₃) else
  if r₁.tail.tail.tail.tail.headD 0 ≠ rdW (m.arr64 EREC) (indP + 3) then some (major, m₃) else
  if r₃.headD 0 = 0 then some (major, m₃) else
  match callW p n "m2c_eta2" [vis, d, T, rdW (m.arr64 EREC) (indP + 6),
      rdW (m.arr64 EREC) (indP + 8), r₂.headD 0, r₂.tail.headD 0, r₁.tail.tail.tail.headD 0,
      major] m₃ with
  | none => none
  | some (r₄, m₄) => some (r₄.headD 0, m₄)

theorem m2cEta_spec (p : Prog) (hp : p.lookup "m2c_eta" = some m2cEtaL) (n : Nat) (s₀ : St)
    (mode vis d T indP major : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_eta" [mode, vis, d, T, indP, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cEtaW p n s₀.mem mode vis d T indP major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cEtaL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "m2c_pre", callW_spec p n "get_app_args", callW_spec p n "caps_never_zero",
    callW_spec p n "m2c_eta2"] <;>
  simp_all [-UInt64.toNat_add, m2cEtaW, EREC, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

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

/-- Model of `m2c_and`. -/
def m2cAndW (p : Prog) (n : Nat) (m : Mem) (mode vis d T major ctor lpl cnP : Word) :
    Option (Word × Mem) :=
  match callW p n "pin_at" [11] m with
  | none => none
  | some (r₁, m₁) =>
  if T ≠ r₁.headD 0 then some (major, m₁) else
  match callW p n "m2c_pre" [mode, vis, d, major] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 = 0 then some (major, m₂) else
  match callW p n "get_app_args" [r₂.tail.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "and_rescue_slots" [vis, ctor, cnP, r₂.tail.tail.tail.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  if r₂.tail.tail.headD 0 ≠ T then some (major, m₄) else
  if r₃.tail.headD 0 ≠ cnP then some (major, m₄) else
  if lpl ≠ r₂.tail.tail.tail.tail.headD 0 then some (major, m₄) else
  if r₄.headD 0 = 0 then some (major, m₄) else
  match callW p n "m2c_and2" [mode, vis, d, ctor, T, r₂.tail.headD 0, r₃.headD 0, r₃.tail.headD 0,
      r₂.tail.tail.tail.headD 0, major] m₄ with
  | none => none
  | some (r₅, m₅) => some (r₅.headD 0, m₅)

theorem m2cAnd_spec (p : Prog) (hp : p.lookup "m2c_and" = some m2cAndL) (n : Nat) (s₀ : St)
    (mode vis d T major ctor lpl cnP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "m2c_and" [mode, vis, d, T, major, ctor, lpl, cnP]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cAndW p n s₀.mem mode vis d T major ctor lpl cnP = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cAndL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "pin_at", callW_spec p n "m2c_pre", callW_spec p n "get_app_args",
    callW_spec p n "and_rescue_slots", callW_spec p n "m2c_and2"] <;>
  simp_all [-UInt64.toNat_add, m2cAndW, Cmp.eval, LocEq,
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

/-- Model of `m2c_and2`. -/
def m2cAnd2W (p : Prog) (n : Nat) (m : Mem) (mode vis d ctor T tmaj to tn ust major : Word) :
    Option (Word × Mem) :=
  match callW p n "mk_proj" [T, 0, major] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "mk_proj" [T, 1, major] m₁ with
  | none => none
  | some (r₂, m₂) =>
  match and2Push m₂ to tn (r₁.headD 0) (r₂.headD 0) with
  | none => none
  | some m₃ =>
  match callW p n "intern_const" [ctor, ust] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "mk_app_n" [r₄.headD 0, to, tn + 2] m₄ with
  | none => none
  | some (r₅, m₅) =>
  match callW p n "m2c_check" [mode, vis, d, tmaj, r₅.headD 0, major] m₅ with
  | none => none
  | some (r₆, m₆) => some (r₆.headD 0, m₆)

theorem m2cAnd2_spec (p : Prog) (hp : p.lookup "m2c_and2" = some m2cAnd2L) (n : Nat) (s₀ : St)
    (mode vis d ctor T tmaj to tn ust major : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "m2c_and2" [mode, vis, d, ctor, T, tmaj, to, tn, ust, major]
    ⦃fun r s' => LocEq s' s₀ ∧
      m2cAnd2W p n s₀.mem mode vis d ctor T tmaj to tn ust major = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cAnd2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "mk_proj", callW_spec p n "intern_const", callW_spec p n "mk_app_n",
    callW_spec p n "m2c_check"] <;>
  simp_all [-UInt64.toNat_add, m2cAnd2W, and2Push, Mem.len64, SPN, CTL, BinOp.eval, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

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
