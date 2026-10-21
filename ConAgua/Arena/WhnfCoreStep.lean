import ConAgua.Arena.WhnfCoreRefine

/-!
# `whnf_core_step` and its `app` arm refine `whnfCoreStep`

The step dispatches on the handle's tag after the view's checks; the `app` arm (`whnf_core_app`,
`WhnfCore.lean`) walks the spine (`get_app_spine`), normalises the head (the knot's `whnfCore`
slot), takes the reduct's own spine (`head_and_args`) and runs the batched β/ι walk (`whnf_app`),
then puts the stack top back. Twin: `whnfCoreStep` (`Arena/Core.lean:2351`), its `.app` clause
named `whnfCoreAppT` here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The `app` arm -/

/-- The twin's `.app` clause of `whnfCoreStep`. -/
def whnfCoreAppT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (depth : Nat)
    (e : EIdx) : AM WhnfStep := do
  let sp ← getAppSpine coreWalkFuel e
  let v ← r.whnfCore cheap depth sp.1
  let same := v == sp.1
  let hv ← headAndArgs v
  whnfApp mode r fe depth v hv.1 hv.2 same sp.2.1 sp.2.2 0

/-- The model of `whnf_core_app2`. -/
def coreApp2W (p : Prog) (n : Nat) (m : Mem) (mode vis d v h so sn : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "head_and_args" [v] m with
  | none => none
  | some (r₃, m₃) =>
    match callW p n "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0, r₃.tail.tail.headD 0,
        Cmp.evalW .eq v h, so, sn, 0] m₃ with
    | none => none
    | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)

theorem coreApp2W_some (p : Prog) (n : Nat) (m m₃ m₄ : Mem) (mode vis d v h so sn : Word)
    (r₃ r₄ : List Word) (h₃ : callW p n "head_and_args" [v] m = some (r₃, m₃))
    (h₄ : callW p n "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0, r₃.tail.tail.headD 0,
        Cmp.evalW .eq v h, so, sn, 0] m₃ = some (r₄, m₄)) :
    coreApp2W p n m mode vis d v h so sn = some (r₄.headD 0, r₄.tail.headD 0, m₄) := by
  simp only [coreApp2W, h₃, h₄]

theorem coreApp2_spec (p : Prog) (hp : p.lookup "whnf_core_app2" = some whnfCoreApp2L) (n : Nat)
    (s₀ : St) (mode vis d v h so sn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_app2" [mode, vis, d, v, h, so, sn]
    ⦃fun r s' => LocEq s' s₀ ∧
      coreApp2W p n s₀.mem mode vis d v h so sn = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, whnfCoreApp2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "whnf_app", callW_spec p n "head_and_args"] <;>
  simp_all [coreApp2W, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- The model of `whnf_core_app`. -/
def coreAppW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "get_app_spine" [e] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      match callW p n "whnf_core_app2" [mode, vis, d, r₂.headD 0, r₁.headD 0, r₁.tail.headD 0,
          r₁.tail.tail.headD 0] m₂ with
      | none => none
      | some (r₄, m₄) =>
        some (r₄.headD 0, r₄.tail.headD 0, m₄.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem coreAppW_some (p : Prog) (n : Nat) (m m₁ m₂ m₄ : Mem) (mode cheap vis d e : Word)
    (r₁ r₂ r₄ : List Word)
    (h₁ : callW p n "get_app_spine" [e] m = some (r₁, m₁))
    (h₂ : callW p n "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ = some (r₂, m₂))
    (h₄ : callW p n "whnf_core_app2" [mode, vis, d, r₂.headD 0, r₁.headD 0, r₁.tail.headD 0,
          r₁.tail.tail.headD 0] m₂ = some (r₄, m₄)) :
    coreAppW p n m mode cheap vis d e =
      some (r₄.headD 0, r₄.tail.headD 0, m₄.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  simp only [coreAppW, h₁, h₂, h₄]

theorem coreApp_spec (p : Prog) (hp : p.lookup "whnf_core_app" = some whnfCoreAppL) (n : Nat)
    (s₀ : St) (mode cheap vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_app" [mode, cheap, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      coreAppW p n s₀.mem mode cheap vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, whnfCoreAppL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "get_app_spine", callW_spec p n "whnf_core", callW_spec p n "whnf_core_app2"] <;>
  simp_all [coreAppW, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL] <;>
  (congr 1; rw [Array.getElem?_eq_getElem]; rfl)

end L.Arena
