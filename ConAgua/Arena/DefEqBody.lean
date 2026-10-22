import ConAgua.Arena.DefEqStuckTail
import ConAgua.Arena.DefEqMidLazy2
import ConAgua.Arena.KnotSlot

/-!
# `defeq_body` refines `defeqBody`; the knot's `defeq` slot one level up (lane `defeq`)

The callW pattern (`DefEqStuckTail.lean`): a word model of `defeq_body` with its callees through
their runs (`dbW`), the L spec by `vcgen` + `simp_all`, the refinement from the callees' specs
(`is_bool_true`, `has_fvar`, `bool_true_shortcut`, `quick_defeq` twice, `prop_irrel`, the cheap
`whnf_core` slot twice, `lazy_delta_reduction`, `defeq_tail`), threaded through the twin's `do`
block by `coreRef_bind`. `DefeqBodySpec p n` (`KnotSlot.lean`) is then a theorem
(`defeqBody_refines`), and with `defeq_refines` the slot step `defeqSlot_step`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- What `defeq_body`'s spec needs of a program. -/
structure DefeqBodyProg (p : Prog) : Prop where
  stuck : StuckProg p
  iota : IotaProg' p
  lazy : LazyProg p
  knot : KnotProg p
  hasFvar : p.lookup "has_fvar" = some hasFvarL
  body : p.lookup "defeq_body" = some defeqBodyL

/-- The callees `defeq_body`'s refinement assumes. -/
structure DefeqBodyCallees (p : Prog) : Prop where
  stuck : StuckCallees p
  lazy : LazyCallees p

/-! ## The model -/

section dbK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

/-- Past `lazy_delta_reduction`'s run. -/
def dbK7 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if r.headD 0 = 1 then some (1, m)
    else call1W p n "defeq_tail" [mode, vis, d, r.tail.headD 0, r.tail.tail.headD 0] m

/-- Past the second `quick_defeq`'s run. -/
def dbK6 (a1 b1 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (r.tail.headD 0, m)
    else dbK7 p n mode vis d (callW p n "lazy_delta_reduction" [mode, vis, d, a1, b1] m)

/-- Past the second cheap `whnf_core`'s run. -/
def dbK5 (a1 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    dbK6 p n mode vis d a1 (r.headD 0) (callW p n "quick_defeq" [mode, vis, d, a1, r.headD 0] m)

/-- Past the first cheap `whnf_core`'s run. -/
def dbK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => dbK5 p n mode vis d b (r.headD 0) (callW p n "whnf_core" [mode, 1, vis, d, b] m)

/-- Past `prop_irrel`'s run. -/
def dbK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m)
    else dbK4 p n mode vis d b (callW p n "whnf_core" [mode, 1, vis, d, a] m)

/-- Past the first `quick_defeq`'s run. -/
def dbK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (r.tail.headD 0, m)
    else dbK3 p n mode vis d a b (callW p n "prop_irrel" [mode, vis, d, a, b] m)

/-- Past the `Bool.true` shortcut (`sc` its verdict word). -/
def dbKsc (sc : Word) (m : Mem) : Option (Word × Mem) :=
  if sc ≠ 0 then some (1, m)
  else dbK2 p n mode vis d a b (callW p n "quick_defeq" [mode, vis, d, a, b] m)

/-- Past `has_fvar`'s run (`bt` is `is_bool_true`'s word). -/
def dbK1b (bt : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if bt ≠ 0 ∧ ((mode >>> 1) &&& 1 ≠ 0 ∨ r.headD 0 = 0) then
      match callW p n "bool_true_shortcut" [mode, vis, d, a] m with
      | none => none
      | some (r', m') => dbKsc p n mode vis d a b (r'.headD 0) m'
    else dbKsc p n mode vis d a b 0 m

/-- Past `is_bool_true`'s run. -/
def dbK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => dbK1b p n mode vis d a b (r.headD 0) (callW p n "has_fvar" [a] m)

/-- **The model of `defeq_body`.** -/
def dbW (m : Mem) : Option (Word × Mem) :=
  if a = b then some (1, m)
  else if d >>> 63 ≠ 0 then none
  else dbK1 p n mode vis d a b (callW p n "is_bool_true" [b] m)

variable (r : List Word) (m : Mem) (bt a1 : Word)
theorem dbK1_some : dbK1 p n mode vis d a b (some (r, m)) =
    dbK1b p n mode vis d a b (r.headD 0) (callW p n "has_fvar" [a] m) := rfl
theorem dbK2_some : dbK2 p n mode vis d a b (some (r, m)) =
    if r.headD 0 ≠ 0 then some (r.tail.headD 0, m)
    else dbK3 p n mode vis d a b (callW p n "prop_irrel" [mode, vis, d, a, b] m) := rfl
theorem dbK4_some : dbK4 p n mode vis d b (some (r, m)) =
    dbK5 p n mode vis d b (r.headD 0) (callW p n "whnf_core" [mode, 1, vis, d, b] m) := rfl
theorem dbK5_some : dbK5 p n mode vis d a1 (some (r, m)) =
    dbK6 p n mode vis d a1 (r.headD 0) (callW p n "quick_defeq" [mode, vis, d, a1, r.headD 0] m) := rfl

end dbK

theorem defeqBody_spec (p : Prog) (hp : DefeqBodyProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_body" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ dbW p n mode vis d a b s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.body]
  simp only [callFn, defeqBodyL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "is_bool_true",
      callW_spec p n "has_fvar", callW_spec p n "bool_true_shortcut", callW_spec p n "quick_defeq",
      callW_spec p n "prop_irrel", callW_spec p n "whnf_core", callW_spec p n "lazy_delta_reduction",
      callW_spec p n "defeq_tail"] <;>
  simp_all [dbW, dbK1, dbK1b, dbKsc, dbK2, dbK3, dbK4, dbK5, dbK6, dbK7, call1W, LocEq, BinOp.eval,
    St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

end L.Arena
