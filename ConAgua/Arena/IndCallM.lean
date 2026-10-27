import ConAgua.Arena.WhnfBase
import ConAgua.Arena.IndIface

/-!
# How a model reads a call of the core (lane `loopt2`'s `CallM`, moved here by lane `indstaget`)

A model that calls the core's entry points (`whnf_top`, `infer_type_core`, `ensure_sort_core`,
`is_def_eq_core`) and `lvl_eq_c` reads the call through a parameter `c : CallM`, always
`realCall p` (the program's own `callW`) now: the second reading `stubCall` (the stubs' `stubM`,
for the `StageR` proofs through the stub contracts) went with those proofs (lane `cleanup`).
Moved from `DeclCvg.lean` so that the inductive stage's models (below `DeclCvg`) can use it.
-/

open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-- **How a model reads a call** of the core's entry points, at an L fuel. -/
abbrev CallM := Nat → FnName → List Word → Mem → Option (List Word × Mem)

/-- The program's own reading of a call. -/
def realCall (p : Prog) : CallM := fun n f args m => callW p n f args m

/-- A call reading is **the L side of every call** of `p`. -/
def CallSpec (p : Prog) (c : CallM) : Prop :=
  ∀ (n : Nat) (f : FnName) (args : List Word) (s₀ : St),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
    ⦃fun r s' => LocEq s' s₀ ∧ c n f args s₀.mem = some (r, s'.mem); ⊤⦄

theorem realCall_spec (p : Prog) : CallSpec p (realCall p) :=
  fun n f args s₀ => callW_spec p n f args s₀

end L.Arena
