module

public import ConLeche.Kernel.ExprOps

public section

/-!
# A stored nested rule's reading

An auxiliary recursor's rules (a nested block's recursor at an OUTSIDE
major) fire `.nested lvls pins` (`auxRuleFire`): the class's levels and
its parameters closed over the rule prefix.  `NestedRead` is what that
datum is, read against the recursor type: the facts `EnvWF`'s `.nested`
clause records — the pins are syntactically well formed in the rule-prefix
context, and the recursor type's major domain applies the class's
inductive at `lvls` to the pins' liftings past the index binders,
followed by the index variables in order — and the pins' count.  The
generated stage establishes it (`genStage_nestedRead`).
-/

namespace ConLeche

/-- **A `.nested` datum, read against the recursor type `tyA`** (major
index `mI`, rule prefix `rP`, the class's parameter count `cnP`,
constants resolving by `resolves`, levels declared in `lps`). -/
@[expose] def NestedRead (resolves : Expr → Bool) (lps : List Name) (tyA : Expr)
    (mI rP cnP : Nat) (lvls : List Level) (pins : List Expr) : Prop :=
  rP ≤ mI ∧
  (∀ l ∈ lvls, l.allParamsDefined lps = true) ∧
  (∀ pin ∈ pins, pin.hasFvar = false ∧
    pin.allLevelParamsDefined lps = true ∧
    resolves pin = true ∧
    pin.looseBVarsBounded rP = true) ∧
  ∃ pre dom body D,
    tyA.stripPis mI = some (pre, .forallE dom body) ∧
    dom.getAppFn = .const D lvls ∧
    dom.getAppArgs =
      pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
        (List.range (mI - rP)).map
          (fun i => Expr.bvar (mI - rP - 1 - i)) ∧
    pins.length = cnP

end ConLeche
