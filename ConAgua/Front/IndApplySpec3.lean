import ConAgua.Front.IndApplySpec2
import ConAgua.Front.IndFieldsSpec

/-!
# The apply step of an `inductive` line: word models and specs, III (the entries)

`apply_ind(v)`: `ind_fields`, `validate_ind_d`, `install_ind_d` in sequence (`applyIndW`);
`apply_ind_line(j)`: the line's one member (`next_member`, key `23`), applied (`applyIndLineW`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member

namespace L.Front.Ind

/-- The two entries, at their names in `p`. -/
structure IndLineLookups (p : Prog) : Prop where
  apply_ind : p.lookup "apply_ind" = some applyInd
  apply_ind_line : p.lookup "apply_ind_line" = some applyIndLine

/-- After a call returning a list of words: the list and the memory. -/
def lK {α : Type} (rest : List Word → Mem → Option α) : Option (List Word × Mem) → Option α
  | none => none
  | some (r, m) => rest r m

@[arena_grind =] theorem lK_none {α : Type} (rest : List Word → Mem → Option α) : lK rest none = none := rfl
@[arena_grind =] theorem lK_some {α : Type} (rest : List Word → Mem → Option α) (r : List Word) (m : Mem) :
    lK rest (some (r, m)) = rest r m := rfl

/-- **The model of `apply_ind(v)`.** -/
def applyIndW : Nat → Array UInt8 → Mem → Word → Option Mem
  | 0, _, _, _ => none
  | n + 1, b, m, v =>
    lK (fun r m₁ => pmK (fun oo np m₂ =>
        installW n b m₂ (r.headD 0) (r.tail.headD 0) oo (r.tail.tail.tail.headD 0)
          (r.tail.tail.tail.tail.headD 0) (r.tail.tail.tail.tail.tail.headD 0) np)
      (validateW n m₁ (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)
        (r.tail.tail.tail.tail.headD 0) (r.tail.tail.tail.tail.tail.headD 0)))
      (indFieldsW b m v)

section specs
variable (p : Prog) (hF : IndFieldLookups p) (hL : IndApplyLookups p) (hI : IndInstallLookups p)
  (hX : IndLineLookups p) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hF hL hI hX hb

theorem applyInd_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "apply_ind" [v]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyIndW n b s₀.mem v = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hX.apply_ind]
  simp only [callFn, applyInd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hno := hL.decl.expr.no_st8
    have h1 : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (v : Word),
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "ind_fields" [v]
        ⦃fun r s' => (LocEq s' s₁ ∧ indFieldsW b s₁.mem v = some (r, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ v => Triple.keep hno (indFields_spec p hF b hb n s₁ hm₁ v)
    have h2 : ∀ (s₁ : St) (to tn co cn ro rn : Word),
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "validate_ind_d" [to, tn, co, cn, ro, rn]
        ⦃fun r s' => (LocEq s' s₁ ∧
          validateW n s₁.mem to tn co cn ro rn = some ((r.headD 0, r.tail.headD 0), s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ to tn co cn ro rn => Triple.keep hno (validate_spec p hL n s₁ to tn co cn ro rn)
    have h3 : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (to tn oo on ro rn np : Word),
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "install_ind_d" [to, tn, oo, on, ro, rn, np]
        ⦃fun _ s' => (LocEq s' s₁ ∧ installW n b s₁.mem to tn oo on ro rn np = some s'.mem) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ to tn oo on ro rn np => Triple.keep hno (install_spec p hL hI b hb n s₁ hm₁ to tn oo on ro rn np)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, h1, h2, h3] <;>
        finish (gen := 20) [applyIndW]

end specs

end L.Front.Ind
