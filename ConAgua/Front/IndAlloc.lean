import ConAgua.Front.IndFields
import ConAgua.Front.IndRel

/-!
# The scratch arrays' allocators: models and specs

`ifr_alloc(n)`, `ifl_alloc(n)` (`IndFields.lean`) bump word `0` of `IFR`/`IFL` (their top) and
return the first index of the `n` words above it; `ifl_push(x)` allocates one word of `IFL` and
writes `x` there. Their models `allocW`, `pushLW`; shared by the fields pass and the apply step.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena

namespace L.Front.Ind

/-- **The model of `ifr_alloc`/`ifl_alloc`** on array `a`: the index and the memory after. -/
def allocW (m : Mem) (a : ArrId) (n : Word) : Option (Word × Mem) :=
  if m.len64 a = 0 then none
  else if m.len64 a < rdW (m.arr64 a) 0 + 1 then none
  else if m.len64 a - (rdW (m.arr64 a) 0 + 1) < n then none
  else some (rdW (m.arr64 a) 0 + 1, m.set64 a 0 (rdW (m.arr64 a) 0 + 1 - 1 + n))

/-- After `ifl_alloc(1)`: the write. -/
def pushK (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (o, m) => some (o, m.set64 IFL o x)

@[arena_grind =] theorem pushK_some (x o : Word) (m : Mem) :
    pushK x (some (o, m)) = some (o, m.set64 IFL o x) := rfl

/-- **The model of `ifl_push(x)`.** -/
def pushLW (m : Mem) (x : Word) : Option (Word × Mem) := pushK x (allocW m IFL 1)

section specs
variable (p : Prog)

theorem ifrAlloc_spec (hp : p.lookup "ifr_alloc" = some ifrAlloc) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifr_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ allocW s₀.mem IFR k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ifrAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;> finish [allocW]

theorem iflAlloc_spec (hp : p.lookup "ifl_alloc" = some iflAlloc) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifl_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ allocW s₀.mem IFL k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iflAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;> finish [allocW]

theorem iflPush_spec (ha : p.lookup "ifl_alloc" = some iflAlloc)
    (hp : p.lookup "ifl_push" = some iflPush) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifl_push" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ pushLW s₀.mem x = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iflPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        iflAlloc_spec p ha n] <;> finish [pushLW]

end specs

end L.Front.Ind
