import ConAgua.Arena.RecCheckSpec.EeK2
import ConAgua.Arena.RecCheckSpec.EraseFVarTys

/-!
# EeW

`eftF`, `eeW`, `eeK0`, `eeW_nil`, `eeW_cons`, `tteK1` and the lemmas only they use.
-/

noncomputable section

/-!
# `RecCheck`: `targetK53`, the L side (lane `indproofs3`, helper `rec`)

K.53′ at one recorded field: `strip_pis` (stub), the telescope check (`target_k53_tele`: both sides
erased by `erase_each`, compared by `sl_eq`), the head check (`target_k53_heads`: `get_app_fn_f`,
`get_app_args_f` stubs, `e_view`), the argument check (`target_k53_args`: erased indices, the
leaf's class `intern_const` + `mk_app_n_f` (stub) + `nest_occ`, then `target_class_match`).
L: `erase_each` is the twin's `mapM` as a self-recursion consing each result (`sl_cons`, D18); a
handle guard after `intern_const` (`mk_app_n_f`'s contract takes a handle).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callees at any exec fuel -/

def eftF : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, e => eftW n m e

mutual
def eeW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some ([0, 0], m) else eeK0 n o l (eftF n m (rdW (m.arr64 IW) o))
def eeK0 (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => eeK1 n (rv.headD 0) (eeW n m (o + 1) (l - 1))
end

section arms
variable (n : Nat) (m : Mem) (o l v : Word) (rv rr rc : List Word)
theorem eeW_nil (h : l = 0) : eeW (n + 1) m o l = some ([0, 0], m) := by simp [eeW, h]
theorem eeW_cons (h : ¬ l = 0) : eeW (n + 1) m o l = eeK0 n o l (eftF n m (rdW (m.arr64 IW) o)) := by
  simp [eeW, h]
end arms
attribute [ind_grind] eeW_nil eeW_cons

def tteK1 (n : Nat) (teo tel : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => tteK2 n r1 (eeW n m teo tel)

def tteW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, bso, bsl, teo, tel => tteK1 n teo tel (eeW n m bso bsl)

section arms
variable (n : Nat) (m : Mem) (bso bsl teo tel e : Word) (r1 r2 : List Word)
theorem tteW_succ : tteW (n + 1) m bso bsl teo tel = tteK1 n teo tel (eeW n m bso bsl) := rfl
end arms
attribute [ind_grind] tteW_succ

end L.Ind

end
end
