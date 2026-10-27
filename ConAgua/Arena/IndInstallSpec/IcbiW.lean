import ConAgua.Arena.IndSumSpec.ConsSumCtors

/-!
# IcbiW

`wrER_append`, `iirK5`, `icbiK4`, `icbiW`, `icbiK1`, `icbiK2` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem wrER_append : ∀ (xs ys : List Word) (m : Mem) (q : Word),
    wrER m q (xs ++ ys) = wrER (wrER m q xs) (q + UInt64.ofNat xs.length) ys
  | [], ys, m, q => by simp [wrER]
  | x :: xs, ys, m, q => by
    simp only [List.cons_append, wrER]
    rw [wrER_append xs ys]
    congr 1
    simp only [List.length_cons]
    rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm (UInt64.ofNat xs.length)]; rfl

/-- The four writes, one continuation each. -/
def iirK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([q], m5)
/-! ## `cons_block_inds` -/

/-- After the rest. -/
def icbiK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- **The model of `cons_block_inds(p1, is_rec, o, l, vis, i)`** at exec fuel `n`. -/
def icbiW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, p1, isRec, o, l, vis, i =>
    if l = 0 then some ([vis], m)
    else icbiK1 p n p1 isRec o l vis i (callW p n "block_caps_at" [p1, i, isRec] m)
/-- After the capability record: the `.indInfo` record. -/
def icbiK1 (p : Prog) (n : Nat) (p1 isRec o l vis i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbiK2 p n p1 isRec o l vis i
      (callW p n "ind_info_rec" [rdW (m.arr64 IW) o, r.headD 0] m)
/-- After the record: the push. -/
def icbiK2 (p : Prog) (n : Nat) (p1 isRec o l vis i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbiK3 p n p1 isRec o l i (callW p n "env_push" [vis, r.headD 0] m)
/-- After the push: the rest. -/
def icbiK3 (p : Prog) (n : Nat) (p1 isRec o l i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbiK4 (icbiW p n m p1 isRec (o + 1) (l - 1) (r.headD 0) (i + 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (p1 isRec o l vis i : Word) (r : List Word)
theorem icbiW_nil (h : l = 0) : icbiW p (n + 1) m p1 isRec o l vis i = some ([vis], m) := by
  simp [icbiW, h]
theorem icbiW_cons (h : l ≠ 0) : icbiW p (n + 1) m p1 isRec o l vis i =
    icbiK1 p n p1 isRec o l vis i (callW p n "block_caps_at" [p1, i, isRec] m) := by simp [icbiW, h]
theorem icbiK1_some : icbiK1 p n p1 isRec o l vis i (some (r, m)) = icbiK2 p n p1 isRec o l vis i
    (callW p n "ind_info_rec" [rdW (m.arr64 IW) o, r.headD 0] m) := by simp [icbiK1]
theorem icbiK2_some : icbiK2 p n p1 isRec o l vis i (some (r, m)) =
    icbiK3 p n p1 isRec o l i (callW p n "env_push" [vis, r.headD 0] m) := by simp [icbiK2]
theorem icbiK3_some : icbiK3 p n p1 isRec o l i (some (r, m)) =
    icbiK4 (icbiW p n m p1 isRec (o + 1) (l - 1) (r.headD 0) (i + 1)) := by simp [icbiK3]
theorem icbiK4_some : icbiK4 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] icbiW_nil icbiW_cons icbiK1_some icbiK2_some icbiK3_some icbiK4_some

theorem icbi_spec (p : Prog) (hp : p.lookup "cons_block_inds" = some consBlockInds) (n : Nat) :
    ∀ (s₀ : St) (p1 isRec o l vis i : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cons_block_inds" [p1, isRec, o, l, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ icbiW p n s₀.mem p1 isRec o l vis i = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ p1 isRec o l vis i; rw [invoke_eq _ hp]; simp only [callFn, consBlockInds]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ p1 isRec o l vis i
    rw [invoke_eq _ hp]
    simp only [callFn, consBlockInds]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "block_caps_at", callW_spec p n "ind_info_rec", callW_spec p n "env_push", ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

end
