import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Scan.Common
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# BlockShapeAllCtorsGo

`ccW`, `acGoW`, `acK1`, `acGoW_nil`, `acGoW_cons`, `acK1_some` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models -/

/-- **The model of `block_shape_ctors_copy`**: the length and the memory after the copy. -/
def ccW (n : Nat) (m : Mem) (off q k : Word) : Option (Word × Mem) :=
  match n with
  | 0 => none
  | n + 1 =>
    match copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with
    | none => none
    | some m1 => some (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3), m1)

mutual
/-- **The model of `block_shape_all_ctors_go`**: the memory after the copies. -/
def acGoW : Nat → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _ => none
  | n + 1, m, off, l, q, k =>
    if l = 0 then some m else acK1 n off l q k (ccW n m off q k)

/-- After `block_shape_ctors_copy`. -/
def acK1 (n : Nat) (off l q k : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (cl, m1) => acGoW n m1 (off + 1) (l - 1) q (k + cl)
end

section arms
variable (n : Nat) (m m1 : Mem) (off l q k cl : Word)
theorem acGoW_nil (h : l = 0) : acGoW (n + 1) m off l q k = some m := by simp [acGoW, h]
theorem acGoW_cons (h : l ≠ 0) : acGoW (n + 1) m off l q k = acK1 n off l q k (ccW n m off q k) := by
  simp [acGoW, h]
theorem acK1_some : acK1 n off l q k (some (cl, m1)) = acGoW n m1 (off + 1) (l - 1) q (k + cl) := by
  simp [acK1]
end arms

grind_pattern [ind_grind] acGoW_nil => acGoW (n + 1) m off l q k
grind_pattern [ind_grind] acGoW_cons => acGoW (n + 1) m off l q k
grind_pattern [ind_grind] acK1_some => acK1 n off l q k (some (cl, m1))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
  (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
  (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
  (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)

include hcp hcc in
theorem blockShapeCtorsCopy_spec (n : Nat) (s₀ : St) (off q k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_ctors_copy" [off, q, k]
    ⦃fun r s' => LocEq s' s₀ ∧ ccW n s₀.mem off q k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hcc]
  simp only [callFn, blockShapeCtorsCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwCopy_spec p hcp n] <;>
      finish (gen := 20) [rdW_eq, ccW]

include hcp hcc hg in
theorem blockShapeAllCtorsGo_spec (n : Nat) : ∀ (s₀ : St) (off l q k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_all_ctors_go" [off, l, q, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ acGoW n s₀.mem off l q k = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off l q k; rw [invoke_eq _ hg]; simp only [callFn, blockShapeAllCtorsGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off l q k
    rw [invoke_eq _ hg]
    simp only [callFn, blockShapeAllCtorsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        blockShapeCtorsCopy_spec p hcp hcc n, ih] <;>
      finish (gen := 20)

/-- **`block_shape_all_ctors` is its model `acW`** (generated). -/
l_model blockShapeAllCtors_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
    (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
    (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)
  fns [hp ↦ acW list]
  specs [numCtorsOf_spec p hnc n, iwAlloc_specW p ha n, blockShapeAllCtorsGo_spec p hcp hcc hg n]
  grind [ind_grind] finish [rdW_eq] gen 20

end spec

end L.Ind

end
