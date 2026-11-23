module

public import ConAgua.Arena.JustifySideRefSide
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.JustifySideModels
import all ConAgua.Arena.JustifyIface

@[expose] public section

/-!
# The record mates: the refinements (lane compare)

`solution_of(cnt)` refines `recordMatesGo ∅` over the front's records (`solutionOf`'s mates):
after it the rows `MAT*` hold the twin's map (`MatesR`), each list a tier-0 `EREC` slice. With
`index_to_solution` (`SolIdxR`) this is `SolR` of `solutionOf`.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option autoImplicit false

open Std.WP
open scoped Lean.Order
open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP DeclsF DeclAtF DeclAt CVAt dw)

/-! ## `mates_set` -/

/-- `mates_set(w, o, l)`'s memory: the row of `w` in its tag's array. -/
def matSetM (m : Mem) (w o l : Word) : Mem :=
  (m.set64 (matArr (rowTag w)) (idxW w <<< 1) o).set64 (matArr (rowTag w)) ((idxW w <<< 1) + 1) l

theorem matesSet_spec (p : Prog) (hp : p.lookup "mates_set" = some matesSetL) (n : Nat) (s₀ : St)
    (w o l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mates_set" [w, o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ rowTier w = 0 ∧ rowTag w ≤ 2 ∧ s'.mem = matSetM s₀.mem w o l ∧
      rowIx w + 1 < (s₀.mem.arr64 (matArr (rowTag w))).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, matesSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, matSetM, matArr, rowTag_of, rowTier_of,
      Locals.init_cons_succ, Locals.init_cons_zero, MATA, MATS, MATN, rowIx, Mem.size_arr64_set64]
    all_goals (try rfl)
    all_goals (have := UInt64.lt_iff_toNat_lt.mp (idxW_lt w); simp [Nat.shiftLeft_eq] at *; omega)

end L.Arena
