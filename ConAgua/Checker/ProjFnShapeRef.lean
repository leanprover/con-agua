import ConAgua.Checker.Entry
import ConAgua.Front.IndApplyRefine
import ConAgua.Arena.DeclCanonLvl
import ConAgua.Census.Attr

/-!
# `is_proj_fn_shape` against the twin

The word model `pfsW` of `is_proj_fn_shape` (`isProjFnShapeL`), its spec (`vcgen`), and the
refinement of `NIdx.isProjFnShape`: two `viewN`s (a `num` node, then its `str` prefix) and the
prefix's string compared to `"proj"` / `"projTable"` as a `POOL` slice. The L code aborts exactly
where a twin `viewN` fails (a handle past its tier's count, or in the scratch tier while it is off).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

open Std.WP
open scoped Lean.Order
open L L.Arena
open ConRon.Arena
open L.Front.Ind (nview_tier viewN_run decN_tag decN_idx rdW_add shr28_lt)

namespace L.Checker

/-! ## The model -/

/-- `is_proj_fn_shape`'s string test, at the `str` node's first word `k`. -/
def pfsStr (m : Mem) (k : Word) : Option Word :=
  if rdW (m.arr64 NSREC) (k + 2) ≠ 4 ∧ rdW (m.arr64 NSREC) (k + 2) ≠ 9 then some 0
  else if ¬ (rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1)) = 112 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 1) = 114 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 2) = 111 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 3) = 106) then some 0
  else if rdW (m.arr64 NSREC) (k + 2) = 4 then some 1
  else if ¬ (rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 4) = 84 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 5) = 97 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 6) = 98 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 7) = 108 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 8) = 101) then some 0
  else some 1

/-- `is_proj_fn_shape`'s prefix step: the `num` node's prefix word `q`. -/
def pfsPre (m : Mem) (q : Word) : Option Word :=
  if 4294967295 < q then none
  else if q >>> 28 ≠ 1 then some 0
  else if tierW q ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (36 + tierW q) ≤ idxW q then none
  else pfsStr m (idxW q * 8 + tierW q * 4)

/-- **The model of `is_proj_fn_shape(n)`.** -/
def pfsW (m : Mem) (n : Word) : Option Word :=
  if 4294967295 < n then none
  else if n >>> 28 ≠ 2 then some 0
  else if tierW n ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (38 + tierW n) ≤ idxW n then none
  else pfsPre m (rdW (m.arr64 NNREC) (idxW n * 4 + tierW n * 2))

/-! ## The spec -/

set_option maxHeartbeats 16000000 in
theorem pfs_spec (p : Prog) (hp : p.lookup "is_proj_fn_shape" = some isProjFnShapeL) (n : Nat)
    (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_proj_fn_shape" [h]
    ⦃fun r s' => s' = s₀ ∧ pfsW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, isProjFnShapeL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;>
        finish [pfsW, pfsPre, pfsStr, tierW, idxW]

end L.Checker
