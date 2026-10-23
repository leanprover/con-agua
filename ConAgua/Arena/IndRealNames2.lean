import ConAgua.Arena.IndRealNames

/-!
# `is_proj_fn_shape` discharged (lane `indproofs4`, helper `indproofs4-names`)
-/

set_option linter.deprecated false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ipf_rd64 (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW, Array.getD_eq_getD_getElem?]

theorem ipf_getElem (a : Array Word) (x : Word) (h : x.toNat < a.size) : a[x.toNat] = rdW a x := by
  simp [rdW, h]

/-! ## `is_proj_fn_shape(n)` (a read of the name store) -/

/-- `is_proj_fn_shape` (calls nothing). -/
def ipfProg : Prog := [("is_proj_fn_shape", L.Checker.isProjFnShapeL)]

def ipfFns : List FnName := ipfProg.map (·.1)

/-- `is_proj_fn_shape` writes nothing. -/
theorem ipfProg_closed : closedA ipfProg [] [] ipfFns = true := by decide +kernel

abbrev IpfF (p : Prog) : Prop := ProgHas p ipfProg

/-- **The model of `is_proj_fn_shape`.** -/
noncomputable def ipfF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ipfProg "is_proj_fn_shape" m args

theorem ipfF_spec (p : Prog) (hp : IpfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_proj_fn_shape" args
    ⦃fun r s' => LocEq s' s₀ ∧ ipfF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ipfProg_closed (hp.agree ipfFns) (by decide) n s₀ args

theorem ipfF_frame {m m' : Mem} {args r : List Word} (h : ipfF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ipfProg_closed (by decide) (run_of_callW hc)).1

/-- The string test on the slice `(o, l)`. -/
def ipfB (m : Mem) (o l : Word) : Word :=
  if l ≠ 4 ∧ l ≠ 9 then 0
  else if rdW (m.arr64 POOL) o ≠ 112 ∨ rdW (m.arr64 POOL) (o + 1) ≠ 114 ∨
      rdW (m.arr64 POOL) (o + 2) ≠ 111 ∨ rdW (m.arr64 POOL) (o + 3) ≠ 106 then 0
  else if l = 4 then 1
  else if rdW (m.arr64 POOL) (o + 4) ≠ 84 ∨ rdW (m.arr64 POOL) (o + 5) ≠ 97 ∨
      rdW (m.arr64 POOL) (o + 6) ≠ 98 ∨ rdW (m.arr64 POOL) (o + 7) ≠ 108 ∨
      rdW (m.arr64 POOL) (o + 8) ≠ 101 then 0
  else 1

/-- The `str` prefix `p`. -/
def ipfS (m : Mem) (p : Word) : Option Word :=
  if 4294967295 < p then none
  else if p >>> 28 ≠ 1 then some 0
  else if tierW p ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (36 + tierW p) ≤ idxW p then none
  else some (ipfB m (nsO m (tierW p) (idxW p)) (nsL m (tierW p) (idxW p)))

/-- `is_proj_fn_shape`'s body. -/
def ipfW (m : Mem) (n : Word) : Option Word :=
  if 4294967295 < n then none
  else if n >>> 28 ≠ 2 then some 0
  else if tierW n ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (38 + tierW n) ≤ idxW n then none
  else ipfS m (nnQ m (tierW n) (idxW n))

set_option maxHeartbeats 3200000 in
theorem isProjFnShape_specW (p : Prog) (hp : p.lookup "is_proj_fn_shape" = some L.Checker.isProjFnShapeL)
    (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_proj_fn_shape" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ ipfW s₀.mem x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Checker.isProjFnShapeL]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, ipf_rd64, ipf_getElem] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, ipfW, ipfS, ipfB, tierW, idxW]

end L.Ind
