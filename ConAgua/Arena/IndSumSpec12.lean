import ConAgua.Arena.IndSumSpec11
import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndSumSpec2A
import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.RecClassSpecB

/-!
# `check_sum_ctor` refines `checkSumCtor` (lane `indproofs2`)

One constructor's type. L splits the twin's body in two: `check_sum_ctor` (the constant check, the
result shape, the parameter pins) and `check_sum_ctor_tail` (the opened residual, the pre-block
resolution, the field sorts); `cscTailT` is the twin's tail verbatim, so `checkSumCtor` is its head
followed by `cscTailT` (`checkSumCtor_eq`). The callees: stubs (`open_pis_at_fvars_f`,
`get_app_fn_f`, `get_app_args_f`, `check_constant_val`, `strip_pis`, `fvar_type_ds`, and those of the
proved callees), `param_levels`, `intern_const` (guarded below `2^32`, as elsewhere),
`field_doms_resolve`/`idx_args_resolve` at the pre-block view `vis0` (the stage relation there is
the restriction of the one at `vis`: `fe₀ = fe.restrictTo vis0`), `check_struct_field_sorts_i`,
`struct_ctor_resid_ok`, `check_struct_doms_at`.

`SumProg p`: the program lookups of this file and the next, bundled (DESIGN.md, lane `indproofs2`
landing 2: a bundle per module instead of 20 hypotheses per statement).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The program lookups of `check_sum_ctor(s)` and their callees. -/
structure SumProg (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsc : p.lookup "sl_cons" = some slCons
  hg : p.lookup "sl_get" = some slGet
  hpf : p.lookup "param_find" = some paramFind
  hpp : p.lookup "param_push" = some paramPush
  hip : p.lookup "intern_param" = some internParam
  hplg : p.lookup "param_levels_go" = some paramLevelsGoL
  hpl : p.lookup "param_levels" = some paramLevelsL
  hcf : p.lookup "const_find" = some constFind
  hcp : p.lookup "const_push" = some constPush
  hic : p.lookup "intern_const" = some internConst
  heq : p.lookup "sl_eq" = some slEq
  hfdr : p.lookup "field_doms_resolve" = some fieldDomsResolveL
  hiar : p.lookup "idx_args_resolve" = some idxArgsResolveL
  hpw : p.lookup "pin_word" = some pinWordL
  het : p.lookup "lvl_eq_true" = some lvlEqTrue
  hcn : p.lookup "sl_contains" = some slContains
  hfsb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL
  hcfg : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL
  hcfs : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL
  htail : p.lookup "check_sum_ctor_tail" = some checkSumCtorTailL
  hbf : p.lookup "bvar_find" = some bvarFind
  hbp : p.lookup "bvar_push" = some bvarPush
  hib : p.lookup "intern_bvar" = some internBVar
  hpg : p.lookup "struct_ps_at_go" = some structPsAtGoL
  hps : p.lookup "struct_ps_at" = some structPsAtL
  hsr : p.lookup "struct_ctor_resid_ok" = some structCtorResidOkL
  hsd : p.lookup "check_struct_doms_at" = some checkStructDomsAtL
  hctor : p.lookup "check_sum_ctor" = some checkSumCtorL
  hrec2 : p.lookup "rec2" = some rec2
  hcsg : p.lookup "check_sum_ctors_go" = some checkSumCtorsGoL
  hcs : p.lookup "check_sum_ctors" = some checkSumCtorsL

/-! ## `check_sum_ctor_tail`: the word model -/

/-- After the field sorts. -/
def ctlK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)
/-- After `idx_args_resolve`: the field sorts. -/
def ctlK8 (n : Nat) (vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK9 (fsortsW n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF)
/-- After `field_doms_resolve`: the index arguments. -/
def ctlK7 (n : Nat) (vis0 vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK8 n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP))
/-- After `sl_eq` (or its skip): the residual's shape. -/
def ctlK6 (n : Nat) (vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0 then none
    else ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl)
/-- After `get_app_args_f`: the parameter prefix. -/
def ctlK5 (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (ra.headD 0) (ra.tail.headD 0) m
      (if nP ≤ ra.tail.headD 0 then eqW (n + 1) m (ra.headD 0) nP cqO cqL else some 0)
/-- After `get_app_fn_f`. -/
def ctlK4 (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (rf.headD 0)
      (stubM "get_app_args_f" m [CWF, xb])
/-- After `intern_const`: the guard, `get_app_fn_f`. -/
def ctlK3 (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m) => if 4294967296 ≤ hd then none
    else ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (stubM "get_app_fn_f" m [CWF, xb])
/-- After `param_levels`: the family's head. -/
def ctlK2 (n : Nat) (vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ru, m) => ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (ru.headD 0))
/-- After `open_pis_at_fvars_f`. -/
def ctlK1 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rx, m) => if rx.headD 0 = 0 then none
    else ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL (rx.tail.headD 0) (rx.tail.tail.headD 0)
      (rx.tail.tail.tail.headD 0) (plW (n + 1) m lo ll)

/-- **The model of `check_sum_ctor_tail(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL,
cqB)`** (its callees at exec fuel `n + 1`). -/
def ctlW (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    Option (List Word × Mem) :=
  ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (stubM "open_pis_at_fvars_f" m [nF, cqB, nP])

section arms
variable (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL xo xl xb hd xfn ao al e : Word)
  (r : List Word)
theorem ctlK9_some : ctlK9 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem ctlK8_no (h : r.headD 0 = 0) : ctlK8 n vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by
  simp only [ctlK8]; rw [if_pos h]
theorem ctlK8_yes (h : r.headD 0 ≠ 0) : ctlK8 n vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK9 (fsortsW n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF) := by simp only [ctlK8]; rw [if_neg h]
theorem ctlK7_no (h : r.headD 0 = 0) :
    ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by simp only [ctlK7]; rw [if_pos h]
theorem ctlK7_yes (h : r.headD 0 ≠ 0) : ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK8 n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP)) := by
  simp only [ctlK7]; rw [if_neg h]
theorem ctlK6_no (h : xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0) :
    ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) = none := by
  simp only [ctlK6]; rw [if_pos h]
theorem ctlK6_yes (h : ¬ (xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0)) :
    ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) =
      ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl) := by
  simp only [ctlK6]; rw [if_neg h]
theorem ctlK5_some : ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn (some (r, m)) =
    ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (r.headD 0) (r.tail.headD 0) m
      (if nP ≤ r.tail.headD 0 then eqW (n + 1) m (r.headD 0) nP cqO cqL else some 0) := rfl
theorem ctlK4_some : ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (some (r, m)) =
    ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (r.headD 0)
      (stubM "get_app_args_f" m [CWF, xb]) := rfl
theorem ctlK3_big (h : 4294967296 ≤ hd) :
    ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) = none := by simp only [ctlK3]; rw [if_pos h]
theorem ctlK3_ok (h : ¬ 4294967296 ≤ hd) :
    ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) =
      ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (stubM "get_app_fn_f" m [CWF, xb]) := by
  simp only [ctlK3]; rw [if_neg h]
theorem ctlK2_some : ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb (some (r, m)) =
    ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (r.headD 0)) := rfl
theorem ctlK1_no (h : r.headD 0 = 0) :
    ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) = none := by simp only [ctlK1]; rw [if_pos h]
theorem ctlK1_yes (h : r.headD 0 ≠ 0) :
    ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) =
      ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) (plW (n + 1) m lo ll) := by simp only [ctlK1]; rw [if_neg h]
end arms
attribute [ind_grind] ctlK9_some ctlK8_no ctlK8_yes ctlK7_no ctlK7_yes ctlK6_no ctlK6_yes ctlK5_some
  ctlK4_some ctlK3_big ctlK3_ok ctlK2_some ctlK1_no ctlK1_yes

set_option maxHeartbeats 2000000 in
theorem ctlW_spec (p : Prog) (hP : SumProg p) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_sum_ctor_tail"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL, cqB]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctlW n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.htail]
  simp only [callFn, checkSumCtorTailL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      stubM_spec p "open_pis_at_fvars_f" (n + 1),
      plW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl (n + 1),
      internConst_spec p hP.hcf hP.hcp hP.hic (n + 1),
      stubM_spec p "get_app_fn_f" (n + 1), stubM_spec p "get_app_args_f" (n + 1),
      slEq_spec p hP.heq (n + 1), fdrW_spec p hP.hfdr (n + 1), iarW_spec p hP.hiar (n + 1),
      fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs n] <;>
    finish (gen := 30) (instances := 5000) [ctlW]

end L.Ind
