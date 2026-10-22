import ConAgua.Arena.IndSumSpec3
import ConAgua.Arena.IndPartsSpec5
import ConAgua.Arena.PinsNatOp

/-!
# Refinements of `IndSum`, fourth file (lane `indproofs`)

`struct_ctor_resid_ok` (through the stubs `get_app_fn`, `get_app_args`, `intern_ls_iw`), with
helper `parts`' `sl_eq` model (`IndPartsSpec5.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The model -/

/-- The three tests, as the L code combines them. -/
def srRes (fn hd al nP nIdx e3 : Word) : Word :=
  (if fn = hd then 1 else 0) &&& (if al = nP + nIdx then 1 else 0) &&& e3

/-- After `struct_ps_at`: the prefix comparison. -/
def srK5 (k : Nat) (nP nIdx hd fn ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m5) =>
    if rp.tail.headD 0 ≤ al then
      match eqW k m5 ao (rp.tail.headD 0) (rp.headD 0) (rp.tail.headD 0) with
      | none => none
      | some e => some ([srRes fn hd al nP nIdx e], m5)
    else some ([srRes fn hd al nP nIdx 0], m5)
/-- After `get_app_args`. -/
def srK4 (k : Nat) (nP o nIdx hd fn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m4) => srK5 k nP nIdx hd fn (ra.headD 0) (ra.tail.headD 0) (psAtW k m4 o nP)
/-- After `get_app_fn`. -/
def srK3 (k : Nat) (nP o nIdx cbody hd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m3) => srK4 k nP o nIdx hd (rf.headD 0) (stubM "get_app_args" m3 [CWF, cbody])
/-- After `intern_const`. -/
def srK2 (k : Nat) (nP o nIdx cbody : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m2) =>
    if 4294967296 ≤ hd then none else srK3 k nP o nIdx cbody hd (stubM "get_app_fn" m2 [CWF, cbody])
/-- After `param_levels`. -/
def srK1 (k : Nat) (T nP o nIdx cbody : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => srK2 k nP o nIdx cbody (ceinternW m1 T (r1.headD 0))
/-- **The model of `struct_ctor_resid_ok`.** -/
def srW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, T, lo, ll, nP, o, nIdx, cbody => srK1 k T nP o nIdx cbody (plW k m lo ll)

section arms
variable (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (T lo ll nP o nIdx cbody hd fn ao al : Word)
  (r1 rf ra rp : List Word)
theorem srW_succ : srW (k + 1) m T lo ll nP o nIdx cbody = srK1 k T nP o nIdx cbody (plW k m lo ll) := rfl
theorem srK1_some : srK1 k T nP o nIdx cbody (some (r1, m1)) =
    srK2 k nP o nIdx cbody (ceinternW m1 T (r1.headD 0)) := rfl
theorem srK2_big (h : 4294967296 ≤ hd) : srK2 k nP o nIdx cbody (some (hd, m2)) = none := by
  simp [srK2, h]
theorem srK2_ok (h : ¬ 4294967296 ≤ hd) : srK2 k nP o nIdx cbody (some (hd, m2)) =
    srK3 k nP o nIdx cbody hd (stubM "get_app_fn" m2 [CWF, cbody]) := by simp only [srK2, if_neg h]
theorem srK3_some : srK3 k nP o nIdx cbody hd (some (rf, m3)) =
    srK4 k nP o nIdx hd (rf.headD 0) (stubM "get_app_args" m3 [CWF, cbody]) := rfl
theorem srK4_some : srK4 k nP o nIdx hd fn (some (ra, m4)) =
    srK5 k nP nIdx hd fn (ra.headD 0) (ra.tail.headD 0) (psAtW k m4 o nP) := rfl
theorem srK5_le (h : rp.tail.headD 0 ≤ al) : srK5 k nP nIdx hd fn ao al (some (rp, m5)) =
    (match eqW k m5 ao (rp.tail.headD 0) (rp.headD 0) (rp.tail.headD 0) with
      | none => none
      | some e => some ([srRes fn hd al nP nIdx e], m5)) := by simp only [srK5, if_pos h]
theorem srK5_gt (h : ¬ rp.tail.headD 0 ≤ al) : srK5 k nP nIdx hd fn ao al (some (rp, m5)) =
    some ([srRes fn hd al nP nIdx 0], m5) := by simp only [srK5, if_neg h]
end arms

grind_pattern [ind_grind] srW_succ => srW (k + 1) m T lo ll nP o nIdx cbody
grind_pattern [ind_grind] srK1_some => srK1 k T nP o nIdx cbody (some (r1, m1))
grind_pattern [ind_grind] srK2_big => srK2 k nP o nIdx cbody (some (hd, m2))
grind_pattern [ind_grind] srK2_ok => srK2 k nP o nIdx cbody (some (hd, m2))
grind_pattern [ind_grind] srK3_some => srK3 k nP o nIdx cbody hd (some (rf, m3))
grind_pattern [ind_grind] srK4_some => srK4 k nP o nIdx hd fn (some (ra, m4))
grind_pattern [ind_grind] srK5_le => srK5 k nP nIdx hd fn ao al (some (rp, m5))
grind_pattern [ind_grind] srK5_gt => srK5 k nP nIdx hd fn ao al (some (rp, m5))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hplg : p.lookup "param_levels_go" = some paramLevelsGoL)
  (hpl : p.lookup "param_levels" = some paramLevelsL)
  (hcf : p.lookup "const_find" = some constFind) (hcp : p.lookup "const_push" = some constPush)
  (hic : p.lookup "intern_const" = some internConst)
  (hbf : p.lookup "bvar_find" = some bvarFind) (hbp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hpg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hps : p.lookup "struct_ps_at" = some structPsAtL)
  (heq : p.lookup "sl_eq" = some slEq)
  (hp : p.lookup "struct_ctor_resid_ok" = some structCtorResidOkL)
include ha hc hsc hg hpf hpp hip hplg hpl hcf hcp hic hbf hbp hib hpg hps heq hp

theorem srW_spec (k : Nat) (s₀ : St) (T lo ll nP o nIdx cbody : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "struct_ctor_resid_ok" [T, lo, ll, nP, o, nIdx, cbody]
    ⦃fun r s' => LocEq s' s₀ ∧ srW k s₀.mem T lo ll nP o nIdx cbody = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structCtorResidOkL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        plW_spec p ha hc hsc hg hpf hpp hip hplg hpl k, internConst_spec p hcf hcp hic k,
        stubM_spec p "get_app_fn" k, stubM_spec p "get_app_args" k,
        psAtW_spec p ha hc hsc hbf hbp hib hpg hps k, slEq_spec p heq k] <;>
      finish (gen := 20) [srRes]

end spec

end L.Ind
