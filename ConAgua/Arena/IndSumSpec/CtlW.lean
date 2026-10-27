import ConAgua.Arena.IndSumSpec.CheckSumCtor
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# CtlW

`sdomsW_zero`, `sdomsW_cons`, `sdomsK1_some`, `sdomsK2_ok`, `sdomsK3_some`, `sdomsW_spec` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 : Mem) (vis off fo fl dO dl j b : Word) (ra rb : List Word)

theorem sdomsW_zero (hj : j = 0) : sdomsW cR (n + 1) m vis off fo fl dO dl j = some ([], m) := by
  simp [sdomsW, hj]
theorem sdomsW_cons (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : ¬ dl ≤ j - 1) :
    sdomsW cR (n + 1) m vis off fo fl dO dl j =
      sdomsK1 cR n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (ftdF m [rdW (m.arr64 IW) (fo + (j - 1))]) := by
  simp [sdomsW, hj, hfl, hdl]
theorem sdomsK1_some :
    sdomsK1 cR n vis off fo fl dO dl j b (some (ra, m1)) =
      sdomsK2 cR n vis off fo fl dO dl j
        (cR n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, b] m1) := by
  rw [sdomsK1]
theorem sdomsK2_ok (heq : rb.headD 0 ≠ 0) :
    sdomsK2 cR n vis off fo fl dO dl j (some (rb, m2)) =
      sdomsK3 (sdomsW cR n m2 vis off fo fl dO dl (j - 1)) := by
  rw [sdomsK2, ite_eq_right heq]
theorem sdomsK3_some (r : List Word) (m : Mem) : sdomsK3 (some (r, m)) = some ([], m) := rfl
end arms

grind_pattern [ind_grind] sdomsW_zero => sdomsW cR (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] sdomsW_cons => sdomsW cR (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] sdomsK1_some => sdomsK1 cR n vis off fo fl dO dl j b (some (ra, m1))
grind_pattern [ind_grind] sdomsK2_ok => sdomsK2 cR n vis off fo fl dO dl j (some (rb, m2))
grind_pattern [ind_grind] sdomsK3_some => sdomsK3 (some (r, m))

section spec
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet)
  (hp : p.lookup "check_struct_doms_at" = some checkStructDomsAtL) (hftd : FtdF p)
include hg hp hftd

theorem sdomsW_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : ∀ (s₀ : St) (vis off fo fl dO dl j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun r s' => LocEq s' s₀ ∧ sdomsW cR n s₀.mem vis off fo fl dO dl j = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]; simp only [callFn, checkStructDomsAtL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]
    simp only [callFn, checkStructDomsAtL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slGet_specW p hg n, ftdF_spec0 p hftd n, hcR n "is_def_eq_core", ih] <;>
      finish (gen := 20) [getW]

end spec

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL xo xl xb hd xfn ao al e : Word)
  (r : List Word)
theorem ctlK9_some : ctlK9 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem ctlK8_yes (h : r.headD 0 ≠ 0) : ctlK8 cR n vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK9 (fsortsW cR n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF) := by simp only [ctlK8]; rw [ite_eq_right h]
theorem ctlK7_yes (h : r.headD 0 ≠ 0) : ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK8 cR n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP)) := by
  simp only [ctlK7]; rw [ite_eq_right h]
theorem ctlK6_yes (h : ¬ (xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0)) :
    ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) =
      ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl) := by
  simp only [ctlK6]; rw [ite_eq_right h]
theorem ctlK5_some : ctlK5 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn (some (r, m)) =
    ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (r.headD 0) (r.tail.headD 0) m
      (if nP ≤ r.tail.headD 0 then eqW (n + 1) m (r.headD 0) nP cqO cqL else some 0) := rfl
theorem ctlK4_some : ctlK4 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (some (r, m)) =
    ctlK5 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (r.headD 0)
      (gaaF m [CWF, xb]) := rfl
theorem ctlK3_ok (h : ¬ 4294967296 ≤ hd) :
    ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) =
      ctlK4 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (gafF m [CWF, xb]) := by
  simp only [ctlK3]; rw [ite_eq_right h]
theorem ctlK2_some : ctlK2 cR n vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb (some (r, m)) =
    ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (r.headD 0)) := rfl
theorem ctlK1_yes (h : r.headD 0 ≠ 0) :
    ctlK1 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) =
      ctlK2 cR n vis0 vis T nP nIdx rs isP lg nF cqO cqL (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) (plW (n + 1) m lo ll) := by simp only [ctlK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] ctlK9_some ctlK8_yes ctlK7_yes ctlK6_yes ctlK5_some ctlK4_some ctlK3_ok ctlK2_some ctlK1_yes

set_option maxHeartbeats 2000000 in
theorem ctlW_spec (p : Prog) (hP : SumProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_sum_ctor_tail"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL, cqB]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctlW cR n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.htail]
  simp only [callFn, checkSumCtorTailL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    hcR (n + 1) "open_pis_at_fvars_f",
    plW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil (n + 1),
    internConst_spec p hP.hcf hP.hcp hP.hic (n + 1),
    gafF_spec p hP.ad (n + 1), gaaF_spec p hP.ad (n + 1),
    slEq_spec p hP.heq (n + 1), fdrW_spec p hP.hfdr hP.ad.ftd hP.hcr (n + 1), iarW_spec p hP.hiar hP.hcr (n + 1),
    fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd cR hcR n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 30) (instances := 5000) [lang_grind, arena_grind, ind_grind, ctlW]

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa cqO cqL cqB : Word)
  (r : List Word)
theorem ctorK9_some : ctorK9 cvC (some (r, m)) = some ([cvC, r.headD 0, r.tail.headD 0], m) := rfl
theorem ctorK8_some : ctorK8 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
    ctorK9 cvC (ctlW cR n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB) := rfl
theorem ctorK7_some : ctorK7 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
    ctorK8 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (sdomsW cR (n + 2) m vis 0 cqO cqL (r.headD 0) (r.tail.headD 0) nP) := rfl
theorem ctorK6_yes (h : r.headD 0 ≠ 0) :
    ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
      ctorK7 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
        (ftdsF m [r.tail.headD 0, r.tail.tail.headD 0]) := by
  simp only [ctorK6]; rw [ite_eq_right h]
theorem ctorK5_yes (h : r.headD 0 ≠ 0) :
    ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0)
        (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m) := by
  simp only [ctorK5]; rw [ite_eq_right h]
theorem ctorK4_yes (h : r.headD 0 ≠ 0) :
    ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
        (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvC + 3), 0] m) := by
  simp only [ctorK4]; rw [ite_eq_right h]
theorem ctorK3_yes (h : r.headD 0 ≠ 0) :
    ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
        (srW (n + 2) m T lo ll nP nF nIdx (r.tail.tail.tail.headD 0)) := by
  simp only [ctorK3]; rw [ite_eq_right h]
theorem ctorK2_some : ctorK2 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
    ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stripF 6 m [nP + nF, rdW (m.arr64 EREC) (cvC + 3)]) := rfl
end arms
attribute [ind_grind] ctorK9_some ctorK8_some ctorK7_some ctorK6_yes ctorK5_yes ctorK4_yes ctorK3_yes ctorK2_some

set_option maxHeartbeats 4000000 in
theorem ctorW_spec (p : Prog) (hP : SumProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "check_sum_ctor"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctorW cR n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.hctor]
  simp only [callFn, checkSumCtorL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    hcR (n + 2) "check_constant_val", stripPis_specF p hP.strip (n + 2),
    srW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil hP.hcf hP.hcp hP.hic
      hP.hbf hP.hbp hP.hib hP.hpg hP.hps hP.heq hP.hsr hP.ad (n + 2),
    hcR (n + 2) "open_pis_at_fvars_f", ftdsF_spec p hP.ad (n + 2),
    sdomsW_spec p hP.hg hP.hsd hP.ad.ftd cR hcR (n + 2), ctlW_spec p hP cR hcR n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 30) (instances := 5000) [lang_grind, arena_grind, ind_grind, ctorW, rdW_eq]

end L.Ind

end

end
