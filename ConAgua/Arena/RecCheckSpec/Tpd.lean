import ConAgua.Arena.RecCheckSpec.TaGoWMfr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.RecClassSpec.MnW

/-!
# Tpd

`tcp_specF`, `ta_specF`, `pdsK11_some`, `pdsK10_some`, `pdsK9_some`, `pdsK8_eq` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem tcp_specF (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpF n s₀.mem pfo pfl e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetCanonParams_spec p L.rx L.r3 L.tcp n s₀ pfo pfl e

theorem ta_specF (p : Prog) (L : TaLook p) (n : Nat) (s₀ : St) (no nl lvls ho hl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ taF n s₀.mem no nl lvls ho hl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetAbs_spec p L n s₀ no nl lvls ho hl e

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis d no nl lvls ho hl pfo pfl a b av bv x : Word) (r : List Word)
theorem pdsK11_some : pdsK11 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem pdsK10_some : pdsK10 cR n vis d av bv (some (r, m)) = pdsK11 (cR n "is_def_eq_core" [vis, d, av, bv] m) := rfl
theorem pdsK9_some : pdsK9 cR n vis d av bv (some (r, m)) =
    pdsK10 cR n vis d av bv (cR n "infer_type_core" [vis, d, bv] m) := rfl
theorem pdsK8_eq (h : ¬ 4294967296 ≤ bv) (he : av = bv) : pdsK8 cR n vis d av (some (bv, m)) = some ([1], m) := by
  simp [pdsK8, h, he]
theorem pdsK8_ne (h : ¬ 4294967296 ≤ bv) (he : ¬ av = bv) : pdsK8 cR n vis d av (some (bv, m)) =
    pdsK9 cR n vis d av bv (cR n "infer_type_core" [vis, d, av] m) := by simp [pdsK8, h, he]
theorem pdsK7_some : pdsK7 cR n vis d no nl lvls ho hl av (some (r, m)) =
    pdsK8 cR n vis d av (taF n m no nl lvls ho hl (r.headD 0)) := rfl
theorem pdsK6_ok (h : ¬ 4294967296 ≤ av) : pdsK6 cR n vis d no nl lvls ho hl pfo pfl b (some (av, m)) =
    pdsK7 cR n vis d no nl lvls ho hl av (tcpF n m pfo pfl b) := by simp [pdsK6, h]
theorem pdsK5_some : pdsK5 cR n vis d no nl lvls ho hl pfo pfl b (some (r, m)) =
    pdsK6 cR n vis d no nl lvls ho hl pfo pfl b (taF n m no nl lvls ho hl (r.headD 0)) := rfl
end arms
attribute [ind_grind] pdsK11_some pdsK10_some pdsK9_some pdsK8_eq pdsK8_ne pdsK7_some pdsK6_ok pdsK5_some

set_option maxHeartbeats 2000000 in
theorem tpdStep_spec (p : Prog) (L : TpLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis d no nl lvls ho hl pfo pfl a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_params_def_eq_step"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ pdsW cR n s₀.mem vis d no nl lvls ho hl pfo pfl a b = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.step]
  simp only [callFn, targetParamsDefEqStep]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bvarBL_spec p L.bvb n, fvbF_spec p L.hf n, tcp_specF p L.rc n, ta_specF p L.ta n,
      hcR n "infer_type_core", hcR n "is_def_eq_core"] <;>
    finish (gen := 40) (instances := 20000) [pdsW, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11]

section arms
variable (cR : CallM) (n : Nat) (m m1 : Mem) (vis d no nl lvls ho hl pfo pfl ao al bo bl : Word) (r : List Word)
theorem pdeW_nil (h : al = 0) : pdeW cR (n + 1) m vis d no nl lvls ho hl pfo pfl ao al bo bl =
    some ([if bl = 0 then 1 else 0], m) := by simp [pdeW, h]
theorem pdeW_nilr (h : ¬ al = 0) (hb : bl = 0) : pdeW cR (n + 1) m vis d no nl lvls ho hl pfo pfl ao al bo bl =
    some ([0], m) := by simp [pdeW, h, hb]
theorem pdeW_cons (h : ¬ al = 0) (hb : ¬ bl = 0) : pdeW cR (n + 1) m vis d no nl lvls ho hl pfo pfl ao al bo bl =
    pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl
      (pdsF cR n m vis d no nl lvls ho hl pfo pfl (rdW (m.arr64 IW) ao) (rdW (m.arr64 IW) bo)) := by
  simp [pdeW, h, hb]
theorem pdeK1_stop (h : r.headD 0 = 0) : pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl (some (r, m1)) =
    some ([0], m1) := by simp only [pdeK1]; rw [ite_eq_left h]
theorem pdeK1_go (h : ¬ r.headD 0 = 0) : pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl (some (r, m1)) =
    pdsK11 (pdeW cR n m1 vis d no nl lvls ho hl pfo pfl (ao + 1) (al - 1) (bo + 1) (bl - 1)) := by simp only [pdeK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] pdeW_nil pdeW_nilr pdeW_cons pdeK1_stop pdeK1_go

theorem pdsF_spec (p : Prog) (L : TpLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis d no nl lvls ho hl pfo pfl a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq_step"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ pdsF cR n s₀.mem vis d no nl lvls ho hl pfo pfl a b = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact tpdStep_spec p L cR hcR n s₀ vis d no nl lvls ho hl pfo pfl a b

theorem tpd_spec (p : Prog) (L : TpLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis d no nl lvls ho hl pfo pfl ao al bo bl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧
      pdeW cR n s₀.mem vis d no nl lvls ho hl pfo pfl ao al bo bl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis d no nl lvls ho hl pfo pfl ao al bo bl
    rw [invoke_eq _ L.tpd]; simp only [callFn, targetParamsDefEq]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis d no nl lvls ho hl pfo pfl ao al bo bl
    rw [invoke_eq _ L.tpd]
    simp only [callFn, targetParamsDefEq]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pdsF_spec p L cR hcR n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10,
        loc_init11, loc_init12]

end L.Ind

end
