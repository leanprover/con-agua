import ConAgua.Arena.IndSumSpec.CtsW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# WtW

`check_sum_tele_slow`'s model's arms and spec (`whnf_telescope` read through its run, `wtR`).
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
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis cv n cvTa0 bo bl s ss q : Word) (r1 rt r5 : List Word)
theorem ctsW_succ : ctsW cR (k + 1) m vis cv n cvTa0 =
    ctsK1 cR k vis cv (wtR cR k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3))) := rfl
theorem ctsK1_some : ctsK1 cR k vis cv (some (r1, m1)) = ctsK2 cR k vis cv (r1.headD 0) (r1.tail.headD 0)
    (r1.tail.tail.headD 0) (sointernW m1 (r1.tail.tail.headD 0)) := rfl
theorem ctsK2_ok (h : ¬ 4294967296 ≤ ss) : ctsK2 cR k vis cv bo bl s (some (ss, m2)) =
    ctsK3 cR k vis cv s (closeW k m2 bo bl 0 ss) := by simp only [ctsK2, ite_eq_right h]
theorem ctsK3_some : ctsK3 cR k vis cv s (some (rt, m3)) = ctsK4 cR k vis s (cvNewW m3 (rdW (m3.arr64 EREC) cv)
    (rdW (m3.arr64 EREC) (cv + 1)) (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0)) := rfl
theorem ctsK4_some : ctsK4 cR k vis s (some (q, m4)) = ctsK5 q s (cR k "check_constant_val" [vis, q] m4) := rfl
theorem ctsK5_some : ctsK5 q s (some (r5, m5)) = some ([q, s], m5) := rfl
end arms

grind_pattern [ind_grind] ctsW_succ => ctsW cR (k + 1) m vis cv n cvTa0
grind_pattern [ind_grind] ctsK1_some => ctsK1 cR k vis cv (some (r1, m1))
grind_pattern [ind_grind] ctsK2_ok => ctsK2 cR k vis cv bo bl s (some (ss, m2))
grind_pattern [ind_grind] ctsK3_some => ctsK3 cR k vis cv s (some (rt, m3))
grind_pattern [ind_grind] ctsK4_some => ctsK4 cR k vis s (some (q, m4))
grind_pattern [ind_grind] ctsK5_some => ctsK5 q s (some (r5, m5))

section spec
variable (p : Prog)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hct : p.lookup "close_telescope" = some closeTelescope)
  (hea : p.lookup "erec_alloc" = some erecAlloc) (hcn : p.lookup "cv_new" = some cvNew)
  (hp : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL) (hab : AbF p)
include hsf hsp his hd hpf hpp hpi hmk hct hea hcn hp hab

theorem ctsW_spec (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St) (vis cv n cvTa0 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele_slow" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ ctsW cR k s₀.mem vis cv n cvTa0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkSumTeleSlowL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        wtR_spec p cR hcR k, internSort_spec p hsf hsp his k,
        closeTelescope_spec p hd hpf hpp hpi hmk hct hab k, cvNew_specW p hea hcn k,
        hcR k "check_constant_val"] <;>
      finish (gen := 20)

end spec

end L.Ind

end

end
