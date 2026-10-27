import ConAgua.Arena.IndSumSpec.CtsW

/-!
# WtW

`wtW_succ`, `wtK1_some`, `wtK2_sort`, `wtK2_pi`, `wtK3_ok`, `wtK4_some` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis i n e x y s fv : Word) (v r1 rb rr ro : List Word)
theorem wtW_succ : wtW cR (k + 1) m vis i n e = wtK1 cR k vis i n (cR k "whnf_top" [vis, i, e] m) := by
  simp [wtW]
theorem wtK1_some : wtK1 cR k vis i n (some (r1, m1)) = wtK2 cR k vis i n m1 (eViewW m1 (r1.headD 0)) := by
  rw [wtK1]
theorem wtK2_sort (h : v.headD 0 = 2) (hn : n = 0) :
    wtK2 cR k vis i n m1 v = some ([0, 0, v.tail.headD 0], m1) := by
  rw [wtK2, ite_eq_left ⟨h, hn⟩]
theorem wtK2_pi (h : v.headD 0 = 6) (hn : n ≠ 0) :
    wtK2 cR k vis i n m1 v =
      wtK3 cR k vis i n (v.tail.headD 0) (v.tail.tail.headD 0) (fvinternW m1 i (v.tail.headD 0)) := by
  rw [wtK2, ite_eq_right (fun h' => by rw [h] at h'; exact absurd h'.1 (by decide)), ite_eq_left ⟨h, hn⟩]
theorem wtK3_ok (h : ¬ 4294967296 ≤ fv) : wtK3 cR k vis i n x y (some (fv, m2)) =
    wtK4 cR k vis i n x (i1F m2 [CWF, y, fv, 0]) := by
  simp only [wtK3, ite_eq_right h]
theorem wtK4_some : wtK4 cR k vis i n x (some (rb, m3)) =
    wtK5 k x (wtW cR k m3 vis (i + 1) (n - 1) (rb.headD 0)) := by rw [wtK4]
theorem wtK5_some : wtK5 k x (some (rr, m4)) =
    wtK6 (rr.tail.tail.headD 0) (consW k m4 x (rr.headD 0) (rr.tail.headD 0)) := by rw [wtK5]
theorem wtK6_some : wtK6 s (some (ro, m5)) = some ([ro.headD 0, ro.tail.headD 0, s], m5) := rfl
end arms

grind_pattern [ind_grind] wtW_succ => wtW cR (k + 1) m vis i n e
grind_pattern [ind_grind] wtK1_some => wtK1 cR k vis i n (some (r1, m1))
grind_pattern [ind_grind] wtK2_sort => wtK2 cR k vis i n m1 v
grind_pattern [ind_grind] wtK2_pi => wtK2 cR k vis i n m1 v
grind_pattern [ind_grind] wtK3_ok => wtK3 cR k vis i n x y (some (fv, m2))
grind_pattern [ind_grind] wtK4_some => wtK4 cR k vis i n x (some (rb, m3))
grind_pattern [ind_grind] wtK5_some => wtK5 k x (some (rr, m4))
grind_pattern [ind_grind] wtK6_some => wtK6 s (some (ro, m5))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "whnf_telescope" = some whnfTelescopeL) (hi1 : I1Prog p)
include ha hc hsc hv hff hfp hif hp hi1

theorem wtW_spec (cR : CallM) (hcR : CallSpec p cR) (k : Nat) : ∀ (s₀ : St) (vis i n e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "whnf_telescope" [vis, i, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧ wtW cR k s₀.mem vis i n e = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis i n e; rw [invoke_eq _ hp]; simp only [callFn, whnfTelescopeL]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis i n e
    rw [invoke_eq _ hp]
    simp only [callFn, whnfTelescopeL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        hcR k "whnf_top", eView_spec p hv k, internFVar_spec p hff hfp hif k,
        i1F_spec p hi1 k, slCons_specW p ha hc hsc k, ih] <;>
      finish (gen := 20)

end spec

local notation "V" => ConLeche.CheckMode.verified

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
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis cv n cvTa0 bo bl s ss q : Word) (r1 rt r5 : List Word)
theorem ctsW_succ : ctsW cR (k + 1) m vis cv n cvTa0 =
    ctsK1 cR k vis cv (wtW cR k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3))) := rfl
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
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hwt : p.lookup "whnf_telescope" = some whnfTelescopeL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hct : p.lookup "close_telescope" = some closeTelescope)
  (hea : p.lookup "erec_alloc" = some erecAlloc) (hcn : p.lookup "cv_new" = some cvNew)
  (hp : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL) (hi1 : I1Prog p) (hab : AbF p)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hp hi1 hab

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
        wtW_spec p ha hc hsc hv hff hfp hif hwt hi1 cR hcR k, internSort_spec p hsf hsp his k,
        closeTelescope_spec p hd hpf hpp hpi hmk hct hab k, cvNew_specW p hea hcn k,
        hcR k "check_constant_val"] <;>
      finish (gen := 20)

end spec

end L.Ind

end

end
