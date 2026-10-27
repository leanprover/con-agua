import ConAgua.Arena.RecGenSpec.ClassFeR

/-!
# ClassConstOk

`ccoW_eq`, `ccoK1_some`, `ccoK2_some`, `ccoK3_some`, `classConstOk_spec`, `rtoW_eq` and the lemmas only they use.
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
variable (cR : CallM) (n : Nat) (m m1 m2 m3 : Mem) (vis q : Word) (r1 r2 r3 : List Word)
theorem ccoW_eq : ccoW cR (n + 1) m vis q = ccoK1 cR n vis q (L.Arena.ihW cR n m vis q) := rfl
theorem ccoK1_some : ccoK1 cR n vis q (some (r1, m1)) =
    ccoK2 cR n vis (cR n "infer_type_core" [vis, 0, rdW (m1.arr64 EREC) (q + 3)] m1) := rfl
theorem ccoK2_some : ccoK2 cR n vis (some (r2, m2)) =
    ccoK3 (cR n "ensure_sort_core" [vis, 0, r2.headD 0] m2) := rfl
theorem ccoK3_some : ccoK3 (some (r3, m3)) = some ([0], m3) := rfl
end arms

grind_pattern [ind_grind] ccoW_eq => ccoW cR (n + 1) m vis q
grind_pattern [ind_grind] ccoK1_some => ccoK1 cR n vis q (some (r1, m1))
grind_pattern [ind_grind] ccoK2_some => ccoK2 cR n vis (some (r2, m2))
grind_pattern [ind_grind] ccoK3_some => ccoK3 (some (r3, m3))

theorem classConstOk_spec (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : p.lookup "class_const_ok" = some classConstOkL) (cR : CallM) (hcR : CallSpec p cR)
    (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ccoW cR n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hc]
  simp only [callFn, classConstOkL]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      classConstOkHeader_spec p h hh cR hcR n,
      hcR n "infer_type_core", hcR n "ensure_sort_core"] <;>
    finish (gen := 20) [rdW_eq]

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
variable (cR : CallM) (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis g k rc cvRi c gty q : Word) (r1 r2 r4 r5 : List Word)
theorem rtoW_eq : rtoW cR (n + 1) m vis g k rc cvRi c = rtoK1 cR n vis g rc cvRi c (rgW n m g k rc c) := rfl
theorem rtoK1_some : rtoK1 cR n vis g rc cvRi c (some (r1, m1)) = rtoK2 cR n vis rc cvRi (gtW n m1 g c) := rfl
theorem rtoK2_ok (h : r2.headD 0 ≠ 0) : rtoK2 cR n vis rc cvRi (some (r2, m2)) =
    rtoK3 cR n vis cvRi (r2.tail.headD 0)
      (cvNewW m2 (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc))
        (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 1)) (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 2))
        (r2.tail.headD 0)) := by
  rw [rtoK2, ite_eq_right h]
theorem rtoK3_some : rtoK3 cR n vis cvRi gty (some (q, m3)) = rtoK4 cR n vis cvRi gty q (ccoW cR n m3 vis q) := rfl
theorem rtoK4_some : rtoK4 cR n vis cvRi gty q (some (r4, m4)) =
    rtoK5 q (cR n "is_def_eq_core" [vis, 0, rdW (m4.arr64 EREC) (cvRi + 3), gty] m4) := rfl
theorem rtoK5_ok (h : r5.headD 0 ≠ 0) : rtoK5 q (some (r5, m5)) = some ([q], m5) := by rw [rtoK5, ite_eq_right h]
end arms

grind_pattern [ind_grind] rtoW_eq => rtoW cR (n + 1) m vis g k rc cvRi c
grind_pattern [ind_grind] rtoK1_some => rtoK1 cR n vis g rc cvRi c (some (r1, m1))
grind_pattern [ind_grind] rtoK2_ok => rtoK2 cR n vis rc cvRi (some (r2, m2))
grind_pattern [ind_grind] rtoK3_some => rtoK3 cR n vis cvRi gty (some (q, m3))
grind_pattern [ind_grind] rtoK4_some => rtoK4 cR n vis cvRi gty q (some (r4, m4))
grind_pattern [ind_grind] rtoK5_ok => rtoK5 q (some (r5, m5))

theorem classRecTyOkGuards_spec (p : Prog) (h : RtoProg p) (n : Nat) (s₀ : St) (g k rc c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok_guards" [g, k, rc, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rgW n s₀.mem g k rc c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rg]
  simp only [callFn, classRecTyOkGuards]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n] <;>
      finish (gen := 20) [rdW_eq, rgK]

theorem classRecTyOk_spec (p : Prog) (h : RtoProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis g k rc cvRi c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rtoW cR n s₀.mem vis g k rc cvRi c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rto]
  simp only [callFn, classRecTyOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRecTyOkGuards_spec p h n, classGenRecTy_spec p h.toGtProg n, cvNew_specW p h.era h.cvn n,
        classConstOk_spec p h.ih h.ccoh h.cco cR hcR n, hcR n "is_def_eq_core"] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

end L.Ind

end

end
