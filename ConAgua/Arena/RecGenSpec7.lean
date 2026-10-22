import ConAgua.Arena.RecClassSpecJ
import ConAgua.Arena.RecGenSpec3

/-!
# `RecGen`: `classRecTyOk` (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constants below the record top -/

theorem rec2DecCV_agree {a b : Array Word} {q T : Nat} (hag : ∀ i, i < T → b[i]? = a[i]?) (hq4 : q + 4 ≤ T)
    (hl : ∀ o l, nat? a (q + 1) = some o → nat? a (q + 2) = some l → o + l ≤ T) :
    decCV b q = decCV a q := by
  have hn : ∀ i, i < T → nat? b i = nat? a i := fun i hi => by simp only [nat?, hag i hi]
  have hh : ∀ {k : IdxKind} i, i < T → (hd? b i : Option (Idx k)) = hd? a i :=
    fun i hi => by simp only [hd?, hag i hi]
  simp only [decCV]
  rw [hh q (by omega), hh (q + 3) (by omega)]
  have hlist : (hlist? b (q + 1) : Option (List (Idx IdxKind.name))) = hlist? a (q + 1) := by
    simp only [hlist?]
    rw [hn (q + 1) (by omega), hn (q + 1 + 1) (by omega)]
    cases ho : nat? a (q + 1) with
    | none => simp
    | some o =>
      cases hl' : nat? a (q + 1 + 1) with
      | none => simp
      | some l =>
        try simp only [Option.bind_some]
        apply hslice?_congr
        intro j hj
        have := hl o l ho hl'
        exact hag (o + j) (by omega)
  rw [hlist]

/-- A constant record below the top decodes in the record pool in use. -/
theorem rec2DecCV_erecP {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) (hq : CVExt m q) :
    decCV (erecP m) q = some cv := by
  rw [rec2DecCV_agree (a := erA m) (T := erTop m) (fun i hi => ?_) hq.1 hq.2]
  · exact h
  · simp only [erecP, erA, Array.getElem?_extract, erecTop, erTop] at hi ⊢
    simp [hi]

/-! ## `class_rec_ty_ok_guards` -/

def rgK (g k rc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if rdW (m1.arr64 IW) (rc + 3) ≠ (if rdW (m1.arr64 IW) (r1.headD 0 + 8) ≠ 0
        then rdW (m1.arr64 IW) (r1.headD 0 + 8) - 1 else k) then none
    else if rdW (m1.arr64 IW) (rc + 1) ≠ rdW (m1.arr64 IW) g + rdW (m1.arr64 IW) (g + 8) then none
    else if rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5) < rdW (m1.arr64 IW) (rc + 1)
      then none
    else if rdW (m1.arr64 IW) (rc + 2) ≠ rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5)
      then none
    else some ([0], m1)

/-- **The model of `class_rec_ty_ok_guards`.** -/
def rgW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, g, k, rc, c => rgK g k rc (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c)

theorem rgW_eq (n : Nat) (m : Mem) (g k rc c : Word) :
    rgW (n + 1) m g k rc c = rgK g k rc (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c) := rfl

grind_pattern [ind_grind] rgW_eq => rgW (n + 1) m g k rc c

/-! ## `class_rec_ty_ok` -/

def rtoK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => if r5.headD 0 = 0 then none else some ([q], m5)

def rtoK4 (vis cvRi gty q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => rtoK5 q (stubM "is_def_eq_core" m4 [vis, 0, rdW (m4.arr64 EREC) (cvRi + 3), gty])

def rtoK3 (n : Nat) (vis cvRi gty : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m3) => rtoK4 vis cvRi gty q (ccoW n m3 vis q)

def rtoK2 (n : Nat) (vis rc cvRi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none
    else rtoK3 n vis cvRi (r2.tail.headD 0)
      (cvNewW m2 (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc))
        (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 1)) (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 2))
        (r2.tail.headD 0))

def rtoK1 (n : Nat) (vis g rc cvRi c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => rtoK2 n vis rc cvRi (gtW n m1 g c)

/-- **The model of `class_rec_ty_ok`.** -/
def rtoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, g, k, rc, cvRi, c => rtoK1 n vis g rc cvRi c (rgW n m g k rc c)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis g k rc cvRi c gty q : Word) (r1 r2 r4 r5 : List Word)
theorem rtoW_eq : rtoW (n + 1) m vis g k rc cvRi c = rtoK1 n vis g rc cvRi c (rgW n m g k rc c) := rfl
theorem rtoK1_some : rtoK1 n vis g rc cvRi c (some (r1, m1)) = rtoK2 n vis rc cvRi (gtW n m1 g c) := rfl
theorem rtoK2_fail (h : r2.headD 0 = 0) : rtoK2 n vis rc cvRi (some (r2, m2)) = none := by
  rw [rtoK2, if_pos h]
theorem rtoK2_ok (h : r2.headD 0 ≠ 0) : rtoK2 n vis rc cvRi (some (r2, m2)) =
    rtoK3 n vis cvRi (r2.tail.headD 0)
      (cvNewW m2 (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc))
        (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 1)) (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 2))
        (r2.tail.headD 0)) := by
  rw [rtoK2, if_neg h]
theorem rtoK3_some : rtoK3 n vis cvRi gty (some (q, m3)) = rtoK4 vis cvRi gty q (ccoW n m3 vis q) := rfl
theorem rtoK4_some : rtoK4 vis cvRi gty q (some (r4, m4)) =
    rtoK5 q (stubM "is_def_eq_core" m4 [vis, 0, rdW (m4.arr64 EREC) (cvRi + 3), gty]) := rfl
theorem rtoK5_fail (h : r5.headD 0 = 0) : rtoK5 q (some (r5, m5)) = none := by rw [rtoK5, if_pos h]
theorem rtoK5_ok (h : r5.headD 0 ≠ 0) : rtoK5 q (some (r5, m5)) = some ([q], m5) := by rw [rtoK5, if_neg h]
end arms

grind_pattern [ind_grind] rtoW_eq => rtoW (n + 1) m vis g k rc cvRi c
grind_pattern [ind_grind] rtoK1_some => rtoK1 n vis g rc cvRi c (some (r1, m1))
grind_pattern [ind_grind] rtoK2_fail => rtoK2 n vis rc cvRi (some (r2, m2))
grind_pattern [ind_grind] rtoK2_ok => rtoK2 n vis rc cvRi (some (r2, m2))
grind_pattern [ind_grind] rtoK3_some => rtoK3 n vis cvRi gty (some (q, m3))
grind_pattern [ind_grind] rtoK4_some => rtoK4 vis cvRi gty q (some (r4, m4))
grind_pattern [ind_grind] rtoK5_fail => rtoK5 q (some (r5, m5))
grind_pattern [ind_grind] rtoK5_ok => rtoK5 q (some (r5, m5))

/-- The lookups `class_rec_ty_ok` needs. -/
structure RtoProg (p : Prog) extends GtProg p : Prop where
  ih : IhProg p
  ccoh : p.lookup "class_const_ok_header" = some classConstOkHeader
  cco : p.lookup "class_const_ok" = some classConstOkL
  era : p.lookup "erec_alloc" = some erecAlloc
  cvn : p.lookup "cv_new" = some cvNew
  rg : p.lookup "class_rec_ty_ok_guards" = some classRecTyOkGuards
  rto : p.lookup "class_rec_ty_ok" = some classRecTyOkL

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
        targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma n] <;>
      finish (gen := 20) [rdW_eq, rgK]

theorem classRecTyOk_spec (p : Prog) (h : RtoProg p) (n : Nat) (s₀ : St) (vis g k rc cvRi c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rtoW n s₀.mem vis g k rc cvRi c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rto]
  simp only [callFn, classRecTyOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRecTyOkGuards_spec p h n, classGenRecTy_spec p h.toGtProg n, cvNew_specW p h.era h.cvn n,
        classConstOk_spec p h.ih h.ccoh h.cco n, stubM_spec p "is_def_eq_core" n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

end L.Ind
