import ConAgua.Arena.RecStab
import ConAgua.Arena.RecCheckSpec3
import ConAgua.Arena.IndPartsSpec3

/-!
# `RecClass`: `classReadMinor` (lane `indproofs2`, helper `rec`)

Word models (one per L function, at the function's own fuel), their `vcgen` specs, and the
relational lemmas as `RSim` chains (`RecSim.lean`).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

section models
variable (n : Nat) (nP mo ml d : Word)

/-- `class_read_minor_ih1` after the last `fvar_head`. -/
def ih1K6 (d t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if r6.headD 0 = 0 then some ([0, 0, 0], m6)
    else if r6.tail.headD 0 < d then some ([0, 0, 0], m6)
    else some ([1, r6.tail.headD 0 - d, t], m6)

/-- After `get_app_args`. -/
def ih1K5 (d t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.tail.headD 0 = 0 then some ([0, 0, 0], m5)
    else ih1K6 d t (fvarHeadW m5 (rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1)))

/-- After `class_of_motive_var`. -/
def ih1K4 (rr : Word) (m3 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r4 =>
    if r4.headD 0 = 0 then some ([0, 0, 0], m3)
    else ih1K5 d (r4.tail.headD 0) (gaaF m3 [CWF, rr])

/-- After the first `fvar_head`. -/
def ih1K3 (rr : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0, 0], m3)
    else ih1K4 d rr m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0))

/-- After `pi_result`. -/
def ih1K2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ih1K3 n nP mo ml d (r2.headD 0) (fvarHeadW m2 (r2.headD 0))

/-- After `fvar_type_d`. -/
def ih1K1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ih1K2 n nP mo ml d (pirF m1 [CWF, r1.headD 0])

end models

/-- **The model of `class_read_minor_ih1`.** -/
def ih1W : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, x => ih1K1 n nP mo ml d (ftdF m [x])

mutual
/-- **The model of `class_read_minor_ihs`.** -/
def ihsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, fo, fl =>
    if fl = 0 then some ([0, 0], m)
    else ihsK1 n nP mo ml d fo fl (ih1W n m nP mo ml d (rdW (m.arr64 IW) fo))

/-- After `class_read_minor_ih1`. -/
def ihsK1 (n : Nat) (nP mo ml d fo fl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ihsK2 n r1 (ihsW n m1 nP mo ml d (fo + 1) (fl - 1))

/-- After the recursive call. -/
def ihsK2 (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r1.headD 0 = 1 then ihsK3 n r2 (recW m2 2 [r1.tail.headD 0, r1.tail.tail.headD 0])
    else some ([r2.headD 0, r2.tail.headD 0], m2)

/-- After `rec2`. -/
def ihsK3 (n : Nat) (r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => ihsK4 (consW n m3 (r3.headD 0) (r2.headD 0) (r2.tail.headD 0))

/-- After `sl_cons`. -/
def ihsK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0, r4.tail.headD 0], m4)
end

/-- `class_read_minor_finish` after `class_read_minor_ihs`. -/
def finK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => some ([1, r2.headD 0], m2)

def finK1 (c cn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => finK2 (recW m1 5 [1, c, cn, r1.headD 0, r1.tail.headD 0])

/-- **The model of `class_read_minor_finish`.** -/
def finW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, fo, fl, hd, c =>
    if hd >>> 28 ≠ 3 then some ([0, 0], m)
    else if eViewW m hd = [] then none
    else finK1 c ((eViewW m hd).tail.headD 0) (ihsW n m nP mo ml d fo fl)

section models2
variable (n : Nat) (nP mo ml d : Word)

def tK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => some ([r7.headD 0, r7.tail.headD 0], m7)

def tK2 (fo fl c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => tK3 (finW n m6 nP mo ml d fo fl (r6.headD 0) c)

def tK1 (fo fl c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.tail.headD 0 = 0 then some ([0, 0], m5)
    else tK2 n nP mo ml d fo fl c
      (gafF m5 [CWF, rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1)])

end models2

/-- **The model of `class_read_minor_tail`.** -/
def tailW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, fo, fl, concl, c =>
    tK1 n nP mo ml d fo fl c (gaaF m [CWF, concl])

section models3
variable (n : Nat) (nP mo ml d : Word)

def mK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([r5.headD 0, r5.tail.headD 0], m5)

def mK4 (fo fl concl : Word) (m3 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r4 =>
    if r4.headD 0 = 0 then some ([0, 0], m3)
    else mK5 (tailW n m3 nP mo ml d fo fl concl (r4.tail.headD 0))

def mK3 (fo fl concl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0], m3)
    else mK4 n nP mo ml d fo fl concl m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0))

def mK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (fvarHeadW m2 (r2.tail.tail.tail.headD 0))

def mK1 (cR : CallM) (dom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => mK2 n nP mo ml d (cR n "open_pis_at_fvars_f" [r1.tail.headD 0, dom, d] m1)

end models3

/-- **The model of `class_read_minor`.** -/
def minorW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, dom => mK1 n nP mo ml d cR dom (piBW n m CWF dom)

/-! ## Arms (for `finish`) -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem) (nP mo ml d x fo fl hd c cn t rr dom concl : Word)
  (cR : CallM)
  (r1 r2 r3 r4 r5 r6 r7 : List Word)

theorem ih1W_eq : ih1W (n + 1) m nP mo ml d x = ih1K1 n nP mo ml d (ftdF m [x]) := rfl
theorem ih1K1_some : ih1K1 n nP mo ml d (some (r1, m1)) =
    ih1K2 n nP mo ml d (pirF m1 [CWF, r1.headD 0]) := rfl
theorem ih1K2_some : ih1K2 n nP mo ml d (some (r2, m2)) =
    ih1K3 n nP mo ml d (r2.headD 0) (fvarHeadW m2 (r2.headD 0)) := rfl
theorem ih1K3_fail (h : r3.headD 0 = 0) : ih1K3 n nP mo ml d rr (some (r3, m3)) = some ([0, 0, 0], m3) := by
  rw [ih1K3, if_pos h]
theorem ih1K3_ok (h : r3.headD 0 ≠ 0) : ih1K3 n nP mo ml d rr (some (r3, m3)) =
    ih1K4 d rr m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0)) := by rw [ih1K3, if_neg h]
theorem ih1K4_fail (h : r4.headD 0 = 0) : ih1K4 d rr m3 (some r4) = some ([0, 0, 0], m3) := by
  rw [ih1K4, if_pos h]
theorem ih1K4_ok (h : r4.headD 0 ≠ 0) : ih1K4 d rr m3 (some r4) =
    ih1K5 d (r4.tail.headD 0) (gaaF m3 [CWF, rr]) := by rw [ih1K4, if_neg h]
theorem ih1K5_fail (h : r5.tail.headD 0 = 0) : ih1K5 d t (some (r5, m5)) = some ([0, 0, 0], m5) := by
  rw [ih1K5, if_pos h]
theorem ih1K5_ok (h : r5.tail.headD 0 ≠ 0) : ih1K5 d t (some (r5, m5)) =
    ih1K6 d t (fvarHeadW m5 (rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1))) := by
  rw [ih1K5, if_neg h]
theorem ih1K6_fail (h : r6.headD 0 = 0) : ih1K6 d t (some (r6, m6)) = some ([0, 0, 0], m6) := by
  rw [ih1K6, if_pos h]
theorem ih1K6_lt (h : r6.headD 0 ≠ 0) (h2 : r6.tail.headD 0 < d) :
    ih1K6 d t (some (r6, m6)) = some ([0, 0, 0], m6) := by rw [ih1K6, if_neg h, if_pos h2]
theorem ih1K6_ok (h : r6.headD 0 ≠ 0) (h2 : ¬ r6.tail.headD 0 < d) :
    ih1K6 d t (some (r6, m6)) = some ([1, r6.tail.headD 0 - d, t], m6) := by rw [ih1K6, if_neg h, if_neg h2]

theorem ihsW_nil (h : fl = 0) : ihsW (n + 1) m nP mo ml d fo fl = some ([0, 0], m) := by simp [ihsW, h]
theorem ihsW_cons (h : fl ≠ 0) : ihsW (n + 1) m nP mo ml d fo fl =
    ihsK1 n nP mo ml d fo fl (ih1W n m nP mo ml d (rdW (m.arr64 IW) fo)) := by simp [ihsW, h]
theorem ihsK1_some : ihsK1 n nP mo ml d fo fl (some (r1, m1)) =
    ihsK2 n r1 (ihsW n m1 nP mo ml d (fo + 1) (fl - 1)) := by rw [ihsK1]
theorem ihsK2_hit (h : r1.headD 0 = 1) : ihsK2 n r1 (some (r2, m2)) =
    ihsK3 n r2 (recW m2 2 [r1.tail.headD 0, r1.tail.tail.headD 0]) := by rw [ihsK2, if_pos h]
theorem ihsK2_miss (h : r1.headD 0 ≠ 1) : ihsK2 n r1 (some (r2, m2)) =
    some ([r2.headD 0, r2.tail.headD 0], m2) := by rw [ihsK2, if_neg h]
theorem ihsK3_some : ihsK3 n r2 (some (r3, m3)) =
    ihsK4 (consW n m3 (r3.headD 0) (r2.headD 0) (r2.tail.headD 0)) := by rw [ihsK3]
theorem ihsK4_some : ihsK4 (some (r4, m4)) = some ([r4.headD 0, r4.tail.headD 0], m4) := by rw [ihsK4]

theorem finW_tag (h : hd >>> 28 ≠ 3) : finW (n + 1) m nP mo ml d fo fl hd c = some ([0, 0], m) := by
  simp [finW, h]
theorem finW_nil (h : ¬ hd >>> 28 ≠ 3) (h2 : eViewW m hd = []) :
    finW (n + 1) m nP mo ml d fo fl hd c = none := by simp only [finW]; rw [if_neg h, if_pos h2]
theorem finW_ok (h : ¬ hd >>> 28 ≠ 3) (h2 : eViewW m hd ≠ []) :
    finW (n + 1) m nP mo ml d fo fl hd c =
      finK1 c ((eViewW m hd).tail.headD 0) (ihsW n m nP mo ml d fo fl) := by
  simp only [finW]; rw [if_neg h, if_neg h2]
theorem finK1_some : finK1 c cn (some (r1, m1)) = finK2 (recW m1 5 [1, c, cn, r1.headD 0, r1.tail.headD 0]) := rfl
theorem finK2_some : finK2 (some (r2, m2)) = some ([1, r2.headD 0], m2) := rfl

theorem minorW_eq : minorW cR (n + 1) m nP mo ml d dom = mK1 n nP mo ml d cR dom (piBW n m CWF dom) := rfl
theorem mK1_some : mK1 n nP mo ml d cR dom (some (r1, m1)) =
    mK2 n nP mo ml d (cR n "open_pis_at_fvars_f" [r1.tail.headD 0, dom, d] m1) := rfl
theorem mK2_fail (h : r2.headD 0 = 0) : mK2 n nP mo ml d (some (r2, m2)) = some ([0, 0], m2) := by
  rw [mK2, if_pos h]
theorem mK2_ok (h : r2.headD 0 ≠ 0) : mK2 n nP mo ml d (some (r2, m2)) =
    mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0) (fvarHeadW m2 (r2.tail.tail.tail.headD 0)) := by
  rw [mK2, if_neg h]
theorem mK3_fail (h : r3.headD 0 = 0) : mK3 n nP mo ml d fo fl concl (some (r3, m3)) = some ([0, 0], m3) := by
  rw [mK3, if_pos h]
theorem mK3_ok (h : r3.headD 0 ≠ 0) : mK3 n nP mo ml d fo fl concl (some (r3, m3)) =
    mK4 n nP mo ml d fo fl concl m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0)) := by rw [mK3, if_neg h]
theorem mK4_fail (h : r4.headD 0 = 0) : mK4 n nP mo ml d fo fl concl m3 (some r4) = some ([0, 0], m3) := by
  rw [mK4, if_pos h]
theorem mK4_ok (h : r4.headD 0 ≠ 0) : mK4 n nP mo ml d fo fl concl m3 (some r4) =
    mK5 (tailW n m3 nP mo ml d fo fl concl (r4.tail.headD 0)) := by rw [mK4, if_neg h]
theorem mK5_some : mK5 (some (r5, m5)) = some ([r5.headD 0, r5.tail.headD 0], m5) := rfl
theorem tailW_eq : tailW (n + 1) m nP mo ml d fo fl concl c =
    tK1 n nP mo ml d fo fl c (gaaF m [CWF, concl]) := rfl
theorem tK1_fail (h : r5.tail.headD 0 = 0) : tK1 n nP mo ml d fo fl c (some (r5, m5)) = some ([0, 0], m5) := by
  rw [tK1, if_pos h]
theorem tK1_ok (h : r5.tail.headD 0 ≠ 0) : tK1 n nP mo ml d fo fl c (some (r5, m5)) =
    tK2 n nP mo ml d fo fl c (gafF m5 [CWF, rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1)]) := by
  rw [tK1, if_neg h]
theorem tK2_some : tK2 n nP mo ml d fo fl c (some (r6, m6)) =
    tK3 (finW n m6 nP mo ml d fo fl (r6.headD 0) c) := rfl
theorem tK3_some : tK3 (some (r7, m7)) = some ([r7.headD 0, r7.tail.headD 0], m7) := rfl
end arms

grind_pattern [ind_grind] ih1W_eq => ih1W (n + 1) m nP mo ml d x
grind_pattern [ind_grind] ih1K1_some => ih1K1 n nP mo ml d (some (r1, m1))
grind_pattern [ind_grind] ih1K2_some => ih1K2 n nP mo ml d (some (r2, m2))
grind_pattern [ind_grind] ih1K3_fail => ih1K3 n nP mo ml d rr (some (r3, m3))
grind_pattern [ind_grind] ih1K3_ok => ih1K3 n nP mo ml d rr (some (r3, m3))
grind_pattern [ind_grind] ih1K4_fail => ih1K4 d rr m3 (some r4)
grind_pattern [ind_grind] ih1K4_ok => ih1K4 d rr m3 (some r4)
grind_pattern [ind_grind] ih1K5_fail => ih1K5 d t (some (r5, m5))
grind_pattern [ind_grind] ih1K5_ok => ih1K5 d t (some (r5, m5))
grind_pattern [ind_grind] ih1K6_fail => ih1K6 d t (some (r6, m6))
grind_pattern [ind_grind] ih1K6_lt => ih1K6 d t (some (r6, m6))
grind_pattern [ind_grind] ih1K6_ok => ih1K6 d t (some (r6, m6))
grind_pattern [ind_grind] ihsW_nil => ihsW (n + 1) m nP mo ml d fo fl
grind_pattern [ind_grind] ihsW_cons => ihsW (n + 1) m nP mo ml d fo fl
grind_pattern [ind_grind] ihsK1_some => ihsK1 n nP mo ml d fo fl (some (r1, m1))
grind_pattern [ind_grind] ihsK2_hit => ihsK2 n r1 (some (r2, m2))
grind_pattern [ind_grind] ihsK2_miss => ihsK2 n r1 (some (r2, m2))
grind_pattern [ind_grind] ihsK3_some => ihsK3 n r2 (some (r3, m3))
grind_pattern [ind_grind] ihsK4_some => ihsK4 (some (r4, m4))
grind_pattern [ind_grind] finW_tag => finW (n + 1) m nP mo ml d fo fl hd c
grind_pattern [ind_grind] finW_nil => finW (n + 1) m nP mo ml d fo fl hd c
grind_pattern [ind_grind] finW_ok => finW (n + 1) m nP mo ml d fo fl hd c
grind_pattern [ind_grind] finK1_some => finK1 c cn (some (r1, m1))
grind_pattern [ind_grind] finK2_some => finK2 (some (r2, m2))
grind_pattern [ind_grind] minorW_eq => minorW cR (n + 1) m nP mo ml d dom
grind_pattern [ind_grind] mK1_some => mK1 n nP mo ml d cR dom (some (r1, m1))
grind_pattern [ind_grind] mK2_fail => mK2 n nP mo ml d (some (r2, m2))
grind_pattern [ind_grind] mK2_ok => mK2 n nP mo ml d (some (r2, m2))
grind_pattern [ind_grind] mK3_fail => mK3 n nP mo ml d fo fl concl (some (r3, m3))
grind_pattern [ind_grind] mK3_ok => mK3 n nP mo ml d fo fl concl (some (r3, m3))
grind_pattern [ind_grind] mK4_fail => mK4 n nP mo ml d fo fl concl m3 (some r4)
grind_pattern [ind_grind] mK4_ok => mK4 n nP mo ml d fo fl concl m3 (some r4)
grind_pattern [ind_grind] mK5_some => mK5 (some (r5, m5))
grind_pattern [ind_grind] tailW_eq => tailW (n + 1) m nP mo ml d fo fl concl c
grind_pattern [ind_grind] tK1_fail => tK1 n nP mo ml d fo fl c (some (r5, m5))
grind_pattern [ind_grind] tK1_ok => tK1 n nP mo ml d fo fl c (some (r5, m5))
grind_pattern [ind_grind] tK2_some => tK2 n nP mo ml d fo fl c (some (r6, m6))
grind_pattern [ind_grind] tK3_some => tK3 (some (r7, m7))

/-! ## Specs -/

section specs
variable (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "sl_find" = some slFind) (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
  (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
  (h5 : p.lookup "rec5" = some rec5)
  (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
  (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
  (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish)
  (hpb : p.lookup "pi_binders" = some piBinders)
  (hmin : p.lookup "class_read_minor" = some classReadMinor)
  (htl : p.lookup "class_read_minor_tail" = some classReadMinorTail) (had : AdF p)

include hfh hv hf hcm hi1 had in
theorem classReadMinorIh1_spec (n : Nat) (s₀ : St) (nP mo ml d x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor_ih1" [nP, mo, ml, d, x]
    ⦃fun r s' => LocEq s' s₀ ∧ ih1W n s₀.mem nP mo ml d x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hi1]; simp only [callFn, classReadMinorIh1]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ftdF_spec p had n, pirF_spec p had n, gaaF_spec p had n,
      fvarHead_spec p hfh hv had n, classOfMotiveVar_spec p hf hcm n] <;>
    finish (gen := 20) [rdW_eq, getD_one, getD_two, getD_three]

include hfh hv hf hcm hi1 hc ha hsc h2 his had in
theorem classReadMinorIhs_spec (n : Nat) : ∀ (s₀ : St) (nP mo ml d fo fl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor_ihs" [nP, mo, ml, d, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ ihsW n s₀.mem nP mo ml d fo fl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP mo ml d fo fl; rw [invoke_eq _ his]; simp only [callFn, classReadMinorIhs]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP mo ml d fo fl
    rw [invoke_eq _ his]; simp only [callFn, classReadMinorIhs]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classReadMinorIh1_spec p hfh hv hf hcm hi1 had n, rec2_specW p ha n h2,
        slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

include hfh hv hf hcm hi1 hc ha hsc h2 his h5 hfin had in
theorem classReadMinorFinish_spec (n : Nat) (s₀ : St) (nP mo ml d fo fl hd c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor_finish" [nP, mo, ml, d, fo, fl, hd, c]
    ⦃fun r s' => LocEq s' s₀ ∧ finW n s₀.mem nP mo ml d fo fl hd c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hfin]; simp only [callFn, classReadMinorFinish]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, classReadMinorIhs_spec p hfh hv hf hcm hc ha hsc h2 hi1 his had n,
      rec5_specW p ha n h5] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

include hfh hv hf hcm hi1 hc ha hsc h2 his h5 hfin htl had in
theorem classReadMinorTail_spec (n : Nat) (s₀ : St) (nP mo ml d fo fl concl c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor_tail" [nP, mo, ml, d, fo, fl, concl, c]
    ⦃fun r s' => LocEq s' s₀ ∧ tailW n s₀.mem nP mo ml d fo fl concl c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ htl]; simp only [callFn, classReadMinorTail]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      gaaF_spec p had n, gafF_spec p had n,
      classReadMinorFinish_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin had n] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

include hfh hv hf hcm hi1 hc ha hsc h2 his h5 hfin htl hpb hmin had in
theorem classReadMinor_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (nP mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor" [nP, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ minorW cR n s₀.mem nP mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hmin]; simp only [callFn, classReadMinor]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      piBinders_spec' p ha hc hv hsc hpb n, hcR n "open_pis_at_fvars_f",
      fvarHead_spec p hfh hv had n, classOfMotiveVar_spec p hf hcm n,
      classReadMinorTail_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin htl had n] <;>
    finish (gen := 20) [rdW_eq, loc_init4]

end specs

end L.Ind
