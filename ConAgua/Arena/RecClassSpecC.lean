import ConAgua.Arena.RecStab
import ConAgua.Arena.IndPartsSpec3
import ConAgua.Arena.WhnfCoreProj

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

l_model classReadMinorIh1_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1) (had : AdF p)
  fns [hi1 ↦ ih1W list]
  specs [ftdF_spec p had n, pirF_spec p had n, gaaF_spec p had n,
    fvarHead_spec p hfh hv had n, classOfMotiveVar_spec p hf hcm n]
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

l_model classReadMinorIhs_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs) (had : AdF p)
  fns [his ↦ ihsW list]
  specs [classReadMinorIh1_spec p hfh hv hf hcm hi1 had n, rec2_specW p ha n h2,
    slCons_specW p ha hc hsc n]
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

l_model classReadMinorFinish_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (h5 : p.lookup "rec5" = some rec5)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
    (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish) (had : AdF p)
  fns [hfin ↦ finW list]
  specs [eView_spec p hv n, classReadMinorIhs_spec p hfh hv hf hcm hc ha hsc h2 hi1 his had n,
    rec5_specW p ha n h5]
  grind [arena_grind] simp [rdW_eq]

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




theorem minorW_eq : minorW cR (n + 1) m nP mo ml d dom = mK1 n nP mo ml d cR dom (piBW n m CWF dom) := rfl
theorem mK1_some : mK1 n nP mo ml d cR dom (some (r1, m1)) =
    mK2 n nP mo ml d (cR n "open_pis_at_fvars_f" [r1.tail.headD 0, dom, d] m1) := rfl
theorem mK2_fail (h : r2.headD 0 = 0) : mK2 n nP mo ml d (some (r2, m2)) = some ([0, 0], m2) := by
  rw [mK2, ite_eq_left h]
theorem mK2_ok (h : r2.headD 0 ≠ 0) : mK2 n nP mo ml d (some (r2, m2)) =
    mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0) (fvarHeadW m2 (r2.tail.tail.tail.headD 0)) := by
  rw [mK2, ite_eq_right h]
theorem mK3_fail (h : r3.headD 0 = 0) : mK3 n nP mo ml d fo fl concl (some (r3, m3)) = some ([0, 0], m3) := by
  rw [mK3, ite_eq_left h]
theorem mK3_ok (h : r3.headD 0 ≠ 0) : mK3 n nP mo ml d fo fl concl (some (r3, m3)) =
    mK4 n nP mo ml d fo fl concl m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0)) := by rw [mK3, ite_eq_right h]
theorem mK4_fail (h : r4.headD 0 = 0) : mK4 n nP mo ml d fo fl concl m3 (some r4) = some ([0, 0], m3) := by
  rw [mK4, ite_eq_left h]
theorem mK4_ok (h : r4.headD 0 ≠ 0) : mK4 n nP mo ml d fo fl concl m3 (some r4) =
    mK5 (tailW n m3 nP mo ml d fo fl concl (r4.tail.headD 0)) := by rw [mK4, ite_eq_right h]
theorem mK5_some : mK5 (some (r5, m5)) = some ([r5.headD 0, r5.tail.headD 0], m5) := rfl
theorem tailW_eq : tailW (n + 1) m nP mo ml d fo fl concl c =
    tK1 n nP mo ml d fo fl c (gaaF m [CWF, concl]) := rfl
theorem tK1_fail (h : r5.tail.headD 0 = 0) : tK1 n nP mo ml d fo fl c (some (r5, m5)) = some ([0, 0], m5) := by
  rw [tK1, ite_eq_left h]
theorem tK1_ok (h : r5.tail.headD 0 ≠ 0) : tK1 n nP mo ml d fo fl c (some (r5, m5)) =
    tK2 n nP mo ml d fo fl c (gafF m5 [CWF, rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1)]) := by
  rw [tK1, ite_eq_right h]
theorem tK2_some : tK2 n nP mo ml d fo fl c (some (r6, m6)) =
    tK3 (finW n m6 nP mo ml d fo fl (r6.headD 0) c) := rfl
theorem tK3_some : tK3 (some (r7, m7)) = some ([r7.headD 0, r7.tail.headD 0], m7) := rfl
end arms

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
