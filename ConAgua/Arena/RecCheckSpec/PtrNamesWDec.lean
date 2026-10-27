import ConAgua.Arena.IndInstallSpec.InstallCtxWord9
import ConAgua.Arena.IndPosSpec.NkcW

/-!
# PtrNamesWDec

`chnW`, `chnW_nil`, `chnW_hit`, `chnW_next`, `ptrNamesCopy_spec`, `ptrNamesW` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ctors_have_name`: `ctors.any (·.1.name == name)` -/

/-- **The model of `ctors_have_name`.** -/
def chnW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, co, cl, name =>
    if cl = 0 then some 0
    else if rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) = name then some 1
    else chnW n m (co + 1) (cl - 1) name

section arms
variable (n : Nat) (m : Mem) (co cl name : Word)
theorem chnW_nil (h : cl = 0) : chnW (n + 1) m co cl name = some 0 := by simp [chnW, h]
theorem chnW_hit (h : cl ≠ 0) (hx : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) = name) :
    chnW (n + 1) m co cl name = some 1 := by simp [chnW, h, hx]
theorem chnW_next (h : cl ≠ 0) (hx : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) ≠ name) :
    chnW (n + 1) m co cl name = chnW n m (co + 1) (cl - 1) name := by simp [chnW, h, hx]
end arms

grind_pattern [ind_grind] chnW_nil => chnW (n + 1) m co cl name
grind_pattern [ind_grind] chnW_hit => chnW (n + 1) m co cl name
grind_pattern [ind_grind] chnW_next => chnW (n + 1) m co cl name

/-! ## `target_major_of_outside_closed`: the same `allM` as `class_key_of_closed` -/

/-! ## `ptr_list_names`: the names of a slice of constant-headed records

`ptr_names_copy` is `member_names_copy`'s loop (same model `nameCopyW`); `ptr_list_names` is
`block_shape_member_names` with the slice a parameter. -/

theorem ptrNamesCopy_spec (p : Prog) (hp : p.lookup "ptr_names_copy" = some ptrNamesCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ptr_names_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ nameCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, ptrNamesCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, ptrNamesCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- The model of `ptr_list_names`. -/
def ptrNamesW (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) :=
  match allocW m l with
  | none => none
  | some (q, m1) =>
    match nameCopyW (n - 1) m1 q o l with
    | none => none
    | some m2 => some ([q, l], m2)

theorem ptrListNames_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "ptr_names_copy" = some ptrNamesCopy)
    (hp : p.lookup "ptr_list_names" = some ptrListNames) (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ptr_list_names" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ptrNamesW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ptrListNames]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ a m1 m2, allocW s₀.mem l = some (a, m1) → nameCopyW n m1 a o l = some m2 →
        ptrNamesW (n + 1) s₀.mem o l = some ([a, l], m2) := by
      intro a m1 m2 h1 h2
      simp [ptrNamesW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, ptrNamesCopy_spec p hc n] <;>
      finish (gen := 20)

/-- **`ptr_list_names` copies the names**: given the slice's records' constants. -/
theorem ptrNamesW_dec {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (cvs : List IConstantVal)
    (h : ptrNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hlen : cvs.length = l.toNat)
    (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hcv : ∀ j (hj : j < cvs.length), ∃ v a, iwN m (o.toNat + j) = some v ∧ v < iwTop m ∧
      iwN m v = some a ∧ decCVp m a = some cvs[j]) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat = some (cvs.map (·.name)) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' := by
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  simp only [ptrNamesW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : nameCopyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq' hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hEE : (allocMem m l).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hptr' : ∀ j < l.toNat,
      (rdW ((allocMem m l).arr64 IW) (UInt64.ofNat (o.toNat + j))).toNat < q.toNat := by
    intro j hj
    obtain ⟨v, a, hv, hvb, -, -⟩ := hcv j (by omega)
    obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
    rw [hIW, hv']
    simp only [iwTop, hqq] at hvb
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; exact hvb
  obtain ⟨hA, hS, hW, hG⟩ := nameCopyW_get (n - 1) _ _ _ _ _ hcp
    (by simp only [iwTop, hqq] at hsrc; omega)
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz) hptr'
  rw [hIW] at hS hG
  rw [hEE] at hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]) hW)
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr, ?_⟩
  · have := decHL_of_get m2 (cvs.map (·.name)) q.toNat (fun j hj => by
      have hj' : j < cvs.length := by simpa using hj
      obtain ⟨v, a, hv, hvb, hva, hcvj⟩ := hcv j hj'
      have hGj := hG (q.toNat + j)
      rw [ite_eq_left (by omega)] at hGj
      have e2 : q.toNat + j - q.toNat = j := by omega
      rw [e2] at hGj
      obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
      rw [hv'] at hGj
      obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
      rw [hva'] at hGj
      obtain ⟨w, hw, hwl', hnm'⟩ := decCV_name (a := erA m) (by simpa [decCVp] using hcvj)
      have hrd : rdW (m.arr64 EREC) (UInt64.ofNat a) = w := by
        have : (UInt64.ofNat a).toNat = a := by simp; omega
        have hw' : (m.arr64 EREC)[a]? = some w := hw
        simp [rdW, this, hw']
      rw [hrd] at hGj
      simp only [List.getElem_map]
      simp only [iwH, hd?, iwA, hGj]
      simp [hwl', hnm'])
    simpa [hlen] using this
  · refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum]

/-! ## `mk_target_major`: a fresh 13-word record -/

/-- The thirteen stores of `mk_target_major` at `q`. -/
def tmWr (m1 : Mem) (q a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) : Mem :=
  ((((((((((((m1.set64 IW q a0).set64 IW (q + 1) a1).set64 IW (q + 2) a2).set64 IW
    (q + 3) a3).set64 IW (q + 4) a4).set64 IW (q + 5) a5).set64 IW (q + 6) a6).set64 IW (q + 7) a7).set64
    IW (q + 8) a8).set64 IW (q + 9) a9).set64 IW (q + 10) a10).set64 IW (q + 11) a11).set64 IW
    (q + 12) a12

/-- The memory after `mk_target_major(...)`. -/
def tmMem (m : Mem) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) : Mem :=
  tmWr (allocMem m 13) (rdW (m.arr64 CTL) 200) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12

/-- **The model of `mk_target_major`.** -/
def mkTMW (m : Mem) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) : Option (List Word × Mem) :=
  match allocW m 13 with
  | none => none
  | some (q, m1) => some ([q], tmWr m1 q a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)

theorem mkTargetMajor_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "mk_target_major" = some mkTargetMajor) (n : Nat) (s₀ : St)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mk_target_major"
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
    ⦃fun r s' => LocEq s' s₀ ∧
      mkTMW s₀.mem a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkTargetMajor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish (gen := 20) [mkTMW, tmWr]

theorem tmMem_eq (m : Mem) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) :
    tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
      wrIW (allocMem m 13) (rdW (m.arr64 CTL) 200) [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] := by
  simp [tmMem, tmWr, wrIW, UInt64.add_assoc]

/-- **What `mk_target_major` leaves**: the pool grew, the thirteen words are readable at the old top,
and (given the slices' decodings at the new memory, which the caller gets by pool growth) the new
record decodes as the `TargetMajor` of its arguments. -/
theorem tmMem_dec (m : Mem) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word)
    (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 13 ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (ds : List EIdx) (ctors : List (IConstantVal × Nat)) (nfs : List NestCtorNf) (pfvs : List EIdx)
    (h0 : a0.toNat < 2 ^ 32) (h1 : a1.toNat < 2 ^ 32)
    (hds : decHL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) a2.toNat a3.toNat = some ds)
    (hct : decPL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
      (decCN (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)) a6.toNat a7.toNat = some ctors)
    (hnf : decPL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
      (decNCN (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)) a9.toNat a10.toNat = some nfs)
    (hpf : decHL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) a11.toNat a12.toNat = some pfvs) :
    IWGrow m (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) ∧
    decTM (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) (rdW (m.arr64 CTL) 200).toNat =
      some { ind := decI a0, lvls := decI a1, ds := ds, nPc := a4.toNat, nIdx := a5.toNat,
             ctors := ctors, member := decON a8.toNat, nfs := nfs, pfvs := pfvs } := by
  have hpost := recMem_post m [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] 13 rfl hc
    (by simpa using hroom) hsz
  rw [← tmMem_eq] at hpost
  obtain ⟨hrd, hgrow, -, -⟩ := hpost
  refine ⟨hgrow, ?_⟩
  generalize hq : rdW (m.arr64 CTL) 200 = q at *
  have r0 := hrd 0 (by simp)
  have r1 := hrd 1 (by simp)
  have r2 := hrd 2 (by simp)
  have r3 := hrd 3 (by simp)
  have r4 := hrd 4 (by simp)
  have r5 := hrd 5 (by simp)
  have r6 := hrd 6 (by simp)
  have r7 := hrd 7 (by simp)
  have r8 := hrd 8 (by simp)
  have r9 := hrd 9 (by simp)
  have r10 := hrd 10 (by simp)
  have r11 := hrd 11 (by simp)
  have r12 := hrd 12 (by simp)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  simp only [decTM, bind, pure, iwH, hd?, iwN, nat?, decAt, iwA, Nat.add_zero] at *
  simp [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, h0, h1, hds, hct, hnf, hpf]

/-! ## `target_major_default` -/

mutual
/-- **The model of `target_major_default`.** -/
def tmdW (m : Mem) : Option (List Word × Mem) := tmdK1 (naF m [])
/-- After `intern_nanon`. -/
def tmdK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) => tmdK2 m1 (ra.headD 0) (pinWordV m1 52)
/-- After `pin_word(52)`. -/
def tmdK2 (m1 : Mem) (anon : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some ls => tmdK3 (mkTMW m1 anon ls 0 0 0 0 0 0 0 0 0 0 0)
/-- After `mk_target_major`. -/
def tmdK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)
end

theorem tmdW_eq (m : Mem) : tmdW m = tmdK1 (naF m []) := rfl
theorem tmdK1_some (ra : List Word) (m1 : Mem) :
    tmdK1 (some (ra, m1)) = tmdK2 m1 (ra.headD 0) (pinWordV m1 52) := rfl
theorem tmdK2_some (m1 : Mem) (anon ls : Word) :
    tmdK2 m1 anon (some ls) = tmdK3 (mkTMW m1 anon ls 0 0 0 0 0 0 0 0 0 0 0) := rfl
theorem tmdK3_some (r : List Word) (m2 : Mem) : tmdK3 (some (r, m2)) = some ([r.headD 0], m2) := rfl

grind_pattern [ind_grind] tmdW_eq => tmdW m
grind_pattern [ind_grind] tmdK1_some => tmdK1 (some (ra, m1))
grind_pattern [ind_grind] tmdK2_some => tmdK2 m1 anon (some ls)
grind_pattern [ind_grind] tmdK3_some => tmdK3 (some (r, m2))

theorem targetMajorDefault_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hp : p.lookup "target_major_default" = some targetMajorDefault) (hna : NaF p) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_major_default" []
    ⦃fun r s' => LocEq s' s₀ ∧ tmdW s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorDefault]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      naF_spec p hna n, pinWord_specV p hpw n, mkTargetMajor_spec p ha hm n] <;>
    finish (gen := 20) [rdW_eq, List.getD_cons_zero, List.getD_cons_succ, List.tail_cons]

/-- **`mkTMW` leaves** (model level): the pointer, the growth, the frame, the new top, and the record
decoded (given the slices' decodes at the new memory). -/
theorem mkTMW_dec {m m' : Mem} {r : List Word} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word)
    (h : mkTMW m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = some (r, m'))
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (ds : List EIdx) (ctors : List (IConstantVal × Nat)) (nfs : List NestCtorNf) (pfvs : List EIdx)
    (h0 : a0.toNat < 2 ^ 32) (h1 : a1.toNat < 2 ^ 32)
    (hds : decHL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) a2.toNat a3.toNat = some ds)
    (hct : decPL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
      (decCN (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)) a6.toNat a7.toNat = some ctors)
    (hnf : decPL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
      (decNCN (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)) a9.toNat a10.toNat = some nfs)
    (hpf : decHL (tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) a11.toNat a12.toNat = some pfvs) :
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ iwTop m' ≤ (m.arr64 IW).size ∧
    decTM m' (r.headD 0).toNat =
      some { ind := decI a0, lvls := decI a1, ds := ds, nPc := a4.toNat, nIdx := a5.toNat,
             ctors := ctors, member := decON a8.toNat, nfs := nfs, pfvs := pfvs } := by
  simp only [mkTMW] at h
  cases hal : allocW m 13 with
  | none => rw [hal] at h; simp at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  rw [hal] at h
  obtain ⟨rfl, hm2⟩ := Prod.mk.inj (Option.some.inj h)
  rw [← hm2]
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  subst hm1
  have hroom' : (rdW (m.arr64 CTL) 200).toNat + 13 ≤ (m.arr64 IW).size := by
    rw [← hq]; simpa using hroom
  obtain ⟨hg, hd⟩ := tmMem_dec m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hc hroom' hsz ds ctors
    nfs pfvs h0 h1 hds hct hnf hpf
  have hmem : tmWr (allocMem m 13) q a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
      tmMem m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 := by rw [tmMem, hq]
  have hpost := recMem_post m [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] 13 rfl hc
    (by simpa using hroom') hsz
  rw [← tmMem_eq] at hpost
  obtain ⟨-, -, hfr, htop⟩ := hpost
  rw [hmem]
  refine ⟨hg, hfr, ?_, by simpa [hq] using hd⟩
  simp only [iwTop, htop]
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

theorem tmdW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a : AState)
    (r : List Word) (h : tmdW m = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ tm a', ConRon.Arena.targetMajorDefault.run a = .ok (tm, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decTM m' (r.headD 0).toNat = some tm := by
  rw [tmdW_eq] at h
  rcases h1 : naF m [] with _ | ⟨ra, m1⟩ <;> simp only [h1, tmdK1, reduceCtorEq] at h
  obtain ⟨anon, a1, hrun1, hS1, hg1, hw1, hl1⟩ := naF_ok dn vis fe m m1 a ra h1 hS
  rcases hp : pinWordV m1 52 with _ | ls <;> simp only [hp, tmdK2, reduceCtorEq] at h
  have hpne : rdW (m1.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hp
  have hz : ls = pinW m1 52 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hp
    rw [← hp]; rfl
  have hfull := hS1.1.pins.full hpne
  have hlslt : ls.toNat < 2 ^ 32 := by rw [hz]; exact hfull.lv_lt.1
  have hrunP : pinEmptyLevels.run a1 = .ok (decI ls, a1) := by rw [hz]; exact pinEmptyLevels_run hfull
  rcases hmk : mkTMW m1 (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 with _ | ⟨r3, m2⟩ <;> simp only [hmk, tmdK3, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hI, hE, hIsz, hEsz, hCsz⟩ := hS1.2
  have hdec0 : ∀ {k : IdxKind} (mm : Mem), (decHL mm (0 : Word).toNat (0 : Word).toNat : Option (List (Idx k))) = some [] := by
    intro k mm; simp [decHL, hslice?]
  have hdecP : ∀ {α : Type} (mm : Mem) (f : Nat → Option α), decPL mm f (0 : Word).toNat (0 : Word).toNat = some [] := by
    intro α mm f; simp [decPL]
  obtain ⟨hg2, hfr, htop, hdec⟩ := mkTMW_dec (m := m1) (m' := m2) (r := r3) (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0
    hmk hIsz hCsz [] [] [] [] hw1 hlslt (hdec0 _) (hdecP _ _) (hdecP _ _) (hdec0 _)
  refine ⟨{ ind := decI (ra.headD 0), lvls := decI ls, ds := [], nPc := (0 : Word).toNat,
            nIdx := (0 : Word).toNat, ctors := [], member := decON (0 : Word).toNat, nfs := [],
            pfvs := [] }, a1, ?_, stage_frame_iw hS1 hfr htop, hg1.trans hg2, ?_⟩
  · simp only [ConRon.Arena.targetMajorDefault, StateT.run_bind]
    rw [hrun1]
    simp only [bind, Except.bind]
    rw [hrunP]
    subst hl1
    simp [StateT.run, decON]
    rfl
  · simpa using hdec

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

/-! ## `ptr_list_names` under the stage relation -/

theorem nameCopyW_src0 (n : Nat) (m : Mem) (d s : Word) : nameCopyW n m d s 0 = nameCopyW n m d 0 0 := by
  cases n <;> simp [nameCopyW]

theorem ptrNamesW_src0 {n : Nat} {m : Mem} {o l : Word} (hl : l = 0) : ptrNamesW n m o l = ptrNamesW n m 0 l := by
  subst hl; simp only [ptrNamesW, nameCopyW_src0]

theorem ptrNamesW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : ptrNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (rdW (m.arr64 CTL) 200).toNat + l.toNat ≤ (m.arr64 IW).size := by
  simp only [ptrNamesW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
    obtain ⟨q, m1⟩ := qm
    obtain ⟨hq, -, hroom⟩ := allocW_facts hal hsz
    rw [← hq]; exact hroom

/-- **`ptr_list_names` under the stage relation**: the names of a slice of records decoded below
the tops whose word `0` is a constant pointer. -/
theorem plnW_stage {α : Type} {f : Mem → Nat → Option α} (cvOf : α → IConstantVal)
    (hf : ∀ q, OMono (fun m => f m q))
    (hcv : ∀ m pp x, f m pp = some x → ∃ a, iwN m pp = some a ∧ decCVp m a = some (cvOf x))
    (hfb : ∀ m pp x, f (truncM m) pp = some x → pp < iwTop m)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : ptrNamesW n m o l = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR0 f xs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200, l] ∧
      decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat = some (xs.map fun x => (cvOf x).name) ∧
      (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' := by
  obtain ⟨-, -, hsz, -, hc⟩ := hS.2
  have hroom := ptrNamesW_room h hsz
  have hlen : xs.length = l.toNat := decPL_length _ hx.1
  by_cases hl : l = 0
  · have hxs := hx.nil hl
    subst hxs
    rw [ptrNamesW_src0 hl] at h
    obtain ⟨hr, hd, hg, hfr, ht⟩ := ptrNamesW_dec [] h hsz hc (by simp [hl]) (by simp [hl])
      (fun j hj => absurd hj (by simp))
    exact ⟨stage_frame_iw hS hfr (by rw [← ht]; exact hroom), hg, hr, by simpa using hd, ht⟩
  · have hP := hx.pslr hl
    obtain ⟨-, hel⟩ := pos2_decPL_trunc hx.1
    obtain ⟨hr, hd, hg, hfr, ht⟩ := ptrNamesW_dec (xs.map cvOf) h hsz hc (by simp [hlen]) hP.2
      (fun j hj => by
        have hj' : j < xs.length := by simpa using hj
        obtain ⟨v, -, hv, hj2, hfv⟩ := hel j (by omega)
        have hvt : v < iwTop m := hfb m v _ hfv
        have hfm : f m v = some xs[j] := (show DecB (fun m => f m v) m xs[j] from hfv).get (hf v)
        obtain ⟨a, ha, hca⟩ := hcv m v _ hfm
        exact ⟨v, a, hv, hvt, ha, by simpa using hca⟩)
    exact ⟨stage_frame_iw hS hfr (by rw [← ht]; exact hroom), hg, hr, by simpa [List.map_map, Function.comp_def] using hd, ht⟩

/-! ## `target_rec_pins_names` -/

def tpnK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tpnK4 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m) => tpnK5 (callW p n "sl_nodup" [rn.headD 0, rn.tail.headD 0] m)
def tpnK3 (p : Prog) (n : Nat) (reco recl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ro, m) => if ro.headD 0 = 0 then some ([0], m)
    else tpnK4 p n (callW p n "ptr_list_names" [reco, recl] m)
section arms
variable (p : Prog) (n : Nat) (m : Mem) (reco recl auxo auxl : Word) (r rw : List Word)
theorem tpnK5_some : tpnK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tpnK3_zero (h : r.headD 0 = 0) : tpnK3 p n reco recl (some (r, m)) = some ([0], m) := by
  simp only [tpnK3]; rw [ite_eq_left h]
theorem tpnK3_ok (h : ¬ r.headD 0 = 0) : tpnK3 p n reco recl (some (r, m)) =
    tpnK4 p n (callW p n "ptr_list_names" [reco, recl] m) := by simp only [tpnK3]; rw [ite_eq_right h]
end arms
attribute [ind_grind] tpnK5_some tpnK3_zero tpnK3_ok

end L.Ind

end

end
