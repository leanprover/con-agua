import ConAgua.Arena.RecCheck
import ConAgua.Arena.RecCheckSpec
import ConAgua.Arena.IndSumSpec2
import ConAgua.Arena.RecGenSpec2
import ConAgua.Arena.IndPartsSpec2

/-!
# More refinements of `RecCheck` (lane `indproofs`, helper `recb`)
-/

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

theorem ctorsHaveName_spec (p : Prog) (hp : p.lookup "ctors_have_name" = some ctorsHaveName) (n : Nat) :
    ∀ (s₀ : St) (co cl name : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctors_have_name" [co, cl, name]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ chnW n s₀.mem co cl name = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ co cl name; rw [invoke_eq _ hp]; simp only [callFn, ctorsHaveName]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ co cl name
    rw [invoke_eq _ hp]
    simp only [callFn, ctorsHaveName]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)


/-- A decoded constructor pair's name word. -/
theorem decCN_nameW {m : Mem} {p : Nat} {x : IConstantVal × Nat} (h : decCN m p = some x)
    (hp : p < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (UInt64.ofNat p)) = w ∧ w.toNat < 2 ^ 32 ∧
      x.1.name = decI w := by
  simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, nF, -, rfl⟩ := h
  have hr := iwN_rdW hq hp
  obtain ⟨w, hw, hw32, hn⟩ := decCV_name hcv
  refine ⟨w, ?_, hw32, hn⟩
  rw [hr.1]
  have : (UInt64.ofNat q).toNat = q := by simp; have := hr.2; omega
  simp only [rdW, this]
  have hw' : (m.arr64 EREC)[q]? = some w := hw
  rw [hw']; rfl

theorem chnW_ok (n : Nat) : ∀ (m : Mem) (co cl name r : Word) (ctors : List (IConstantVal × Nat)),
    chnW n m co cl name = some r → decPL m (decCN m) co.toNat cl.toNat = some ctors →
    name.toNat < 2 ^ 32 → co.toNat + cl.toNat < 2 ^ 64 →
    (r != 0) = ctors.any (fun c => c.1.name == (decI name : NIdx)) ∧ r.toNat ≤ 1 := by
  induction n with
  | zero => intro m co cl name r ctors h; simp [chnW] at h
  | succ n ih =>
    intro m co cl name r ctors h hd hn hb
    by_cases hl : cl = 0
    · rw [chnW_nil n m co cl name hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hz : cl.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, cl.toNat = l1 + 1 := ⟨cl.toNat - 1, by
        have : cl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, x, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      obtain ⟨w, hw, hw32, hname⟩ := decCN_nameW hx hrd.2
      have hiff : (w = name) ↔ (x.1.name == (decI name : NIdx)) = true := by
        rw [hname, beq_iff_eq, decI_eq_iff w hw32, decI_word_self name hn]
      rw [← hrd.1] at hw
      by_cases he : w = name
      · rw [chnW_hit n m co cl name hl (by rw [hw]; exact he)] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.any_cons, hiff.mp he]
      · rw [chnW_next n m co cl name hl (by rw [hw]; exact he)] at h
        have hys' : decPL m (decCN m) (co + 1).toNat (cl - 1).toNat = some ys := by
          have hl1' : (cl - 1).toNat = l1 := by omega
          rw [hco1, hl1']; exact hys
        have := ih m (co + 1) (cl - 1) name r ys h hys' hn (by omega)
        have hne : ¬ (x.1.name == (decI name : NIdx)) = true := fun e => he (hiff.mpr e)
        simpa [List.any_cons, hne] using this


/-- **`ctors_have_name` is `ctors.any (·.1.name == name)`** (the test inside `targetMajorNfs`; pure,
the state untouched). -/
theorem ctorsHaveName_refines (p : Prog) (hp : p.lookup "ctors_have_name" = some ctorsHaveName)
    (n : Nat) (s₀ : St) (co cl name : Word) (ctors : List (IConstantVal × Nat))
    (hd : decPL s₀.mem (decCN s₀.mem) co.toNat cl.toNat = some ctors) (hn : name.toNat < 2 ^ 32)
    (hb : co.toNat + cl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctors_have_name" [co, cl, name]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = ctors.any (fun c => c.1.name == (decI name : NIdx)) ∧
      (r.headD 0).toNat ≤ 1; ⊤⦄ := by
  refine triple_post (ctorsHaveName_spec p hp n s₀ co cl name) ?_
  rintro r s' ⟨hl, hm, hw⟩
  exact ⟨hl, hm, chnW_ok n s₀.mem co cl name _ ctors hw hd hn hb⟩


/-! ## `target_major_of_outside_closed`: the same `allM` as `class_key_of_closed` -/

theorem targetMajorOfOutsideClosed_spec (p : Prog)
    (hp : p.lookup "target_major_of_outside_closed" = some targetMajorOfOutsideClosed) (n : Nat) :
    ∀ (s₀ : St) (dso dsl nP : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_of_outside_closed" [dso, dsl, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ ckcW n s₀.mem nP dso dsl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dso dsl nP; rw [invoke_eq _ hp]; simp only [callFn, targetMajorOfOutsideClosed]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ dso dsl nP
    rw [invoke_eq _ hp]
    simp only [callFn, targetMajorOfOutsideClosed]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "bvar_b" n, stubM_spec p "fvar_b" n, ih] <;>
      finish (gen := 20)

/-- **`target_major_of_outside_closed` refines the `allM` closedness test of `targetMajorOf`'s
outside branch** (through the stubs `bvar_b`, `fvar_b`). A piece of `targetMajorOf`. -/
theorem targetMajorOfOutsideClosed_refines (p : Prog)
    (hp : p.lookup "target_major_of_outside_closed" = some targetMajorOfOutsideClosed) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis dso dsl nP : Word)
    (xs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hd : decHL s₀.mem dso.toNat dsl.toNat = some xs)
    (hb : dso.toNat + dsl.toNat < 2 ^ 64) (ht : dso.toNat + dsl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_of_outside_closed" [dso, dsl, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (xs.allM (keyClosedTest nP.toNat)) a₀ ∧
      KeepPost dn vis fe decW0B s₀.mem s'.mem (AM.st (xs.allM (keyClosedTest nP.toNat)) a₀) r
        (AM.res (xs.allM (keyClosedTest nP.toNat)) a₀); ⊤⦄ := by
  refine triple_post (targetMajorOfOutsideClosed_spec p hp n s₀ dso dsl nP) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost⟩ := ckcW_ok dn fe n _ _ a₀ vis nP dso dsl xs r hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost⟩


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
      rw [if_pos (by omega)] at hGj
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
      simp only [iwH, hd?, iwA, hGj, hwl', if_true, Option.bind_some]
      simp [hwl', hnm'])
    simpa [hlen] using this
  · refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, if_neg (by omega)]
  · simp only [iwTop, htop, hsum]


/-- **`ptr_list_names` is `xs.map (cvOf · |>.name)`** for any slice decoded by `f` whose records
lead with a constant pointer (`RecShape`: `decRS`/`.cvR`, constructor entry: `decCN`/`.1`). Through
`iw_alloc`; a piece of `targetRecPins` and `targetMajorNfs`' callers. -/
theorem ptrListNames_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "ptr_names_copy" = some ptrNamesCopy)
    (hp : p.lookup "ptr_list_names" = some ptrListNames) (n : Nat) (s₀ : St) (o l : Word)
    {α : Type} (f : Nat → Option α) (cvOf : α → IConstantVal) (xs : List α)
    (hf : ∀ pp x, f pp = some x → ∃ a, iwN s₀.mem pp = some a ∧ decCVp s₀.mem a = some (cvOf x))
    (hd : decPL s₀.mem f o.toNat l.toNat = some xs) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hcl : 200 < (s₀.mem.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop s₀.mem)
    (hptr : ∀ j v, j < l.toNat → iwN s₀.mem (o.toNat + j) = some v → v < iwTop s₀.mem) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ptr_list_names" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 CTL) 200, l] ∧
      decHL s'.mem (rdW (s₀.mem.arr64 CTL) 200).toNat l.toNat = some (xs.map (fun x => (cvOf x).name)) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + l.toNat = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (ptrListNames_spec p ha hc hp n s₀ o l) ?_
  rintro r s' ⟨hl, h⟩
  have hlen := decPL_length s₀.mem hd
  have := ptrNamesW_dec (xs.map cvOf) h hsz hcl (by simpa using hlen) hsrc (fun j hj => by
    have hj' : j < l.toNat := by simpa [hlen] using hj
    obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l.toNat o.toNat xs hd j hj'
    obtain ⟨a, hva, hcv⟩ := hf v y hy
    refine ⟨v, a, hv, hptr j v hj' hv, hva, ?_⟩
    have hy' : xs[j]'(by omega) = y := by
      simpa [List.getElem?_eq_getElem (show j < xs.length by omega)] using hget
    simpa [List.getElem_map, hy'] using hcv)
  obtain ⟨h1, h2, h3, h4, h5⟩ := this
  refine ⟨hl, h1, ?_, h3, h4, h5⟩
  rw [List.map_map] at h2
  exact h2

end L.Ind
