import ConAgua.Arena.RecCheckSpec5
import ConAgua.Arena.IndPos2SpecA
import ConAgua.Arena.IndPos2SpecE
import ConAgua.Arena.StageInst1

/-!
# More refinements of `RecCheck` (lane `indproofs2`, helper `rec`): `targetOutsideInst`
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_outside_inst` -/

def toiK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if eViewW m5 (r5.tail.tail.headD 0) = [] then none
    else if (eViewW m5 (r5.tail.tail.headD 0)).headD 0 ≠ 2 then none
    else some ([r5.tail.headD 0, (eViewW m5 (r5.tail.tail.headD 0)).tail.headD 0], m5)

def toiK4 (N : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then none else toiK5 (piBW N m4 CWF (r4.tail.headD 0))

def toiK3 (N : Nat) (dso dsl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => toiK4 N (instW N m3 dso dsl (r3.headD 0))

def toiK2 (cR : CallM) (N : Nat) (us dso dsl q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => toiK3 N dso dsl (cR N "inst_lp_fast"
      [CWF, r2.headD 0, r2.tail.headD 0, us, rdW (m2.arr64 EREC) (q + 4)] m2)

def toiK1 (cR : CallM) (N : Nat) (us dso dsl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then none
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 3 then none
    else toiK2 cR N us dso dsl (r1.tail.headD 0) (erToIwW N m1 (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 2))
      (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 3)))

/-- **The model of `target_outside_inst`** (its `inst_lp_fast` read through `cR`). -/
def toiW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, vis, I, us, dso, dsl => toiK1 cR N us dso dsl (envFindW m I vis)

section arms
variable (cR : CallM) (N : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis I us dso dsl q : Word) (r1 r2 r3 r4 r5 : List Word)
theorem toiW_eq : toiW cR (N + 1) m vis I us dso dsl = toiK1 cR N us dso dsl (envFindW m I vis) := rfl
theorem toiK1_some : toiK1 cR N us dso dsl (some (r1, m1)) =
    if r1.headD 0 = 0 then none
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 3 then none
    else toiK2 cR N us dso dsl (r1.tail.headD 0) (erToIwW N m1 (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 2))
      (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 3))) := rfl
theorem toiK2_some : toiK2 cR N us dso dsl q (some (r2, m2)) = toiK3 N dso dsl (cR N "inst_lp_fast"
      [CWF, r2.headD 0, r2.tail.headD 0, us, rdW (m2.arr64 EREC) (q + 4)] m2) := rfl
theorem toiK3_some : toiK3 N dso dsl (some (r3, m3)) = toiK4 N (instW N m3 dso dsl (r3.headD 0)) := rfl
theorem toiK4_some : toiK4 N (some (r4, m4)) =
    if r4.headD 0 = 0 then none else toiK5 (piBW N m4 CWF (r4.tail.headD 0)) := rfl
theorem toiK5_some : toiK5 (some (r5, m5)) =
    if eViewW m5 (r5.tail.tail.headD 0) = [] then none
    else if (eViewW m5 (r5.tail.tail.headD 0)).headD 0 ≠ 2 then none
    else some ([r5.tail.headD 0, (eViewW m5 (r5.tail.tail.headD 0)).tail.headD 0], m5) := rfl
end arms

grind_pattern [ind_grind] toiW_eq => toiW cR (N + 1) m vis I us dso dsl
grind_pattern [ind_grind] toiK1_some => toiK1 cR N us dso dsl (some (r1, m1))
grind_pattern [ind_grind] toiK2_some => toiK2 cR N us dso dsl q (some (r2, m2))
grind_pattern [ind_grind] toiK3_some => toiK3 N dso dsl (some (r3, m3))
grind_pattern [ind_grind] toiK4_some => toiK4 N (some (r4, m4))
grind_pattern [ind_grind] toiK5_some => toiK5 (some (r5, m5))

/-- The lookups `target_outside_inst` needs. -/
structure ToiProg (p : Prog) : Prop where
  hi1 : I1Prog p
  ix : p.lookup "env_ix" = some envIxL
  rowGet : p.lookup "env_row_get" = some envRowGetL
  find : p.lookup "env_find" = some envFindL
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  icopy : p.lookup "iw_copy" = some iwCopy
  v : p.lookup "e_view" = some eView
  sc : p.lookup "sl_cons" = some slCons
  pb : p.lookup "pi_binders" = some piBinders
  ipw : p.lookup "inst_pis_with" = some instPisWith
  toi : p.lookup "target_outside_inst" = some targetOutsideInst

theorem targetOutsideInst_spec (p : Prog) (h : ToiProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St)
    (vis I us dso dsl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_outside_inst" [vis, I, us, dso, dsl]
    ⦃fun r s' => LocEq s' s₀ ∧ toiW cR N s₀.mem vis I us dso dsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.toi]
  simp only [callFn, targetOutsideInst]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.ix h.rowGet h.find N, erToIw_specW p h.alloc h.copy h.eti N,
        hcR N "inst_lp_fast", instPisWith_spec p h.v h.ipw h.hi1 N,
        piBinders_spec' p h.alloc h.icopy h.v h.sc h.pb N, eView_spec p h.v N] <;>
      finish (gen := 20) [rdW_eq]

/-- `inst_pis_with` from a stable decoding of the arguments. -/
theorem instW_okB {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {n : Nat}
    {m m' : Mem} {a : AState} {ao al e : Word} {args : List EIdx} {r : List Word}
    (h : instW n m ao al e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e)
    (hdec : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hb : ao.toNat + al.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.instPisWith args (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x := by
  have hds : decHL m ao.toNat al.toNat = some args :=
    (OMono.decHL ao.toNat al.toNat).mono _ _ _ (IWGrow.refl m).truncExt hdec
  by_cases hl0 : al.toNat = 0
  · cases n with
    | zero => simp [instW] at h
    | succ n =>
    rw [instW_nil (h := UInt64.toNat_inj.mp (by simpa using hl0))] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : args = [] := by rw [hl0] at hds; simpa [decHL, hslice?] using hds.symm
    subst this
    exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
  exact instW_ok n dn fe vis m m' a ao al e args r h hS he hds hb (decHL_truncM_bound hdec hl0)

/-- The words `[bsl, x]` of `target_outside_inst` denote the twin's `(index count, sort)`. -/
def ToiR (r : List Word) (x : Nat × LIdx) : Prop :=
  r = [r.headD 0, r.tail.headD 0] ∧ (r.headD 0).toNat = x.1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧
    decI (r.tail.headD 0) = x.2

/-- `AbsOK` across `target_outside_inst`'s callees after `inst_lp_fast` (`IndT/RecGenTmf.toiAfr`). -/
def ToiAfr : Prop :=
  ∀ (N : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW N m fuel h = some (r, m') → AFr m m'

theorem toiW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {I us dso dsl : Word} {r : List Word} {ds : List EIdx} {cR : CallM}
    (hIl : IlpRd cR dn vis fe (IlpBase m a))
    (h : toiW cR N m vis I us dso dsl = some (r, m')) (hS : StageR dn vis fe m a) (hI : H I) (hu : H us)
    (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds) (hb : dso.toNat + dsl.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ ToiR r x ∧ (ToiAfr → AFr m m') := by
  cases N with
  | zero => simp [toiW] at h
  | succ N =>
  rw [toiW_eq] at h
  cases h2 : envFindW m I vis with
  | none => rw [h2] at h; simp [toiK1] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, toiK1_some] at h
  obtain ⟨hm2, hfind, hdec⟩ := envFindW_found h2 hS.1.env hI
  subst m2
  by_cases hf0 : r2.headD 0 = 0
  · rw [if_pos hf0] at h; cases h
  rw [if_neg hf0] at h
  by_cases hk3 : rdW (m.arr64 EREC) (r2.tail.headD 0) ≠ 3
  · rw [if_pos hk3] at h; cases h
  rw [if_neg hk3] at h
  obtain ⟨ci, hci⟩ := hdec hf0
  have hfci : fe.find? (decI I) = some ci := by rw [hfind, decFound, if_neg hf0, hci]
  obtain ⟨kk, hkk, hcase⟩ := decCI_ind_cases hci
  have hkr := erec_nat (w := r2.tail.headD 0) (c := 0) (by simpa using hkk) (by decide)
  rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
  have hkind : kk = 3 := by
    have : rdW (m.arr64 EREC) (r2.tail.headD 0) = 3 := by simpa using hk3
    rw [hkr.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; exact hkr.2)] at this
  obtain ⟨-, cv, caps, rfl, -⟩ := hcase.resolve_right (fun ⟨hne, _⟩ => hne hkind)
  have hcvP := decCI_ind_cv hci
  have hcvA : decCV (erA m) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hcvP
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hcvA
  have hqE := (Array.getElem?_eq_some_iff.mp hw2).1
  have hE64 := hS.2.2.2.2.1
  have e1 : rdW (m.arr64 EREC) (r2.tail.headD 0 + 2) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE ⊢; omega) hw1
  have e2 : rdW (m.arr64 EREC) (r2.tail.headD 0 + 3) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE ⊢; omega) hw2
  rw [e1, e2] at h
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  cases h3 : erToIwW N m w1 w2 with
  | none => rw [h3] at h; simp [toiK2] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, toiK2_some] at h
  obtain ⟨-, hr3t, hdec3, hS3, hg3, -⟩ := L.Arena.erToIwW_stage h3 hS hsrc
  rw [hr3t] at h
  have hdecL : decHL m3 (r3.headD 0).toNat w2.toNat = some cv.levelParams := by rw [hdec3]; exact hsl
  have hcv3 : decCV (erA m3) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt hg3) hcvP
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hcv3
  have hqE3 := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE364 := hS3.2.2.2.2.1
  have et : rdW (m3.arr64 EREC) (r2.tail.headD 0 + 4) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE3 ⊢; omega) hwt
  rw [et] at h
  cases h4 : cR N "inst_lp_fast" [CWF, r3.headD 0, w2, us, wt] m3 with
  | none => rw [h4] at h; simp [toiK3] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, toiK3_some] at h
  obtain ⟨x4, a4, hrun4, ⟨hS4, hg4, hx4⟩, -, hA4⟩ := hIl N CWF (r3.headD 0) w2 us wt cv.levelParams m3 m4 a r4
    hu hwtH ⟨rfl, erToIwW_iwFr h3⟩ hS3 hdecL h4
  rw [CWF_eq, ← hwtE] at hrun4
  have hg34 := (hg3.trans hg4)
  cases h5 : instW N m4 dso dsl (r4.headD 0) with
  | none => rw [h5] at h; simp [toiK4] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, toiK4_some] at h
  obtain ⟨hx4H, rfl⟩ := hx4
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5⟩ := instW_okB h5 hS4 hx4H
    (DecB.grow (OMono.decHL _ _) hg34 hds) hb
  by_cases hok : r5.headD 0 = 0
  · rw [if_pos hok] at h; cases h
  rw [if_neg hok] at h
  cases x5 with
  | none => simp only [decOE] at hx5; exact absurd hx5 hok
  | some ty =>
  obtain ⟨-, hty⟩ := hx5
  cases h6 : piBW N m5 CWF (r5.tail.headD 0) with
  | none => rw [h6] at h; simp [toiK5] at h
  | some rm6 =>
  obtain ⟨r6, m6⟩ := rm6
  rw [h6, toiK5_some] at h
  obtain ⟨bs, e, hrun6, hdec6, hb6, he6, hS6, hg6, -⟩ := piBW_cwf h6 hS5 hty.1
  rw [hty.2] at hrun6
  by_cases hne : eViewW m6 (r6.tail.tail.headD 0) = []
  · rw [if_pos hne] at h; cases h
  rw [if_neg hne] at h
  by_cases hs2 : (eViewW m6 (r6.tail.tail.headD 0)).headD 0 ≠ 2
  · rw [if_pos hs2] at h; cases h
  rw [if_neg hs2] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨v, hv, hvr⟩ := eViewW_ok m6 a5 hS6.1.arena.1 _ hne
  rw [getD_two] at he6
  rw [he6] at hv
  have h2' : (eViewW m6 (r6.tail.tail.headD 0)).headD 0 = 2 := by simpa using hs2
  cases v
  case sort u =>
    obtain ⟨-, hu1, hu2⟩ := hvr
    rw [getD_one] at hu1 hu2
    refine ⟨(bs.length, u), a5, ?_, hS6, hg34.trans (hg5.trans hg6), ⟨rfl, ?_, hu1, hu2⟩,
      fun hT => (((AFr.iw (erToIwW_iwFr h3)).trans hA4).trans (instW_afr _ _ _ _ _ _ _ h5)).trans
        (hT _ _ _ _ _ _ h6)⟩
    · simp only [ConRon.Arena.targetOutsideInst, hfci, StateT.run_bind, hrun4, exc_ok_bind', hrun5,
        hrun6, view_run _ _ _ hv]
      rfl
    · simp only [List.headD_cons]
      rw [getD_one] at hdec6
      exact (decHL_length _ hdec6).symm
  all_goals (exfalso; revert hvr; simp only [ViewR, h2']; simp)

/-- **`target_outside_inst` refines `targetOutsideInst`** (through the stub `inst_lp_fast`). -/
@[refines ConRon.Arena.targetOutsideInst]
theorem targetOutsideInst_refines (p : Prog) (hp : ToiProg p) (N : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (I us dso dsl : Word) (ds : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hI : H I) (hu : H us)
    (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) s₀.mem ds) (hb : dso.toNat + dsl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_outside_inst" [vis, I, us, dso, dsl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      ToiR r (AM.res (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds) a₀); ⊤⦄ := by
  refine triple_post (targetOutsideInst_spec p hp stubCall (stubCall_spec p) N s₀ vis I us dso dsl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hd, -⟩ := toiW_ok IlpRd.stub hm hS hI hu hds hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd⟩

end L.Ind
