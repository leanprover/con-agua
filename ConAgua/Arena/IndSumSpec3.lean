import ConAgua.Arena.IndSumSpec2
import ConAgua.Arena.IndPos2Spec

/-!
# Refinements of `IndSum`, third file (lane `indproofs`)

Functions of `IndSum.lean` that call into `IndPos` (`close_telescope`, helper `pos`'s
`IndPos2Spec.lean`): `check_sum_tele_slow`, `check_sum_tele`.
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constant values read from `EREC` below its top -/

theorem decCVp_grow {m m' : Mem} (hg : IWGrow m m') {cq : Nat} (hcq : cq + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cq + 1) = some lo → nat? (erA m) (cq + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0) {cv : IConstantVal} (h : decCVp m cq = some cv) :
    decCVp m' cq = some cv := by
  have e : ∀ i, i < erTop m → (erA m')[i]? = (erA m)[i]? := fun i hi => hg.2.2.2 i hi
  simp only [decCVp] at h ⊢
  simp only [decCV, bind, Option.bind, pure, hlist?] at h ⊢
  have e0 : (hd? (erA m') cq : Option NIdx) = hd? (erA m) cq := by simp only [hd?, e cq (by omega)]
  have e1 : nat? (erA m') (cq + 1) = nat? (erA m) (cq + 1) := by simp only [nat?, e (cq + 1) (by omega)]
  have e2 : nat? (erA m') (cq + 1 + 1) = nat? (erA m) (cq + 1 + 1) := by
    simp only [nat?, e (cq + 1 + 1) (by omega)]
  have e3 : (hd? (erA m') (cq + 3) : Option EIdx) = hd? (erA m) (cq + 3) := by
    simp only [hd?, e (cq + 3) (by omega)]
  rw [e0, e1, e2, e3]
  cases h1 : nat? (erA m) (cq + 1) with
  | none => rw [h1] at h; revert h; cases (hd? (erA m) cq : Option NIdx) <;> simp
  | some lo =>
  cases h2 : nat? (erA m) (cq + 1 + 1) with
  | none => rw [h1, h2] at h; revert h; cases (hd? (erA m) cq : Option NIdx) <;> simp
  | some ll =>
  have hN := hsl lo ll h1 (by simpa using h2)
  have hs : (hslice? (erA m') lo ll : Option (List NIdx)) = hslice? (erA m) lo ll := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      simp only [hd?, e (lo + j) (by omega)])
  rw [h1, h2] at h
  simp only [hs]
  exact h

/-! ## `check_sum_tele_slow` -/

/-- After `check_constant_val`. -/
def ctsK5 (q s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([q, s], m5)
/-- After `cv_new`. -/
def ctsK4 (cR : CallM) (k : Nat) (vis s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m4) => ctsK5 q s (cR k "check_constant_val" [vis, q] m4)
/-- After `close_telescope`. -/
def ctsK3 (cR : CallM) (k : Nat) (vis cv s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m3) => ctsK4 cR k vis s (cvNewW m3 (rdW (m3.arr64 EREC) cv) (rdW (m3.arr64 EREC) (cv + 1))
      (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0))
/-- After `intern_sort`. -/
def ctsK2 (cR : CallM) (k : Nat) (vis cv bo bl s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ss, m2) => if 4294967296 ≤ ss then none else ctsK3 cR k vis cv s (closeW k m2 bo bl 0 ss)
/-- After `whnf_telescope`. -/
def ctsK1 (cR : CallM) (k : Nat) (vis cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ctsK2 cR k vis cv (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0)
      (sointernW m1 (r1.tail.tail.headD 0))
/-- **The model of `check_sum_tele_slow`.** -/
def ctsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, cv, n, cvTa0 => ctsK1 cR k vis cv (wtW cR k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3)))

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis cv n cvTa0 bo bl s ss q : Word) (r1 rt r5 : List Word)
theorem ctsW_succ : ctsW cR (k + 1) m vis cv n cvTa0 =
    ctsK1 cR k vis cv (wtW cR k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3))) := rfl
theorem ctsK1_some : ctsK1 cR k vis cv (some (r1, m1)) = ctsK2 cR k vis cv (r1.headD 0) (r1.tail.headD 0)
    (r1.tail.tail.headD 0) (sointernW m1 (r1.tail.tail.headD 0)) := rfl
theorem ctsK2_big (h : 4294967296 ≤ ss) : ctsK2 cR k vis cv bo bl s (some (ss, m2)) = none := by
  simp [ctsK2, h]
theorem ctsK2_ok (h : ¬ 4294967296 ≤ ss) : ctsK2 cR k vis cv bo bl s (some (ss, m2)) =
    ctsK3 cR k vis cv s (closeW k m2 bo bl 0 ss) := by simp only [ctsK2, if_neg h]
theorem ctsK3_some : ctsK3 cR k vis cv s (some (rt, m3)) = ctsK4 cR k vis s (cvNewW m3 (rdW (m3.arr64 EREC) cv)
    (rdW (m3.arr64 EREC) (cv + 1)) (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0)) := rfl
theorem ctsK4_some : ctsK4 cR k vis s (some (q, m4)) = ctsK5 q s (cR k "check_constant_val" [vis, q] m4) := rfl
theorem ctsK5_some : ctsK5 q s (some (r5, m5)) = some ([q, s], m5) := rfl
end arms

grind_pattern [ind_grind] ctsW_succ => ctsW cR (k + 1) m vis cv n cvTa0
grind_pattern [ind_grind] ctsK1_some => ctsK1 cR k vis cv (some (r1, m1))
grind_pattern [ind_grind] ctsK2_big => ctsK2 cR k vis cv bo bl s (some (ss, m2))
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

/-- A record's handle field, as the word L reads. -/
theorem hd?_rdW {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x)
    (hi : i < 2 ^ 64) : ∃ w, rdW a (UInt64.ofNat i) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  simp only [hd?] at h
  cases hw : a[i]? with
  | none => simp [hw] at h
  | some w =>
    simp only [hw] at h
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at h
      have hiw : (UInt64.ofNat i).toNat = i := by simp; omega
      exact ⟨w, by simp [rdW, hiw, hw], hl, h⟩
    · simp [hl] at h

/-- `whnf_telescope` keeps the `abstract1` memo. -/
theorem wtW_afr : ∀ (k : Nat) (m m' : Mem) (vis i n e : Word) (r : List Word),
    wtW stubCall k m vis i n e = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [wtW] at h
  | k + 1, m, m', vis, i, n, e, r, h => by
    simp only [wtW, stubCall, wtK1.eq_def, wtK2, wtK3.eq_def, wtK4.eq_def, wtK5.eq_def, wtK6.eq_def] at h
    afr_auto h [stub_afr, fvinternW_afr, i1F_afr, wtW_afr k _ _ _ _ _ _ _, consW_afr]

theorem ctsW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (cv n cvTa0 : Word) (r : List Word) (cvv cvTa : IConstantVal)
    (h : ctsW stubCall k m vis cv n cvTa0 = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m) (hA : AbsOK m) :
    ∃ res a', (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some res.1 ∧
      (r.headD 0).toNat + 4 ≤ erTop m' ∧
      (∀ lo ll, nat? (erA m') ((r.headD 0).toNat + 1) = some lo →
        nat? (erA m') ((r.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop m' ∨ ll = 0) ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = res.2 ∧ AbsOK m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  cases k with
  | zero => cases h
  | succ k =>
  rw [ctsW_succ stubCall] at h
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at h
  cases h1 : wtW stubCall k m vis 0 n w with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, ctsK1_some] at h
  obtain ⟨bs, s, a1, hrun1, hS1, hg1, hd1, ht1, hs32, hs⟩ :=
    wtW_ok dn fe k m m1 a vis 0 n w r1 h1 hS hw32 (by simpa using n.toNat_lt)
  cases h2 : sointernW m1 (r1.tail.tail.headD 0) with
  | none => rw [h2] at h; cases h
  | some x2 =>
  obtain ⟨ss, m2⟩ := x2
  rw [h2] at h
  by_cases hss : 4294967296 ≤ ss
  · rw [ctsK2_big _ k m2 vis cv _ _ _ ss hss] at h; cases h
  rw [ctsK2_ok _ k m2 vis cv _ _ _ ss hss] at h
  have hss32 : ss.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ ss.toNat := hss; omega
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internSort_stage hS1 _ hs32 h2
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    obtain ⟨hI, -, hsz1, -⟩ := hS1.2; simp only [iwTop] at hI ht1 ⊢; omega
  cases h3 : closeW k m2 (r1.headD 0) (r1.tail.headD 0) 0 ss with
  | none => rw [h3] at h; cases h
  | some x3 =>
  obtain ⟨rt, m3⟩ := x3
  rw [h3, ctsK3_some] at h
  obtain ⟨ty, a3, hrun3, hS3, hg3, ⟨hty32, htyd⟩, hA3⟩ := closeW_ok k dn fe vis m2 m3 a2 _ _ 0 ss bs rt h3 hS2
    hss32 (by rw [decHL_grow hg2 ht1]; exact hd1) hb1 (by have := hg2.1; omega)
    (by rw [show (0 : Word).toNat = 0 from rfl]; omega) (sointernW_afr h2 (wtW_afr _ _ _ _ _ _ _ _ h1 hA))
  have hg13 := (hg1.trans hg2).trans hg3
  cases h4 : cvNewW m3 (rdW (m3.arr64 EREC) cv) (rdW (m3.arr64 EREC) (cv + 1))
      (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0) with
  | none => rw [h4] at h; cases h
  | some x4 =>
  obtain ⟨q, m4⟩ := x4
  rw [h4, ctsK4_some] at h
  simp only [stubCall] at h
  have hnat : ∀ j, j < 4 → nat? (erA m3) (cv.toNat + j) = nat? (erA m) (cv.toNat + j) := fun j hj => by
    simp only [nat?, erA]; rw [hg13.2.2.2 _ (by omega)]
  obtain ⟨hS4, hg4, hq, htop4, hsl4, hdq⟩ := cvNew_stage h4 hS3 (decCVp_grow hg13 hcvb hsl hcv)
    (by have := hg13.2.1; omega)
    (fun lo ll e1 e2 => by
      rw [show cv.toNat + 1 = cv.toNat + 1 from rfl, hnat 1 (by decide)] at e1
      rw [hnat 2 (by decide)] at e2
      have := hsl lo ll e1 e2; have := hg13.2.1; omega)
    hty32
  cases h5 : stubM "check_constant_val" m4 [vis, q] with
  | none => rw [h5] at h; cases h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5, ctsK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨u, a5, hrun5, hS5, hg5, -⟩ :=
    checkConstantVal_spec dn vis fe q { cvv with type := decI (rt.headD 0) } m4 m5 a3 r5 h5 ⟨hS4, hdq⟩
  have hg15 := (hg13.trans hg4).trans hg5
  refine ⟨({ cvv with type := ty }, s), a5, ?_, hS5, hg15, ?_, ?_, ?_, by simpa using hs32, by simpa using hs,
    stub_afr h5 (by decide) (cvNewW_afr h4 hA3)⟩
  · rw [show (0 : Word).toNat = 0 from rfl] at hrun1 hrun3
    simp only [checkSumTele.checkSumTeleSlow, StateT.run_bind]
    rw [← hwd, hrun1]
    simp only [bind, Except.bind, StateT.run_bind]
    rw [hs] at hrun2
    rw [hrun2]
    simp only [bind, Except.bind]
    rw [← decE_eq] at hrun3
    rw [hrun3]
    simp only [bind, Except.bind, StateT.run_bind]
    rw [← htyd]
    rw [hrun5]
    rfl
  · simp only [List.headD]
    rw [decCVp_grow hg5 (by omega) (fun lo ll e1 e2 => by have := hsl4 lo ll e1 e2; omega) hdq, htyd]
  · simp only [List.headD]; have := hg5.2.1; omega
  · intro lo ll e1 e2
    simp only [List.headD] at e1 e2
    have hn : ∀ j, j < 4 → nat? (erA m5) (q.toNat + j) = nat? (erA m4) (q.toNat + j) := fun j hj => by
      simp only [nat?, erA]; rw [hg5.2.2.2 _ (by omega)]
    rw [hn 1 (by decide)] at e1; rw [hn 2 (by decide)] at e2
    have := hsl4 lo ll e1 e2; have := hg4.2.1; have := hg5.2.1; omega

section census
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

/-- **`check_sum_tele_slow` refines `checkSumTele.checkSumTeleSlow .verified`** (through the stubs
`whnf`, `instantiate1_fast`, `abstract1_fast`, `check_constant_val`): the new constant value is a
record in `EREC`. Under `StageR`; the census link is `checkSumTeleSlow_refinesC` (`IndT/Sum2.lean`). -/
theorem checkSumTeleSlow_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (cv n cvTa0 : Word) (cvv cvTa : IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hcv : decCVp s₀.mem cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop s₀.mem)
    (hsl : ∀ lo ll, nat? (erA s₀.mem) (cv.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cv.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop s₀.mem)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele_slow" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decCVp s'.mem (r.headD 0).toNat =
        some (AM.res (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀).1 ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = (AM.res (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀).2 ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (ctsW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct
    hea hcn hp hi1 hab stubCall (stubCall_spec p) k s₀ vis cv n cvTa0) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hdec, -, -, hs32, hs, hA'⟩ :=
    ctsW_ok dn vis fe k _ _ _ _ _ _ _ _ _ hm hS hcv hcvb hsl hta hta4 hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hs32, by rw [hres]; exact hs, hA'⟩

end census

/-! ## `check_sum_tele` -/

theorem getSort_of_get (t : ETables) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : t.get i = some (.sort u)) : t.getSort i = some u := by
  unfold ETables.get at h
  rw [ht] at h
  simp only [show (ETag.sort == ETag.bvar) = false by decide,
    show (ETag.sort == ETag.fvar) = false by decide, show (ETag.sort == ETag.sort) = true by decide,
    ite_true, ite_false, Bool.false_eq_true] at h
  unfold ETables.getSort
  cases e : t.sorts.node? i.idxNat with
  | none => rw [e] at h; cases h
  | some r => rw [e] at h; simp at h; simp [h]

theorem viewSort_of_view (st : EStore) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : st.view i = some (.sort u)) : st.viewSort i = some u := by
  unfold EStore.view at h; unfold EStore.viewSort EStore.persGetSort
  split at h
  · rw [if_pos (by assumption)]; exact getSort_of_get _ _ _ ht h
  · rw [if_neg (by assumption)]
    split at h
    · rw [if_pos (by assumption)]; exact getSort_of_get _ _ _ ht h
    · cases h

theorem eViewW_head2 (m : Mem) (h : Word) (hg : h >>> 28 = 2) (hne : eViewW m h ≠ []) :
    (eViewW m h).headD 0 = 2 := by
  revert hne; unfold eViewW
  simp only [hg, show ((2 : Word) = 0) = False from by decide, show ((2 : Word) = 1) = False from by decide,
    if_false, if_true]
  repeat' split
  all_goals simp

theorem viewSort_run {a : AState} {h : EIdx} {u : Option LIdx} (hv : a.store.viewSort h = u) :
    (viewSort h).run a = .ok (u, a) := by
  simp [viewSort, hv, StateT.run_bind, StateT.run_get]; rfl

/-- After the slow arm. -/
def ctK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.tail.headD 0], m2)
/-- After `strip_pis`: the syntactic sort, or the slow arm. -/
def ctK1 (cR : CallM) (k : Nat) (vis cv n cvTa0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2 then
      if eViewW m1 (r1.tail.tail.tail.headD 0) = [] then none
      else some ([cvTa0, (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0], m1)
    else ctK2 (ctsW cR k m1 vis cv n cvTa0)
/-- **The model of `check_sum_tele`.** -/
def ctW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, cv, n, cvTa0 =>
    ctK1 cR k vis cv n cvTa0 (stripF 6 m [n, rdW (m.arr64 EREC) (cvTa0 + 3)])

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 : Mem) (vis cv n cvTa0 : Word) (r r1 : List Word)
theorem ctW_succ : ctW cR (k + 1) m vis cv n cvTa0 =
    ctK1 cR k vis cv n cvTa0 (stripF 6 m [n, rdW (m.arr64 EREC) (cvTa0 + 3)]) := rfl
theorem ctK1_fast (h : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2)
    (hne : eViewW m1 (r1.tail.tail.tail.headD 0) ≠ []) : ctK1 cR k vis cv n cvTa0 (some (r1, m1)) =
      some ([cvTa0, (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0], m1) := by
  simp only [ctK1, if_pos h, if_neg hne]
theorem ctK1_fast0 (h : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2)
    (hne : eViewW m1 (r1.tail.tail.tail.headD 0) = []) : ctK1 cR k vis cv n cvTa0 (some (r1, m1)) = none := by
  simp only [ctK1, if_pos h, if_pos hne]
theorem ctK1_slow (h : ¬ (r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2)) :
    ctK1 cR k vis cv n cvTa0 (some (r1, m1)) = ctK2 (ctsW cR k m1 vis cv n cvTa0) := by
  simp only [ctK1, if_neg h]
theorem ctK2_some : ctK2 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] ctW_succ => ctW cR (k + 1) m vis cv n cvTa0
grind_pattern [ind_grind] ctK1_fast => ctK1 cR k vis cv n cvTa0 (some (r1, m1))
grind_pattern [ind_grind] ctK1_fast0 => ctK1 cR k vis cv n cvTa0 (some (r1, m1))
grind_pattern [ind_grind] ctK1_slow => ctK1 cR k vis cv n cvTa0 (some (r1, m1))
grind_pattern [ind_grind] ctK2_some => ctK2 (some (r, m2))

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
  (hsl : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL)
  (hp : p.lookup "check_sum_tele" = some checkSumTeleL) (hst : StripProg p) (hi1 : I1Prog p) (hab : AbF p)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hp hst hi1 hab

theorem ctW_spec (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St) (vis cv n cvTa0 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ ctW cR k s₀.mem vis cv n cvTa0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkSumTeleL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stripPis_specF p hst k, eView_spec p hv k,
        ctsW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hi1 hab cR hcR k] <;>
      finish (gen := 20)

end spec

theorem tag_sort_iff (b : Word) (hb : b.toNat < 2 ^ 32) :
    (decE b).tag = ETag.sort ↔ b >>> 28 = 2 := by
  rw [decE_tag b hb]
  have hlt : (b >>> 28).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]; simp; omega
  constructor
  · intro h
    apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat h
    simp [ETag.sort] at this
    simp only [UInt64.toNat_shiftRight] at hlt ⊢
    simp; omega
  · intro h; rw [h]; rfl

theorem ctW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (cv n cvTa0 : Word) (r : List Word) (cvv cvTa : IConstantVal)
    (h : ctW stubCall k m vis cv n cvTa0 = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m)
    (hslTa : ∀ lo ll, nat? (erA m) (cvTa0.toNat + 1) = some lo →
      nat? (erA m) (cvTa0.toNat + 2) = some ll → lo + ll ≤ erTop m ∨ ll = 0) (hA : AbsOK m) :
    ∃ res a', (checkSumTele V fe cvv n.toNat cvTa).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some res.1 ∧
      (r.headD 0).toNat + 4 ≤ erTop m' ∧
      (∀ lo ll, nat? (erA m') ((r.headD 0).toNat + 1) = some lo →
        nat? (erA m') ((r.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop m' ∨ ll = 0) ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = res.2 ∧ AbsOK m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  cases k with
  | zero => cases h
  | succ k =>
  rw [ctW_succ stubCall] at h
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at h
  cases h1 : stripF 6 m [n, w] with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec⟩ := stripF_pis_ok dn vis fe n w hw32 m m1 a r1 h1 hS
  have hA1 := stripF_afr h1 hA
  have hcv1 := decCVp_grow hg1 hcvb hsl hcv
  have hta1 := decCVp_grow hg1 hta4 hslTa hta
  have hnat : ∀ q : Word, q.toNat + 4 ≤ erTop m → ∀ j, j < 4 →
      nat? (erA m1) (q.toNat + j) = nat? (erA m) (q.toNat + j) := fun q hq j hj => by
    simp only [nat?, erA]; rw [hg1.2.2.2 _ (by omega)]
  have hrun0 : ∀ {β : Type} (f : Option (List EIdx × EIdx) → AM β),
      (stripPis n.toNat cvTa.type >>= f).run a = (f x).run a1 := by
    intro β f; rw [StateT.run_bind, ← hwd, hrun1]; rfl
  by_cases hf : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2
  · cases x with
    | none => simp only [decOLE] at hdec; rw [hf.1] at hdec; cases hdec
    | some le =>
    obtain ⟨l, e⟩ := le
    simp only [decOLE, decW0E] at hdec
    obtain ⟨-, -, hb32, hbe⟩ := hdec
    rw [drop3_eq] at hb32 hbe
    by_cases hne : eViewW m1 (r1.tail.tail.tail.headD 0) = []
    · rw [ctK1_fast0 stubCall k m1 vis cv n cvTa0 r1 hf hne] at h; cases h
    rw [ctK1_fast stubCall k m1 vis cv n cvTa0 r1 hf hne] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 _ hne
    have h2 := eViewW_head2 m1 _ hf.2 hne
    have htag : (decE (r1.tail.tail.tail.headD 0)).tag = ETag.sort :=
      (tag_sort_iff _ (by simpa using hb32)).mpr hf.2
    cases vv with
    | sort u =>
      obtain ⟨-, hu32, hu⟩ := hVR
      have hvs := viewSort_of_view _ _ _ htag hview
      have hx1 : (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0 =
          (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0 := by
        cases eViewW m1 (r1.tail.tail.tail.headD 0) with
        | nil => rfl
        | cons _ t => cases t <;> rfl
      refine ⟨(cvTa, u), a1, ?_, hS1, hg1, by simpa using hta1, by simp only [List.headD]; have := hg1.2.1; omega,
        fun lo ll e1 e2 => by
          simp only [List.headD] at e1 e2
          rw [hnat cvTa0 hta4 1 (by decide)] at e1; rw [hnat cvTa0 hta4 2 (by decide)] at e2
          have := hslTa lo ll e1 e2; have := hg1.2.1; omega,
        by simpa [hx1] using hu32, by simpa [hx1] using hu, hA1⟩
      simp only [checkSumTele]
      rw [hrun0]
      simp only []
      rw [← hbe, ← decE_eq, htag]
      simp only [beq_self_eq_true, ite_true, StateT.run_bind]
      rw [viewSort_run hvs]
      rfl
    | _ => simp only [ViewR] at hVR <;> (rw [h2] at hVR) <;> simp at hVR
  · rw [ctK1_slow stubCall k m1 vis cv n cvTa0 r1 hf] at h
    cases h2 : ctsW stubCall k m1 vis cv n cvTa0 with
    | none => rw [h2] at h; cases h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, ctK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨res, a2, hrun2, hS2, hg2, hdec2, hb2, hsl2, hs32, hs, hA2⟩ := ctsW_ok dn vis fe k m1 m2 a1 cv n cvTa0 r2
      cvv cvTa h2 hS1 hcv1 (by have := hg1.2.1; omega)
      (fun lo ll e1 e2 => by
        rw [hnat cv hcvb 1 (by decide)] at e1; rw [hnat cv hcvb 2 (by decide)] at e2
        have := hsl lo ll e1 e2; have := hg1.2.1; omega)
      hta1 (by have := hg1.2.1; omega) hA1
    refine ⟨res, a2, ?_, hS2, hg1.trans hg2, by simpa using hdec2, by simpa using hb2, by simpa using hsl2,
      by simpa using hs32, by simpa using hs, hA2⟩
    simp only [checkSumTele]
    rw [hrun0]
    cases x with
    | none => exact hrun2
    | some le =>
      obtain ⟨l, e⟩ := le
      simp only [decOLE, decW0E] at hdec
      obtain ⟨h1', -, hb32, hbe⟩ := hdec
      rw [drop3_eq] at hb32 hbe
      have hnt : ¬ (e.tag == ETag.sort) = true := by
        rw [← hbe, ← decE_eq]
        intro ht
        exact hf ⟨h1', (tag_sort_iff _ (by simpa using hb32)).mp (by simpa using ht)⟩
      simp only [hnt, if_false]
      simp only [Bool.false_eq_true, ite_false]
      exact hrun2

section census2
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
  (hsl : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL)
  (hp : p.lookup "check_sum_tele" = some checkSumTeleL) (hst : StripProg p) (hi1 : I1Prog p) (hab : AbF p)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hp hst hi1 hab

/-- **`check_sum_tele` refines `checkSumTele .verified`** (through the stubs `strip_pis`, `whnf`,
`instantiate1_fast`, `abstract1_fast`, `check_constant_val`). Under `StageR`; the census link is
`checkSumTele_refinesC` (`IndT/Sum2.lean`). -/
theorem checkSumTele_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (cv n cvTa0 : Word) (cvv cvTa : IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hcv : decCVp s₀.mem cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop s₀.mem)
    (hsl' : ∀ lo ll, nat? (erA s₀.mem) (cv.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cv.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop s₀.mem)
    (hslTa : ∀ lo ll, nat? (erA s₀.mem) (cvTa0.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cvTa0.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkSumTele V fe cvv n.toNat cvTa) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (checkSumTele V fe cvv n.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decCVp s'.mem (r.headD 0).toNat = some (AM.res (checkSumTele V fe cvv n.toNat cvTa) a₀).1 ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = (AM.res (checkSumTele V fe cvv n.toNat cvTa) a₀).2 ∧
      (r.headD 0).toNat + 4 ≤ erTop s'.mem ∧
      (∀ lo ll, nat? (erA s'.mem) ((r.headD 0).toNat + 1) = some lo →
        nat? (erA s'.mem) ((r.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop s'.mem ∨ ll = 0) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (ctW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct
    hea hcn hsl hp hst hi1 hab stubCall (stubCall_spec p) k s₀ vis cv n cvTa0) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hdec, hb, hslr, hs32, hs, hA'⟩ :=
    ctW_ok dn vis fe k _ _ _ _ _ _ _ _ _ hm hS hcv hcvb hsl' hta hta4 hslTa hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hs32, by rw [hres]; exact hs,
    hb, hslr, hA'⟩

end census2

end L.Ind
