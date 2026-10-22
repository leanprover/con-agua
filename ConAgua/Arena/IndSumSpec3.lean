import ConAgua.Arena.IndSumSpec2
import ConAgua.Arena.IndPos2Spec

/-!
# Refinements of `IndSum`, third file (lane `indproofs`)

Functions of `IndSum.lean` that call into `IndPos` (`close_telescope`, helper `pos`'s
`IndPos2Spec.lean`): `check_sum_tele_slow`, `check_sum_tele`.
-/

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
      lo + ll ≤ erTop m) {cv : IConstantVal} (h : decCVp m cq = some cv) :
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
def ctsK4 (vis s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m4) => ctsK5 q s (stubM "check_constant_val" m4 [vis, q])
/-- After `close_telescope`. -/
def ctsK3 (vis cv s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m3) => ctsK4 vis s (cvNewW m3 (rdW (m3.arr64 EREC) cv) (rdW (m3.arr64 EREC) (cv + 1))
      (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0))
/-- After `intern_sort`. -/
def ctsK2 (k : Nat) (vis cv bo bl s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ss, m2) => if 4294967296 ≤ ss then none else ctsK3 vis cv s (closeW k m2 bo bl 0 ss)
/-- After `whnf_telescope`. -/
def ctsK1 (k : Nat) (vis cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ctsK2 k vis cv (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0)
      (sointernW m1 (r1.tail.tail.headD 0))
/-- **The model of `check_sum_tele_slow`.** -/
def ctsW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, cv, n, cvTa0 => ctsK1 k vis cv (wtW k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3)))

section arms
variable (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis cv n cvTa0 bo bl s ss q : Word) (r1 rt r5 : List Word)
theorem ctsW_succ : ctsW (k + 1) m vis cv n cvTa0 =
    ctsK1 k vis cv (wtW k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3))) := rfl
theorem ctsK1_some : ctsK1 k vis cv (some (r1, m1)) = ctsK2 k vis cv (r1.headD 0) (r1.tail.headD 0)
    (r1.tail.tail.headD 0) (sointernW m1 (r1.tail.tail.headD 0)) := rfl
theorem ctsK2_big (h : 4294967296 ≤ ss) : ctsK2 k vis cv bo bl s (some (ss, m2)) = none := by
  simp [ctsK2, h]
theorem ctsK2_ok (h : ¬ 4294967296 ≤ ss) : ctsK2 k vis cv bo bl s (some (ss, m2)) =
    ctsK3 vis cv s (closeW k m2 bo bl 0 ss) := by simp only [ctsK2, if_neg h]
theorem ctsK3_some : ctsK3 vis cv s (some (rt, m3)) = ctsK4 vis s (cvNewW m3 (rdW (m3.arr64 EREC) cv)
    (rdW (m3.arr64 EREC) (cv + 1)) (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0)) := rfl
theorem ctsK4_some : ctsK4 vis s (some (q, m4)) = ctsK5 q s (stubM "check_constant_val" m4 [vis, q]) := rfl
theorem ctsK5_some : ctsK5 q s (some (r5, m5)) = some ([q, s], m5) := rfl
end arms

grind_pattern [ind_grind] ctsW_succ => ctsW (k + 1) m vis cv n cvTa0
grind_pattern [ind_grind] ctsK1_some => ctsK1 k vis cv (some (r1, m1))
grind_pattern [ind_grind] ctsK2_big => ctsK2 k vis cv bo bl s (some (ss, m2))
grind_pattern [ind_grind] ctsK2_ok => ctsK2 k vis cv bo bl s (some (ss, m2))
grind_pattern [ind_grind] ctsK3_some => ctsK3 vis cv s (some (rt, m3))
grind_pattern [ind_grind] ctsK4_some => ctsK4 vis s (some (q, m4))
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
  (hp : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hp

theorem ctsW_spec (k : Nat) (s₀ : St) (vis cv n cvTa0 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele_slow" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ ctsW k s₀.mem vis cv n cvTa0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkSumTeleSlowL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        wtW_spec p ha hc hsc hv hff hfp hif hwt k, internSort_spec p hsf hsp his k,
        closeTelescope_spec p hd hpf hpp hpi hmk hct k, cvNew_specW p hea hcn k,
        stubM_spec p "check_constant_val" k] <;>
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

theorem ctsW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (cv n cvTa0 : Word) (r : List Word) (cvv cvTa : IConstantVal)
    (h : ctsW k m vis cv n cvTa0 = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m) :
    ∃ res a', (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some res.1 ∧
      (r.headD 0).toNat + 4 ≤ erTop m' ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = res.2 := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  cases k with
  | zero => cases h
  | succ k =>
  rw [ctsW_succ] at h
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at h
  cases h1 : wtW k m vis 0 n w with
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
  · rw [ctsK2_big k m2 vis cv _ _ _ ss hss] at h; cases h
  rw [ctsK2_ok k m2 vis cv _ _ _ ss hss] at h
  have hss32 : ss.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ ss.toNat := hss; omega
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internSort_stage hS1 _ hs32 h2
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    obtain ⟨hI, -, hsz1, -⟩ := hS1.2; simp only [iwTop] at hI ht1 ⊢; omega
  cases h3 : closeW k m2 (r1.headD 0) (r1.tail.headD 0) 0 ss with
  | none => rw [h3] at h; cases h
  | some x3 =>
  obtain ⟨rt, m3⟩ := x3
  rw [h3, ctsK3_some] at h
  obtain ⟨ty, a3, hrun3, hS3, hg3, hty32, htyd⟩ := closeW_ok k dn fe vis m2 m3 a2 _ _ 0 ss bs rt h3 hS2
    hss32 (by rw [decHL_grow hg2 ht1]; exact hd1) hb1 (by have := hg2.1; omega)
    (by rw [show (0 : Word).toNat = 0 from rfl]; omega)
  have hg13 := (hg1.trans hg2).trans hg3
  cases h4 : cvNewW m3 (rdW (m3.arr64 EREC) cv) (rdW (m3.arr64 EREC) (cv + 1))
      (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0) with
  | none => rw [h4] at h; cases h
  | some x4 =>
  obtain ⟨q, m4⟩ := x4
  rw [h4, ctsK4_some] at h
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
  refine ⟨({ cvv with type := ty }, s), a5, ?_, hS5, hg15, ?_, ?_, by simpa using hs32, by simpa using hs⟩
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
  (hp : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hp

/-- **`check_sum_tele_slow` refines `checkSumTele.checkSumTeleSlow .verified`** (through the stubs
`whnf`, `instantiate1_fast`, `abstract1_fast`, `check_constant_val`): the new constant value is a
record in `EREC`. -/
@[refines ConRon.Arena.checkSumTele.checkSumTeleSlow]
theorem checkSumTeleSlow_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (cv n cvTa0 : Word) (cvv cvTa : IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hcv : decCVp s₀.mem cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop s₀.mem)
    (hsl : ∀ lo ll, nat? (erA s₀.mem) (cv.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cv.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele_slow" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decCVp s'.mem (r.headD 0).toNat =
        some (AM.res (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀).1 ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = (AM.res (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀).2; ⊤⦄ := by
  refine triple_post (ctsW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct
    hea hcn hp k s₀ vis cv n cvTa0) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hdec, -, hs32, hs⟩ :=
    ctsW_ok dn vis fe k _ _ _ _ _ _ _ _ _ hm hS hcv hcvb hsl hta hta4
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hs32, by rw [hres]; exact hs⟩

end census

end L.Ind
