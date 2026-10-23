import ConAgua.Arena.RecGenSpec3
import ConAgua.Arena.IndSumSpec2C
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.CoreRefine
import ConAgua.Arena.ScratchRefine

/-!
# `RecGen`: `classRuleOk` (lane `indproofs2`, helper `rec`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Shared pieces -/

/-- The stage relation at a smaller view of the same index. -/
theorem StageR.restrict {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn vis fe m a) (k : Word) : StageR dn k (fe.restrictTo k.toNat) m a :=
  ⟨⟨h.1.arena, h.1.core, h.1.pins, h.1.env.restrictTo k⟩, h.2⟩

/-- Back from a smaller view (`fe`'s own view is `vis`). -/
theorem StageR.unrestrict {dn : NIdx → Option ConLeche.Name} {vis k : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn k (fe.restrictTo k.toNat) m a) (hv : fe.visibleBelow = vis.toNat) :
    StageR dn vis fe m a :=
  ⟨⟨h.1.arena, h.1.core, h.1.pins, ⟨hv, h.1.env.keys, h.1.env.vals, h.1.env.consts⟩⟩, h.2⟩

/-- `flush_caches()` under the stage relation. -/
theorem flush_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn vis fe m a) (hok : FlushOK m) :
    StageR dn vis fe (flushMem m) { a with caches := Caches.empty } ∧ IWGrow m (flushMem m) := by
  have hf := flushMem_frame m
  have hC : CheckR dn (flushMem m) { a with caches := Caches.empty } vis fe :=
    ⟨ArenaD.caches_irrel _ ⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ hf _ h.1.arena.1,
      DerR.frameM [] _ _ _ hf (by simp) _ h.1.arena.2⟩,
    h.1.core.flush hok,
    h.1.pins.frame (.of_lt (k := 0) (by simp) (by decide)) hf,
    h.1.env.frame (.of_lt (k := 0) (by simp) (by decide)) (.of_lt flushCtl_lt (by decide)) hf⟩
  have hIW : (flushMem m).arr64 IW = m.arr64 IW := hf.1 IW (by simp) (by decide)
  have hE : (flushMem m).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp) (by decide)
  have h200 : rdW ((flushMem m).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 :=
    hf.2.1 200 (by simp [flushCtl])
  have h129 : rdW ((flushMem m).arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
    hf.2.1 129 (by simp [flushCtl])
  refine ⟨⟨hC, ?_⟩, ?_⟩
  · simp only [IWOK, iwTop, erTop, hIW, hE, h200, h129, hf.2.2.1 CTL]; exact h.2
  · refine ⟨?_, ?_, fun i _ => by rw [hIW], fun i _ => by rw [hE]⟩
    · simp only [iwTop, h200]; exact Nat.le_refl _
    · simp only [erTop, h129]; exact Nat.le_refl _

/-- `cv_lps(q)` under the stage relation: the level parameters, a slice below the top. -/
theorem cvLpsA_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : L.Arena.cvLpsW n m q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erA m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [L.Arena.cvLpsW] at h
  | succ n =>
  rw [L.Arena.cvLpsW_step, e1, e2] at h
  obtain ⟨-, hr4t, hdec4, hS4, hg4, htop4⟩ := L.Arena.erToIwW_stage h hS hsrc
  rw [hr4t]
  exact ⟨hS4, hg4, by rw [hdec4]; exact hsl, htop4⟩

/-! ## `class_rule_ok` -/

def crgK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then none else some ([0], m4)

def crgK3 (visR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 = 0 then none else crgK4 (crfF m3 [visR, gen])

def crgK2 (visR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    crgK3 visR gen (stubM "all_level_params_defined" m2 [r2.headD 0, r2.tail.headD 0, gen])

def crgK1 (N : Nat) (visR cvR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then none else crgK2 visR gen (L.Arena.cvLpsW N m1 cvR)

def crgK0 (N : Nat) (visR cvR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r0, m0) =>
    if r0.headD 0 = 0 then none else crgK1 N visR cvR gen (hffF m0 [CWF, gen])

/-- **The model of `class_rule_ok_guards`.** -/
def crgW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, visR, cvR, gen => crgK0 N visR cvR gen (lbbF m [CWF, 0, gen])

def cruK4 (gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then none else some ([gen], m4)

def cruK3 (N : Nat) (visT gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none
    else cruK4 gen (iarW N m3 visT (r3.tail.headD 0) (r3.tail.tail.headD 0))

open Classical in
noncomputable def cruK2 (N : Nat) (visT n gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) =>
    if FlushOK m2 then cruK3 N visT gen (stripF 5 (flushMem m2) [n, gen]) else none

noncomputable def cruK1 (cR : CallM) (N : Nat) (visT visR n gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => cruK2 N visT n gen (cR N "infer_type_core" [visR, 0, gen] m1)

/-- **The model of `class_rule_ok`.** -/
noncomputable def cruleW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, visT, visR, cvR, n, gen => cruK1 cR N visT visR n gen (crgW N m visR cvR gen)

section arms
variable (cR : CallM) (N : Nat) (m m0 m1 m2 m3 m4 : Mem) (visT visR cvR n gen : Word) (r0 r1 r2 r3 r4 : List Word)
theorem crgW_eq : crgW (N + 1) m visR cvR gen =
    crgK0 N visR cvR gen (lbbF m [CWF, 0, gen]) := rfl
theorem crgK0_some : crgK0 N visR cvR gen (some (r0, m0)) =
    if r0.headD 0 = 0 then none else crgK1 N visR cvR gen (hffF m0 [CWF, gen]) := rfl
theorem crgK1_some : crgK1 N visR cvR gen (some (r1, m1)) =
    if r1.headD 0 ≠ 0 then none else crgK2 visR gen (L.Arena.cvLpsW N m1 cvR) := rfl
theorem crgK2_some : crgK2 visR gen (some (r2, m2)) =
    crgK3 visR gen (stubM "all_level_params_defined" m2 [r2.headD 0, r2.tail.headD 0, gen]) := rfl
theorem crgK3_some : crgK3 visR gen (some (r3, m3)) =
    if r3.headD 0 = 0 then none else crgK4 (crfF m3 [visR, gen]) := rfl
theorem crgK4_some : crgK4 (some (r4, m4)) = if r4.headD 0 = 0 then none else some ([0], m4) := rfl
theorem cruleW_eq : cruleW cR (N + 1) m visT visR cvR n gen =
    cruK1 cR N visT visR n gen (crgW N m visR cvR gen) := rfl
theorem cruK1_some : cruK1 cR N visT visR n gen (some (r1, m1)) =
    cruK2 N visT n gen (cR N "infer_type_core" [visR, 0, gen] m1) := rfl
theorem cruK2_some (h : FlushOK m2) : cruK2 N visT n gen (some (r2, m2)) =
    cruK3 N visT gen (stripF 5 (flushMem m2) [n, gen]) := by simp [cruK2, h]
theorem cruK2_bad (h : ¬ FlushOK m2) : cruK2 N visT n gen (some (r2, m2)) = none := by
  simp [cruK2, h]
theorem cruK3_some : cruK3 N visT gen (some (r3, m3)) =
    if r3.headD 0 = 0 then none
    else cruK4 gen (iarW N m3 visT (r3.tail.headD 0) (r3.tail.tail.headD 0)) := rfl
theorem cruK4_some : cruK4 gen (some (r4, m4)) = if r4.headD 0 = 0 then none else some ([gen], m4) := rfl
end arms

grind_pattern [ind_grind] crgW_eq => crgW (N + 1) m visR cvR gen
grind_pattern [ind_grind] crgK0_some => crgK0 N visR cvR gen (some (r0, m0))
grind_pattern [ind_grind] crgK1_some => crgK1 N visR cvR gen (some (r1, m1))
grind_pattern [ind_grind] crgK2_some => crgK2 visR gen (some (r2, m2))
grind_pattern [ind_grind] crgK3_some => crgK3 visR gen (some (r3, m3))
grind_pattern [ind_grind] crgK4_some => crgK4 (some (r4, m4))
grind_pattern [ind_grind] cruleW_eq => cruleW cR (N + 1) m visT visR cvR n gen
grind_pattern [ind_grind] cruK1_some => cruK1 cR N visT visR n gen (some (r1, m1))
grind_pattern [ind_grind] cruK2_some => cruK2 N visT n gen (some (r2, m2))
grind_pattern [ind_grind] cruK2_bad => cruK2 N visT n gen (some (r2, m2))
grind_pattern [ind_grind] cruK3_some => cruK3 N visT gen (some (r3, m3))
grind_pattern [ind_grind] cruK4_some => cruK4 gen (some (r4, m4))

/-- The lookups `class_rule_ok` needs. -/
structure CruleProg (p : Prog) extends FlushProg p : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "cv_lps" = some cvLps
  dom : p.lookup "class_rule_ok_domains" = some classRuleOkDomains
  guards : p.lookup "class_rule_ok_guards" = some classRuleOkGuards
  rule : p.lookup "class_rule_ok" = some classRuleOkL
  strip : StripProg p
  bvb : BvbProg p
  hf : HfF p
  hcr : CrfF p

theorem classRuleOkGuards_spec (p : Prog) (h : CruleProg p) (N : Nat) (s₀ : St) (visR cvR gen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_rule_ok_guards" [visR, cvR, gen]
    ⦃fun r s' => LocEq s' s₀ ∧ crgW N s₀.mem visR cvR gen = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.guards]
  simp only [callFn, classRuleOkGuards]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lbbF_spec p h.bvb N, hffF_spec p h.hf N,
        L.Arena.cvLps_specW p h.alloc h.copy h.eti h.lps N,
        stubM_spec p "all_level_params_defined" N, crfF_spec p h.hcr N] <;>
      finish (gen := 20)

theorem classRuleOk_spec (p : Prog) (h : CruleProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St) (visT visR cvR n gen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_rule_ok" [visT, visR, cvR, n, gen]
    ⦃fun r s' => LocEq s' s₀ ∧ cruleW cR N s₀.mem visT visR cvR n gen = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rule]
  simp only [callFn, classRuleOkL]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRuleOkGuards_spec p h N, hcR N "infer_type_core",
        flushCaches_spec p h.toFlushProg N, stripLams_specF p h.strip N,
        classRuleOkDomains_spec p h.dom h.hcr N] <;>
      finish (gen := 20) [loc_init4]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `class_rule_ok`: the relational lemma -/

theorem crgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {cvR gen : Word} {r : List Word} {cv : IConstantVal}
    (h : crgW N m vis cvR gen = some (r, m')) (hS : StageR dn vis fe m a) (hgen : H gen)
    (hq : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m) :
    ∃ a1 a2 a4 a5, (looseBVarsBoundedFast coreWalkFuel 0 (decI gen)).run a = .ok (true, a1) ∧
      (hasFvarFast coreWalkFuel (decI gen)).run a1 = .ok (false, a2) ∧
      (allLevelParamsDefined cv.levelParams (decI gen)).run a2 = .ok (true, a4) ∧
      (constsResolveFFast fe (decI gen)).run a4 = .ok (true, a5) ∧
      StageR dn vis fe m' a5 ∧ IWGrow m m' ∧ AbsOK m' := by
  cases N with
  | zero => simp [crgW] at h
  | succ N =>
  rw [crgW_eq] at h
  cases h1 : lbbF m [CWF, 0, gen] with
  | none => rw [h1] at h; simp [crgK0] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, crgK0_some] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1, -⟩ :=
    lbbF_ok dn vis fe CWF 0 gen hgen m m1 a r1 h1 hS
  by_cases hb1 : r1.headD 0 = 0
  · rw [if_pos hb1] at h; simp at h
  rw [if_neg hb1] at h
  cases h2 : hffF m1 [CWF, gen] with
  | none => rw [h2] at h; simp [crgK1] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, crgK1_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    hffF_ok dn vis fe CWF gen hgen m1 m2 a1 r2 h2 hS1
  by_cases hb2 : r2.headD 0 ≠ 0
  · rw [if_pos hb2] at h; simp at h
  rw [if_neg hb2] at h
  cases h3 : L.Arena.cvLpsW N m2 cvR with
  | none => rw [h3] at h; simp [crgK2] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, crgK2_some] at h
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, hd3, -⟩ := cvLpsA_stage h3 hS2 (ArrExt.decCV (IWGrow.erecExt hg12) hq) hqb
  have hA3 : AbsOK m3 := by
    have hA2 : AbsOK m2 := (AFr.of_frame (lbbF_frame h1)).trans (AFr.of_frame (hffF_frame h2)) hA
    cases N with
    | zero => simp [L.Arena.cvLpsW] at h3
    | succ N => exact erToIwW_afr h3 hA2
  cases h4 : stubM "all_level_params_defined" m3 [r3.headD 0, r3.tail.headD 0, gen] with
  | none => rw [h4] at h; simp [crgK3] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, crgK3_some] at h
  have hA4 : AbsOK m4 := AbsOK.stub (by decide) hA3 h4
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    allLevelParamsDefined_spec dn vis fe _ _ gen hgen cv.levelParams m3 m4 a2 r4 h4 ⟨hS3, hd3⟩
  by_cases hb4 : r4.headD 0 = 0
  · rw [if_pos hb4] at h; simp at h
  rw [if_neg hb4] at h
  cases h5 : crfF m4 [vis, gen] with
  | none => rw [h5] at h; simp [crgK4] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, crgK4_some] at h
  obtain ⟨x5, a5, hrun5, ⟨hS5, hg5, hx5, -⟩, hA5⟩ :=
    crfF_ok dn vis fe gen hgen m4 m5 a4 r5 h5 ⟨hS4, hA4⟩
  by_cases hb5 : r5.headD 0 = 0
  · rw [if_pos hb5] at h; simp at h
  rw [if_neg hb5] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex1 : x1 = true := by rw [← hx1]; simpa using hb1
  have ex2 : x2 = false := by rw [← hx2]; simpa using hb2
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  have ex5 : x5 = true := by rw [← hx5]; simpa using hb5
  rw [CWF_eq] at hrun1 hrun2
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun1
  subst ex1 ex2 ex4 ex5
  exact ⟨a1, a2, a4, a5, hrun1, hrun2, hrun4, hrun5, hS5, ((hg12.trans hg3).trans hg4).trans hg5, hA5⟩

theorem cruleW_ok {dn : NIdx → Option ConLeche.Name} {visT visR : Word} {feR : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {cvR n gen : Word} {r : List Word} {cv : IConstantVal}
    (h : cruleW stubCall N m visT visR cvR n gen = some (r, m')) (hS : StageR dn visR feR m a) (hgen : H gen)
    (hq : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m) :
    ∃ a', (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)).run a =
      .ok (decI gen, a') ∧ StageR dn visR feR m' a' ∧ IWGrow m m' ∧ r = [gen] ∧ AbsOK m' := by
  cases N with
  | zero => simp [cruleW] at h
  | succ N =>
  rw [cruleW_eq] at h
  cases h1 : crgW N m visR cvR gen with
  | none => rw [h1] at h; simp [cruK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cruK1_some] at h
  obtain ⟨a1, a2, a4, a5, hl, hf, ha, hc, hS1, hg1, hA1⟩ := crgW_ok h1 hS hgen hq hqb hA
  cases h2 : stubCall N "infer_type_core" [visR, 0, gen] m1 with
  | none => rw [h2] at h; simp [cruK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2] at h
  obtain ⟨x6, a6, hi, hS2, hg2, -⟩ := inferTypeCore_spec dn visR feR 0 gen hgen m1 m2 a5 r2 h2 hS1
  have hA2 : AbsOK m2 := AbsOK.stub (by decide) hA1 h2
  rw [show ((0 : Word).toNat) = 0 from rfl] at hi
  have hok : FlushOK m2 := Classical.byContradiction fun hn => by
    rw [cruK2_bad (h := hn)] at h; cases h
  rw [cruK2_some (h := hok)] at h
  obtain ⟨hS3, hg3⟩ := flush_stage hS2 hok
  cases h4 : stripF 5 (flushMem m2) [n, gen] with
  | none => rw [h4] at h; simp [cruK3] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4] at h
  obtain ⟨x7, a7, hs, hS4, hg4, hd4⟩ := stripF_lams_ok dn visR feR n gen hgen _ m4 _ r4 h4 hS3
  have hA4 : AbsOK m4 := (AFr.of_frame (flushMem_frame _)).trans (stripF_afr h4) hA2
  cases x7 with
  | none =>
    have h0 : r4.headD 0 = 0 := hd4
    rw [cruK3_some, if_pos h0] at h; cases h
  | some rb =>
  obtain ⟨rbs, body⟩ := rb
  obtain ⟨h41, ⟨hdl, htl⟩, -⟩ := hd4
  rw [cruK3_some, if_neg (by rw [h41]; decide)] at h
  simp only [getD_one, getD_two, Nat.reduceAdd] at hdl htl
  cases h5 : iarW N m4 visT (r4.tail.headD 0) (r4.tail.tail.headD 0) with
  | none => rw [h5] at h; simp [cruK4] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cruK4_some] at h
  have hb4 : (r4.tail.headD 0).toNat + (r4.tail.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m4 ≤ (m4.arr64 IW).size := hS4.2.1
    have h2 : (m4.arr64 IW).size < 2 ^ 64 := hS4.2.2.2.1
    omega
  obtain ⟨b, a8, hdom, ⟨hS5, hg5, hb5⟩, hA5⟩ := iarW_ok dn (feR.restrictTo visT.toNat) N m4 m5 a7 visT _ _
    rbs r5 h5 (hS4.restrict visT) hdl hb4 htl hA4
  rw [← allM_resolve_eq] at hdom
  by_cases hb : r5.headD 0 = 0
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have eb : b = true := by rw [← hb5.1]; simpa using hb
  subst eb
  refine ⟨a8, ?_, hS5.unrestrict hS.1.env.vis, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, rfl, hA5⟩
  simp only [ConRon.Arena.classRuleOk, StateT.run_bind, hl, exc_ok_bind', hf, ha, hc, hi,
    flushCaches_run, hs, hdom, if_true, if_false, Bool.false_eq_true, ite_true, ite_false, Bool.not_true,
    Bool.not_false]
  rfl

/-- **`class_rule_ok` refines `classRuleOk`** (through the stubs of its guards, `infer_type_core`,
`strip_lams`, and `class_rule_ok_domains`'s `consts_resolve_ffast`): the rule is returned as built.
Under `StageR`; the census link is `classRuleOk_refinesC` (`IndT/RecGen4.lean`). -/
theorem classRuleOk_refines (p : Prog) (hp : CruleProg p) (N : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (visT visR : Word) (feR : IFEnv) (cvR n gen : Word)
    (cv : IConstantVal) (hS : StageR dn visR feR s₀.mem a₀) (hgen : H gen)
    (hq : decCV (erecP s₀.mem) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_rule_ok" [visT, visR, cvR, n, gen]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a₀ ∧
      KP dn visR feR s₀.mem decW0E (r, s'.mem)
        (AM.st (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a₀)
        (AM.res (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (classRuleOk_spec p hp stubCall (stubCall_spec p) N s₀ visT visR cvR n gen) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg, rfl, hA'⟩ := cruleW_ok hm hS hgen hq hqb hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, ⟨by rw [hst]; exact hS', hg, by rw [hres]; exact ⟨hgen, rfl⟩⟩, hA'⟩

end L.Ind
