import ConAgua.Arena.RecGenSpec3
import ConAgua.Arena.CoreRefine
import ConAgua.Arena.ScratchRefine

/-!
# `RecGen`: `classRuleOk` (lane `indproofs2`, helper `rec`)
-/

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
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_words hq
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
  | some (r3, m3) => if r3.headD 0 = 0 then none else crgK4 (stubM "consts_resolve_ffast" m3 [visR, gen])

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
    if r0.headD 0 = 0 then none else crgK1 N visR cvR gen (stubM "has_fvar_fast" m0 [CWF, gen])

/-- **The model of `class_rule_ok_guards`.** -/
def crgW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, visR, cvR, gen => crgK0 N visR cvR gen (stubM "loose_bvars_bounded_fast" m [CWF, 0, gen])

def cruK4 (gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then none else some ([gen], m4)

def cruK3 (N : Nat) (visT gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none
    else cruK4 gen (iarW N m3 visT (r3.tail.headD 0) (r3.tail.tail.headD 0))

def cruK2 (N : Nat) (visT n gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => cruK3 N visT gen (stubM "strip_lams" (flushMem m2) [n, gen])

def cruK1 (N : Nat) (visT visR n gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => cruK2 N visT n gen (stubM "infer_type_core" m1 [visR, 0, gen])

/-- **The model of `class_rule_ok`.** -/
def cruleW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, visT, visR, cvR, n, gen => cruK1 N visT visR n gen (crgW N m visR cvR gen)

section arms
variable (N : Nat) (m m0 m1 m2 m3 m4 : Mem) (visT visR cvR n gen : Word) (r0 r1 r2 r3 r4 : List Word)
theorem crgW_eq : crgW (N + 1) m visR cvR gen =
    crgK0 N visR cvR gen (stubM "loose_bvars_bounded_fast" m [CWF, 0, gen]) := rfl
theorem crgK0_some : crgK0 N visR cvR gen (some (r0, m0)) =
    if r0.headD 0 = 0 then none else crgK1 N visR cvR gen (stubM "has_fvar_fast" m0 [CWF, gen]) := rfl
theorem crgK1_some : crgK1 N visR cvR gen (some (r1, m1)) =
    if r1.headD 0 ≠ 0 then none else crgK2 visR gen (L.Arena.cvLpsW N m1 cvR) := rfl
theorem crgK2_some : crgK2 visR gen (some (r2, m2)) =
    crgK3 visR gen (stubM "all_level_params_defined" m2 [r2.headD 0, r2.tail.headD 0, gen]) := rfl
theorem crgK3_some : crgK3 visR gen (some (r3, m3)) =
    if r3.headD 0 = 0 then none else crgK4 (stubM "consts_resolve_ffast" m3 [visR, gen]) := rfl
theorem crgK4_some : crgK4 (some (r4, m4)) = if r4.headD 0 = 0 then none else some ([0], m4) := rfl
theorem cruleW_eq : cruleW (N + 1) m visT visR cvR n gen =
    cruK1 N visT visR n gen (crgW N m visR cvR gen) := rfl
theorem cruK1_some : cruK1 N visT visR n gen (some (r1, m1)) =
    cruK2 N visT n gen (stubM "infer_type_core" m1 [visR, 0, gen]) := rfl
theorem cruK2_some : cruK2 N visT n gen (some (r2, m2)) =
    cruK3 N visT gen (stubM "strip_lams" (flushMem m2) [n, gen]) := rfl
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
grind_pattern [ind_grind] cruleW_eq => cruleW (N + 1) m visT visR cvR n gen
grind_pattern [ind_grind] cruK1_some => cruK1 N visT visR n gen (some (r1, m1))
grind_pattern [ind_grind] cruK2_some => cruK2 N visT n gen (some (r2, m2))
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
        stubM_spec p "loose_bvars_bounded_fast" N, stubM_spec p "has_fvar_fast" N,
        L.Arena.cvLps_specW p h.alloc h.copy h.eti h.lps N,
        stubM_spec p "all_level_params_defined" N, stubM_spec p "consts_resolve_ffast" N] <;>
      finish (gen := 20)

theorem classRuleOk_spec (p : Prog) (h : CruleProg p) (N : Nat) (s₀ : St) (visT visR cvR n gen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_rule_ok" [visT, visR, cvR, n, gen]
    ⦃fun r s' => LocEq s' s₀ ∧ cruleW N s₀.mem visT visR cvR n gen = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rule]
  simp only [callFn, classRuleOkL]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRuleOkGuards_spec p h N, stubM_spec p "infer_type_core" N,
        flushCaches_spec p h.toFlushProg N, stubM_spec p "strip_lams" N,
        classRuleOkDomains_spec p h.dom N] <;>
      finish (gen := 20) [loc_init4]

end L.Ind
