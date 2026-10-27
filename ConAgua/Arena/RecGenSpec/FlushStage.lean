import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.RecGenSpec.CruleProg

/-!
# FlushStage

`flush_stage`, `cvLpsA_stage`, `cruK3`, `cruK2`, `cruK1`, `cruleW` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

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
    h.1.env.frame (.of_lt (k := 0) (by simp) (by decide)) (.of_lt flushCtl_lt (by decide)) hf,
    h.1.mode.frame hf (by simp [flushCtl]) (by simp [flushCtl])⟩
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
  rcases n with _ | n
  · simp [L.Arena.cvLpsW] at h
  rw [L.Arena.cvLpsW_step, e1, e2] at h
  obtain ⟨-, hr4t, hdec4, hS4, hg4, htop4⟩ := L.Arena.erToIwW_stage h hS hsrc
  rw [hr4t]
  exact ⟨hS4, hg4, by rw [hdec4]; exact hsl, htop4⟩

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
  | N + 1, m, visT, visR, cvR, n, gen => cruK1 cR N visT visR n gen (crgW cR N m visR cvR gen)

section arms
variable (cR : CallM) (N : Nat) (m m0 m1 m2 m3 m4 : Mem) (visT visR cvR n gen : Word) (r0 r1 r2 r3 r4 : List Word)
theorem cruK2_bad (h : ¬ FlushOK m2) : cruK2 N visT n gen (some (r2, m2)) = none := by
  simp [cruK2, h]
end arms

grind_pattern [ind_grind] cruK2_bad => cruK2 N visT n gen (some (r2, m2))
end L.Ind

end
