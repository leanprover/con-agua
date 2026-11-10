module

public import ConAgua.Arena.DeclCvg
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DerRel
import ConAgua.Arena.ScratchRefine
import ConAgua.Arena.RecCheckSpec.ErToIwWStage

@[expose] public section

/-!
# FlushStage

`flush_stage`, `cvLpsA_stage` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `flush_caches()` under the stage relation. -/
theorem flush_stage {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR vis fe m a) (hok : FlushOK m) :
    StageR vis fe (flushMem m) { a with caches := Caches.empty } ∧ IWGrow m (flushMem m) := by
  have hf := flushMem_frame m
  have hC : CheckR (flushMem m) { a with caches := Caches.empty } vis fe :=
    ⟨ArenaD.caches_irrel _ ⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ hf _ h.check.arena.base,
      DerR.frameM [] _ _ _ hf (by simp) _ h.check.arena.der⟩,
    h.check.core.flush hok,
    h.check.pins.frame (.of_lt (k := 0) (by simp) (by decide)) hf,
    h.check.env.frame (by simp) (fun x hx => not_mem_envCtl (by have := flushCtl_lt x hx; omega)) hf,
    h.check.mode.frame hf (by simp [flushCtl]) (by simp [flushCtl])⟩
  have hA3 : (IW : TieredArray) ∉ ([] : List TieredArray) ∧ (EREC : TieredArray) ∉ ([] : List TieredArray) ∧
      tier1 EREC ∉ ([] : List TieredArray) := by simp
  have hC3 : (129 : Word) ∉ flushCtl ∧ (130 : Word) ∉ flushCtl ∧ (200 : Word) ∉ flushCtl := by
    simp [flushCtl]
  exact ⟨⟨hC, IWOK.of_keep hf hA3 hC3 h.iw⟩, IWGrow.of_keep hf hA3 hC3⟩

/-- `cv_lps(q)` under the stage relation: the level parameters, a slice below the top. -/
theorem cvLpsA_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : L.Arena.cvLpsW n m q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erA m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hq
  obtain ⟨nm, -, lv, hlv, ty, -, rfl⟩ := hq
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
  simp only [nat?, Option.map_eq_some_iff] at ho2 hl2
  obtain ⟨w1, hw1, rfl⟩ := ho2
  obtain ⟨w2, hw2, rfl⟩ := hl2
  have e1 : erRd m (q + 1) = w1 :=
    erRd_of_erA (by rw [show (q + 1).toNat = q.toNat + 1 by rw [UInt64.toNat_add]; simp; omega]; exact hw1)
  have e2 : erRd m (q + 2) = w2 :=
    erRd_of_erA (by rw [show (q + 2).toNat = q.toNat + 2 by rw [UInt64.toNat_add]; simp; omega]; exact hw2)
  rcases n with _ | n
  · simp [L.Arena.cvLpsW] at h
  rw [L.Arena.cvLpsW_step] at h
  change erToIwW n m (erRd m (q + 1)) (erRd m (q + 2)) = some (r, m') at h
  rw [e1, e2] at h
  obtain ⟨hS4, hg4, hdec4, htop4, -⟩ := erToIwW_stage h hS hsl
  exact ⟨hS4, hg4, hdec4, Nat.le_of_eq htop4⟩

end L.Ind

end
