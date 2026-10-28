import ConAgua.Arena.IndT.RecCheckTpd
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx

/-!
# `target_holes`' model keeps the arena (`thW_afr`)

For `target_class_match`'s refinement (`tcm_ref`, `Verdict/IndBTcm.lean`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem thW_afr : ∀ (n : Nat) {m m' : Mem} {tyo tyl base : Word} {r : List Word},
    thW n m tyo tyl base = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [thW] at h
  | n + 1, m, m', tyo, tyl, base, r, h => by
    by_cases hl : tyl = 0
    · rw [thW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact AFr.refl _
    rw [thW_cons (h := hl)] at h
    rcases hf : fvinternW m base (rdW (m.arr64 IW) tyo) with _ | ⟨v, m1⟩ <;> rw [hf] at h <;>
      try (simp only [thK1, reduceCtorEq] at h; done)
    by_cases hb : 4294967296 ≤ v
    · rw [thK1_big (h := hb)] at h; cases h
    rw [thK1_ok (h := hb)] at h
    rcases hg : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with _ | ⟨r2, m2⟩ <;> simp only [hg, thK2, reduceCtorEq] at h
    rcases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, thK3, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((fvinternW_afr hf).trans (thW_afr n hg)).trans (consW_afr hc)

end L.Ind
