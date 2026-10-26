import ConAgua.Arena.LevelArena
import ConAgua.Arena.LevelHeap
import ConAgua.Arena.View

/-!
# `lv_node` against the twin's level view, converse direction (lane `decls3`)

Moved here from `DeclCanonView.lean` (lane `defeq2`, so the inference side can use it without
the declaration modules): a returning `lv_node` run means the twin's level view succeeds (the
twin fails on a dangling handle).
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

section lview
variable {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
include hR hh

theorem lview_of_lvNodeW (hne : lvNodeW m h ≠ []) : ∃ v, a.store.lss.ls.view (decI h) = some v := by
  have ht1 := tierW_le h
  have hidx := decL_idx h
  have hfl := ConsR.flag hR.zero
  unfold lvNodeW at hne
  simp only [h32 hh, ne_eq, not_true_eq_false, ↓reduceIte] at hne
  by_cases hsc : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hsc] at hne
  rw [ite_eq_right hsc] at hne
  have e0 : ((decI h : LIdx).tag = 0 ↔ h >>> 28 = 0) := decL_tag_eq h hh 0 (by decide)
  have e1 : ((decI h : LIdx).tag = 1 ↔ h >>> 28 = 1) := decL_tag_eq h hh 1 (by decide)
  have e2 : ((decI h : LIdx).tag = 2 ↔ h >>> 28 = 2) := decL_tag_eq h hh 2 (by decide)
  have e3 : ((decI h : LIdx).tag = 3 ↔ h >>> 28 = 3) := decL_tag_eq h hh 3 (by decide)
  have e4 : ((decI h : LIdx).tag = 4 ↔ h >>> 28 = 4) := decL_tag_eq h hh 4 (by decide)
  have hview : ∀ (P : LTables → Prop), (∀ T : LTables, P T → ∃ v, T.get (decI h) = some v) →
      (tierW h = 0 → P a.store.lss.ls.pers) → (tierW h ≠ 0 → P a.store.lss.ls.scr) →
      ∃ v, a.store.lss.ls.view (decI h) = some v := by
    intro P hP hp hs
    unfold LStore.view
    rw [decL_pers h hh]
    by_cases ht : tierW h = 0
    · simp only [ht, beq_self_eq_true, ↓reduceIte]; exact hP _ (hp ht)
    · have hon : a.store.lss.ls.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hsc ⟨ht, h1⟩
      simp only [ht, beq_iff_eq, ↓reduceIte, hon]; exact hP _ (hs ht)
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ↓reduceIte] at hne
    have hc : ¬ tcnt m ZERO (tierW h) ≤ idxW h := fun c => hne (by simp [c])
    obtain ⟨x, hx, -⟩ := ConsR.node hR.zero (tierW h) ht1 (idxW h)
      (UInt64.not_le.mp hc)
    refine hview (fun T => T.zeros.nodes[(idxW h).toNat]? = some x) ?_ ?_ ?_
    · intro T hT
      refine ⟨.zero, ?_⟩
      simp (config := { decide := true }) only [LTables.get, LTag.zero, beq_iff_eq, e0, g0, ↓reduceIte, Tbl.node?, decL_idx h, hT, Option.map_some]
    · intro ht; simpa [ht] using hx
    · intro ht; simpa [ht] using hx
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ↓reduceIte] at hne
    have hc : ¬ tcnt m SUCC (tierW h) ≤ idxW h := fun c => hne (by simp [c])
    obtain ⟨x, hx, -⟩ := ConsR.node hR.succ (tierW h) ht1 (idxW h)
      (UInt64.not_le.mp hc)
    refine hview (fun T => T.succs.nodes[(idxW h).toNat]? = some x) ?_ ?_ ?_
    · intro T hT
      refine ⟨.succ x.u, ?_⟩
      simp (config := { decide := true }) only [LTables.get, LTag.zero, LTag.succ, beq_iff_eq, e0, e1, g1, ↓reduceIte, Tbl.node?, decL_idx h, hT, Option.map_some]
    · intro ht; simpa [ht] using hx
    · intro ht; simpa [ht] using hx
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ↓reduceIte] at hne
    have hc : ¬ tcnt m MAX (tierW h) ≤ idxW h := fun c => hne (by simp [c])
    obtain ⟨x, hx, -⟩ := ConsR.node hR.max (tierW h) ht1 (idxW h)
      (UInt64.not_le.mp hc)
    refine hview (fun T => T.maxs.nodes[(idxW h).toNat]? = some x) ?_ ?_ ?_
    · intro T hT
      refine ⟨.max x.u x.v, ?_⟩
      simp (config := { decide := true }) only [LTables.get, LTag.zero, LTag.succ, LTag.max, beq_iff_eq, e0, e1, e2, g2, ↓reduceIte, Tbl.node?, decL_idx h, hT, Option.map_some]
    · intro ht; simpa [ht] using hx
    · intro ht; simpa [ht] using hx
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ↓reduceIte] at hne
    have hc : ¬ tcnt m IMAX (tierW h) ≤ idxW h := fun c => hne (by simp [c])
    obtain ⟨x, hx, -⟩ := ConsR.node hR.imax (tierW h) ht1 (idxW h)
      (UInt64.not_le.mp hc)
    refine hview (fun T => T.imaxs.nodes[(idxW h).toNat]? = some x) ?_ ?_ ?_
    · intro T hT
      refine ⟨.imax x.u x.v, ?_⟩
      simp (config := { decide := true }) only [LTables.get, LTag.zero, LTag.succ, LTag.max, LTag.imax, beq_iff_eq, e0, e1, e2, e3, g3, ↓reduceIte, Tbl.node?, decL_idx h, hT, Option.map_some]
    · intro ht; simpa [ht] using hx
    · intro ht; simpa [ht] using hx
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ↓reduceIte] at hne
    have hc : ¬ tcnt m PARAM (tierW h) ≤ idxW h := fun c => hne (by simp [c])
    obtain ⟨x, hx, -⟩ := ConsR.node hR.param (tierW h) ht1 (idxW h)
      (UInt64.not_le.mp hc)
    refine hview (fun T => T.params.nodes[(idxW h).toNat]? = some x) ?_ ?_ ?_
    · intro T hT
      refine ⟨.param x.n, ?_⟩
      simp (config := { decide := true }) only [LTables.get, LTag.zero, LTag.succ, LTag.max, LTag.imax, LTag.param, beq_iff_eq, e0, e1, e2, e3, e4, g4, ↓reduceIte, Tbl.node?, decL_idx h, hT, Option.map_some]
    · intro ht; simpa [ht] using hx
    · intro ht; simpa [ht] using hx
  simp [g0, g1, g2, g3, g4] at hne

end lview

end L.Ind
