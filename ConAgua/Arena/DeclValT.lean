module

public import ConAgua.Arena.DeclRec

@[expose] public section

/-!
# `env_push`'s frame

The value checks end with `env_push`, which changes the environment; it writes the index rows,
`ECON` and `CTL[128]` only (`envPushW_frame`), so the core's memos (`CoreMemos`) stay well formed
across it.
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`env_push` writes the index rows, `ECON` and its count** (`CTL[128]`). -/
theorem envPushW_frame {m m' : Mem} {vis q : Word} {r : List Word}
    (h : envPushW m vis q = some (r, m')) :
    MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m m' := by
  simp only [envPushW] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  rename_i hc
  obtain ⟨ht, -⟩ := hc
  have hrow : (rowArr (rdW (m.arr64 EREC) (q + 1)) : TieredArray) ∈
      ([EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] : List TieredArray) := by
    rcases rowArr_names (rdW (m.arr64 EREC) (q + 1)) with h | h | h | h | h | h <;> rw [h] <;> decide
  have hf1 : MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m
      (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact ((MemFrame.set64 m _ (TieredArray.t0_ne (rowArr_ne _ (by decide))) _ _).mono
      (by intro b hb; simp at hb; subst hb; exact hrow) (by simp)).trans
      ((MemFrame.set64 _ _ (TieredArray.t0_ne (rowArr_ne _ (by decide))) _ _).mono
        (by intro b hb; simp at hb; subst hb; exact hrow) (by simp))
  simp only [envPushK] at h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (hf1.trans ((MemFrame.set64 _ ECON (by decide) _ _).mono (by simp) (by simp))).trans
    ((MemFrame.setCtl _ 128 _).mono (by simp) (by simp))

end L.Arena
