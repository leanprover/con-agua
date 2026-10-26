import ConAgua.Arena.PromoteCIRef25

/-!
# The environment index around a promotion: `erase_installed`, `index_promoted`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem rowSet_frame (m : Mem) (w c q : Word) (ht : rowTag w ≤ 2) :
    MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1] [] m (rowSet m w c q) := by
  have hne : rowArr w ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have h1 := MemFrame.set64 m (rowArr w) hne (ixW w) c
  have h2 := MemFrame.set64 (m.set64 (rowArr w) (ixW w) c) (rowArr w) hne (ixW w + 1) q
  have hmem : rowArr w ∈ [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1] := by
    have : rowTier w < 2 := Nat.mod_lt _ (by decide)
    simp only [rowArr, EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1, ArrId, List.mem_cons, List.not_mem_nil, or_false]; omega
  exact (h1.trans h2).mono (by simpa using hmem) (by simp)

/-- **`EnvR` after a promotion**: the rows (constant and table) are untouched, the pool grew, the
constants and tables lists are the promoted ones. -/
theorem EnvR.promoted {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe)
    (he : ∀ b : Nat, 132 ≤ b → b < 143 → (b < 135 ∨ 140 ≤ b) → m'.arr64 b = m.arr64 b)
    (htr : ∀ w, rowTag w ≤ 2 → m'.arr64 (tblArr w) = m.arr64 (tblArr w))
    (hg : ErecGrow m m') (consts' : List IConstantInfo) (tables' : List IProjTable)
    (hcons : envConsts dn m' = some consts') (htabs : envTables m' = some tables') :
    EnvR dn m' vis ⟨⟨consts', tables'⟩, fe.idx, fe.visibleBelow, fe.tbls⟩ := by
  have hC : ∀ w, rowC m' w = rowC m w := fun w => by
    unfold rowC; split
    · have : rowTier w < 2 := Nat.mod_lt _ (by decide)
      rw [he _ (by simp only [rowArr]; omega) (by simp only [rowArr]; omega)
        (by simp only [rowArr]; omega)]
    · rfl
  have hP : ∀ w, rowP m' w = rowP m w := fun w => by
    unfold rowP; split
    · have : rowTier w < 2 := Nat.mod_lt _ (by decide)
      rw [he _ (by simp only [rowArr]; omega) (by simp only [rowArr]; omega)
        (by simp only [rowArr]; omega)]
    · rfl
  have hW : ∀ w, rowW m' w = rowW m w := fun w => by simp only [rowW, hC, hP]
  have hT : ∀ w, tblRow m' w = tblRow m w := fun w => by
    unfold tblRow; split
    · rename_i hw; rw [htr w hw]
    · rfl
  have hx := hg.ext
  refine ⟨h.vis, fun n hn => (hW _).symm ▸ h.keys n hn, fun n hn h0 => ?_, hcons,
    fun n hn => (hT _).symm ▸ h.tkeys n hn, fun n hn h0 => ?_, htabs⟩
  · rw [hC] at h0
    have hv := h.vals n hn h0
    have hk := h.keys n hn
    simp only [rowW, h0, ite_false, Option.map_some] at hk
    cases e : fe.idx[n]? with
    | none => simp [e] at hk
    | some r =>
      simp only [e, Option.map_some] at hv ⊢
      rw [hP]
      exact (hx.decCI hv.symm).symm
  · rw [hT] at h0 ⊢
    have hv := h.tvals n hn h0
    cases e : fe.tbls[n]? with
    | none => rw [e] at hv; have := h.tkeys n hn; simp [e, h0] at this
    | some t => rw [e] at hv ⊢; exact (hx.decTbl hv.symm).symm

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem envErase_mem (n : Nat) (s₀ : St) (w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "env_erase" [w]
    ⦃fun _ s' => s'.mem = rowSet s₀.mem w 0 0 ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧
      rowIx w + 1 < (s₀.mem.arr64 (rowArr w)).size; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "env_erase")]
  simp only [callFn, envEraseL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        envRowSet_spec p (hp.get "env_ix") (hp.get "env_row_set") n] <;>
      finish

end rel

end L.Arena
