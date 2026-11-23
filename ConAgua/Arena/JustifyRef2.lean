module

public import ConAgua.Arena.JustifyRef1
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# The cone walk refines the twin's (lane compare, helper compare-cone)

`cone_push` (the cited `ns ++ work` on the stack `CWK`), then `rec_names`, `entry_needs`,
`cone_entry`, `cone_go` against `recNames`, `entryNeeds`, `coneEntry`, `coneGo`.
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

/-- **The cone walk's state with room for its top word**: `ConeR` and the control word `CTL[228]`
inside `CTL` (as the needs walk's `NdR`). -/
structure CnR (m : Mem) (seen : Std.HashMap NIdx Bool) (work : List NIdx) : Prop where
  rel : ConeR m seen work
  ctl : CTOPC.toNat < (m.arr64 CTL).size

/-! ## `cone_push` -/

/-- **`cone_push`'s loop**: from height `h` with `k` names left, the names `NACC[k-1] … NACC[0]`
written at `CWK[h‥h + k)`, nothing else. -/
theorem conePush_loop : ∀ (n : Nat) (m : Mem) (k h h' : Word) (m' : Mem),
    conePushW.loop1 n m k h = some (h', m') →
    h'.toNat = h.toNat + k.toNat ∧ MemFrame [CWK] [] m m' ∧
    (h.toNat ≤ (m.arr64 CWK).size → h'.toNat ≤ (m.arr64 CWK).size) ∧
    ∀ i, rdN (m'.arr64 CWK) i = if h.toNat ≤ i ∧ i < h.toNat + k.toNat then
      rdN (m.arr64 NACC) (k.toNat - 1 - (i - h.toNat)) else rdN (m.arr64 CWK) i := by
  intro n
  induction n with
  | zero => intro m k h h' m' e; rw [conePushW.loop1.eq_def] at e; cases e
  | succ n ih =>
    intro m k h h' m' e
    by_cases hk : k = 0
    · rw [conePushW.loop1.arm2 _ _ _ _ hk] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      subst hk
      refine ⟨by simp, MemFrame.refl _ _ _, id, fun i => ?_⟩
      split
      · rename_i hc; simp at hc; omega
      · rfl
    by_cases hl : m.len64 CWK ≤ h
    · rw [conePushW.loop1.abort1 _ _ _ _ hk hl] at e; cases e
    rw [conePushW.loop1.arm1 _ _ _ _ hk hl] at e
    have hl' : h.toNat < (m.arr64 CWK).size % 2 ^ 64 := by
      simp only [Mem.len64, UInt64.le_iff_toNat_le, Nat.not_le] at hl; exact hl
    have hlt : h.toNat < (m.arr64 CWK).size :=
      Nat.lt_of_lt_of_le hl' (Nat.mod_le _ _)
    have hlt2 : h.toNat + 1 < 2 ^ 64 :=
      Nat.lt_of_le_of_lt hl' (Nat.mod_lt _ (by decide)) |> fun h' => by omega
    have hk0 : k.toNat ≠ 0 := fun e => hk (UInt64.toNat_inj.mp (by simp [e]))
    have hh1 : (h + 1).toNat = h.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hk1 : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    obtain ⟨e1, hf, hro, hr⟩ := ih _ _ _ _ _ e
    refine ⟨by rw [e1, hh1, hk1]; omega,
      (MemFrame.set64 m CWK (by decide) _ _).trans hf, fun _ => ?_, fun i => ?_⟩
    · have := hro (by rw [hh1, L.Mem.size64_set64]; omega)
      rwa [L.Mem.size64_set64] at this
    rw [hr i, hh1, hk1]
    simp only [rdN_set64]
    have hne : ¬ ((NACC : TieredArray) = CWK) := by decide
    simp only [hne, false_and, ↓reduceIte]
    have hw : rdW (m.arr64 NACC) (k - 1) = rdN (m.arr64 NACC) (k.toNat - 1) := by
      show rdN _ (k - 1).toNat = _; rw [hk1]
    by_cases hih : i = h.toNat
    · subst hih
      have c1 : ¬ (h.toNat + 1 ≤ h.toNat ∧ h.toNat < h.toNat + 1 + (k.toNat - 1)) := by omega
      have c2 : h.toNat ≤ h.toNat ∧ h.toNat < h.toNat + k.toNat := by omega
      simp only [c1, c2, ↓reduceIte, hlt, and_self, hw, Nat.sub_self, Nat.sub_zero]
    · have c3 : (h = h ∧ h.toNat = i ∧ i < (m.arr64 CWK).size) ↔ False := by
        constructor
        · rintro ⟨-, e, -⟩; exact hih e.symm
        · intro f; exact f.elim
      by_cases hi : h.toNat + 1 ≤ i ∧ i < h.toNat + 1 + (k.toNat - 1)
      · have hi' : h.toNat ≤ i ∧ i < h.toNat + k.toNat := by omega
        rw [ite_eq_left hi, ite_eq_left hi']
        rw [show k.toNat - 1 - 1 - (i - (h.toNat + 1)) = k.toNat - 1 - (i - h.toNat) by omega]
      · have hi' : ¬ (h.toNat ≤ i ∧ i < h.toNat + k.toNat) := by omega
        simp only [hi, hi', ↓reduceIte, true_and]
        have : ¬ (h.toNat = i ∧ i < (m.arr64 CWK).size) := fun ⟨e, _⟩ => hih e.symm
        simp [this]
