module

public import ConAgua.Arena.QuotRecW
public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.BasisBlockT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.L.WordOff
import ConRon.Bridge.Checker.Basis
import all ConAgua.Arena.BasisL

@[expose] public section

/-!
# The reserved names' check (`basis_names_ok`, `basis_names_error`) refines the twin's

con-ron #493's `basisNamesOk`/`basisNamesError` (`Basis.lean`): a block under a pinned block's
names compared with its pin (`basis_name_hit`, `rom_basis_decls`, `er_to_iw`, `pin_list_ok`),
any other block's members unreserved (`block_names_unreserved`), a one-constant declaration's
name unreserved (`basis_name_unreserved`) but for `Quot.sound` and the quotient records.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `reserved_contains` -/

theorem resFromW_hit (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), j.toNat ≤ 16 →
    resFromW n m x j = some b → b ≠ 0 → ∃ i, j.toNat ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j b _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b hj h hb
    rw [resFromW_step] at h
    by_cases h16 : 16 ≤ j
    · rw [ite_eq_left h16] at h; simp at h; exact absurd h.symm hb
    rw [ite_eq_right h16] at h
    have hj16 : j.toNat < 16 := by rw [UInt64.le_iff_toNat_le] at h16; simp at h16; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, Nat.le_refl _, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨i, hi1, hi2, hi3⟩ := ih m x (j + 1) b (by omega) h hb
    exact ⟨i, by omega, hi2, hi3⟩

theorem resFromW_01 (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), resFromW n m x j = some b →
    b = 0 ∨ b = 1 := by
  induction n with
  | zero => intro m x j b h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b h
    rw [resFromW_step] at h
    split at h
    · simp at h; exact Or.inl h.symm
    split at h
    · simp at h; exact Or.inr h.symm
    exact ih _ _ _ _ h

/-- **`reserved_contains` is the twin's `reservedBasisNames.contains`**, as a word. -/
theorem resContW_res {m : Mem} {a : AState} {n : Nat} {x b : Word} (hx : x.toNat < 2 ^ 32)
    (h : resContW n m x = some b) (hP : PinsR m a.pins) :
    ∃ R, reservedBasisNames.run a = .ok (R, a) ∧ b = if R.contains (decI x) then 1 else 0 := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  rcases resFromW_01 n m x 0 b h with rfl | rfl
  · have hm := resFromW_miss n m x 0 (by simp) h
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, e⟩ := hc
      exact hm i (Nat.zero_le _) hi ((decI_eq_iff _ (hF.reserved_lt i hi) _).mp e ▸ decI_word_self x hx)
    rw [this]; rfl
  · obtain ⟨i, -, hi, he⟩ := resFromW_hit n m x 0 1 (by simp) h (by decide)
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = true := by
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [he]⟩
    rw [this]; rfl


/-! ## `basis_name_unreserved` -/

theorem bnuW_ok {m m' : Mem} {a : AState} {n : Nat} {x : Word} {r : List Word}
    (hx : x.toNat < 2 ^ 32) (hP : PinsR m a.pins) (h : basisNameUnreservedW n m x = some (r, m')) :
    m' = m ∧ ∃ b, (basisNameUnreserved (decI x)).run a = .ok (b, a) ∧ (r.headD 0 ≠ 0 ↔ b = true) := by
  cases n with
  | zero => simp [basisNameUnreservedW] at h
  | succ n =>
  simp only [basisNameUnreservedW] at h
  rcases hc : resContW n m x with _ | c <;> rw [hc] at h
  · simp [basisNameUnreservedW.k_reserved_contains] at h
  simp only [basisNameUnreservedW.k_reserved_contains, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨R, hR, hb⟩ := resContW_res hx hc hP
  refine ⟨rfl, !R.contains (decI x), ?_, ?_⟩
  · simp only [basisNameUnreserved, StateT.run_bind, hR, except_ok_bind]; rfl
  · rw [hb]; cases R.contains (decI x) <;> simp

end L.Ind
