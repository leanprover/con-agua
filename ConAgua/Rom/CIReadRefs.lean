import ConAgua.Rom.CIReadRefData

/-!
# The ROM constant readers refine the twin (helper `decls4-rom`)

The six entries of `CIRead.lean` against `CIReadSpec.lean`'s statements: `rom_ci`, `rom_cv`,
`rom_expr_pin`, `rom_and_pin`, and `rom_basis_decls`/`rom_basis_decls_a` for the four kinds
`basisPinHit` tries (`eqK`, `natK`, `emptyK`, `falseK`). The quotient kind (`4`) is open: its block
holds `Quot`, whose `sortZ` is `.ifAllZero [u]`, and `decCaps` reads the name `u` back through
`dn`, which `StageR` does not relate to the store (`CIReadRefCaps.lean`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-! ## The region's entries and the twin's values, by index -/

theorem ciEntries_ci (i : Nat) (hi : i < 8) :
    ciEntries[10 + i]'(by rw [ciEntries_len]; omega) = (encCI [] (romCiVals[i]'(by simp [romCiVals]; omega))).1 := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | _ + 8, h => exact absurd h (by omega)

theorem ciEntries_cv (i : Nat) (hi : i < 10) :
    ciEntries[18 + i]'(by rw [ciEntries_len]; omega) = (encCV [] (romCvVals[i]'(by simp [romCvVals]; omega))).1 := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | _ + 10, h => exact absurd h (by omega)

theorem ciEntries_ex (i : Nat) (hi : i < 2) :
    ciEntries[28 + i]'(by rw [ciEntries_len]; omega) =
      (encExprM [] (romExprVals[i]'(by simp [romExprVals]; omega))).1 := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => exact absurd h (by omega)

theorem ciEntries_b (i : Nat) (hi : i < 5) :
    ciEntries[i]'(by rw [ciEntries_len]; omega) =
      encBlock (ConLeche.BasisKind.decls (basisKinds[i]'(by simp [basisKinds]; omega))) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem ciEntries_bA (i : Nat) (hi : i < 5) :
    ciEntries[5 + i]'(by rw [ciEntries_len]; omega) =
      encBlock (ConLeche.BasisKind.declsA (basisKinds[i]'(by simp [basisKinds]; omega))) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem ciEntries_and : ciEntries[30]'(by rw [ciEntries_len]; omega) = encBlock ConLeche.andPin := rfl

theorem romCiT_eq (i : Nat) (hi : i < 8) :
    romCiT i = ConRon.Arena.internCI (romCiVals[i]'(by simp [romCiVals]; omega)) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | _ + 8, h => exact absurd h (by omega)

theorem romCvT_eq (i : Nat) (hi : i < 10) :
    romCvT i = ConRon.Arena.internCV (romCvVals[i]'(by simp [romCvVals]; omega)) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | _ + 10, h => exact absurd h (by omega)

theorem romExprT_eq (i : Nat) (hi : i < 2) :
    romExprT i = ConRon.Arena.internExpr (romExprVals[i]'(by simp [romExprVals]; omega)) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => exact absurd h (by omega)

theorem basisOfW_eq (i : Nat) (hi : i < 5) : basisOfW i = basisKinds[i]'(by simp [basisKinds]; omega) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem word_add_toNat (c : Nat) (w : Word) (h : c + w.toNat < 2 ^ 64) :
    (UInt64.ofNat c + w).toNat = c + w.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega

/-! ## The entries -/

section entries
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom) (rest : List UInt8)
  (hrom : rom = romData ++ rest)
include hL hr hrom

/-- **`rom_ci(id)` refines `romCiT id`.** -/
theorem romCiRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomCiRef p dn vis fe := by
  intro id hid n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => ciEntryW p n mq id) (ciEntry_specW rom p hL n · id) hc
  unfold ciEntryW at hw
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  cases h1 : callW p n "rci_slot" [10 + id] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  have h10 : (10 + id).toNat = 10 + id.toNat := word_add_toNat 10 id (by omega)
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom (10 + id) (by omega)
  simp only [h10, ciEntries_ci id.toNat hid] at hpos
  have hI0 := RInv.refl hS
  cases h2 : callW p n "rci_fresh" [] m1 with
  | none => rw [h2] at hw; simp at hw
  | some t2 =>
  obtain ⟨r2, m2⟩ := t2
  rw [h2, bW_some] at hw
  obtain ⟨hI2, hM2, hs2, -, -, -, -⟩ := freshCall hL hI0 h2
  cases n with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ n =>
  cases h3 : callW p (n + 1) "rci_ci" [ciOff + u64W rom (ciOff + 8 * (10 + id))] m2 with
  | none => simp only [List.headD_cons] at hw; rw [h3] at hw; simp at hw
  | some t3 =>
  obtain ⟨r3, m3⟩ := t3
  simp only [List.headD_cons] at hw
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hfit : ciFits (romCiVals[id.toNat]'(by simp [romCiVals]; omega)) = true :=
    List.all_eq_true.mp romCiVals_fit _ (List.getElem_mem _)
  obtain ⟨memo', ici, a', hrun, hI3, -, -, -, -, -, -, hH⟩ :=
    ci_rel hL hr dn [] ∅ _ hfit n m2 a _ rest' r3 m3 hI2 hM2 hs2 hpos h3
  refine ⟨ici, a', ?_, hI3.stage hS, hI3.grow, ?_⟩
  · rw [romCiT_eq id.toNat hid]
    simp only [ConRon.Arena.internCI]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · unfold decRCI
    simp only [List.headD_cons]
    exact hH.decB (fun i hi => hi.2) (fun _ h => h.elim)

end entries

end L.Rom
