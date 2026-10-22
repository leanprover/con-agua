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

/-- **`rom_cv(id)` refines `romCvT id`.** -/
theorem romCvRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomCvRef p dn vis fe := by
  intro id hid n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cvEntryW p n mq id) (cvEntry_specW rom p hL n · id) hc
  unfold cvEntryW at hw
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  cases h1 : callW p n "rci_slot" [18 + id] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  have h18 : (18 + id).toNat = 18 + id.toNat := word_add_toNat 18 id (by omega)
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom (18 + id) (by omega)
  simp only [h18, ciEntries_cv id.toNat hid] at hpos
  have hI0 := RInv.refl hS
  cases h2 : callW p n "erec_alloc" [4] m1 with
  | none => rw [h2] at hw; simp at hw
  | some t2 =>
  obtain ⟨r2, m2⟩ := t2
  rw [h2, bW_some] at hw
  obtain ⟨hI2, ho2, ht2, -, -, -⟩ := hI0.erAlloc (erAllocCall hL h2)
  cases h3 : callW p n "rci_fresh" [] m2 with
  | none => rw [h3] at hw; simp at hw
  | some t3 =>
  obtain ⟨r3, m3⟩ := t3
  rw [h3, bW_some] at hw
  obtain ⟨hI3, hM3, hs3, -, -, ht3, -⟩ := freshCall hL hI2 h3
  cases n with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ n =>
  simp only [List.headD_cons] at hw
  cases h4 : callW p (n + 1) "rci_cv" [ciOff + u64W rom (ciOff + 8 * (18 + id)), r2.headD 0] m3 with
  | none => rw [h4] at hw; simp at hw
  | some t4 =>
  obtain ⟨r4, m4⟩ := t4
  rw [h4, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hfit : cvFits (romCvVals[id.toNat]'(by simp [romCvVals]; omega)) = true :=
    List.all_eq_true.mp romCvVals_fit _ (List.getElem_mem _)
  replace ht2 : erTop m2 = erTop m1 + 4 := ht2
  obtain ⟨memo', icv, a', hrun, hI4, -, -, -, -, ht4, -, hH⟩ :=
    cv_rel hL hr [] ∅ _ hfit n m3 a _ _ rest' r4 m4 hI3 hM3 hs3 hpos (by omega) (by omega) h4
  refine ⟨icv, a', ?_, hI4.stage hS, hI4.grow, ?_⟩
  · rw [romCvT_eq id.toNat hid]
    simp only [ConRon.Arena.internCV]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · unfold decRCV
    simp only [List.headD_cons]
    exact hH.decB (fun i hi => by omega) (fun _ h => h.elim)

/-- **`rom_expr_pin(id)` refines `romExprT id`.** -/
theorem romExprPinRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomExprPinRef p dn vis fe := by
  intro id hid n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => exprPinW p n mq id) (exprPin_specW rom p hL n · id) hc
  unfold exprPinW at hw
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  cases h1 : callW p n "rci_slot" [28 + id] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  have h28 : (28 + id).toNat = 28 + id.toNat := word_add_toNat 28 id (by omega)
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom (28 + id) (by omega)
  simp only [h28, ciEntries_ex id.toNat hid] at hpos
  have hI0 := RInv.refl hS
  cases h2 : callW p n "rci_fresh" [] m1 with
  | none => rw [h2] at hw; simp at hw
  | some t2 =>
  obtain ⟨r2, m2⟩ := t2
  rw [h2, bW_some] at hw
  obtain ⟨hI2, hM2, hs2, -, -, -, -⟩ := freshCall hL hI0 h2
  simp only [List.headD_cons] at hw
  cases h3 : callW p n "rom_expr" [ciOff + u64W rom (ciOff + 8 * (28 + id))] m2 with
  | none => rw [h3] at hw; simp at hw
  | some t3 =>
  obtain ⟨r3, m3⟩ := t3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hfit : exprFits (romExprVals[id.toNat]'(by simp [romExprVals]; omega)) = true :=
    List.all_eq_true.mp romExprVals_fit _ (List.getElem_mem _)
  obtain ⟨memo', a', hrun, hA3, hk3, -, hlt, -, hf3, -⟩ :=
    exprCall hL hr _ hfit hI2.arena (seen := []) (memo := ∅) hM2 hpos (by rw [hs2]; decide)
      (by have := hI2.ok.2.2.2.2; omega) h3
  obtain ⟨hI3, -⟩ := hI2.expr hA3 hf3 hk3
  refine ⟨decI (r3.headD 0), a', ?_, hI3.stage hS, hI3.grow, ?_⟩
  · rw [romExprT_eq id.toNat hid]
    simp only [ConRon.Arena.internExpr, Frontend.internExpr]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · exact ⟨by simpa using hlt, by simp⟩

/-- **`rci_block(s)` refines `internCIList`** of the block at slot `s`. -/
theorem blockCall (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (s : Word)
    (hs : s.toNat < 31) (cs : List ConLeche.ConstantInfo)
    (hcs : ciEntries[s.toNat]'(by rw [ciEntries_len]; exact hs) = encBlock cs)
    (hfit : cs.all ciFits = true) (hcl : cs.length < 2 ^ 63) {n : Nat} {m m' : Mem} {a : AState}
    {r : List Word} (hS : StageR dn vis fe m a) (hc : callW p n "rci_block" [s] m = some (r, m')) :
    ∃ (ics : List IConstantInfo) (a' : AState), (ConRon.Arena.internCIList cs).run a = .ok (ics, a') ∧
      KeepPost dn vis fe (decRBlk dn) m m' a' r ics := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => blockW p n mq s) (block_specW rom p hL n · s) hc
  unfold blockW at hw
  cases h1 : callW p n "rci_slot" [s] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  simp only [List.headD_cons] at hw
  replace hw := rdU_some hL hw
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom s hs
  rw [hcs] at hpos
  have hrl := hr; simp only [RomOK] at hrl
  have hlenB := drop_len rom _ (u64B cs.length) _ (by rw [hpos, encBlock, List.append_assoc])
    (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil] at hlenB
  have hc0 := u64_at hr (ciOff + u64W rom (ciOff + 8 * s)) 0 [] cs.length _
    (by rw [hpos, encBlock, List.append_assoc]; rfl) (by simp) (by omega)
  simp only [UInt64.add_zero] at hc0
  rw [hc0] at hw
  have hcN : (UInt64.ofNat cs.length).toNat = cs.length := ofNat_toNat_lt (by omega)
  have hI0 := RInv.refl hS
  cases h2 : callW p n "rci_fresh" [] m1 with
  | none => rw [h2] at hw; simp at hw
  | some t2 =>
  obtain ⟨r2, m2⟩ := t2
  rw [h2, bW_some] at hw
  obtain ⟨hI2, hM2, hs2, -, -, -, hi2⟩ := freshCall hL hI0 h2
  cases h3 : callW p n "iw_alloc" [UInt64.ofNat cs.length] m2 with
  | none => rw [h3] at hw; simp at hw
  | some t3 =>
  obtain ⟨r3, m3⟩ := t3
  rw [h3, bW_some] at hw
  have hal := iwAllocCall hL h3
  obtain ⟨hI3, ho3, ht3, -, -, -⟩ := hI2.iwAlloc hal
  obtain ⟨-, rfl, -⟩ := allocW_facts hal hI2.ok.2.2.1
  have hf3 := allocMem_frame m2 (UInt64.ofNat cs.length)
  have hM3 := hM2.frameG hf3 (by decide) (by decide)
  have hs3 : stkTop (allocMem m2 (UInt64.ofNat cs.length)) = stkTop m2 := hf3.2.1 131 (by decide)
  cases h4 : callW p n "rci_block_to" [ciOff + u64W rom (ciOff + 8 * s) + 8, r3.headD 0,
      UInt64.ofNat cs.length] (allocMem m2 (UInt64.ofNat cs.length)) with
  | none => rw [h4] at hw; simp at hw
  | some t4 =>
  obtain ⟨r4, m4⟩ := t4
  rw [h4, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hq8 : (ciOff + u64W rom (ciOff + 8 * s) + 8).toNat = (ciOff + u64W rom (ciOff + 8 * s)).toNat + 8 := by
    rw [UInt64.toNat_add, show (8 : Word).toNat = 8 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hd8 : rom.drop (ciOff + u64W rom (ciOff + 8 * s) + 8).toNat = (encCIsM [] cs).1 ++ rest' := by
    rw [hq8, ← List.drop_drop, hpos, encBlock, List.append_assoc]; simp [u64B]
  have hlt := hI2.iw_lt
  obtain ⟨memo', ics, a', hrun, hlen, hI4, -, -, -, -, -, hik4, hB4⟩ :=
    blockTo_rel hL hr dn cs hfit [] ∅ n _ a _ (r3.headD 0) _ rest' r4 m4 hI3 hM3 (by rw [hs3, hs2])
      hd8 hcN (by rw [ho3, hi2]; exact Nat.le_refl _) (by rw [ho3, ht3, hcN]; exact Nat.le_refl _) h4
  refine ⟨ics, a', ?_, hI4.stage hS, hI4.grow, ?_, rfl⟩
  · simp only [ConRon.Arena.internCIList]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · simp only [List.headD_cons, List.tail_cons, hcN]
    rw [← hlen]
    have hH := holds_mapM_range (m := m4) (SE := fun i => erTop (allocMem m2 (UInt64.ofNat cs.length)) ≤ i ∧
        i < erTop m4) (SI := fun i => (r3.headD 0).toNat ≤ i ∧ i < (r3.headD 0).toNat + ics.length)
      (g := fun m j => do decCI (erA m) dn (← iwN m ((r3.headD 0).toNat + j))) ics (fun j hj => by
        obtain ⟨w, hw1, hw2⟩ := hB4 j hj
        intro m'' h1 h2
        have e := (h2 _ ⟨by omega, by omega⟩).trans hw1
        have ed := hw2 m'' h1 (fun _ h => h.elim)
        simp only [iwN, nat?, e, Option.map_some, Option.bind_eq_bind, Option.bind_some]
        exact ed)
    exact hH.decB (fun i hi => hi.2) (fun i hi => by rw [hik4.1, ht3, ← ho3]; omega)

/-- **`rom_and_pin()` refines `andPinDecls`.** -/
theorem romAndPinRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomAndPinRef p dn vis fe := by
  intro n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => andPinW p n mq) (andPin_specW rom p hL n ·) hc
  unfold andPinW at hw
  cases h1 : callW p n "rci_block" [30] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨ics, a', hrun, hS', hg, hdec, hr1⟩ :=
    blockCall hL hr rest hrom dn vis fe 30 (by decide) ConLeche.andPin ciEntries_and andPin_fit.1
      andPin_fit.2 hS h1
  refine ⟨ics, a', hrun, hS', hg, ?_, rfl⟩
  simpa using hdec

/-- The raw basis block of a kind `basisPinHit` tries (`eqK`, `natK`, `emptyK`, `falseK`). -/
theorem romBasisRef_lt4 (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Word)
    (hk : k.toNat < 4) :
    RomRef p "rom_basis_decls" [k] (StageR dn vis fe) (BasisKind.decls (basisOfW k.toNat))
      (KeepPost dn vis fe (decRBlk dn)) := by
  intro n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => basisW p n mq k 0) (basis_specW rom p hL n · k) hc
  unfold basisW at hw
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  cases h1 : callW p n "rci_block" [k + 0] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hk0 : (k + 0).toNat = k.toNat := by simp
  obtain ⟨hf1, hf2⟩ := basisDecls_fit k.toNat hk
  obtain ⟨ics, a', hrun, hS', hg, hdec, hr1⟩ :=
    blockCall hL hr rest hrom dn vis fe (k + 0) (by omega) _
      (by simp only [hk0]; exact ciEntries_b k.toNat (by omega)) hf1 hf2 hS h1
  refine ⟨ics, a', ?_, hS', hg, ?_, rfl⟩
  · rw [basisOfW_eq k.toNat (by omega)]; exact hrun
  · simpa using hdec

/-- The annotated basis block of a kind `basisPinHit` tries. -/
theorem romBasisARef_lt4 (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Word)
    (hk : k.toNat < 4) :
    RomRef p "rom_basis_decls_a" [k] (StageR dn vis fe) (BasisKind.declsA (basisOfW k.toNat))
      (KeepPost dn vis fe (decRBlk dn)) := by
  intro n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => basisW p n mq k 5) (basisA_specW rom p hL n · k) hc
  unfold basisW at hw
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  cases h1 : callW p n "rci_block" [k + 5] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hk5 : (k + 5).toNat = 5 + k.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hf1, hf2⟩ := basisDeclsA_fit k.toNat hk
  obtain ⟨ics, a', hrun, hS', hg, hdec, hr1⟩ :=
    blockCall hL hr rest hrom dn vis fe (k + 5) (by omega) _
      (by simp only [hk5]; exact ciEntries_bA k.toNat (by omega)) hf1 hf2 hS h1
  refine ⟨ics, a', ?_, hS', hg, ?_, rfl⟩
  · rw [basisOfW_eq k.toNat (by omega)]; exact hrun
  · simpa using hdec

end entries

end L.Rom
