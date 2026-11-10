module

import ConAgua.Rom.CIReadRefData
import ConAgua.Rom.CIReadRefNames
import ConAgua.Rom.ReadScr
public import ConAgua.Rom.CIReadRefCI
import ConAgua.L.WordOff
import ConAgua.Arena.DeclNatCv

@[expose] public section

/-!
# The ROM constant readers refine the twin (helper `decls4-rom`)

The six entries of `CIRead.lean` against `CIReadSpec.lean`'s statements: `rom_ci`, `rom_cv`,
`rom_expr_pin`, `rom_and_pin`, and `rom_basis_decls`/`rom_basis_decls_a` for the four kinds
`basisPinHit` tries (`eqK`, `natK`, `emptyK`, `falseK`) and the quotient kind (`4`). The quotient
block holds `Quot`, whose `sortZ` is `.ifAllZero [u]`; `decCaps` reads the name `u` back through
`dn`, which `StageR` does not relate to the store, so its refinement starts from a well-formed
twin state in which `dn` reads `u` back (`NamesDn dn a quotNames`, `CIReadRefCaps.lean`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-! ## The region's entries and the twin's values, by index -/

theorem ciEntries_ci (i : Nat) (hi : i < 7) :
    ciEntries[5 + i]'(by rw [ciEntries_len]; omega) = (encCI [] (romCiVals[i]'(by simp [romCiVals]; omega))).1 := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl
  | _ + 7, h => exact absurd h (by omega)

theorem ciEntries_cv (i : Nat) (hi : i < 10) :
    ciEntries[12 + i]'(by rw [ciEntries_len]; omega) = (encCV [] (romCvVals[i]'(by simp [romCvVals]; omega))).1 := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl
  | _ + 10, h => exact absurd h (by omega)

theorem ciEntries_ex (i : Nat) (hi : i < 2) :
    ciEntries[22 + i]'(by rw [ciEntries_len]; omega) =
      (encExprM [] (romExprVals[i]'(by simp [romExprVals]; omega))).1 := by
  match i, hi with
  | 0, _ | 1, _ => rfl
  | _ + 2, h => exact absurd h (by omega)

theorem ciEntries_b (i : Nat) (hi : i < 5) :
    ciEntries[i]'(by rw [ciEntries_len]; omega) =
      encBlock (ConLeche.BasisKind.decls (basisKinds[i]'(by simp [basisKinds]; omega))) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem ciEntries_and : ciEntries[24]'(by rw [ciEntries_len]; omega) = encBlock ConLeche.andPin := rfl

theorem romCiT_eq (i : Nat) (hi : i < 7) :
    L.Ind.romCiT i = ConRon.Arena.internCI (romCiVals[i]'(by simp [romCiVals]; omega)) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl
  | _ + 7, h => exact absurd h (by omega)

theorem romCvT_eq (i : Nat) (hi : i < 10) :
    romCvT i = ConRon.Arena.internCV (romCvVals[i]'(by simp [romCvVals]; omega)) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl
  | _ + 10, h => exact absurd h (by omega)

theorem romExprT_eq (i : Nat) (hi : i < 2) :
    romExprT i = ConRon.Arena.internExpr (romExprVals[i]'(by simp [romExprVals]; omega)) := by
  match i, hi with
  | 0, _ | 1, _ => rfl
  | _ + 2, h => exact absurd h (by omega)

theorem basisOfW_eq (i : Nat) (hi : i < 5) : basisOfW i = basisKinds[i]'(by simp [basisKinds]; omega) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem word_add_toNat (c : Nat) (w : Word) (h : c + w.toNat < 2 ^ 64) :
    (UInt64.ofNat c + w).toNat = c + w.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega

/-! ## The entries -/

/-- A model that answers its callee's first two words. -/
theorem ntBW_pair {mo : Option (List Word × Mem)} {r : List Word} {m' : Mem}
    (hw : ntBW mo (fun r m1 => some ([r.headD 0, r.tail.headD 0], m1)) = some (r, m')) :
    ∃ r1, mo = some (r1, m') ∧ r = [r1.headD 0, r1.tail.headD 0] := by
  match mo, hw with
  | some (r1, m1), hw =>
    simp only [bW_some, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw; exact ⟨r1, rfl, rfl⟩

section entries
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom) (rest : List UInt8)
  (hrom : rom = romData ++ rest)
include hL hr hrom

/-- **`rom_ci(id)` refines `romCiT id`.** -/
@[refines ConRon.Arena.natA ConRon.Arena.iffA ConRon.Arena.iffIntroA
  ConRon.Arena.iffRecA ConRon.Arena.nonemptyA ConRon.Arena.nonemptyIntroA ConRon.Arena.nonemptyRecA]
theorem romCiRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomCiRef p dn vis fe := by
  intro id hid n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => ciEntryW p n mq id) (ciEntry_specW rom p hL n · id) hc
  unfold ciEntryW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  have h5 : (5 + id).toNat = 5 + id.toNat := word_add_toNat 5 id (by omega)
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom (5 + id) (by omega)
  simp only [h5, ciEntries_ci id.toNat hid] at hpos
  have hI0 := RInv.refl hS
  obtain ⟨r2, m2, h2, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨hI2, hM2, hs2, -, -, -, -, -⟩ := freshCall hL hI0 h2
  cases n with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ n =>
  simp only [List.headD_cons] at hw
  obtain ⟨r3, m3, h3, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hfit : ciFits (romCiVals[id.toNat]'(by simp [romCiVals]; omega)) = true :=
    List.all_eq_true.mp romCiVals_fit _ (List.getElem_mem _)
  obtain ⟨memo', ici, a', hrun, hI3, -, -, -, -, -, -, hH⟩ :=
    ci_rel hL hr [] ∅ _ hfit n m2 a _ rest' r3 m3 hI2 hM2 hs2 hpos h3
  refine ⟨ici, a', ?_, hI3.stage hS, hI3.grow, ?_⟩
  · rw [romCiT_eq id.toNat hid]
    simp only [ConRon.Arena.internCI]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · unfold decRCI
    simp only [List.headD_cons]
    exact hH.decB (fun _ h => h.elim)

/-- **`rom_cv(id)` refines `romCvT id`.** -/
@[refines ConRon.Arena.propextA ConRon.Arena.choiceA ConRon.Arena.trueCvA ConRon.Arena.trueIntroCvA
  ConRon.Arena.trustCompilerA ConRon.Arena.boolCvA ConRon.Arena.reduceNatCvA ConRon.Arena.reduceBoolCvA
  ConRon.Arena.ofReduceNatA ConRon.Arena.ofReduceBoolA]
theorem romCvRef_of (vis : Word) (fe : IFEnv) : RomCvRef p vis fe := by
  intro id hid n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cvEntryW p n mq id) (cvEntry_specW rom p hL n · id) hc
  unfold cvEntryW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  have h12 : (12 + id).toNat = 12 + id.toNat := word_add_toNat 12 id (by omega)
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom (12 + id) (by omega)
  simp only [h12, ciEntries_cv id.toNat hid] at hpos
  have hI0 := RInv.refl hS
  obtain ⟨r2, m2, h2, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨hI2, ho2, ht2, -, -, -, -, -, -⟩ := hI0.erAlloc (erAllocCall hL h2)
  obtain ⟨r3, m3, h3, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨hI3, hM3, hs3, -, -, ht3, -, -⟩ := freshCall hL hI2 h3
  cases n with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ n =>
  simp only [List.headD_cons] at hw
  obtain ⟨r4, m4, h4, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hfit : cvFits (romCvVals[id.toNat]'(by simp [romCvVals]; omega)) = true :=
    List.all_eq_true.mp romCvVals_fit _ (List.getElem_mem _)
  replace ht2 : erT m2 = erT m1 + 4 := ht2
  have hgo := hI0.erT_mono
  obtain ⟨memo', icv, a', hrun, hI4, -, -, -, -, ht4, -, hH⟩ :=
    cv_rel hL hr [] ∅ _ hfit n m3 a _ _ rest' r4 m4 hI3 hM3 hs3 hpos (by omega) (by omega) h4
  refine ⟨icv, a', ?_, hI4.stage hS, hI4.grow, ?_⟩
  · rw [romCvT_eq id.toNat hid]
    simp only [ConRon.Arena.internCV]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · unfold decRCV
    simp only [List.headD_cons]
    exact hH.decB (fun _ h => h.elim)

/-- **`rom_expr_pin(id)` refines `romExprT id`.** -/
@[refines ConRon.Arena.reduceNatDeclPin ConRon.Arena.reduceBoolDeclPin]
theorem romExprPinRef_of (vis : Word) (fe : IFEnv) : RomExprPinRef p vis fe := by
  intro id hid n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => exprPinW p n mq id) (exprPin_specW rom p hL n · id) hc
  unfold exprPinW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  have h22 : (22 + id).toNat = 22 + id.toNat := word_add_toNat 22 id (by omega)
  obtain ⟨rest', hpos⟩ := slot_pos hr rest hrom (22 + id) (by omega)
  simp only [h22, ciEntries_ex id.toNat hid] at hpos
  have hI0 := RInv.refl hS
  obtain ⟨r2, m2, h2, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨hI2, hM2, hs2, -, -, -, -, -⟩ := freshCall hL hI0 h2
  simp only [List.headD_cons] at hw
  obtain ⟨r3, m3, h3, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hfit : exprFits (romExprVals[id.toNat]'(by simp [romExprVals]; omega)) = true :=
    List.all_eq_true.mp romExprVals_fit _ (List.getElem_mem _)
  obtain ⟨memo', a', hrun, hA3, hk3, -, hlt, -, hf3, -, hmo3⟩ :=
    exprCall hL hr _ hfit hI2.arena hI2.mode (seen := []) (memo := ∅) hM2 hpos (by rw [hs2]; decide)
      (by have := hI2.ok.ctl; omega) h3
  obtain ⟨hI3, -⟩ := hI2.expr hA3 hmo3 hf3 hk3 (L.Arena.internExprGo_ks _ _ _ _ _ hrun)
  refine ⟨decI (r3.headD 0), a', ?_, hI3.stage hS, hI3.grow, ?_⟩
  · rw [romExprT_eq id.toNat hid]
    simp only [ConRon.Arena.internExpr, Frontend.internExpr]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · exact ⟨by simpa using hlt, by simp⟩

/-- **`rci_block(s)` refines `internCIList`** of the block at slot `s`. -/
@[refines_part ConRon.Arena.internCIList "the blocks of the ROM region"]
theorem blockCall (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (s : Word)
    (hs : s.toNat < 25) (cs : List ConLeche.ConstantInfo)
    (hcs : ciEntries[s.toNat]'(by rw [ciEntries_len]; exact hs) = encBlock cs)
    (hfit : cs.all ciFits = true) (hcl : cs.length < 2 ^ 63) {n : Nat} {m m' : Mem} {a : AState}
    {r : List Word} (hS : StageR vis fe m a) (hc : callW p n "rci_block" [s] m = some (r, m')) :
    ∃ (ics : List IConstantInfo) (a' : AState), (ConRon.Arena.internCIList cs).run a = .ok (ics, a') ∧
      KeepPost vis fe (decRBlk dn) m m' a' r ics := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => blockW p n mq s) (block_specW rom p hL n · s) hc
  unfold blockW at hw
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨rfl, rfl⟩ := slotCall hL h1
  simp only [List.headD_cons] at hw
  replace hw := u64_some hL hw
  simp only [List.headD_cons] at hw
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
  have hcN : (UInt64.ofNat cs.length).toNat = cs.length := L.toNat_ofNat_of_lt (by omega)
  have hI0 := RInv.refl hS
  obtain ⟨r2, m2, h2, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨hI2, hM2, hs2, -, -, -, hi2, -⟩ := freshCall hL hI0 h2
  obtain ⟨r3, m3, h3, hw⟩ := L.Ind.ntBW_some hw
  have hal := iwAllocCall hL h3
  obtain ⟨hI3, ho3, ht3, -, -, -⟩ := hI2.iwAlloc hal
  obtain ⟨-, rfl, -⟩ := allocW_facts hal hI2.ok.iwSize
  have hf3 := allocMem_frame m2 (UInt64.ofNat cs.length)
  have hM3 := hM2.frameG hf3 (by decide) (by decide)
  have hs3 : stkTop (allocMem m2 (UInt64.ofNat cs.length)) = stkTop m2 := hf3.ctl 131 (by decide)
  obtain ⟨r4, m4, h4, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hq8 : (ciOff + u64W rom (ciOff + 8 * s) + 8).toNat = (ciOff + u64W rom (ciOff + 8 * s)).toNat + 8 := by
    rw [UInt64.toNat_add, show (8 : Word).toNat = 8 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hd8 : rom.drop (ciOff + u64W rom (ciOff + 8 * s) + 8).toNat = (encCIsM [] cs).1 ++ rest' := by
    rw [hq8, ← List.drop_drop, hpos, encBlock, List.append_assoc]; simp [u64B]
  have hlt := hI2.iw_lt
  obtain ⟨memo', ics, a', hrun, hlen, hI4, -, -, -, -, -, hik4, hB4⟩ :=
    blockTo_rel hL hr cs hfit [] ∅ n _ a _ (r3.headD 0) _ rest' r4 m4 hI3 hM3 (by rw [hs3, hs2])
      hd8 hcN (by rw [ho3, hi2]; exact Nat.le_refl _) (by rw [ho3, ht3, hcN]; exact Nat.le_refl _) h4
  refine ⟨ics, a', ?_, hI4.stage hS, hI4.grow, ?_, rfl⟩
  · simp only [ConRon.Arena.internCIList]
    rw [run_bind_of _ _ _ _ _ hrun]; rfl
  · simp only [List.headD_cons, List.tail_cons, hcN]
    rw [← hlen]
    have hH := holds_mapM_range (m := m4) (SE := fun i => erT (allocMem m2 (UInt64.ofNat cs.length)) ≤ i ∧
        i < erT m4) (SI := fun i => (r3.headD 0).toNat ≤ i ∧ i < (r3.headD 0).toNat + ics.length)
      (g := fun m j => do decCI (erA m) (← iwN m ((r3.headD 0).toNat + j))) ics (fun j hj => by
        obtain ⟨w, hw1, hw2⟩ := hB4 j hj
        intro m'' h1 h2
        have e := (h2 _ ⟨by omega, by omega⟩).trans hw1
        have ed := hw2 m'' h1 (fun _ h => h.elim)
        simp only [iwN, nat?, e, Option.map_some, Option.bind_eq_bind, Option.bind_some]
        exact ed)
    exact hH.decB (fun i hi => by rw [hik4.1, ht3, ← ho3]; omega)

/-- **`rom_and_pin()` refines `andPinDecls`.** -/
@[refines ConRon.Arena.andPinDecls]
theorem romAndPinRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomAndPinRef p dn vis fe := by
  intro n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => andPinW p n mq) (andPin_specW rom p hL n ·) hc
  unfold andPinW at hw
  obtain ⟨r1, h1, rfl⟩ := ntBW_pair hw
  obtain ⟨ics, a', hrun, hS', hg, hdec, hr1⟩ :=
    blockCall hL hr rest hrom dn vis fe 24 (by decide) ConLeche.andPin ciEntries_and andPin_fit.1
      andPin_fit.2 hS h1
  refine ⟨ics, a', hrun, hS', hg, ?_, rfl⟩
  simpa using hdec

/-- The raw basis block of a kind below `5`. -/
theorem romBasisRef_lt5 (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Word)
    (hk : k.toNat < 5) :
    RomRef p "rom_basis_decls" [k] (StageR vis fe) (BasisKind.decls (basisOfW k.toNat))
      (KeepPost vis fe (decRBlk dn)) := by
  intro n m a r m' hS hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => basisW p n mq k) (basis_specW rom p hL n · k) hc
  unfold basisW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  obtain ⟨r1, h1, rfl⟩ := ntBW_pair hw
  obtain ⟨hf1, hf2⟩ := basisDecls_fit k.toNat hk
  obtain ⟨ics, a', hrun, hS', hg, hdec, hr1⟩ :=
    blockCall hL hr rest hrom dn vis fe k (by omega) _ (ciEntries_b k.toNat hk) hf1 hf2 hS h1
  refine ⟨ics, a', ?_, hS', hg, ?_, rfl⟩
  · rw [basisOfW_eq k.toNat hk]; exact hrun
  · simpa using hdec

/-- The raw basis block of a kind `basisPinHit` tries (`eqK`, `natK`, `emptyK`, `falseK`). -/
@[refines_part ConRon.Arena.BasisKind.decls "the four kinds basisPinHit tries"]
theorem romBasisRef_lt4 (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomBasisRef p dn vis fe := fun k hk => romBasisRef_lt5 hL hr rest hrom dn vis fe k (by omega)

/-- **The raw quotient block** (`rom_basis_decls(4)`). -/
@[refines_part ConRon.Arena.BasisKind.decls "the quotient block"]
theorem romBasisRef_quot (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomQuotRef p dn vis fe := fun n m a r m' hpre hc =>
  romBasisRef_lt5 hL hr rest hrom dn vis fe 4 (by decide) n m a r m' hpre.1 hc

end entries

/-! ## All of them -/

/-- **The readers refine the twin**, for a program whose readers read the constant data. -/
theorem romRefs_of (p : Prog) (h : RomReady p) : RomRefs p := by
  have hL : RomCIProg romData p := by rw [← romDataLit_eq]; exact h
  have hr : RomOK romData := romData_len
  have hrom : romData = romData ++ [] := by simp
  exact ⟨romCiRef_of hL hr [] hrom, romCvRef_of hL hr [] hrom, romExprPinRef_of hL hr [] hrom,
    romBasisRef_lt4 hL hr [] hrom, romBasisRef_quot hL hr [] hrom, romAndPinRef_of hL hr [] hrom⟩

end L.Rom
