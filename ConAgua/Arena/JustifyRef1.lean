module

public import ConAgua.Arena.JustifyModels
public import ConAgua.Arena.PinListRef
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.RecLayout.CIDec
import ConRon.Bridge.Specs
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# The justification's comparisons refine the twin's (lane compare, helper compare-cone)

`levels_renaming`, `same_cv_up_to_levels`, `tbl_eq`/`tbl_beq_p`, `is_stmt_kind`, `copy_b`,
`refines_b` against `levelsRenaming`, `sameCvUpToLevels`, `tableBeqP`,
`IConstantInfo.isStmtKind`, `copyB`, `refinesB`, under `StageT` (the job's stage relation with
the twin's invariants), in the shape of `pinCopyOk_sim` (`PinListRef.lean`): the generated model
walked callee by callee, each callee by its refinement (`cvLps_sim`, `slNodup_refines`,
`ciEqB_ok`, the pin at new names `CiAtLpsSim`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind

/-- **The program the comparisons run in**: the pin comparison's (`PinListLProg`) and this
module's functions. -/
structure JfCmpProg (p : Prog) : Prop where
  pl : PinListLProg p
  lr : p.lookup "levels_renaming" = some levelsRenamingL
  sc : p.lookup "same_cv_up_to_levels" = some sameCvUpToLevelsL
  te : p.lookup "tbl_eq" = some tblEqL
  tb : p.lookup "tbl_beq_p" = some tblBeqPL
  sk : p.lookup "is_stmt_kind" = some isStmtKindL
  cb : p.lookup "copy_b" = some copyBL
  rb : p.lookup "refines_b" = some refinesBL

section lr
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`levels_renaming(x + CI.cv, y + CI.cv)` is `levelsRenaming`** of the two records' level
parameters: the stage kept, only `IW` grown, the records untouched. -/
theorem levelsRenaming_ok (hP : JfCmpProg p) {n : Nat} {m m' : Mem} {a : AState} {x y : Word}
    {r : List Word} {cx cy : IConstantInfo} (hT : StageT dn vis fe m a)
    (hx : decCI (erecP m) x.toNat = some cx) (hy : decCI (erecP m) y.toNat = some cy)
    (h : callW p n "levels_renaming" [x + CI.cv, y + CI.cv] m = some (r, m')) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ erecP m' = erecP m ∧ (∀ z, erRd m' z = erRd m z) ∧
      (r.headD 0 ≠ 0 ↔ levelsRenaming cx.toConstantVal.levelParams cy.toConstantVal.levelParams = true) := by
  have hQ := hP.pl.basis.rules.toQuotAtProg
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (levelsRenaming_specW p hP.lr n _ (x + CI.cv) (y + CI.cv)) h
  cases n with
  | zero => simp [levelsRenamingW] at hW
  | succ n =>
  simp only [levelsRenamingW] at hW
  obtain ⟨-, -, hslx, hlenx, -⟩ := decCV_rd_ci (erRdOK m) (decCI_cv hx)
  obtain ⟨-, -, hsly, hleny, -⟩ := decCV_rd_ci (erRdOK m) (decCI_cv hy)
  have hlx := hslice?_lenR hslx
  have hly := hslice?_lenR hsly
  have hlen : (erRd m (x + CI.cv + CV.lpsLen) ≠ erRd m (y + CI.cv + CV.lpsLen)) ↔
      ¬ (cx.toConstantVal.levelParams.length = cy.toConstantVal.levelParams.length) := by
    rw [hlx, hly, UInt64.add_assoc, UInt64.add_assoc]
    exact not_congr ⟨fun e => by rw [e], fun e => UInt64.toNat_inj.mp e⟩
  by_cases hl : erRd m (x + CI.cv + CV.lpsLen) ≠ erRd m (y + CI.cv + CV.lpsLen)
  · rw [ite_eq_left hl] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨hT, IWGrow.refl _, rfl, fun _ => rfl, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, levelsRenaming,
      Bool.and_eq_true, beq_iff_eq, not_and]
    exact fun e _ => absurd e.1 (hlen.mp hl)
  rw [ite_eq_right hl] at hW
  have hl' : cx.toConstantVal.levelParams.length = cy.toConstantVal.levelParams.length :=
    Classical.not_not.mp (mt hlen.mpr hl)
  -- `cv_lps(x + CI.cv)`, `sl_nodup`
  cases h1 : callW p n "cv_lps" [x + CI.cv] m with
  | none => rw [h1] at hW; simp [levelsRenamingW.k_cv_lps] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [levelsRenamingW.k_cv_lps] at hW
  obtain ⟨hT1, hg1, he1, hrd1, hn1⟩ := cvLps_sim hP.pl hT hx h1
  obtain ⟨ws1, hws1, hwsd1, hwH1⟩ := slR_of_decHL m1 _ _ _ hn1.dec
    (by have := hn1.bound; have := (rdW (m1.arr64 CTL) 200).toNat_lt; simp only [iwTop] at *; omega)
  simp only [UInt64.ofNat_toNat] at hws1
  cases h2 : callW p n "sl_nodup" [r1.headD 0, r1.tail.headD 0] m1 with
  | none => rw [h2] at hW; simp [levelsRenamingW.k_sl_nodup] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨s2, rfl, -, hm2, hnd2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (slNodup_refines p hQ.slContains hQ.slNodup n _ _ _ ws1 hws1 hwH1) h2
  rw [h2] at hW; simp only [levelsRenamingW.k_sl_nodup] at hW
  simp only at hm2
  rw [← hwsd1] at hnd2
  have hT2 : StageT dn vis fe s2.mem a := by rw [hm2]; exact hT1
  by_cases hz : r2.headD 0 = 0
  · rw [ite_eq_left hz] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    rw [← e]
    refine ⟨hT2, by rw [hm2]; exact hg1, by rw [hm2]; exact he1, fun z => by rw [hm2]; exact hrd1 z, ?_⟩
    have hb : nameNodup cx.toConstantVal.levelParams = false := by rw [← hnd2, hz]; rfl
    simp [levelsRenaming, hb]
  rw [ite_eq_right hz] at hW
  have hy1 : decCI (erecP s2.mem) y.toNat = some cy := by rw [hm2, he1]; exact hy
  cases h3 : callW p n "cv_lps" [y + CI.cv] s2.mem with
  | none => rw [h3] at hW; simp [levelsRenamingW.k_cv_lps_2] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at hW; simp only [levelsRenamingW.k_cv_lps_2] at hW
  obtain ⟨hT3, hg3, he3, hrd3, hn3⟩ := cvLps_sim hP.pl hT2 hy1 h3
  obtain ⟨ws3, hws3, hwsd3, hwH3⟩ := slR_of_decHL m3 _ _ _ hn3.dec
    (by have := hn3.bound; have := (rdW (m3.arr64 CTL) 200).toNat_lt; simp only [iwTop] at *; omega)
  simp only [UInt64.ofNat_toNat] at hws3
  cases h4 : callW p n "sl_nodup" [r3.headD 0, r3.tail.headD 0] m3 with
  | none => rw [h4] at hW; simp [levelsRenamingW.k_sl_nodup_2] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  obtain ⟨s4, rfl, -, hm4, hnd4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slNodup_refines p hQ.slContains hQ.slNodup n _ _ _ ws3 hws3 hwH3) h4
  rw [h4] at hW; simp only [levelsRenamingW.k_sl_nodup_2] at hW
  simp only at hm4
  rw [← hwsd3] at hnd4
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  rw [← e, hm4]
  refine ⟨hT3, hg1.trans (by rw [← hm2]; exact hg3), by rw [he3, hm2, he1],
    fun z => by rw [hrd3, hm2, hrd1], ?_⟩
  have hb2 : nameNodup cx.toConstantVal.levelParams = true := by
    rw [← hnd2]; simpa using hz
  simp only [levelsRenaming, hl', beq_self_eq_true, hb2, Bool.true_and, ← hnd4, bne_iff_ne, ne_eq, List.headD_cons]

end lr

end L.Arena
