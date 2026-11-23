module

public import ConAgua.Arena.JustifyModels
public import ConAgua.Arena.PinListRef
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclBasisNames
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
  rf : p.lookup "reserved_from" = some reservedFrom
  rc : p.lookup "reserved_contains" = some reservedContains

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

section cb
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- `is_stmt_kind(x)` of a decoded record is `IConstantInfo.isStmtKind`. -/
theorem isStmtKind_ok (hP : JfCmpProg p) {n : Nat} {m m' : Mem} {x : Word} {r : List Word}
    {ci : IConstantInfo} (hx : decCI (erecP m) x.toNat = some ci)
    (h : callW p n "is_stmt_kind" [x] m = some (r, m')) :
    m' = m ∧ (r.headD 0 ≠ 0 ↔ ci.isStmtKind = true) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (isStmtKind_specW p hP.sk n _ x) h
  simp only [isStmtKindW, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  refine ⟨e.symm, ?_⟩
  have hk := kindW hx
  have hle : erRd m x ≤ 2 ↔ ciKindQ ci ≤ 2 := by rw [UInt64.le_iff_toNat_le, hk]; rfl
  cases ci <;> simp_all [ciKindQ, IConstantInfo.isStmtKind]

/-- **`copy_b(d, c)` refines `copyB ci' ci`** (`d` the solution's record, `c` the input's): the
level-parameter slices compared (`er_sl_eq`), at equal ones the records (`ci_eq`); else a
statement kind (`is_stmt_kind`) at an unreserved name (`reserved_contains`), a renaming
(`levels_renaming`), and the solution's at the input's names (`ci_at_lps`) compared. -/
theorem copyB_sim (hP : JfCmpProg p) (n : Nat) {m : Mem} {a : AState} {d c : Word}
    {ci' ci : IConstantInfo} {C' C : ConLeche.ConstantInfo}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hd : decCI (erecP m) d.toNat = some ci') (hc : decCI (erecP m) c.toNat = some ci)
    (hdd : Frontend.denoteCI a.store ci' = some C') (hdc : Frontend.denoteCI a.store ci = some C) :
    Sim (callW p n "copy_b" [d, c] m) (ConRon.Arena.copyB ci' ci) a
      (fun r b m' a' => CmpPost dn vis fe m a r b m' a') := by
  have hK := hP.pl.canon
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (copyB_specW p hP.cb n _ d c) h
  cases n with
  | zero => simp [copyBW] at hW
  | succ n =>
  rw [copyBW.arm1] at hW
  obtain ⟨hnd, hnde, hsld, -, -⟩ := decCV_rd_ci (erRdOK m) (decCI_cv hd)
  obtain ⟨-, -, hslc, -, -⟩ := decCV_rd_ci (erRdOK m) (decCI_cv hc)
  -- `er_sl_eq` of the two level-parameter slices
  cases h1 : callW p n "er_sl_eq" [erRd m (c + (CI.cv + CV.lpsOff)), erRd m (c + (CI.cv + CV.lpsLen)),
      erRd m (d + (CI.cv + CV.lpsOff)), erRd m (d + (CI.cv + CV.lpsLen))] m with
  | none => rw [h1] at hW; simp [copyBW.k_er_sl_eq] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hm1, hb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erSlEq_spec p hK n _ _ _ _ _) h1
  rw [h1] at hW; simp only [copyBW.k_er_sl_eq] at hW
  rw [erSlEqB_ok (erRdOK m) hslc hsld] at hb1
  simp only at hm1
  subst hm1
  by_cases heq : ci.toConstantVal.levelParams = ci'.toConstantVal.levelParams
  · rw [ite_eq_left (by rw [hb1]; simp [heq])] at hW
    cases h2 : callW p n "ci_eq" [c, d] s1.mem with
    | none => rw [h2] at hW; simp [copyBW.k_ci_eq] at hW
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    obtain ⟨s2, rfl, -, hm2, hb2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (ciEq_spec' p hK n _ _ _) h2
    rw [h2] at hW; simp only [copyBW.k_ci_eq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    simp only at hm2
    rw [ciEqB_ok (erRdOK _) hc hd] at hb2
    refine ⟨decide (ci = ci'), a, ?_, ?_⟩
    · simp only [ConRon.Arena.copyB, heq, beq_self_eq_true, ↓reduceIte]
      rfl
    · rw [← e, hm2]
      refine ⟨hT, IWGrow.refl _, hok, hr, Ext.refl _, ?_⟩
      simp only [List.headD_cons, hb2]
      by_cases h : ci = ci' <;> simp [h]
  rw [ite_eq_right (by rw [hb1]; simp [heq])] at hW
  have hne : (ci.toConstantVal.levelParams == ci'.toConstantVal.levelParams) = false := by
    simpa using heq
  -- `is_stmt_kind(d)`
  cases h2 : callW p n "is_stmt_kind" [d] s1.mem with
  | none => rw [h2] at hW; simp [copyBW.k_is_stmt_kind] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨rfl, hk2⟩ := isStmtKind_ok hP hd h2
  rw [h2] at hW; simp only [copyBW.k_is_stmt_kind] at hW
  by_cases hk : r2.headD 0 = 0
  · rw [ite_eq_left hk] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have hk' : ci'.isStmtKind = false := by
      rw [hk] at hk2; simpa using hk2
    refine ⟨false, a, ?_, ?_⟩
    · simp only [ConRon.Arena.copyB, hne, hk', Bool.false_eq_true, ↓reduceIte]; rfl
    · rw [← e]; exact ⟨hT, IWGrow.refl _, hok, hr, Ext.refl _, by simp⟩
  rw [ite_eq_right hk] at hW
  have hk' : ci'.isStmtKind = true := hk2.mp hk
  -- `reserved_contains(name)`
  cases h3 : callW p n "reserved_contains" [erRd s1.mem (d + (CI.cv + CV.name))] s1.mem with
  | none => rw [h3] at hW; simp [copyBW.k_reserved_contains] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (resCont_spec p hP.rf hP.rc n _ _) h3
  obtain ⟨hm3, hW3⟩ := hW3
  simp only at hm3 hW3
  obtain ⟨R, hR, hb3⟩ := resContW_res hnd hW3 hT.stage.check.pins
  rw [← hnde] at hb3
  rw [h3] at hW; simp only [copyBW.k_reserved_contains] at hW
  rw [hm3] at hW
  have hcopy : ∀ b a', (do
      let rs ← reservedBasisNames
      if (!rs.contains ci'.toConstantVal.name && levelsRenaming ci'.toConstantVal.levelParams
          ci.toConstantVal.levelParams) = true then
        let r ← ci'.atLps ci.toConstantVal.levelParams
        pure (r == ci)
      else pure false : AM Bool).run a = .ok (b, a') →
      (ConRon.Arena.copyB ci' ci).run a = .ok (b, a') := by
    intro b a' h0
    simp only [ConRon.Arena.copyB, hne, hk', Bool.false_eq_true, ↓reduceIte]
    exact h0
  by_cases hrs : r3.headD 0 ≠ 0
  · rw [ite_eq_left hrs] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have hcon : R.contains ci'.toConstantVal.name = true := by
      cases hn : R.contains ci'.toConstantVal.name
      · rw [hb3, hn] at hrs; simp at hrs
      · rfl
    refine ⟨false, a, hcopy _ _ ?_, ?_⟩
    · simp only [StateT.run_bind, hR, except_ok_bind, hcon, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]; rfl
    · rw [← e]; exact ⟨hT, IWGrow.refl _, hok, hr, Ext.refl _, by simp⟩
  rw [ite_eq_right hrs] at hW
  have hcon : R.contains ci'.toConstantVal.name = false := by
    cases hn : R.contains ci'.toConstantVal.name
    · rfl
    · rw [hb3, hn] at hrs; simp at hrs
  -- `levels_renaming(d + CI.cv, c + CI.cv)`
  cases h4 : callW p n "levels_renaming" [d + CI.cv, c + CI.cv] s1.mem with
  | none => rw [h4] at hW; simp [copyBW.k_levels_renaming] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  obtain ⟨hT4, hg4, he4, hrd4, hb4⟩ := levelsRenaming_ok hP hT hd hc h4
  rw [h4] at hW; simp only [copyBW.k_levels_renaming] at hW
  by_cases hz : r4.headD 0 = 0
  · rw [ite_eq_left hz] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have hlr : levelsRenaming ci'.toConstantVal.levelParams ci.toConstantVal.levelParams = false := by
      cases hn : levelsRenaming ci'.toConstantVal.levelParams ci.toConstantVal.levelParams
      · rfl
      · exact absurd (hb4.mpr hn) (by rw [hz]; simp)
    refine ⟨false, a, hcopy _ _ ?_, ?_⟩
    · simp only [StateT.run_bind, hR, except_ok_bind, hcon, hlr, Bool.not_false, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte]; rfl
    · rw [← e]; exact ⟨hT4, hg4, hok, hr, Ext.refl _, by simp⟩
  rw [ite_eq_right hz] at hW
  have hlr : levelsRenaming ci'.toConstantVal.levelParams ci.toConstantVal.levelParams = true :=
    hb4.mp hz
  -- `ci_at_lps(d, c's names)`
  rw [hrd4, hrd4] at hW
  cases h5 : callW p n "ci_at_lps" [d, erRd s1.mem (c + (CI.cv + CV.lpsOff)),
      erRd s1.mem (c + (CI.cv + CV.lpsLen))] m4 with
  | none => rw [h5] at hW; simp [copyBW.k_ci_at_lps] at hW
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at hW; simp only [copyBW.k_ci_at_lps] at hW
  have hps := (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hdc)).2.1
  obtain ⟨x, a5, hrun5, hT5, hg5, hx5⟩ :=
    (ciAtLpsSim_of hP.pl.basis.rules.toCiProg (rulesAtSim_of hP.pl.basis.rules)).ci n vis fe m4 a
      _ _ _ ci' ci.toConstantVal.levelParams _ C' hT4 hok hr (by rw [he4]; exact hd) hdd
      (by rw [he4]; exact hslc) hps r5 m5 h5
  obtain ⟨hst5, -⟩ := ConRon.Bridge.IConstantInfo.atLps_run hok hr hdd hps hrun5
  -- `ci_eq(x, c)`
  cases h6 : callW p n "ci_eq" [r5.headD 0, c] m5 with
  | none => rw [h6] at hW; simp [copyBW.k_ci_eq] at hW
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  obtain ⟨s6, rfl, -, hm6, hb6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (ciEq_spec' p hK n _ _ _) h6
  rw [h6] at hW; simp only [copyBW.k_ci_eq, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  simp only at hm6
  have hc5 : decCI (erecP m5) c.toNat = some ci := ArrExt.decCI hg5.ext (by rw [he4]; exact hc)
  rw [ciEqB_ok (erRdOK _) hx5 hc5] at hb6
  refine ⟨decide (x = ci), a5, hcopy _ _ ?_, ?_⟩
  · simp only [StateT.run_bind, hR, except_ok_bind, hcon, hlr, Bool.not_false, Bool.true_and,
      ↓reduceIte, hrun5]
    rfl
  · rw [← e, hm6]
    refine ⟨hT5, hg4.trans hg5, hst5.ok, hst5.read, hst5.ext, ?_⟩
    simp only [List.headD_cons, hb6]
    by_cases h : x = ci <;> simp [h]

end cb

end L.Arena
