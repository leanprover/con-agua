module

public import ConAgua.Arena.JustifyModels
public import ConAgua.Arena.PinListRef
import ConAgua.Arena.DeclBasisNames
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclStepGo
import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.RecLayout.CIDec
import ConRon.Bridge.Specs
import ConRon.Bridge.Compare.Justify
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
  pa : p.lookup "pin_at" = some pinAtL
  rcp : RecProg p

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

/-- A decoded constant value's slice words, read in any extension of the record pool. -/
theorem cvSliceW {m M : Mem} {q : Word} {cv : IConstantVal}
    (h : decCV (erecP m) q.toNat = some cv) (hx : ArrExt (erecP m) (erecP M)) :
    hslice? (erecP m) (erRd M (q + CV.lpsOff)).toNat (erRd M (q + CV.lpsLen)).toNat =
      some cv.levelParams := by
  obtain ⟨w1, w2, h1, h2, hs⟩ := decCV_slice h
  have e1 : erRd M (q + CV.lpsOff) = w1 :=
    (erRdOK M).rd _ _ (by rw [rd_off_toNat (erRdOK m) h1]; exact hx _ _ h1)
  have e2 : erRd M (q + CV.lpsLen) = w2 :=
    (erRdOK M).rd _ _ (by rw [rd_off_toNat (erRdOK m) h2]; exact hx _ _ h2)
  rw [e1, e2]; exact hs

section tbl
variable {p : Prog}

theorem IProjTable.eq_iff (t t' : IProjTable) :
    t = t' ↔ (t.structName = t'.structName ∧ t.levelParams = t'.levelParams ∧
      t.numParams = t'.numParams ∧ t.ctor = t'.ctor ∧ t.numFields = t'.numFields ∧
      t.bodies.toList = t'.bodies.toList) := by
  obtain ⟨a, b, c, d, e, f⟩ := t
  obtain ⟨a', b', c', d', e', f'⟩ := t'
  simp only [IProjTable.mk.injEq, Array.toList_inj]

/-- **`tbl_eq(q, r)` is the tables' equality** (`decTbl` at both). -/
theorem tblEq_ok (hP : JfCmpProg p) {n : Nat} {m m' : Mem} {q r : Word} {res : List Word}
    {t t' : IProjTable} (hq : decTbl (erecP m) q.toNat = some t) (hr : decTbl (erecP m) r.toNat = some t')
    (h : callW p n "tbl_eq" [q, r] m = some (res, m')) :
    m' = m ∧ (res.headD 0 ≠ 0 ↔ t = t') := by
  have hK := hP.pl.canon
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tblEq_specW p hP.te n _ q r) h
  obtain ⟨hn1, en1, hl1, ep1, hc1, ec1, ef1, hb1⟩ := decTbl_rd (erRdOK m) hq
  obtain ⟨hn2, en2, hl2, ep2, hc2, ec2, ef2, hb2⟩ := decTbl_rd (erRdOK m) hr
  rw [IProjTable.eq_iff, en1, en2, ec1, ec2, ep1, ep2, ef1, ef2, decI_inj_iff hn1 hn2,
    decI_inj_iff hc1 hc2]
  have tn : ∀ a b : Word, a.toNat = b.toNat ↔ a = b := fun a b => UInt64.toNat_inj
  simp only [tn]
  cases n with
  | zero => simp [tblEqW] at hW
  | succ n =>
  simp only [tblEqW] at hW
  by_cases g1 : erRd m (q + ProjTbl.structName) ≠ erRd m (r + ProjTbl.structName)
  · rw [ite_eq_left g1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    exact ⟨e.symm, by simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, not_and]; exact fun h => absurd h g1⟩
  rw [ite_eq_right g1] at hW
  have g1' := Classical.not_not.mp g1
  cases h1 : callW p n "er_sl_eq" [erRd m (q + ProjTbl.lpsOff), erRd m (q + ProjTbl.lpsLen),
      erRd m (r + ProjTbl.lpsOff), erRd m (r + ProjTbl.lpsLen)] m with
  | none => rw [h1] at hW; simp [tblEqW.k_er_sl_eq] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hm1, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erSlEq_spec p hK n _ _ _ _ _) h1
  rw [h1] at hW; simp only [tblEqW.k_er_sl_eq] at hW
  rw [erSlEqB_ok (erRdOK m) hl1 hl2] at hb
  simp only at hm1
  subst hm1
  by_cases g2 : r1.headD 0 = 0
  · rw [ite_eq_left g2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨e.symm, ?_⟩
    have : ¬ t.levelParams = t'.levelParams := fun hh => by rw [hb, hh] at g2; simp at g2
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun _ hh => absurd hh this
  rw [ite_eq_right g2] at hW
  have g2' : t.levelParams = t'.levelParams := Classical.byContradiction fun hh => by
    rw [hb] at g2; simp [hh] at g2
  by_cases g3 : erRd s1.mem (q + ProjTbl.numParams) ≠ erRd s1.mem (r + ProjTbl.numParams)
  · rw [ite_eq_left g3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨e.symm, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun _ _ hh => absurd hh g3
  rw [ite_eq_right g3] at hW
  by_cases g4 : erRd s1.mem (q + ProjTbl.ctor) ≠ erRd s1.mem (r + ProjTbl.ctor)
  · rw [ite_eq_left g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨e.symm, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun _ _ _ hh => absurd hh g4
  rw [ite_eq_right g4] at hW
  by_cases g5 : erRd s1.mem (q + ProjTbl.numFields) ≠ erRd s1.mem (r + ProjTbl.numFields)
  · rw [ite_eq_left g5] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨e.symm, ?_⟩
    simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun _ _ _ _ hh => absurd hh g5
  rw [ite_eq_right g5] at hW
  cases h2 : callW p n "er_sl_eq" [erRd s1.mem (q + ProjTbl.bodiesOff), erRd s1.mem (q + ProjTbl.bodiesLen),
      erRd s1.mem (r + ProjTbl.bodiesOff), erRd s1.mem (r + ProjTbl.bodiesLen)] s1.mem with
  | none => rw [h2] at hW; simp [tblEqW.k_er_sl_eq_2] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨s2, rfl, -, hm2, hbb⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (erSlEq_spec p hK n _ _ _ _ _) h2
  rw [h2] at hW; simp only [tblEqW.k_er_sl_eq_2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  simp only at hm2
  rw [erSlEqB_ok (erRdOK _) hb1 hb2] at hbb
  refine ⟨by rw [← e, hm2], ?_⟩
  simp only [List.headD_cons, hbb, g1', g2', Classical.not_not.mp g3, Classical.not_not.mp g4,
    Classical.not_not.mp g5, true_and]
  by_cases hh : t.bodies.toList = t'.bodies.toList <;> simp [hh]

theorem sub1_toNat {a : Word} (h : a ≠ 0) : (a - 1).toNat = a.toNat - 1 := by
  have : a.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simp [e]))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp

/-- **`tbl_beq_p(a, b)` is `tableBeqP`** of two lookups' tables (`tblFound`: a record's address
plus one, `0` for none). -/
theorem tblBeqP_ok (hP : JfCmpProg p) {n : Nat} {m m' : Mem} {a b : Word} {res : List Word}
    (hda : a ≠ 0 → ∃ t, decTbl (erecP m) (a.toNat - 1) = some t)
    (hdb : b ≠ 0 → ∃ t, decTbl (erecP m) (b.toNat - 1) = some t)
    (h : callW p n "tbl_beq_p" [a, b] m = some (res, m')) :
    m' = m ∧ (res.headD 0 ≠ 0 ↔ tableBeqP (tblFound m a) (tblFound m b) = true) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tblBeqP_specW p hP.tb n _ a b) h
  cases n with
  | zero => simp [tblBeqPW] at hW
  | succ n =>
  simp only [tblBeqPW] at hW
  by_cases ha : a = 0
  · rw [ite_eq_left ha] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨e.symm, ?_⟩
    by_cases hb : b = 0
    · simp [tblFound, ha, hb, tableBeqP]
    · obtain ⟨t, ht⟩ := hdb hb
      simp [tblFound, ha, hb, ht, tableBeqP]
  rw [ite_eq_right ha] at hW
  obtain ⟨ta, hta⟩ := hda ha
  by_cases hb : b = 0
  · rw [ite_eq_left hb] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨e.symm, ?_⟩
    simp [tblFound, ha, hb, hta, tableBeqP]
  rw [ite_eq_right hb] at hW
  obtain ⟨tb, htb⟩ := hdb hb
  cases h1 : callW p n "tbl_eq" [a - 1, b - 1] m with
  | none => rw [h1] at hW; simp [tblBeqPW.k_tbl_eq] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [tblBeqPW.k_tbl_eq, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  obtain ⟨hm1, hb1⟩ := tblEq_ok hP (by rw [sub1_toNat ha]; exact hta) (by rw [sub1_toNat hb]; exact htb) h1
  refine ⟨by rw [← e, hm1], ?_⟩
  simp only [List.headD_cons, tblFound, ha, hb, ↓reduceIte, hta, htb, tableBeqP, beq_iff_eq]
  exact hb1

end tbl

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

/-- **`refines_b(c, d)` refines `refinesB ci ci'`** (`c` the input's record, `d` the solution's): a
copy (`copy_b`), or the input's an axiom (kind word `0`) and the solution's a statement kind
(`is_stmt_kind`) not at a compiler-trust name (pin slots `43`, `44`, the twin's `reduceOpNames`),
whose statement as a fresh axiom record (`ccv_rec`'s stores) the input copies. -/
theorem refinesB_sim (hP : JfCmpProg p) (n : Nat) {m : Mem} {a : AState} {c d : Word}
    {ci ci' : IConstantInfo} {C C' : ConLeche.ConstantInfo}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hc : decCI (erecP m) c.toNat = some ci) (hd : decCI (erecP m) d.toNat = some ci')
    (hdc : Frontend.denoteCI a.store ci = some C) (hdd : Frontend.denoteCI a.store ci' = some C') :
    Sim (callW p n "refines_b" [c, d] m) (ConRon.Arena.refinesB ci ci') a
      (fun r b m' a' => CmpPost dn vis fe m a r b m' a') := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (refinesB_specW p hP.rb n _ c d) h
  cases n with
  | zero => simp [refinesBW] at hW
  | succ n =>
  simp only [refinesBW] at hW
  -- `copy_b(d, c)`
  cases h1 : callW p n "copy_b" [d, c] m with
  | none => rw [h1] at hW; simp [refinesBW.k_copy_b] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨b1, a1, hrun1, hT1, hg1, hok1, hr1, hx1, hb1⟩ := copyB_sim hP n hT hok hr hd hc hdd hdc r1 m1 h1
  rw [h1] at hW; simp only [refinesBW.k_copy_b] at hW
  by_cases h0 : r1.headD 0 ≠ 0
  · rw [ite_eq_left h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have hb : b1 = true := hb1.mp h0
    refine ⟨true, a1, ?_, ?_⟩
    · simp only [ConRon.Arena.refinesB, StateT.run_bind, hrun1, except_ok_bind, hb, ↓reduceIte]; rfl
    · rw [← e]; exact ⟨hT1, hg1, hok1, hr1, hx1, by simp⟩
  rw [ite_eq_right h0] at hW
  have hb : b1 = false := by
    cases hq : b1
    · rfl
    · exact absurd (hb1.mpr hq) h0
  have hc1 : decCI (erecP m1) c.toNat = some ci := ArrExt.decCI hg1.ext hc
  have hd1 : decCI (erecP m1) d.toNat = some ci' := ArrExt.decCI hg1.ext hd
  have hrun1' : (ConRon.Arena.refinesB ci ci').run a = (match ci with
      | .axiomInfo _ =>
        if ci'.isStmtKind = true then
          (do let rs ← reduceOpNames
              if rs.contains ci'.toConstantVal.name = true then pure false
              else ConRon.Arena.copyB (.axiomInfo ci'.toConstantVal) ci : AM Bool)
        else pure false
      | _ => pure false : AM Bool).run a1 := by
    simp only [ConRon.Arena.refinesB, StateT.run_bind, hrun1, except_ok_bind, hb,
      Bool.false_eq_true, ↓reduceIte]
    cases ci <;> rfl
  have hk := kindW hc1
  by_cases hax : erRd m1 c ≠ 0
  · rw [ite_eq_left hax] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨false, a1, ?_, ?_⟩
    · rw [hrun1']
      have : ciKindQ ci ≠ 0 := by rw [← hk]; exact fun h => hax (UInt64.toNat_inj.mp h)
      cases ci <;> simp_all [ciKindQ] <;> rfl
    · rw [← e]; exact ⟨hT1, hg1, hok1, hr1, hx1, by simp⟩
  rw [ite_eq_right hax] at hW
  obtain ⟨cv0, rfl⟩ : ∃ cv0, ci = .axiomInfo cv0 := by
    have : ciKindQ ci = 0 := by rw [← hk]; simp at hax; rw [hax]; rfl
    cases ci <;> simp_all [ciKindQ]
  simp only at hrun1'
  -- `is_stmt_kind(d)`
  cases h2 : callW p n "is_stmt_kind" [d] m1 with
  | none => rw [h2] at hW; simp [refinesBW.k_is_stmt_kind] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨e2, hk2⟩ := isStmtKind_ok hP hd1 h2
  subst m2
  rw [h2] at hW; simp only [refinesBW.k_is_stmt_kind] at hW
  by_cases hz : r2.headD 0 = 0
  · rw [ite_eq_left hz] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have hk' : ci'.isStmtKind = false := by rw [hz] at hk2; simpa using hk2
    refine ⟨false, a1, by rw [hrun1', hk']; rfl, ?_⟩
    rw [← e]; exact ⟨hT1, hg1, hok1, hr1, hx1, by simp⟩
  rw [ite_eq_right hz] at hW
  have hk' : ci'.isStmtKind = true := hk2.mp hz
  rw [hk'] at hrun1'
  simp only [↓reduceIte] at hrun1'
  have hF1 : PinsFull m1 a1.pins := hT1.stage.check.pins.full hT1.flag
  simp only [StateT.run_bind, reduceOpNames_run hF1, except_ok_bind] at hrun1'
  obtain ⟨hnw, hnde, -, -, -⟩ := decCV_rd_ci (erRdOK m1) (decCI_cv hd1)
  -- `pin_at(43)`, `pin_at(44)`
  cases h3 : callW p n "pin_at" [43] m1 with
  | none => rw [h3] at hW; simp [refinesBW.k_pin_at] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (pinAt_specW p hP.pa n _ 43) h3
  rw [h3] at hW; simp only [refinesBW.k_pin_at] at hW
  simp only [pinAtW, hT1.flag, ↓reduceIte] at hW3
  have e43 : rdW (m1.arr64 PINS) (1 + 43) = pinW m1 44 := rfl
  rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hW3
  simp only [Option.some.injEq, Prod.mk.injEq] at hW3
  obtain ⟨rfl, e3⟩ := hW3
  cases h4 : callW p n "pin_at" [44] s3.mem with
  | none => rw [h4] at hW; simp [refinesBW.k_pin_at_2] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩) (pinAt_specW p hP.pa n _ 44) h4
  rw [h4] at hW; simp only [refinesBW.k_pin_at_2] at hW
  rw [← e3] at hW4
  simp only [pinAtW, hT1.flag, ↓reduceIte] at hW4
  rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hW4
  simp only [Option.some.injEq, Prod.mk.injEq] at hW4
  obtain ⟨rfl, e4⟩ := hW4
  have e44 : rdW (m1.arr64 PINS) (1 + 44) = pinW m1 45 := rfl
  simp only [List.headD_cons, e43, e44] at hW
  have hp44 : (pinW m1 44).toNat < 2 ^ 32 := hF1.names_lt 43 (by decide)
  have hp45 : (pinW m1 45).toNat < 2 ^ 32 := hF1.names_lt 44 (by decide)
  have hcond : (erRd m1 (d + (CI.cv + CV.name)) = pinW m1 44 ∨
      erRd m1 (d + (CI.cv + CV.name)) = pinW m1 45) ↔
      ((List.range' 44 2).map (fun j => (decI (pinW m1 j) : NIdx))).contains ci'.toConstantVal.name = true := by
    rw [hnde]
    simp only [List.range', List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      Bool.or_false, Bool.or_eq_true, beq_iff_eq, decI_inj_iff hnw hp44, decI_inj_iff hnw hp45]
  by_cases hpin : erRd m1 (d + (CI.cv + CV.name)) = pinW m1 44 ∨
      erRd m1 (d + (CI.cv + CV.name)) = pinW m1 45
  · rw [ite_eq_left hpin] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    refine ⟨false, a1, by rw [hrun1', ite_eq_left (hcond.mp hpin)]; rfl, ?_⟩
    rw [← e, ← e4]; exact ⟨hT1, hg1, hok1, hr1, hx1, by simp⟩
  rw [ite_eq_right hpin] at hW
  rw [ite_eq_right (mt hcond.mpr hpin)] at hrun1'
  -- the fresh `axiomInfo` record of `ci'`'s statement
  have hm4 : s4.mem = m1 := by rw [← e4]
  rw [hm4] at hW
  have hcv1 := decCI_cv hd1
  obtain ⟨w0, hw0, -, -⟩ := decCV_name hcv1
  have hq : (d + CI.cv).toNat = d.toNat + CI.cv.toNat := off_add_toNat rfl (erecP_lt64 hw0)
  have hqd : decCV (erecP m1) (d + CI.cv).toNat = some ci'.toConstantVal := by rw [hq]; exact hcv1
  cases h5 : callW p n "erec_alloc" [CI.axiomSize] m1 with
  | none => rw [h5] at hW; simp [refinesBW.k_erec_alloc] at hW
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at hW; simp only [refinesBW.k_erec_alloc] at hW
  cases h6 : callW p n "erec_put" [r5.headD 0, 0] m5 with
  | none => rw [h6] at hW; simp [refinesBW.k_erec_put] at hW
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6] at hW; simp only [refinesBW.k_erec_put] at hW
  cases h7 : callW p n "erec_put" [r5.headD 0 + (CI.cv + CV.name), erRd m1 (d + (CI.cv + CV.name))] m6 with
  | none => rw [h7] at hW; simp [refinesBW.k_erec_put_2] at hW
  | some x7 =>
  obtain ⟨r7, m7⟩ := x7
  rw [h7] at hW; simp only [refinesBW.k_erec_put_2] at hW
  cases h8 : callW p n "erec_put" [r5.headD 0 + (CI.cv + CV.lpsOff), erRd m7 (d + (CI.cv + CV.lpsOff))] m7 with
  | none => rw [h8] at hW; simp [refinesBW.k_erec_put_3] at hW
  | some x8 =>
  obtain ⟨r8, m8⟩ := x8
  rw [h8] at hW; simp only [refinesBW.k_erec_put_3] at hW
  cases h9 : callW p n "erec_put" [r5.headD 0 + (CI.cv + CV.lpsLen), erRd m8 (d + (CI.cv + CV.lpsLen))] m8 with
  | none => rw [h9] at hW; simp [refinesBW.k_erec_put_4] at hW
  | some x9 =>
  obtain ⟨r9, m9⟩ := x9
  rw [h9] at hW; simp only [refinesBW.k_erec_put_4] at hW
  cases h10 : callW p n "erec_put" [r5.headD 0 + (CI.cv + CV.type), erRd m1 (d + (CI.cv + CV.type))] m9 with
  | none => rw [h10] at hW; simp [refinesBW.k_erec_put_5] at hW
  | some x10 =>
  obtain ⟨r10, m10⟩ := x10
  rw [h10] at hW; simp only [refinesBW.k_erec_put_5] at hW
  have h8' := h8; rw [show d + (CI.cv + CV.lpsOff) = d + CI.cv + CV.lpsOff from (UInt64.add_assoc _ _ _).symm] at h8'
  have h9' := h9; rw [show d + (CI.cv + CV.lpsLen) = d + CI.cv + CV.lpsLen from (UInt64.add_assoc _ _ _).symm] at h9'
  obtain ⟨hT10, hg10, -, hx10⟩ := ccv_rec hP.rcp hT1 hqd
    (by rw [show (CI.cv + CV.name : Word) = CI.cv by decide]) (by rw [UInt64.add_assoc])
    h5 h6 h7 h8' h9' h10
  -- `copy_b(x, c)`
  cases h11 : callW p n "copy_b" [r5.headD 0, c] m10 with
  | none => rw [h11] at hW; simp [refinesBW.k_copy_b_2] at hW
  | some x11 =>
  obtain ⟨r11, m11⟩ := x11
  rw [h11] at hW; simp only [refinesBW.k_copy_b_2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  have hcv' := ConRon.Bridge.denoteCI_toConstantVal hdd
  have hda : Frontend.denoteCI a1.store (.axiomInfo ci'.toConstantVal) =
      some (.axiomInfo C'.toConstantVal) := by
    simp only [Frontend.denoteCI, ConRon.Bridge.denoteCV_ext hcv' hx1, Option.map_some]
  have hc10 : decCI (erecP m10) c.toNat = some (.axiomInfo cv0) :=
    ArrExt.decCI hg10.ext (ArrExt.decCI hg1.ext hc)
  obtain ⟨b11, a11, hrun11, hT11, hg11, hok11, hr11, hx11, hb11⟩ :=
    copyB_sim hP n hT10 hok1 hr1 hx10 hc10 hda (ConRon.Bridge.denoteCI_ext hdc hx1) r11 m11 h11
  refine ⟨b11, a11, by rw [hrun1']; exact hrun11, ?_⟩
  rw [← e]
  exact ⟨hT11, hg1.trans (hg10.trans hg11), hok11, hr11, hx1.trans hx11, by simpa using hb11⟩
/-- **`same_cv_up_to_levels(x + CI.cv, y + CI.cv)` refines `sameCvUpToLevels cv cv'`** (`x` the
input's record, `y` the solution's): the slices compared (`er_sl_eq`), at equal ones the values
(`cv_eq`); else a renaming (`levels_renaming`) and the solution's at the input's names (`cv_at_lps`
into a fresh value) compared. -/
theorem sameCv_sim (hP : JfCmpProg p) (n : Nat) {m : Mem} {a : AState} {x y : Word}
    {cx cy : IConstantInfo} {C C' : ConLeche.ConstantInfo}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hx : decCI (erecP m) x.toNat = some cx) (hy : decCI (erecP m) y.toNat = some cy)
    (hdx : Frontend.denoteCI a.store cx = some C) (hdy : Frontend.denoteCI a.store cy = some C') :
    Sim (callW p n "same_cv_up_to_levels" [x + CI.cv, y + CI.cv] m)
      (ConRon.Arena.sameCvUpToLevels cx.toConstantVal cy.toConstantVal) a
      (fun r b m' a' => CmpPost dn vis fe m a r b m' a') := by
  have hK := hP.pl.canon
  have hQ := hP.pl.basis.rules.toQuotAtProg
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (sameCvUpToLevels_specW p hP.sc n _ (x + CI.cv) (y + CI.cv)) h
  cases n with
  | zero => simp [sameCvUpToLevelsW] at hW
  | succ n =>
  simp only [sameCvUpToLevelsW] at hW
  have hcx := decCI_cv hx
  have hcy := decCI_cv hy
  obtain ⟨wx, hwx, -, -⟩ := decCV_name hcx
  obtain ⟨wy, hwy, -, -⟩ := decCV_name hcy
  have hqx : (x + CI.cv).toNat = x.toNat + CI.cv.toNat := off_add_toNat rfl (erecP_lt64 hwx)
  have hqy : (y + CI.cv).toNat = y.toNat + CI.cv.toNat := off_add_toNat rfl (erecP_lt64 hwy)
  rw [← hqx] at hcx; rw [← hqy] at hcy
  obtain ⟨-, ox, lx, -, -, ex1, ex2, -, -, -, -, -, hslx⟩ := cvFields (erRdOK m) hcx
  obtain ⟨-, oy, ly, -, -, ey1, ey2, -, -, -, -, -, hsly⟩ := cvFields (erRdOK m) hcy
  rw [← ex1, ← ex2] at hslx; rw [← ey1, ← ey2] at hsly
  have hrunT := fun b a' (hb : (ConRon.Arena.sameCvUpToLevels cx.toConstantVal cy.toConstantVal).run a = .ok (b, a')) =>
    ConRon.Bridge.sameCvUpToLevels_run hok hr (ConRon.Bridge.denoteCI_toConstantVal hdx)
      (ConRon.Bridge.denoteCI_toConstantVal hdy) hb
  cases h1 : callW p n "er_sl_eq" [erRd m (x + CI.cv + CV.lpsOff), erRd m (x + CI.cv + CV.lpsLen),
      erRd m (y + CI.cv + CV.lpsOff), erRd m (y + CI.cv + CV.lpsLen)] m with
  | none => rw [h1] at hW; simp [sameCvUpToLevelsW.k_er_sl_eq] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hm1, hb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erSlEq_spec p hK n _ _ _ _ _) h1
  rw [h1] at hW; simp only [sameCvUpToLevelsW.k_er_sl_eq] at hW
  rw [erSlEqB_ok (erRdOK m) hslx hsly] at hb1
  simp only at hm1
  subst hm1
  by_cases heq : cx.toConstantVal.levelParams = cy.toConstantVal.levelParams
  · rw [ite_eq_left (by rw [hb1]; simp [heq])] at hW
    cases h2 : callW p n "cv_eq" [x + CI.cv, y + CI.cv] s1.mem with
    | none => rw [h2] at hW; simp [sameCvUpToLevelsW.k_cv_eq] at hW
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    obtain ⟨s2, rfl, -, hm2, hb2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (cvEq_spec' p hK n _ _ _) h2
    rw [h2] at hW; simp only [sameCvUpToLevelsW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    simp only at hm2
    rw [cvEqB_ok (erRdOK _) hcx hcy] at hb2
    have hrun : (ConRon.Arena.sameCvUpToLevels cx.toConstantVal cy.toConstantVal).run a =
        .ok (decide (cx.toConstantVal = cy.toConstantVal), a) := by
      simp only [ConRon.Arena.sameCvUpToLevels, heq, beq_self_eq_true, ↓reduceIte]; rfl
    refine ⟨_, a, hrun, ?_⟩
    rw [← e, hm2]
    refine ⟨hT, IWGrow.refl _, hok, hr, Ext.refl _, ?_⟩
    simp only [List.headD_cons, hb2]
    by_cases h : cx.toConstantVal = cy.toConstantVal <;> simp [h]
  rw [ite_eq_right (by rw [hb1]; simp [heq])] at hW
  have hne : (cx.toConstantVal.levelParams == cy.toConstantVal.levelParams) = false := by simpa using heq
  -- `levels_renaming`
  cases h2 : callW p n "levels_renaming" [x + CI.cv, y + CI.cv] s1.mem with
  | none => rw [h2] at hW; simp [sameCvUpToLevelsW.k_levels_renaming] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  obtain ⟨hT2, hg2, he2, hrd2, hb2⟩ := levelsRenaming_ok hP hT hx hy h2
  rw [h2] at hW; simp only [sameCvUpToLevelsW.k_levels_renaming] at hW
  by_cases hz : r2.headD 0 = 0
  · rw [ite_eq_left hz] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have hlr : levelsRenaming cx.toConstantVal.levelParams cy.toConstantVal.levelParams = false := by
      cases hn : levelsRenaming cx.toConstantVal.levelParams cy.toConstantVal.levelParams
      · rfl
      · exact absurd (hb2.mpr hn) (by rw [hz]; simp)
    refine ⟨false, a, ?_, ?_⟩
    · simp only [ConRon.Arena.sameCvUpToLevels, hne, hlr, Bool.false_eq_true, ↓reduceIte]; rfl
    · rw [← e]; exact ⟨hT2, hg2, hok, hr, Ext.refl _, by simp⟩
  rw [ite_eq_right hz] at hW
  have hlr := hb2.mp hz
  -- `erec_alloc(CV.size)`
  cases h3 : callW p n "erec_alloc" [CV.size] m2 with
  | none => rw [h3] at hW; simp [sameCvUpToLevelsW.k_erec_alloc] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at hW; simp only [sameCvUpToLevelsW.k_erec_alloc] at hW
  have hA := callW_erecAlloc hQ.erAlloc h3
  have hqf3 := callW_quotFrame hQ.quot (by decide) h3
  obtain ⟨hT3, hg3, hoff, htop, hr41⟩ := erAlloc_stageT hA hT2
  -- `cv_at_lps(d, y + CI.cv, x's names)`
  have hcx2 : decCV (erecP m2) (x + CI.cv).toNat = some cx.toConstantVal := by rw [he2]; exact hcx
  have hcy3 : decCV (erecP m3) (y.toNat + CI.cv.toNat) = some cy.toConstantVal :=
    ArrExt.decCV hg3.ext (by rw [he2, ← hqy]; exact hcy)
  have hsl := cvSliceW hcx2 hg3.ext
  have hps := (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hdx)).2.1
  cases h4 : callW p n "cv_at_lps" [r3.headD 0, y + CI.cv, erRd m3 (x + CI.cv + CV.lpsOff),
      erRd m3 (x + CI.cv + CV.lpsLen)] m3 with
  | none => rw [h4] at hW; simp [sameCvUpToLevelsW.k_cv_at_lps] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4] at hW; simp only [sameCvUpToLevelsW.k_cv_at_lps] at hW
  obtain ⟨cv', a4, hrun4, hT4, hg4, -, hdec4, -, -, -, -⟩ :=
    cvAtLps_sim hQ n hT2.stage hT3 hok hqf3 hg3 (d := r3.headD 0) (c := y)
      (by rw [hoff]; exact Nat.le_refl _) (by rw [htop, hoff]; exact Nat.le_refl _) hr41 hcy3 hsl hps r4 m4 h4
  -- `cv_eq(d, x + CI.cv)`
  cases h5 : callW p n "cv_eq" [r3.headD 0, x + CI.cv] m4 with
  | none => rw [h5] at hW; simp [sameCvUpToLevelsW.k_cv_eq] at hW
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  obtain ⟨s5, rfl, -, hm5, hb5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (cvEq_spec' p hK n _ _ _) h5
  rw [h5] at hW; simp only [sameCvUpToLevelsW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  simp only at hm5
  have hcx4 : decCV (erecP m4) (x + CI.cv).toNat = some cx.toConstantVal :=
    ArrExt.decCV hg4.ext hcx2
  rw [cvEqB_ok (erRdOK _) hdec4 hcx4] at hb5
  have hrun : (ConRon.Arena.sameCvUpToLevels cx.toConstantVal cy.toConstantVal).run a =
      .ok (decide (cv' = cx.toConstantVal), a4) := by
    simp only [ConRon.Arena.sameCvUpToLevels, hne, hlr, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, hrun4, except_ok_bind]
    rfl
  obtain ⟨hst, -⟩ := hrunT _ _ hrun
  refine ⟨_, a4, hrun, ?_⟩
  rw [← e, hm5]
  refine ⟨hT4, hg2.trans hg4, hst.ok, hst.read, hst.ext, ?_⟩
  simp only [List.headD_cons, hb5]
  by_cases h : cv' = cx.toConstantVal <;> simp [h]

end cb

end L.Arena
