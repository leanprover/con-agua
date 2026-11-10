module

public import ConAgua.Arena.IndDeclConstsCtors
public import ConAgua.Arena.StageInst1
public import ConAgua.Arena.IndPosSpec.MatesW
public import ConAgua.Arena.IndSumSpec.StructProjArgP
public import ConAgua.Arena.IndInstallSpec.DomsW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# A declaration's constants: dropping variables (lane `ronsync2`, stage 3)

`expr_drop_vars(n, e)` refines con-ron's `exprDropVars` (`Arena/Install.lean`): `n` times, `Sort 0`
(`pin_word(53)`, `intern_sort`; `internSort_stage`) instantiated for the loose variable `0`
(`instantiate1_fast`, `i1F_ok`). `expr_drop_vars_list(n, a.off, a.len)` refines `as.mapM
(exprDropVars n)`: a fresh `IW` slice of handles (`sl_cons`, `consW_stage`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `expr_drop_vars(_list)`. -/
structure DropProg (p : Prog) : Prop extends DcCtorsProg p where
  pinWord : p.lookup "pin_word" = some pinWordL
  sortFind : p.lookup "sort_find" = some sortFind
  sortPush : p.lookup "sort_push" = some sortPush
  internSort : p.lookup "intern_sort" = some internSort
  i1 : I1Prog p
  edv : p.lookup "expr_drop_vars" = some exprDropVars
  edvl : p.lookup "expr_drop_vars_list" = some exprDropVarsList

/-! ## `expr_drop_vars` -/

/-- **The model of `expr_drop_vars(k, e)`** at exec fuel `n`. -/
l_model edv_spec {p : Prog} (hP : DropProg p)
  fns [hP.edv ↦ edvW list]
  specs [pinWord_specV p hP.pinWord n, internSort_spec p hP.sortFind hP.sortPush hP.internSort n,
    i1F_spec p hP.i1 n]
  grind [arena_grind]

/-- **`expr_drop_vars` refines `exprDropVars`** (its model, from the stage relation). -/
theorem edvW_ok (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k e : Word) (r : List Word),
    StageR vis fe m a → H e → edvW n m k e = some (r, m') →
    ∃ x a', (ConRon.Arena.exprDropVars k.toNat (decI e)).run a = .ok (x, a') ∧
      KeepPost vis fe decW0E m m' a' r x := by
  induction n with
  | zero => intro m m' a k e r _ _ h; simp [edvW] at h
  | succ n ih =>
  intro m m' a k e r hS he h
  by_cases hk : k = 0
  · rw [edvW.arm1 n m k e hk] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst hk
    exact ⟨decI e, a, rfl, hS, IWGrow.refl m, he, rfl⟩
  rw [edvW.arm2 n m k e hk] at h
  rcases hpw : pinWordV m 53 with _ | z <;> rw [hpw] at h; · simp [edvW.k_pin_word.none] at h
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hpw
  have hz : z = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hpw
    rw [← hpw]; simp [pinW, rdW]
  have hpin0 : pinW m 0 ≠ 0 := by simpa [pinW, rdW] using hpne
  have hfull := hS.check.pins.full hpin0
  have hzlt : z.toNat < 2 ^ 32 := by rw [hz]; exact hfull.lv_lt.2.1
  rw [edvW.k_pin_word.arm1] at h
  rcases hso : sointernW m z with _ | ⟨s1, m1⟩ <;> rw [hso] at h; · simp [edvW.k_intern_sort.none] at h
  by_cases hsb : 4294967296 ≤ s1
  · rw [edvW.k_intern_sort.abort1 (hc1 := hsb)] at h; simp at h
  rw [edvW.k_intern_sort.arm1 (hc1 := hsb)] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ := internSort_stage hS z hzlt hso
  have hs1lt : s1.toNat < 2 ^ 32 := lt_of_notbig hsb
  rcases hi : i1F m1 [CWF, e, s1, 0] with _ | ⟨ri, m2⟩ <;> rw [hi] at h; · simp [edvW.k_instantiate1_fast.none] at h
  obtain ⟨t1, a2, hrun2, hS2, hg2, hd21, hd22⟩ := i1F_ok (fun _ => none) vis fe e s1 0 he m1 m2 a1 ri hi hS1
  rw [edvW.k_instantiate1_fast.arm1] at h
  rcases hr : edvW n m2 (k - 1) (ri.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hr] at h
  · simp [edvW.k_expr_drop_vars.none] at h
  rw [edvW.k_expr_drop_vars.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a3, hrun3, hS3, hg3, hd31, hd32⟩ := ih m2 m3 a2 (k - 1) (ri.headD 0) r3 hS2 hd21 hr
  refine ⟨x, a3, ?_, hS3, hg1.trans (hg2.trans hg3), by simpa using hd31, by simpa using hd32⟩
  have hk1 : k.toNat = (k - 1).toNat + 1 := by
    have : k.toNat ≠ 0 := fun e => hk (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  have hzl : (zeroLevel).run a = .ok (decI z, a) := by
    rw [hz]; exact pinZeroLevel_run hfull
  have hrun2' : (instantiate1Fast coreWalkFuel (decI e) (decE s1) 0).run a1 = .ok (t1, a2) := by
    have := hrun2
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [CWF_eq, h0] at this
    exact this
  rw [hd22] at hrun3
  rw [hk1]
  simp only [ConRon.Arena.exprDropVars, StateT.run_bind, hzl, except_ok_bind,
    ConRon.Arena.internSortE, hrun1, hrun2', hrun3]

/-! ## `expr_drop_vars_list` -/

/-- **The model of `expr_drop_vars_list(k, ao, al)`** at exec fuel `n`. -/
l_model edvl_spec (p : Prog) (hP : DropProg p)
  fns [hP.edvl ↦ edvlW list]
  specs [edv_spec hP n, callW_spec p n "sl_cons"]
  grind [arena_grind]

/-- **`expr_drop_vars_list` refines `as.mapM (exprDropVars k)`**: a fresh `IW` slice of handles
below the pool's top. -/
theorem edvlW_ok {p : Prog} (hP : DropProg p) (vis : Word) (fe : IFEnv) (k : Word) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (ao al : Word) (xs : List EIdx) (r : List Word),
    StageR vis fe m a → decHL m ao.toNat al.toNat = some xs → ao.toNat + al.toNat ≤ iwTop m →
    edvlW p n m k ao al = some (r, m') →
    ∃ ys a', (xs.mapM (ConRon.Arena.exprDropVars k.toNat)).run a = .ok (ys, a') ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ys ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' a ao al xs r _ _ _ h; simp [edvlW] at h
  | succ n ih =>
  intro m m' a ao al xs r hS hxs hb h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hl : al = 0
  · rw [edvlW.arm1 p n m k ao al hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst hl
    have : xs = [] := by simpa [decHL, hslice?] using hxs.symm
    subst this
    exact ⟨[], a, rfl, by simp [decHL, hslice?], by simp, hS, IWGrow.refl m⟩
  obtain ⟨w, xs', rfl, hw, hwlt, hrest⟩ := decHL_cons hxs hl (by omega)
  rw [edvlW.arm2 p n m k ao al hl, hw] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [edvlW.k_expr_drop_vars.none])
  rw [edvlW.k_expr_drop_vars.arm1] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hx1, hx2⟩ := edvW_ok vis fe n m m1 a k w r1 hS hwlt h1
  have hlpos : 0 < al.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have ho1 : (ao + 1).toNat = ao.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (al - 1).toNat = al.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hb' : (ao + 1).toNat + (al - 1).toNat ≤ iwTop m := by omega
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [edvlW.k_expr_drop_vars_list.none])
  obtain ⟨ys, a3, hrun3, hd3, hb3, hS3, hg3⟩ := ih m1 m3 a1 (ao + 1) (al - 1) xs' r3 hS1
    (by rw [decHL_grow hg1 hb']; exact hrest) (by have := hg1.iw; omega) h3
  rw [edvlW.k_expr_drop_vars_list.arm1] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [edvlW.k_sl_cons.none])
  rw [edvlW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS5, hg5, hd5, hb5⟩ := consW_stage (consCall hP.toFormersProg h4) hS3 hb3 hx1 hd3
  refine ⟨x :: ys, a3, ?_, by rw [← hx2]; simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega,
    hS5, hg1.trans (hg3.trans hg5)⟩
  simp only [List.mapM_cons, StateT.run_bind, hrun1, except_ok_bind, hrun3]
  rfl

end L.Ind

end
