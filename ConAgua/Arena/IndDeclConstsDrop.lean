module

public import ConAgua.Arena.IndDeclConstsCtors
public import ConAgua.Arena.StageInst1
public import ConAgua.Arena.IndPosSpec.MatesW
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.IndSumSpec.StructProjArgP
public import ConAgua.Arena.IndSumSpec.DecHLTake
public import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.CanonW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
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
structure DropProg (p : Prog) : Prop extends CtorsProg p where
  pinWord : p.lookup "pin_word" = some pinWordL
  sortFind : p.lookup "sort_find" = some sortFind
  sortPush : p.lookup "sort_push" = some sortPush
  internSort : p.lookup "intern_sort" = some internSort
  i1 : I1Prog p
  edv : p.lookup "expr_drop_vars" = some exprDropVars
  edvl : p.lookup "expr_drop_vars_list" = some exprDropVarsList

/-! ## `expr_drop_vars` -/

mutual
/-- **The model of `expr_drop_vars(k, e)`** at exec fuel `n`. -/
def edvW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, k, e => if k = 0 then some ([e], m) else edvK1 p n m k e (pinWordV m 53)
/-- After the pin: the sort. -/
def edvK1 (p : Prog) (n : Nat) (m : Mem) (k e : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => edvK2 p n k e (sointernW m z)
/-- After the sort: the instantiation. -/
def edvK2 (p : Prog) (n : Nat) (k e : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else edvK3 p n k (i1F m1 [CWF, e, s, 0])
/-- After the instantiation: the rest. -/
def edvK3 (p : Prog) (n : Nat) (k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => fwd1 (edvW p n m2 (k - 1) (r.headD 0))
end

section arms
variable (p : Prog) (n : Nat) (m m1 : Mem) (k e z s : Word) (r : List Word)
theorem edvW_zero (h : k = 0) : edvW p (n + 1) m k e = some ([e], m) := by simp [edvW, h]
theorem edvW_succ (h : k ≠ 0) : edvW p (n + 1) m k e = edvK1 p n m k e (pinWordV m 53) := by
  simp [edvW, h]
theorem edvK1_some : edvK1 p n m k e (some z) = edvK2 p n k e (sointernW m z) := by simp [edvK1]
theorem edvK2_big (h : 4294967296 ≤ s) : edvK2 p n k e (some (s, m1)) = none := by simp [edvK2, h]
theorem edvK2_ok (h : ¬ 4294967296 ≤ s) : edvK2 p n k e (some (s, m1)) =
    edvK3 p n k (i1F m1 [CWF, e, s, 0]) := by simp [edvK2, h]
theorem edvK3_some : edvK3 p n k (some (r, m1)) = fwd1 (edvW p n m1 (k - 1) (r.headD 0)) := by
  simp [edvK3]
end arms
attribute [ind_grind] edvW_zero edvW_succ edvK1_some edvK2_big edvK2_ok edvK3_some fwd1_some

theorem edv_spec {p : Prog} (hP : DropProg p) (n : Nat) :
    ∀ (s₀ : St) (k e : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "expr_drop_vars" [k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ edvW p n s₀.mem k e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ k e; rw [invoke_eq _ hP.edv]; simp only [callFn, exprDropVars]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ k e
    rw [invoke_eq _ hP.edv]
    simp only [callFn, exprDropVars]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pinWord_specV p hP.pinWord n, internSort_spec p hP.sortFind hP.sortPush hP.internSort n,
        i1F_spec p hP.i1 n, ih] <;>
      finish (gen := 20)

/-- **`expr_drop_vars` refines `exprDropVars`** (its model, from the stage relation). -/
theorem edvW_ok {p : Prog} (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k e : Word) (r : List Word),
    StageR vis fe m a → H e → edvW p n m k e = some (r, m') →
    ∃ x a', (ConRon.Arena.exprDropVars k.toNat (decI e)).run a = .ok (x, a') ∧
      KeepPost vis fe decW0E m m' a' r x := by
  induction n with
  | zero => intro m m' a k e r _ _ h; simp [edvW] at h
  | succ n ih =>
  intro m m' a k e r hS he h
  by_cases hk : k = 0
  · rw [edvW_zero p n m k e hk] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst hk
    exact ⟨decI e, a, rfl, hS, IWGrow.refl m, he, rfl⟩
  rw [edvW_succ p n m k e hk] at h
  rcases hpw : pinWordV m 53 with _ | z <;> rw [hpw] at h; · simp [edvK1] at h
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hpw
  have hz : z = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hpw
    rw [← hpw]; simp [pinW, rdW]
  have hpin0 : pinW m 0 ≠ 0 := by simpa [pinW, rdW] using hpne
  have hfull := hS.check.pins.full hpin0
  have hzlt : z.toNat < 2 ^ 32 := by rw [hz]; exact hfull.lv_lt.2.1
  rw [edvK1_some] at h
  rcases hso : sointernW m z with _ | ⟨s1, m1⟩ <;> rw [hso] at h; · simp [edvK2] at h
  by_cases hsb : 4294967296 ≤ s1
  · rw [edvK2_big _ _ _ _ _ _ hsb] at h; simp at h
  rw [edvK2_ok _ _ _ _ _ _ hsb] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ := internSort_stage hS z hzlt hso
  have hs1lt : s1.toNat < 2 ^ 32 := lt_of_notbig hsb
  rcases hi : i1F m1 [CWF, e, s1, 0] with _ | ⟨ri, m2⟩ <;> rw [hi] at h; · simp [edvK3] at h
  obtain ⟨t1, a2, hrun2, hS2, hg2, hd21, hd22⟩ := i1F_ok (fun _ => none) vis fe e s1 0 he m1 m2 a1 ri hi hS1
  rw [edvK3_some] at h
  rcases hr : edvW p n m2 (k - 1) (ri.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hr] at h; · simp [fwd1] at h
  rw [fwd1_some] at h
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

/-- `expr_drop_vars`' run, as its model. -/
theorem edvCall {p : Prog} (hP : DropProg p) {n : Nat} {m m' : Mem} {k e : Word} {r : List Word}
    (h : callW p n "expr_drop_vars" [k, e] m = some (r, m')) : edvW p n m k e = some (r, m') := by
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (edv_spec hP n _ k e) h
  exact hK

/-! ## `expr_drop_vars_list` -/

mutual
/-- **The model of `expr_drop_vars_list(k, ao, al)`** at exec fuel `n`. -/
def edvlW (p : Prog) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, k, ao, al =>
    if al = 0 then some ([0, 0], m)
    else edvlK1 p n k ao al (callW p n "expr_drop_vars" [k, rdW (m.arr64 IW) ao] m)
/-- After the head: the rest, then the consing. -/
def edvlK1 (p : Prog) (n : Nat) (k ao al : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK3 p n (r.headD 0) (edvlW p n m k (ao + 1) (al - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (k ao al : Word) (r : List Word)
theorem edvlW_nil (h : al = 0) : edvlW p (n + 1) m k ao al = some ([0, 0], m) := by simp [edvlW, h]
theorem edvlW_cons (h : al ≠ 0) : edvlW p (n + 1) m k ao al =
    edvlK1 p n k ao al (callW p n "expr_drop_vars" [k, rdW (m.arr64 IW) ao] m) := by simp [edvlW, h]
theorem edvlK1_some : edvlK1 p n k ao al (some (r, m)) =
    bfgK3 p n (r.headD 0) (edvlW p n m k (ao + 1) (al - 1)) := by simp [edvlK1]
end arms
attribute [ind_grind] edvlW_nil edvlW_cons edvlK1_some

theorem edvl_spec {p : Prog} (hP : DropProg p) (n : Nat) :
    ∀ (s₀ : St) (k ao al : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "expr_drop_vars_list" [k, ao, al]
    ⦃fun r s' => LocEq s' s₀ ∧ edvlW p n s₀.mem k ao al = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ k ao al; rw [invoke_eq _ hP.edvl]; simp only [callFn, exprDropVarsList]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ k ao al
    rw [invoke_eq _ hP.edvl]
    simp only [callFn, exprDropVarsList]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "expr_drop_vars", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

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
  · rw [edvlW_nil p n m k ao al hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst hl
    have : xs = [] := by simpa [decHL, hslice?] using hxs.symm
    subst this
    exact ⟨[], a, rfl, by simp [decHL, hslice?], by simp, hS, IWGrow.refl m⟩
  obtain ⟨w, xs', rfl, hw, hwlt, hrest⟩ := decHL_cons hxs hl (by omega)
  rw [edvlW_cons p n m k ao al hl, hw] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [edvlK1])
  rw [edvlK1_some] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hx1, hx2⟩ := edvW_ok vis fe n m m1 a k w r1 hS hwlt (edvCall hP h1)
  have hlpos : 0 < al.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have ho1 : (ao + 1).toNat = ao.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (al - 1).toNat = al.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hb' : (ao + 1).toNat + (al - 1).toNat ≤ iwTop m := by omega
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bfgK3])
  obtain ⟨ys, a3, hrun3, hd3, hb3, hS3, hg3⟩ := ih m1 m3 a1 (ao + 1) (al - 1) xs' r3 hS1
    (by rw [decHL_grow hg1 hb']; exact hrest) (by have := hg1.iw; omega) h3
  rw [bfgK3_some] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bfgK4])
  rw [bfgK4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS5, hg5, hd5, hb5⟩ := consW_stage (consCall hP.toFormersProg h4) hS3 hb3 hx1 hd3
  refine ⟨x :: ys, a3, ?_, by rw [← hx2]; simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega,
    hS5, hg1.trans (hg3.trans hg5)⟩
  simp only [List.mapM_cons, StateT.run_bind, hrun1, except_ok_bind, hrun3]
  rfl

end L.Ind

end
