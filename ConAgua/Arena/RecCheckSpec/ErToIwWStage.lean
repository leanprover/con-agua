module

import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndCallM
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.LdRd
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.IndRealAr
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# ErToIwWStage

`absPrefW`, `apK1`, `apK2`, `absPrefW_nil`, `absPrefW_cons`, `apK1_some` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_ctor_at`'s MEMBER arm -/

/-! ## `abstract_prefix`: one `ar_entry` pass -/

/-- **`abstract_prefix` is its model `absPrefW`** (generated). -/
l_model abstractPrefix_spec (p : Prog) (hp : p.lookup "abstract_prefix" = some abstractPrefix) (har : ArF p)
  fns [hp ↦ absPrefW list]
  specs [arF_spec p har n]
  grind [ind_grind]

theorem absPrefW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (m m' : Mem) (a : AState) (k c e : Word) (r : List Word)
    (h : absPrefW m k c e = some (r, m')) (hS : StageR vis fe m a) (he : H e)
    (_hb : c.toNat + k.toNat < 2 ^ 64) (hA : AbsOK m) :
    ∃ x a', (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)).run a = .ok (x, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x ∧
      AbsOK m' := by
  rw [absPrefW] at h
  obtain ⟨⟨ra, m1⟩, ha, h⟩ := of_K h (absPrefW.k_ar_entry.none ..)
  rw [absPrefW.k_ar_entry.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a1, hrun, ⟨hS1, hg1, hd1, hd2⟩, hA1⟩ := arF_ok dn vis fe e 0 k c he m m1 a ra ha ⟨hS, hA⟩
  exact ⟨x, a1, by simpa [ConRon.Arena.abstractPrefix] using hrun, hS1, hg1, by simpa using hd1,
    by simpa using hd2, hA1⟩

/-! ## `abstract_prefix_list` (the round-1 `while` rewritten as a self-recursion: first element,
then the rest, then `sl_cons`) -/

l_model abstractPrefixList_spec (p : Prog) (hap : p.lookup "abstract_prefix" = some abstractPrefix)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "abstract_prefix_list" = some abstractPrefixList) (har : ArF p)
  fns [hp ↦ aplW]
  specs [abstractPrefix_spec p hap har n, slCons_specW p ha hc hsc n]
  grind [arena_grind] extra [ld64_rd_spec]

/-- **One step of a handle slice** `(o, l)`, `l ≠ 0`: the head read at `o`, the rest at
`(o + 1, l - 1)`. -/
theorem rcSl_step {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hl : l ≠ 0) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∃ x xs' w, xs = x :: xs' ∧ decHL m (o + 1).toNat (l - 1).toNat = some xs' ∧
      rdW (m.arr64 IW) o = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x ∧
      (o + 1).toNat = o.toNat + 1 ∧ (l - 1).toNat + 1 = l.toNat := by
  have hpos : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  obtain ⟨c1, hc1⟩ : ∃ c1, l.toNat = c1 + 1 := ⟨l.toNat - 1, by omega⟩
  rw [hc1] at h
  obtain ⟨x, xs', rfl, hxs', hx⟩ := decHL_cons_r h
  obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hx (by omega)
  rw [UInt64.ofNat_toNat] at hw1
  have hl1 : (l - 1).toNat = c1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  exact ⟨x, xs', w, rfl, by rw [ho1, hl1]; exact hxs', hw1, hw2, hw3, ho1, by omega⟩

theorem aplW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (rP dso dsl : Word) (r : List Word) (ds : List EIdx),
    aplW n m rP dso dsl = some (r, m') → StageR vis fe m a →
    decHL m dso.toNat dsl.toNat = some ds → dso.toNat + dsl.toNat < 2 ^ 64 →
    dso.toNat + dsl.toNat ≤ iwTop m → rP.toNat < 2 ^ 64 → AbsOK m →
    ∃ xs a', (ConRon.Arena.abstractPrefixList rP.toNat ds).run a = .ok (xs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a rP dso dsl r ds h; simp [aplW] at h
  | succ n ih =>
    intro m m' a rP dso dsl r ds h hS hds hb hbt hrP hA
    by_cases hdsl : dsl = 0
    · rw [aplW.arm1 n m rP dso dsl hdsl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hz : dsl.toNat = 0 := by rw [hdsl]; rfl
      rw [hz] at hds
      simp [decHL, hslice?] at hds
      subst hds
      refine ⟨[], a, rfl, hS, IWGrow.refl m, by simp [decHL, hslice?], by simp, hA⟩
    · rw [aplW.arm2 n m rP dso dsl hdsl] at h
      obtain ⟨d, ds', w, rfl, hds', hw1, hw2, hw3, hdso1, hdsl1⟩ := rcSl_step hds hdsl hb
      rw [hw1] at h
      rcases ha : absPrefW m rP 0 w with _ | ⟨ra, m1⟩ <;> simp only [ha, aplW.k_abstract_prefix, reduceCtorEq] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, hd11, hd12, hA1⟩ := absPrefW_ok dn vis fe m m1 a rP 0 w ra ha hS hw2
        (by simpa using hrP) hA
      simp only [UInt64.toNat_zero] at hrun1
      rcases hr : aplW n m1 rP (dso + 1) (dsl - 1) with _ | ⟨r2, m2⟩ <;> simp only [hr, aplW.k_abstract_prefix_list, reduceCtorEq] at h
      have hds1 : decHL m1 (dso + 1).toNat (dsl - 1).toNat = some ds' := by
        rw [decHL_grow hg1 (by omega)]; exact hds'
      obtain ⟨xs2, a2, hrun2, hS2, hg2, hd2, ht2, hA2⟩ := ih m1 m2 a1 rP (dso + 1) (dsl - 1) r2 ds' hr hS1 hds1
        (by omega) (by have := hg1.iw; omega) hrP hA1
      rcases hc : consW n m2 (ra.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, aplW.k_sl_cons, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 ht2 hd11 hd2
      refine ⟨x1 :: xs2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by rw [← hd12]; simpa using hd3,
        by simpa using Nat.le_of_eq ht3, hA2.consW hc⟩
      simp only [ConRon.Arena.abstractPrefixList, StateT.run_bind, ← hw3, hrun1, except_ok_bind, hrun2]
      rfl

/-! ## `target_holes` (loop rewritten as recursion: first hole, the rest, `sl_cons`) -/

mutual
/-- **The model of `target_holes`.** -/
def thW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, tyo, tyl, base =>
    if tyl = 0 then some ([0, 0], m)
    else thK1 n tyo tyl base (fvinternW m base (rdW (m.arr64 IW) tyo))

/-- After the first interning (guarded). -/
def thK1 (n : Nat) (tyo tyl base : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m1) =>
    if 4294967296 ≤ v then none
    else thK2 n v (thW n m1 (tyo + 1) (tyl - 1) (base + 1))

/-- After the recursive call: `sl_cons`. -/
def thK2 (n : Nat) (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => thK3 (consW n m2 v (r.headD 0) (r.tail.headD 0))

/-- After `sl_cons`. -/
def thK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (tyo tyl base v : Word) (r : List Word)
theorem thW_nil (h : tyl = 0) : thW (n + 1) m tyo tyl base = some ([0, 0], m) := by simp [thW, h]
theorem thW_cons (h : tyl ≠ 0) :
    thW (n + 1) m tyo tyl base = thK1 n tyo tyl base (fvinternW m base (rdW (m.arr64 IW) tyo)) := by
  simp [thW, h]
theorem thK1_big (h : 4294967296 ≤ v) : thK1 n tyo tyl base (some (v, m1)) = none := by
  rw [thK1]; simp [h]
theorem thK1_ok (h : ¬ 4294967296 ≤ v) : thK1 n tyo tyl base (some (v, m1)) =
    thK2 n v (thW n m1 (tyo + 1) (tyl - 1) (base + 1)) := by
  rw [thK1]; simp [h]
theorem thK2_some : thK2 n v (some (r, m2)) = thK3 (consW n m2 v (r.headD 0) (r.tail.headD 0)) := by
  rw [thK2]
theorem thK3_some : thK3 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := by rw [thK3]
end arms

grind_pattern [ind_grind] thW_nil => thW (n + 1) m tyo tyl base
grind_pattern [ind_grind] thW_cons => thW (n + 1) m tyo tyl base
grind_pattern [ind_grind] thK1_big => thK1 n tyo tyl base (some (v, m1))
grind_pattern [ind_grind] thK1_ok => thK1 n tyo tyl base (some (v, m1))
grind_pattern [ind_grind] thK2_some => thK2 n v (some (r, m2))
grind_pattern [ind_grind] thK3_some => thK3 (some (r, m3))

theorem targetHoles_spec (p : Prog) (hff : p.lookup "fvar_find" = some fvarFind)
    (hfp : p.lookup "fvar_push" = some fvarPush) (hif : p.lookup "intern_fvar" = some internFVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_holes" = some targetHoles) (n : Nat) :
    ∀ (s₀ : St) (tyo tyl base : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_holes" [tyo, tyl, base]
    ⦃fun r s' => LocEq s' s₀ ∧ thW n s₀.mem tyo tyl base = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ tyo tyl base; rw [invoke_eq _ hp]; simp only [callFn, targetHoles]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ tyo tyl base
    rw [invoke_eq _ hp]
    simp only [callFn, targetHoles]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internFVar_spec p hff hfp hif n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)

theorem thW_ok (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (tyo tyl base : Word) (r : List Word) (tys : List EIdx),
    thW n m tyo tyl base = some (r, m') → StageR vis fe m a →
    decHL m tyo.toNat tyl.toNat = some tys → tyo.toNat + tyl.toNat < 2 ^ 64 →
    tyo.toNat + tyl.toNat ≤ iwTop m → base.toNat + tyl.toNat < 2 ^ 64 →
    ∃ xs a', (ConRon.Arena.targetHoles tys base.toNat).run a = .ok (xs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a tyo tyl base r tys h; simp [thW] at h
  | succ n ih =>
    intro m m' a tyo tyl base r tys h hS htys hb hbt hbase
    by_cases htyl : tyl = 0
    · rw [thW_nil n m tyo tyl base htyl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hz : tyl.toNat = 0 := by rw [htyl]; rfl
      rw [hz] at htys
      simp [decHL, hslice?] at htys
      subst htys
      refine ⟨[], a, rfl, hS, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩
    · rw [thW_cons n m tyo tyl base htyl] at h
      obtain ⟨ty, tys', w, rfl, htys', hw1, hw2, hw3, htyo1, htyl1⟩ := rcSl_step htys htyl hb
      have hbase1 : (base + 1).toNat = base.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [hw1] at h
      rcases hf : fvinternW m base w with _ | ⟨v, m1⟩ <;> rw [hf] at h <;>
        try (simp only [thK1, reduceCtorEq] at h; done)
      by_cases hv : 4294967296 ≤ v
      · rw [thK1_big n m1 tyo tyl base v hv] at h; simp at h
      rw [thK1_ok n m1 tyo tyl base v hv] at h
      have hv32 : v.toNat < 2 ^ 32 := by
        have : ¬ (4294967296 : Nat) ≤ v.toNat := hv
        omega
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internFVar_stage hS base w hw2 hf
      rcases hr : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with _ | ⟨r2, m2⟩ <;> simp only [hr, thK2, reduceCtorEq] at h
      have htys1 : decHL m1 (tyo + 1).toNat (tyl - 1).toNat = some tys' := by
        rw [decHL_grow hg1 (by omega)]; exact htys'
      obtain ⟨xs2, a2, hrun2, hS2, hg2, hd2, ht2⟩ := ih m1 m2 a1 (tyo + 1) (tyl - 1) (base + 1) r2 tys' hr hS1
        htys1 (by omega) (by have := hg1.iw; omega) (by omega)
      rcases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, thK3, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 ht2 hv32 hd2
      refine ⟨decE v :: xs2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa [decE_eq] using hd3, by simpa using Nat.le_of_eq ht3⟩
      rw [hbase1] at hrun2
      simp only [ConRon.Arena.targetHoles, ConRon.Arena.internFVarE, StateT.run_bind]
      rw [← hw3, show (decI w : EIdx) = decE w from rfl]
      simp only [hrun1, except_ok_bind, hrun2]
      rfl

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_pi_doms_with` (loop rewritten as recursion on the binder telescope) -/

mutual
/-- **The model of `target_pi_doms_with`.** -/
def pdW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, xo, xl, e =>
    if xl = 0 then some ([1, 0, 0], m)
    else if tagW e ≠ 6 then some ([0, 0, 0], m)
    else if eViewW m e = [] then none
    else pdK1 n xo xl ((eViewW m e).tail.headD 0)
      (i1F m [CWF, (eViewW m e).tail.tail.headD 0, rdW (m.arr64 IW) xo, 0])

/-- After `instantiate1_fast`. -/
def pdK1 (n : Nat) (xo xl d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => pdK2 n d (pdW n m1 (xo + 1) (xl - 1) (r.headD 0))

/-- After the recursive call: `sl_cons`. -/
def pdK2 (n : Nat) (d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if r.headD 0 = 0 then some ([0, 0, 0], m2)
    else pdK3 (consW n m2 d (r.tail.headD 0) (r.tail.tail.headD 0))

/-- After `sl_cons`. -/
def pdK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([1, r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (xo xl e d : Word) (r : List Word)
theorem pdW_nil (h : xl = 0) : pdW (n + 1) m xo xl e = some ([1, 0, 0], m) := by simp [pdW, h]
theorem pdW_nf (h : xl ≠ 0) (h1 : tagW e ≠ 6) : pdW (n + 1) m xo xl e = some ([0, 0, 0], m) := by
  simp [pdW, h, h1]
theorem pdW_ev (h : xl ≠ 0) (h1 : ¬ tagW e ≠ 6) (h2 : eViewW m e = []) :
    pdW (n + 1) m xo xl e = none := by
  simp only [pdW, h, h1, h2, ite_false, ite_true]
theorem pdW_cons (h : xl ≠ 0) (h1 : ¬ tagW e ≠ 6) (h2 : eViewW m e ≠ []) : pdW (n + 1) m xo xl e =
    pdK1 n xo xl ((eViewW m e).tail.headD 0)
      (i1F m [CWF, (eViewW m e).tail.tail.headD 0, rdW (m.arr64 IW) xo, 0]) := by
  simp only [pdW, h, h1, h2, ite_false]
theorem pdK1_some : pdK1 n xo xl d (some (r, m1)) = pdK2 n d (pdW n m1 (xo + 1) (xl - 1) (r.headD 0)) := by
  rw [pdK1]
theorem pdK2_none (h : r.headD 0 = 0) : pdK2 n d (some (r, m2)) = some ([0, 0, 0], m2) := by
  rw [pdK2, ite_eq_left h]
theorem pdK2_ok (h : r.headD 0 ≠ 0) : pdK2 n d (some (r, m2)) =
    pdK3 (consW n m2 d (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  rw [pdK2, ite_eq_right h]
theorem pdK3_some : pdK3 (some (r, m3)) = some ([1, r.headD 0, r.tail.headD 0], m3) := by rw [pdK3]
end arms

grind_pattern [ind_grind] pdW_nil => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdW_nf => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdW_ev => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdW_cons => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdK1_some => pdK1 n xo xl d (some (r, m1))
grind_pattern [ind_grind] pdK2_none => pdK2 n d (some (r, m2))
grind_pattern [ind_grind] pdK2_ok => pdK2 n d (some (r, m2))
grind_pattern [ind_grind] pdK3_some => pdK3 (some (r, m3))

theorem targetPiDomsWith_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_pi_doms_with" = some targetPiDomsWith) (hi1 : I1Prog p) (n : Nat) :
    ∀ (s₀ : St) (xo xl e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pi_doms_with" [xo, xl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pdW n s₀.mem xo xl e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ xo xl e; rw [invoke_eq _ hp]; simp only [callFn, targetPiDomsWith]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ xo xl e
    rw [invoke_eq _ hp]
    simp only [callFn, targetPiDomsWith]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, i1F_spec p hi1 n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)

/-- The result words of `target_pi_doms_with` against the twin's result. -/
def PdRes (m' : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some ds => r.headD 0 = 1 ∧ decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ds ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m'

/-! ## `er_to_iw` and `cv_lps` under the stage relation -/

theorem erToIwW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {k : IdxKind} {xs : List (Idx k)}
    (h : erToIwW n m o l = some (r, m')) (hS : StageR vis fe m a)
    (hxs : hslice? (erA m) o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ m'.arr64 EREC = m.arr64 EREC := by
  have hsz := hS.iw.iwSize
  obtain ⟨hr, hd, hg, hf, hE, ht⟩ := erToIwW_dec h hsz hS.iw.ctl hxs
  have hroom : iwTop m' ≤ (m'.arr64 IW).size := by
    rw [← ht, hf.size IW]
    simp only [erToIwW] at h
    cases hal : allocW m l with
    | none => simp [hal] at h
    | some qm =>
      obtain ⟨q, m1⟩ := qm
      obtain ⟨hq, -, hr2⟩ := allocW_facts hal hsz
      simp only [hal] at h
      cases hcp : erCopyW (n - 1) m1 q o l with
      | none => simp [hcp] at h
      | some m2 =>
        simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        subst hq
        simpa using hr2
  subst hr
  exact ⟨⟨CheckR.frame_iw hf hS.check, hS.iw.of_iw hf hroom⟩, hg, by simpa using hd, by simpa using ht, hE⟩

/-- The model of `cv_lps(q)`. -/
def cvLpsW (n : Nat) (m : Mem) (q : Word) : Option (List Word × Mem) :=
  erToIwW (n - 1) m (erRd m (q + CV.lpsOff)) (erRd m (q + CV.lpsLen))

theorem cvLps_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "cv_lps" = some cvLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ cvLpsW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, cvLps]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erToIw_specW2 p ha hc he n] <;>
      finish (gen := 20) [cvLpsW, rdW_eq, erRd]

theorem cvLpsW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : cvLpsW n m q = some (r, m')) (hS : StageR vis fe m a)
    (hcv : decCVp m q.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨w1, w2, hw1, hw2, hs⟩ := decCV_slice (show decCV (erecP m) q.toNat = some cv from hcv)
  have hr1 : erRd m (q + CV.lpsOff) = w1 := (erRdOK m).at _ rfl hw1
  have hr2 : erRd m (q + CV.lpsLen) = w2 := (erRdOK m).at _ rfl hw2
  simp only [cvLpsW, hr1, hr2] at h
  obtain ⟨hS', hg, hdec, ht, hE⟩ := erToIwW_stage h hS hs
  exact ⟨hS', hg, hE, hdec, ht⟩

/-! ## `target_ctor_at` -/

/-- After `inst_lp_fast`. -/
def tcK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)

/-- After `cv_lps`. -/
def tcK1 (cR : CallM) (n : Nat) (us c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    tcK2 (cR n "inst_lp_fast" [CWF, r.headD 0, r.tail.headD 0, us, erRd m1 (c + CV.type)] m1)

/-- **The model of `target_ctor_at`** (its `inst_lp_fast` read through `cR`). -/
def tcW (cR : CallM) (n : Nat) (m : Mem) (M c : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (M + 8) ≠ 0 then some ([erRd m (c + CV.type)], m)
  else tcK1 cR n (rdW (m.arr64 IW) (M + 1)) c (cvLpsW n m c)

theorem decTM_ds {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    ∃ o l, iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧ decHL m o l = some M.ds := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some h4
  exact ⟨o, l, ho, by simpa using hl, hd⟩

end L.Ind

end

end
