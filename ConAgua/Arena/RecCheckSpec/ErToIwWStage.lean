import ConAgua.Arena.IlpRd
import ConAgua.Arena.RecCheckSpec.DecHLTruncMBound
import ConAgua.Arena.RecClassSpec.CloseLams

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

/-! ## `abstract_prefix` (the round-1 `while` rewritten as a self-recursion) -/

mutual
/-- **The model of `abstract_prefix`.** -/
def absPrefW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, k, c, e =>
    if k = 0 then some ([e], m)
    else apK1 n k c (abF m [CWF, e, k - 1, c])

/-- After `abstract1_fast`. -/
def apK1 (n : Nat) (k c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => apK2 (absPrefW n m1 (k - 1) (c + 1) (r.headD 0))

/-- After the recursive call. -/
def apK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 : Mem) (k c e : Word) (r : List Word)
theorem absPrefW_nil (h : k = 0) : absPrefW (n + 1) m k c e = some ([e], m) := by simp [absPrefW, h]
theorem absPrefW_cons (h : k ≠ 0) :
    absPrefW (n + 1) m k c e = apK1 n k c (abF m [CWF, e, k - 1, c]) := by
  simp [absPrefW, h]
theorem apK1_some : apK1 n k c (some (r, m1)) = apK2 (absPrefW n m1 (k - 1) (c + 1) (r.headD 0)) := by
  rw [apK1]
theorem apK2_some : apK2 (some (r, m)) = some ([r.headD 0], m) := by
  rw [apK2]
end arms

grind_pattern [ind_grind] absPrefW_nil => absPrefW (n + 1) m k c e
grind_pattern [ind_grind] absPrefW_cons => absPrefW (n + 1) m k c e
grind_pattern [ind_grind] apK1_some => apK1 n k c (some (r, m1))
grind_pattern [ind_grind] apK2_some => apK2 (some (r, m))

theorem abstractPrefix_spec (p : Prog) (hp : p.lookup "abstract_prefix" = some abstractPrefix) (hab : AbF p)
    (n : Nat) :
    ∀ (s₀ : St) (k c e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix" [k, c, e]
    ⦃fun r s' => LocEq s' s₀ ∧ absPrefW n s₀.mem k c e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ k c e; rw [invoke_eq _ hp]; simp only [callFn, abstractPrefix]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ k c e
    rw [invoke_eq _ hp]
    simp only [callFn, abstractPrefix]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        abF_spec p hab n, ih] <;>
      finish (gen := 20)

theorem absPrefW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k c e : Word) (r : List Word),
    absPrefW n m k c e = some (r, m') → StageR dn vis fe m a → H e → c.toNat + k.toNat < 2 ^ 64 →
    AbsOK m →
    ∃ x a', (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x ∧
      AbsOK m' := by
  induction n with
  | zero => intro m m' a k c e r h; simp [absPrefW] at h
  | succ n ih =>
    intro m m' a k c e r h hS he hb hA
    by_cases hk : k = 0
    · rw [absPrefW_nil n m k c e hk] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hk0 : k.toNat = 0 := by rw [hk]; rfl
      rw [hk0]
      exact ⟨decI e, a, rfl, hS, IWGrow.refl m, by simpa using he, rfl, hA⟩
    · rw [absPrefW_cons n m k c e hk] at h
      have hpos : 1 ≤ k.toNat := by
        rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hk
        · omega
      have hk1 : (k - 1).toNat = k.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp
      have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rcases ha : abF m [CWF, e, k - 1, c] with _ | ⟨ra, m1⟩ <;> simp only [ha, apK1, reduceCtorEq] at h
      obtain ⟨x1, a1, hrun1, ⟨hS1, hg1, hd1, hd2⟩, hA1⟩ :=
        abF_ok dn vis fe e (k - 1) c he m m1 a ra ha ⟨hS, hA⟩
      rcases hr : absPrefW n m1 (k - 1) (c + 1) (ra.headD 0) with _ | ⟨r2, m2⟩ <;> simp only [hr, apK2, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨x2, a2, hrun2, hS2, hg2, hd21, hd22, hA2⟩ := ih m1 m2 a1 (k - 1) (c + 1) (ra.headD 0) r2 hr hS1 hd1
        (by rw [hk1, hc1]; omega) hA1
      refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, by simpa using hd21, by simpa using hd22, hA2⟩
      rw [CWF_eq, hk1] at hrun1
      have hz : k.toNat = (k.toNat - 1) + 1 := by omega
      rw [hk1, hc1] at hrun2
      rw [hz]
      simp only [ConRon.Arena.abstractPrefix, StateT.run_bind, hrun1, except_ok_bind, ← hd2]
      exact hrun2

/-! ## `abstract_prefix_list` (the round-1 `while` rewritten as a self-recursion: first element,
then the rest, then `sl_cons`) -/

l_model abstractPrefixList_spec (p : Prog) (hap : p.lookup "abstract_prefix" = some abstractPrefix)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "abstract_prefix_list" = some abstractPrefixList) (hab : AbF p)
  fns [hp ↦ aplW]
  specs [abstractPrefix_spec p hap hab n, slCons_specW p ha hc hsc n]
  grind [arena_grind] simp [getElem_rdW']

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
    aplW n m rP dso dsl = some (r, m') → StageR dn vis fe m a →
    decHL m dso.toNat dsl.toNat = some ds → dso.toNat + dsl.toNat < 2 ^ 64 →
    dso.toNat + dsl.toNat ≤ iwTop m → rP.toNat < 2 ^ 64 → AbsOK m →
    ∃ xs a', (ConRon.Arena.abstractPrefixList rP.toNat ds).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
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
      rcases ha : absPrefW n m rP 0 w with _ | ⟨ra, m1⟩ <;> simp only [ha, aplW.k_abstract_prefix, reduceCtorEq] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, hd11, hd12, hA1⟩ := absPrefW_ok dn vis fe n m m1 a rP 0 w ra ha hS hw2
        (by simpa using hrP) hA
      simp only [UInt64.toNat_zero] at hrun1
      rcases hr : aplW n m1 rP (dso + 1) (dsl - 1) with _ | ⟨r2, m2⟩ <;> simp only [hr, aplW.k_abstract_prefix_list, reduceCtorEq] at h
      have hds1 : decHL m1 (dso + 1).toNat (dsl - 1).toNat = some ds' := by
        rw [decHL_grow hg1 (by omega)]; exact hds'
      obtain ⟨xs2, a2, hrun2, hS2, hg2, hd2, ht2, hA2⟩ := ih m1 m2 a1 rP (dso + 1) (dsl - 1) r2 ds' hr hS1 hds1
        (by omega) (by have := hg1.1; omega) hrP hA1
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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internFVar_spec p hff hfp hif n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)

theorem thW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (tyo tyl base : Word) (r : List Word) (tys : List EIdx),
    thW n m tyo tyl base = some (r, m') → StageR dn vis fe m a →
    decHL m tyo.toNat tyl.toNat = some tys → tyo.toNat + tyl.toNat < 2 ^ 64 →
    tyo.toNat + tyl.toNat ≤ iwTop m → base.toNat + tyl.toNat < 2 ^ 64 →
    ∃ xs a', (ConRon.Arena.targetHoles tys base.toNat).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
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
        htys1 (by omega) (by have := hg1.1; omega) (by omega)
      rcases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, thK3, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 ht2 hv32 hd2
      refine ⟨decE v :: xs2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa [decE_eq] using hd3, by simpa using Nat.le_of_eq ht3⟩
      rw [hbase1] at hrun2
      simp only [ConRon.Arena.targetHoles, ConRon.Arena.internFVarE, StateT.run_bind]
      rw [← hw3, show (decI w : EIdx) = decE w from rfl]
      simp only [hrun1, except_ok_bind, hrun2]
      rfl

/-! ## `target_pin_tys` (loop rewritten as recursion) -/

mutual
/-- **The model of `target_pin_tys`.** -/
def tptW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, d, xo, xl =>
    if xl = 0 then some ([], m)
    else tptK cR n vis d xo xl (cR n "infer_type_core" [vis, d, rdW (m.arr64 IW) xo] m)

/-- After `infer_type_core`. -/
def tptK (cR : CallM) (n : Nat) (vis d xo xl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => tptK2 (tptW cR n m1 vis d (xo + 1) (xl - 1))

/-- After the recursive call: the function falls off its end. -/
def tptK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => some ([], m2)
end

section arms
variable (cR : CallM) (n : Nat) (m m1 : Mem) (vis d xo xl : Word) (r : List Word)
theorem tptW_nil (h : xl = 0) : tptW cR (n + 1) m vis d xo xl = some ([], m) := by simp [tptW, h]
theorem tptW_cons (h : xl ≠ 0) :
    tptW cR (n + 1) m vis d xo xl = tptK cR n vis d xo xl (cR n "infer_type_core" [vis, d, rdW (m.arr64 IW) xo] m) := by
  simp [tptW, h]
theorem tptK_some : tptK cR n vis d xo xl (some (r, m1)) = tptK2 (tptW cR n m1 vis d (xo + 1) (xl - 1)) := by rw [tptK]
theorem tptK2_some : tptK2 (some (r, m1)) = some ([], m1) := by rw [tptK2]
end arms

grind_pattern [ind_grind] tptW_nil => tptW cR (n + 1) m vis d xo xl
grind_pattern [ind_grind] tptW_cons => tptW cR (n + 1) m vis d xo xl
grind_pattern [ind_grind] tptK_some => tptK cR n vis d xo xl (some (r, m1))
grind_pattern [ind_grind] tptK2_some => tptK2 (some (r, m1))

theorem targetPinTys_spec (p : Prog) (hp : p.lookup "target_pin_tys" = some targetPinTys) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis d xo xl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pin_tys" [vis, d, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧ tptW cR n s₀.mem vis d xo xl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis d xo xl; rw [invoke_eq _ hp]; simp only [callFn, targetPinTys]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis d xo xl
    rw [invoke_eq _ hp]
    simp only [callFn, targetPinTys]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hcR n "infer_type_core", ih] <;>
      finish (gen := 20)

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_pi_doms_with` (loop rewritten as recursion on the binder telescope) -/

mutual
/-- **The model of `target_pi_doms_with`.** -/
def pdW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, xo, xl, e =>
    if xl = 0 then some ([1, 0, 0], m)
    else if e >>> 28 ≠ 6 then some ([0, 0, 0], m)
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
theorem pdW_nf (h : xl ≠ 0) (h1 : e >>> 28 ≠ 6) : pdW (n + 1) m xo xl e = some ([0, 0, 0], m) := by
  simp [pdW, h, h1]
theorem pdW_ev (h : xl ≠ 0) (h1 : ¬ e >>> 28 ≠ 6) (h2 : eViewW m e = []) :
    pdW (n + 1) m xo xl e = none := by
  simp only [pdW, h, h1, h2, ite_false, ite_true]
theorem pdW_cons (h : xl ≠ 0) (h1 : ¬ e >>> 28 ≠ 6) (h2 : eViewW m e ≠ []) : pdW (n + 1) m xo xl e =
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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, i1F_spec p hi1 n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)

/-- The result words of `target_pi_doms_with` against the twin's result. -/
def PdRes (m' : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some ds => r.headD 0 = 1 ∧ decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ds ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m'

/-! ## `er_to_iw` and `cv_lps` under the stage relation -/

theorem erToIwW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {k : IdxKind}
    (h : erToIwW n m o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : l.toNat = 0 ∨ o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      (decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat : Option (List (Idx k))) =
        hslice? (erA m) o.toNat l.toNat ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ m'.arr64 EREC = m.arr64 EREC := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  rcases hsrc with hl0 | hsrc
  · have hl : l = 0 := UInt64.toNat_inj.mp (by simpa using hl0)
    subst hl
    simp only [erToIwW] at h
    cases hal : allocW m 0 with
    | none => simp [hal] at h
    | some qm =>
    obtain ⟨q, m1⟩ := qm
    obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hS
    obtain ⟨-, hm1, -⟩ := allocW_facts hal hsz
    simp only [hal] at h
    obtain _ | n := n
    · simp [erCopyW] at h
    obtain _ | n := n
    · simp [erCopyW] at h
    simp only [Nat.add_sub_cancel, erCopyW_nil n _ _ _ _ rfl, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hS1, hg1, by simp [decHL, hslice?], ?_, ?_⟩
    · simp only [List.headD_cons, List.tail_cons]; rw [hq, ht1]
    · rw [hm1]; simp only [allocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  obtain ⟨hr, hd, hg, hf, hE, ht⟩ := erToIwW_dec (k := k) h hsz hc hEs hsrc
  have hroom : iwTop m' ≤ (m'.arr64 IW).size := by
    rw [← ht, hf.2.2.1 IW]
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
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  subst hr
  refine ⟨⟨CheckR.frame_iw hf hS.1, hroom, ?_, ?_, ?_, ?_⟩, hg, by simpa using hd, by simpa using ht, hE⟩
  · simp only [erTop, h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc

/-- The model of `cv_lps(q)`. -/
def cvLpsW (n : Nat) (m : Mem) (q : Word) : Option (List Word × Mem) :=
  erToIwW (n - 1) m (rdW (m.arr64 EREC) (q + 1)) (rdW (m.arr64 EREC) (q + 2))

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erToIw_specW2 p ha hc he n] <;>
      finish (gen := 20) [cvLpsW, rdW_eq]

theorem cvLpsW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : cvLpsW n m q = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCVp m q.toNat = some cv) (hq : q.toNat + 3 < 2 ^ 64)
    (hlpb : (rdW (m.arr64 EREC) (q + 2)).toNat = 0 ∨
      (rdW (m.arr64 EREC) (q + 1)).toNat + (rdW (m.arr64 EREC) (q + 2)).toNat ≤ (m.arr64 EREC).size) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨-, hl, -⟩ := decCV_some (a := erA m) (q := q.toNat) hcv
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o', ho, l', hl', hs⟩ := hl
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hr1 : rdW (m.arr64 EREC) (q + 1) = UInt64.ofNat o' := by
    simp only [nat?, erA, Option.map_eq_some_iff] at ho
    obtain ⟨w, hw, rfl⟩ := ho
    simp [rdW, hq1, hw]
  have hr2 : rdW (m.arr64 EREC) (q + 2) = UInt64.ofNat l' := by
    simp only [nat?, erA, Option.map_eq_some_iff] at hl'
    obtain ⟨w, hw, rfl⟩ := hl'
    simp [rdW, hq2, hw]
  have hob : o' < 2 ^ 64 := by
    simp only [nat?, erA, Option.map_eq_some_iff] at ho
    obtain ⟨w, hw, rfl⟩ := ho; exact w.toNat_lt
  have hlb : l' < 2 ^ 64 := by
    simp only [nat?, erA, Option.map_eq_some_iff] at hl'
    obtain ⟨w, hw, rfl⟩ := hl'; exact w.toNat_lt
  simp only [cvLpsW, hr1, hr2] at h
  have hsrc := hlpb
  rw [hr1, hr2] at hsrc
  obtain ⟨hS', hg, hdec, ht, hE⟩ := erToIwW_stage (k := IdxKind.name) h hS hsrc
  refine ⟨hS', hg, hE, ?_, ht⟩
  · rw [hdec]; rw [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]; exact hs

/-! ## `target_ctor_at` -/

/-- After `inst_lp_fast`. -/
def tcK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)

/-- After `cv_lps`. -/
def tcK1 (cR : CallM) (n : Nat) (us c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    tcK2 (cR n "inst_lp_fast" [CWF, r.headD 0, r.tail.headD 0, us, rdW (m1.arr64 EREC) (c + 3)] m1)

/-- **The model of `target_ctor_at`** (its `inst_lp_fast` read through `cR`). -/
def tcW (cR : CallM) (n : Nat) (m : Mem) (M c : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (M + 8) ≠ 0 then some ([rdW (m.arr64 EREC) (c + 3)], m)
  else tcK1 cR n (rdW (m.arr64 IW) (M + 1)) c (cvLpsW n m c)

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

def tmpK3 (cR : CallM) (N : Nat) (vis rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tmpK4 (cR N "infer_type_core" [vis, rP, r3.headD 0] m3)

def tmpK2 (cR : CallM) (N : Nat) (vis rP M : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m2) =>
    if 4294967296 ≤ hd then none
    else tmpK3 cR N vis rP (mknF m2
      [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)])

def tmpK1 (cR : CallM) (N : Nat) (vis rP M : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => tmpK2 cR N vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1)))

/-- **The model of `target_major_pins`** (the core's call read through `cR`). -/
def tmpW (cR : CallM) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, vis, rP, M =>
    if rdW (m.arr64 IW) (M + 8) ≠ 0 then some ([], m)
    else tmpK1 cR N vis rP M (tptW cR N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3)))

section arms
variable (cR : CallM) (N : Nat) (m m1 m2 m3 m4 : Mem) (vis rP M hd : Word) (r1 r3 r4 : List Word)
theorem tmpW_mem (h : rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW cR (N + 1) m vis rP M = some ([], m) := by
  simp only [tmpW]; rw [ite_eq_left h]
theorem tmpW_out (h : ¬ rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW cR (N + 1) m vis rP M =
    tmpK1 cR N vis rP M (tptW cR N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3))) := by
  simp only [tmpW]; rw [ite_eq_right h]
theorem tmpK1_some : tmpK1 cR N vis rP M (some (r1, m1)) =
    tmpK2 cR N vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1))) := rfl
theorem tmpK2_some : tmpK2 cR N vis rP M (some (hd, m2)) =
    if 4294967296 ≤ hd then none
    else tmpK3 cR N vis rP (mknF m2 [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)]) := rfl
theorem tmpK3_some : tmpK3 cR N vis rP (some (r3, m3)) =
    tmpK4 (cR N "infer_type_core" [vis, rP, r3.headD 0] m3) := rfl
theorem tmpK4_some : tmpK4 (some (r4, m4)) = some ([], m4) := rfl
end arms

grind_pattern [ind_grind] tmpW_mem => tmpW cR (N + 1) m vis rP M
grind_pattern [ind_grind] tmpW_out => tmpW cR (N + 1) m vis rP M
grind_pattern [ind_grind] tmpK1_some => tmpK1 cR N vis rP M (some (r1, m1))
grind_pattern [ind_grind] tmpK2_some => tmpK2 cR N vis rP M (some (hd, m2))
grind_pattern [ind_grind] tmpK3_some => tmpK3 cR N vis rP (some (r3, m3))
grind_pattern [ind_grind] tmpK4_some => tmpK4 (some (r4, m4))

theorem targetMajorPins_spec (p : Prog) (h : TmpProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat)
    (s₀ : St) (vis rP M : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, M]
    ⦃fun r s' => LocEq s' s₀ ∧ tmpW cR N s₀.mem vis rP M = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tmp]
  simp only [callFn, targetMajorPins]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetPinTys_spec p h.tpt cR hcR N, internConst_spec p h.cf h.cp h.ic N,
        mknF_spec p h.ad N, hcR N "infer_type_core"] <;>
      finish (gen := 20) [rdW_eq]

theorem decTM_ds {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    ∃ o l, iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧ decHL m o l = some M.ds := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some h4
  exact ⟨o, l, ho, by simpa using hl, hd⟩

end L.Ind

end

end
