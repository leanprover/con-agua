import ConAgua.Arena.RecGen
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.RecGenSpec
import ConAgua.Arena.IndSumSpec2

/-!
# More refinements of `RecGen` (lane `indproofs`, helper `recb`)

Leaves whose loops were rewritten as self-recursions on the shifted slice.
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `class_rule_ok_domains`: `rbs.allM (constsResolveFFast fe₀)`, the model of `idx_args_resolve` -/

theorem classRuleOkDomains_spec (p : Prog)
    (hp : p.lookup "class_rule_ok_domains" = some classRuleOkDomains) (n : Nat) :
    ∀ (s₀ : St) (v o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rule_ok_domains" [v, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ iarW n s₀.mem v o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ v o l; rw [invoke_eq _ hp]; simp only [callFn, classRuleOkDomains]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ v o l
    rw [invoke_eq _ hp]
    simp only [callFn, classRuleOkDomains]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "consts_resolve_ffast" n, ih] <;>
      finish (gen := 20)

/-- The twin's `allM` is `idxArgsResolve`. -/
theorem allM_resolve_eq (fe : IFEnv) : ∀ xs : List EIdx,
    xs.allM (fun b => constsResolveFFast fe b) = idxArgsResolve fe xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.allM_cons, idxArgsResolve, ih]

/-- **`class_rule_ok_domains`** is `rbs.allM (constsResolveFFast fe₀)` (`fe₀ = feR.restrictTo visT`, the
view `visT`), through the stub `consts_resolve_ffast`. A piece of `classRuleOk`. -/
theorem classRuleOkDomains_refines (p : Prog)
    (hp : p.lookup "class_rule_ok_domains" = some classRuleOkDomains) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe₀ : IFEnv) (visT o l : Word) (xs : List EIdx)
    (hS : StageR dn visT fe₀ s₀.mem a₀) (hd : decHL s₀.mem o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rule_ok_domains" [visT, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (xs.allM (fun b => constsResolveFFast fe₀ b)) a₀ ∧
      KeepPost dn visT fe₀ decW0B s₀.mem s'.mem (AM.st (xs.allM (fun b => constsResolveFFast fe₀ b)) a₀) r
        (AM.res (xs.allM (fun b => constsResolveFFast fe₀ b)) a₀); ⊤⦄ := by
  rw [allM_resolve_eq]
  refine triple_post (classRuleOkDomains_spec p hp n s₀ visT o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost⟩ := iarW_ok dn fe₀ n _ _ a₀ visT o l xs r hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost⟩

/-! ## `class_key_of_closed`: `ds.allM` of the `bvarB`/`fvarB` closedness test -/

mutual
/-- **The model of `class_key_of_closed`.** -/
def ckcW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, nP, o, l =>
    if l = 0 then some ([1], m)
    else ckcK1 n nP o l (rdW (m.arr64 IW) o) (bvbF m [CWF, rdW (m.arr64 IW) o])
/-- After `bvar_b`. -/
def ckcK1 (n : Nat) (nP o l e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) =>
    if rb.headD 0 ≠ 0 then some ([0], m1) else ckcK2 n nP o l (fvbF m1 [CWF, e])
/-- After `fvar_b`. -/
def ckcK2 (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m2) =>
    if nP < rf.headD 0 then some ([0], m2) else ckcK3 (ckcW n m2 nP (o + 1) (l - 1))
/-- After the recursive call: its first word. -/
def ckcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (nP o l e : Word) (rb rf r : List Word)
theorem ckcW_nil (hl : l = 0) : ckcW (n + 1) m nP o l = some ([1], m) := by simp [ckcW, hl]
theorem ckcW_cons (hl : l ≠ 0) :
    ckcW (n + 1) m nP o l =
      ckcK1 n nP o l (rdW (m.arr64 IW) o) (bvbF m [CWF, rdW (m.arr64 IW) o]) := by
  simp [ckcW, hl]
theorem ckcK1_open (h : rb.headD 0 ≠ 0) : ckcK1 n nP o l e (some (rb, m1)) = some ([0], m1) := by
  rw [ckcK1, if_pos h]
theorem ckcK1_closed (h : ¬ rb.headD 0 ≠ 0) :
    ckcK1 n nP o l e (some (rb, m1)) = ckcK2 n nP o l (fvbF m1 [CWF, e]) := by
  rw [ckcK1, if_neg h]
theorem ckcK2_open (h : nP < rf.headD 0) : ckcK2 n nP o l (some (rf, m2)) = some ([0], m2) := by
  rw [ckcK2, if_pos h]
theorem ckcK2_closed (h : ¬ nP < rf.headD 0) :
    ckcK2 n nP o l (some (rf, m2)) = ckcK3 (ckcW n m2 nP (o + 1) (l - 1)) := by
  rw [ckcK2, if_neg h]
theorem ckcK3_some : ckcK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] ckcW_nil => ckcW (n + 1) m nP o l
grind_pattern [ind_grind] ckcW_cons => ckcW (n + 1) m nP o l
grind_pattern [ind_grind] ckcK1_open => ckcK1 n nP o l e (some (rb, m1))
grind_pattern [ind_grind] ckcK1_closed => ckcK1 n nP o l e (some (rb, m1))
grind_pattern [ind_grind] ckcK2_open => ckcK2 n nP o l (some (rf, m2))
grind_pattern [ind_grind] ckcK2_closed => ckcK2 n nP o l (some (rf, m2))
grind_pattern [ind_grind] ckcK3_some => ckcK3 (some (r, m))

theorem classKeyOfClosed_spec (p : Prog) (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "class_key_of_closed" = some classKeyOfClosed) (n : Nat) :
    ∀ (s₀ : St) (nP o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_key_of_closed" [nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ckcW n s₀.mem nP o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP o l; rw [invoke_eq _ hp]; simp only [callFn, classKeyOfClosed]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP o l
    rw [invoke_eq _ hp]
    simp only [callFn, classKeyOfClosed]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvbF_spec p hb n, fvbF_spec p hf n, ih] <;>
      finish (gen := 20)

/-- The twin's per-parameter closedness test. -/
def keyClosedTest (nP : Nat) (x : EIdx) : AM Bool := do
  if (← bvarB coreWalkFuel x) != 0 then pure false
  else pure ((← fvarB coreWalkFuel x) ≤ nP)

theorem ckcW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (v nP o l : Word) (xs : List EIdx) (r : List Word),
    ckcW n m nP o l = some (r, m') → StageR dn v fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ b a', (xs.allM (keyClosedTest nP.toNat)).run a = .ok (b, a') ∧
      KeepPost dn v fe decW0B m m' a' r b := by
  induction n with
  | zero => intro m m' a v nP o l xs r h; simp [ckcW] at h
  | succ n ih =>
    intro m m' a v nP o l xs r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [ckcW_nil n m nP o 0 rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl m, by simp [decW0B]⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [ckcW_cons n m nP o l hl, hw] at h
      cases h2 : bvbF m [CWF, w] with
      | none => rw [h2] at h; simp [ckcK1] at h
      | some x2 =>
      obtain ⟨rb, m1⟩ := x2
      rw [h2] at h
      obtain ⟨kb, a1, hrun1, hS1, hg1, hkb⟩ := bvbF_ok dn v fe CWF w hw32 m m1 a rb h2 hS
      rw [CWF_eq] at hrun1
      by_cases hz : rb.headD 0 ≠ 0
      · rw [ckcK1_open n m1 nP o l w rb hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hk : kb ≠ 0 := by
          intro e
          have : (rb.headD 0).toNat = 0 := by rw [hkb, e]
          exact hz (UInt64.toNat_inj.mp (by simpa using this))
        refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
        simp only [List.allM_cons, StateT.run_bind, keyClosedTest]
        rw [hrun1]
        simp only [bind, Except.bind, hk, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
        rfl
      · rw [ckcK1_closed n m1 nP o l w rb hz] at h
        have hk : kb = 0 := by
          have hz' : rb.headD 0 = 0 := by simpa using hz
          rw [← hkb, hz']; rfl
        cases h3 : fvbF m1 [CWF, w] with
        | none => rw [h3] at h; simp [ckcK2] at h
        | some x3 =>
        obtain ⟨rf, m2⟩ := x3
        rw [h3] at h
        obtain ⟨kf, a2, hrun2, hS2, hg2, hkf⟩ := fvbF_ok dn v fe CWF w hw32 m1 m2 a1 rf h3 hS1
        rw [CWF_eq] at hrun2
        have hg12 := hg1.trans hg2
        have hlt : (nP < rf.headD 0) ↔ ¬ kf ≤ nP.toNat := by
          rw [UInt64.lt_iff_toNat_lt, hkf]; omega
        have hrunT : (keyClosedTest nP.toNat (decI w)).run a = .ok (decide (kf ≤ nP.toNat), a2) := by
          simp only [keyClosedTest, StateT.run_bind]
          rw [hrun1]
          simp only [bind, Except.bind, hk, bne_self_eq_false, Bool.false_eq_true, ite_false]
          simp only [StateT.bind, StateT.run] at hrun2 ⊢
          rw [hrun2]
          rfl
        by_cases hn : nP < rf.headD 0
        · rw [ckcK2_open n m2 nP o l rf hn] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hn' := hlt.mp hn
          refine ⟨false, a2, ?_, hS2, hg12, by simp [decW0B]⟩
          simp only [List.allM_cons, StateT.run_bind]
          rw [hrunT]
          simp only [bind, Except.bind, hn', decide_false, Bool.false_eq_true, ite_false]
          rfl
        · rw [ckcK2_closed n m2 nP o l rf hn] at h
          have hn' : kf ≤ nP.toNat := by have := mt hlt.mpr hn; omega
          cases h4 : ckcW n m2 nP (o + 1) (l - 1) with
          | none => rw [h4] at h; simp [ckcK3] at h
          | some x4 =>
          obtain ⟨r4, m3⟩ := x4
          rw [h4, ckcK3_some] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨b3, a3, hrun3, hS3, hg3, hd3, hd31⟩ := ih m2 m3 a2 v nP (o + 1) (l - 1) xs' r4 h4 hS2
            (by rw [decHL_grow hg12 (by omega)]; exact hd') (by omega) (by have := hg12.1; omega)
          refine ⟨b3, a3, ?_, hS3, hg12.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩
          simp only [List.allM_cons, StateT.run_bind]
          rw [hrunT]
          simp only [bind, Except.bind, hn', decide_true, ite_true]
          exact hrun3


/-- **`class_key_of_closed` refines the `allM` closedness test of `classKeyOf`** (through the stubs
`bvar_b`, `fvar_b`). A piece of `classKeyOf`. -/
theorem classKeyOfClosed_refines (p : Prog) (hb' : BvbProg p) (hf : HfF p)
    (hp : p.lookup "class_key_of_closed" = some classKeyOfClosed) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nP o l : Word) (xs : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hd : decHL s₀.mem o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_key_of_closed" [nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (xs.allM (keyClosedTest nP.toNat)) a₀ ∧
      KeepPost dn vis fe decW0B s₀.mem s'.mem (AM.st (xs.allM (keyClosedTest nP.toNat)) a₀) r
        (AM.res (xs.allM (keyClosedTest nP.toNat)) a₀); ⊤⦄ := by
  refine triple_post (classKeyOfClosed_spec p hb' hf hp n
 s₀ nP o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost⟩ := ckcW_ok dn fe n _ _ a₀ vis nP o l xs r hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost⟩


/-! ## `class_fields_of_hits`: the count and class of `ihs.filter (·.1 == i)` -/

mutual
/-- **The model of `class_fields_of_hits`.** -/
def cfhW : Nat → Mem → Word → Word → Word → Option (Word × Word)
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, i =>
    if l = 0 then some (0, 0)
    else cfhK m (rdW (m.arr64 IW) o) i (cfhW n m (o + 1) (l - 1) i)
/-- After the recursive call. -/
def cfhK (m : Mem) (q i : Word) : Option (Word × Word) → Option (Word × Word)
  | none => none
  | some (cnt, cls) =>
    if rdW (m.arr64 IW) q = i then
      (if cnt = 0 then some (1, rdW (m.arr64 IW) (q + 1)) else some (cnt + 1, cls))
    else some (cnt, cls)
end

section arms
variable (n : Nat) (m : Mem) (o l i q cnt cls : Word)
theorem cfhW_nil (h : l = 0) : cfhW (n + 1) m o l i = some (0, 0) := by simp [cfhW, h]
theorem cfhW_cons (h : l ≠ 0) :
    cfhW (n + 1) m o l i = cfhK m (rdW (m.arr64 IW) o) i (cfhW n m (o + 1) (l - 1) i) := by
  simp [cfhW, h]
theorem cfhK_miss (h : rdW (m.arr64 IW) q ≠ i) : cfhK m q i (some (cnt, cls)) = some (cnt, cls) := by
  simp [cfhK, h]
theorem cfhK_first (h : rdW (m.arr64 IW) q = i) (hc : cnt = 0) :
    cfhK m q i (some (cnt, cls)) = some (1, rdW (m.arr64 IW) (q + 1)) := by simp [cfhK, h, hc]
theorem cfhK_more (h : rdW (m.arr64 IW) q = i) (hc : cnt ≠ 0) :
    cfhK m q i (some (cnt, cls)) = some (cnt + 1, cls) := by simp [cfhK, h, hc]
end arms

grind_pattern [ind_grind] cfhW_nil => cfhW (n + 1) m o l i
grind_pattern [ind_grind] cfhW_cons => cfhW (n + 1) m o l i
grind_pattern [ind_grind] cfhK_miss => cfhK m q i (some (cnt, cls))
grind_pattern [ind_grind] cfhK_first => cfhK m q i (some (cnt, cls))
grind_pattern [ind_grind] cfhK_more => cfhK m q i (some (cnt, cls))

theorem classFieldsOfHits_spec (p : Prog)
    (hp : p.lookup "class_fields_of_hits" = some classFieldsOfHits) (n : Nat) :
    ∀ (s₀ : St) (o l i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_of_hits" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      ∃ x y, cfhW n s₀.mem o l i = some (x, y) ∧ r = [x, y]; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o l i; rw [invoke_eq _ hp]; simp only [callFn, classFieldsOfHits]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l i
    rw [invoke_eq _ hp]
    simp only [callFn, classFieldsOfHits]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)


/-- What `class_fields_of_hits` returns about the twin's `hits`: their count, and, when there is
exactly one, its class. -/
def HitsRes (hits : List (Nat × Nat)) (cnt cls : Word) : Prop :=
  cnt.toNat = hits.length ∧ ∀ h, hits = [h] → cls = UInt64.ofNat h.2 ∧ h.2 < 2 ^ 64

theorem decNN_words {m : Mem} {pp : Nat} {a b : Nat} (h : decNN m pp = some (a, b)) (hp : pp + 1 < 2 ^ 64) :
    rdW (m.arr64 IW) (UInt64.ofNat pp) = UInt64.ofNat a ∧ a < 2 ^ 64 ∧
    rdW (m.arr64 IW) (UInt64.ofNat pp + 1) = UInt64.ofNat b ∧ b < 2 ^ 64 := by
  simp only [decNN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, b', hb, rfl, rfl⟩ := h
  have h1 := iwN_rdW ha (by omega)
  have h2 := iwN_rdW hb hp
  refine ⟨h1.1, h1.2, ?_, h2.2⟩
  rw [← h2.1]
  congr 1
  rw [UInt64.ofNat_add]; rfl

theorem cfhW_ok (n : Nat) : ∀ (m : Mem) (o l i x y : Word) (ihs : List (Nat × Nat)),
    cfhW n m o l i = some (x, y) → decPL m (decNN m) o.toNat l.toNat = some ihs →
    o.toNat + l.toNat < 2 ^ 64 → (m.arr64 IW).size < 2 ^ 64 →
    HitsRes (ihs.filter (fun h => h.1 == i.toNat)) x y := by
  induction n with
  | zero => intro m o l i x y ihs h; simp [cfhW] at h
  | succ n ih =>
    intro m o l i x y ihs h hd hb hsz
    by_cases hl : l = 0
    · rw [cfhW_nil n m o l i hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : l.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp [HitsRes]
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, l.toNat = l1 + 1 := ⟨l.toNat - 1, by
        have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, hh, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      have hppsz : pp + 1 < (m.arr64 IW).size := by
        simp only [decNN, bind, Option.bind_eq_some_iff] at hx
        obtain ⟨a', ha, b', hb', -⟩ := hx
        exact iwN_lt hb'
      obtain ⟨hw1, ha64, hw2, hb64⟩ := decNN_words hx (by omega)
      rw [cfhW_cons n m o l i hl, hrd.1] at h
      cases h2 : cfhW n m (o + 1) (l - 1) i with
      | none => rw [h2] at h; simp [cfhK] at h
      | some cc =>
        obtain ⟨c0, k0⟩ := cc
        rw [h2] at h
        have hl1' : (l - 1).toNat = l1 := by omega
        have hys' : decPL m (decNN m) (o + 1).toNat (l - 1).toNat = some ys := by
          rw [hco1, hl1']; exact hys
        obtain ⟨g1, g2⟩ := ih m (o + 1) (l - 1) i c0 k0 ys h2 hys' (by omega) hsz
        have hlen := decPL_length m hys
        have hfl := List.length_filter_le (fun h => h.1 == i.toNat) ys
        by_cases hmatch : rdW (m.arr64 IW) (UInt64.ofNat pp) = i
        · have hai : hh.1 = i.toNat := by
            rw [hw1] at hmatch
            have := congrArg UInt64.toNat hmatch
            rw [UInt64.toNat_ofNat_of_lt' ha64] at this; exact this
          have hf : (hh :: ys).filter (fun h => h.1 == i.toNat) =
              hh :: ys.filter (fun h => h.1 == i.toNat) := by simp [List.filter_cons, hai]
          rw [hf]
          by_cases hc : c0 = 0
          · rw [cfhK_first m i _ c0 k0 hmatch hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hnil : ys.filter (fun h => h.1 == i.toNat) = [] := by
              apply List.eq_nil_of_length_eq_zero; rw [← g1, hc]; rfl
            rw [hnil]
            refine ⟨by simp, fun h' hh' => ?_⟩
            simp only [List.cons.injEq, and_true] at hh'
            subst hh'
            exact ⟨hw2, hb64⟩
          · rw [cfhK_more m i _ c0 k0 hmatch hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hpos : 0 < c0.toNat := by
              rcases Nat.eq_zero_or_pos c0.toNat with h0 | h0
              · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hc
              · exact h0
            refine ⟨?_, fun h' hh' => ?_⟩
            · have hc1 : (c0 + 1).toNat = c0.toNat + 1 := by
                rw [UInt64.toNat_add]; simp; omega
              rw [hc1, g1]; simp
            · exfalso
              have : (hh :: ys.filter (fun h => h.1 == i.toNat)).length = 1 := by rw [hh']; rfl
              simp only [List.length_cons] at this
              omega
        · rw [cfhK_miss m i _ c0 k0 hmatch] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hai : ¬ hh.1 = i.toNat := by
            intro e; apply hmatch
            rw [hw1, e]; exact UInt64.ofNat_toNat
          have hf : (hh :: ys).filter (fun h => h.1 == i.toNat) = ys.filter (fun h => h.1 == i.toNat) := by
            simp [List.filter_cons, hai]
          rw [hf]; exact ⟨g1, g2⟩


/-- **`class_fields_of_hits` computes `ihs.filter (·.1 == i)`'s count and (sole) class** (a piece of
`classFieldsOf`; pure, the state untouched). -/
theorem classFieldsOfHits_refines (p : Prog)
    (hp : p.lookup "class_fields_of_hits" = some classFieldsOfHits) (n : Nat) (s₀ : St)
    (o l i : Word) (ihs : List (Nat × Nat))
    (hd : decPL s₀.mem (decNN s₀.mem) o.toNat l.toNat = some ihs) (hb : o.toNat + l.toNat < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_of_hits" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      HitsRes (ihs.filter (fun h => h.1 == i.toNat)) (r.headD 0) (r.tail.headD 0); ⊤⦄ := by
  refine triple_post (classFieldsOfHits_spec p hp n s₀ o l i) ?_
  rintro r s' ⟨hl, hm, x, y, hw, rfl⟩
  exact ⟨hl, hm, cfhW_ok n s₀.mem o l i x y ihs hw hd hb hsz⟩


/-! ## `gen_rec_check_any_no_member`: `ms.any (·.member.isNone)` -/

/-- **The model of `gen_rec_check_any_no_member`.** -/
def anmW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some 0
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = 0 then some 1
    else anmW n m (o + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (o l : Word)
theorem anmW_nil (h : l = 0) : anmW (n + 1) m o l = some 0 := by simp [anmW, h]
theorem anmW_hit (h : l ≠ 0) (hx : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = 0) :
    anmW (n + 1) m o l = some 1 := by simp [anmW, h, hx]
theorem anmW_next (h : l ≠ 0) (hx : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) ≠ 0) :
    anmW (n + 1) m o l = anmW n m (o + 1) (l - 1) := by simp [anmW, h, hx]
end arms

grind_pattern [ind_grind] anmW_nil => anmW (n + 1) m o l
grind_pattern [ind_grind] anmW_hit => anmW (n + 1) m o l
grind_pattern [ind_grind] anmW_next => anmW (n + 1) m o l

theorem genRecCheckAnyNoMember_spec (p : Prog)
    (hp : p.lookup "gen_rec_check_any_no_member" = some genRecCheckAnyNoMember) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_any_no_member" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ anmW n s₀.mem o l = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o l; rw [invoke_eq _ hp]; simp only [callFn, genRecCheckAnyNoMember]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ hp]
    simp only [callFn, genRecCheckAnyNoMember]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

theorem decTM_member {m : Mem} {pp : Nat} {t : TargetMajor} (h : decTM m pp = some t) :
    ∃ k, iwN m (pp + 8) = some k ∧ t.member = decON k := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, k, hk, _, -, _, -, rfl⟩ := h
  exact ⟨k, hk, rfl⟩

theorem anmW_ok (n : Nat) : ∀ (m : Mem) (o l r : Word) (ms : List TargetMajor),
    anmW n m o l = some r → decPL m (decTM m) o.toNat l.toNat = some ms →
    o.toNat + l.toNat < 2 ^ 64 → (m.arr64 IW).size < 2 ^ 64 →
    (r != 0) = ms.any (fun t => t.member.isNone) ∧ r.toNat ≤ 1 := by
  induction n with
  | zero => intro m o l r ms h; simp [anmW] at h
  | succ n ih =>
    intro m o l r ms h hd hb hsz
    by_cases hl : l = 0
    · rw [anmW_nil n m o l hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hz : l.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, l.toNat = l1 + 1 := ⟨l.toNat - 1, by
        have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, t, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      obtain ⟨k, hk, hmem⟩ := decTM_member hx
      have hk8 := iwN_lt hk
      have hk' := iwN_rdW hk (by omega)
      have e8 : UInt64.ofNat pp + 8 = UInt64.ofNat (pp + 8) := by rw [UInt64.ofNat_add]; rfl
      have hrd8 : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = UInt64.ofNat k := by
        rw [hrd.1, e8]; exact hk'.1
      have hk0 : (UInt64.ofNat k = 0) ↔ k = 0 := by
        constructor
        · intro e
          have := congrArg UInt64.toNat e
          rw [UInt64.toNat_ofNat_of_lt' hk'.2] at this; simpa using this
        · intro e; subst e; rfl
      by_cases he : k = 0
      · rw [anmW_hit n m o l hl (by rw [hrd8]; exact hk0.mpr he)] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.any_cons, hmem, decON, he]
      · rw [anmW_next n m o l hl (by rw [hrd8]; exact fun e => he (hk0.mp e))] at h
        have hys' : decPL m (decTM m) (o + 1).toNat (l - 1).toNat = some ys := by
          have hl1' : (l - 1).toNat = l1 := by omega
          rw [hco1, hl1']; exact hys
        have := ih m (o + 1) (l - 1) r ys h hys' (by omega) hsz
        simpa [List.any_cons, hmem, decON, he] using this

/-- **`gen_rec_check_any_no_member` is `ms.any (·.member.isNone)`** (a piece of `genRecCheck`;
pure, the state untouched). -/
theorem genRecCheckAnyNoMember_refines (p : Prog)
    (hp : p.lookup "gen_rec_check_any_no_member" = some genRecCheckAnyNoMember) (n : Nat) (s₀ : St)
    (o l : Word) (ms : List TargetMajor)
    (hd : decPL s₀.mem (decTM s₀.mem) o.toNat l.toNat = some ms) (hb : o.toNat + l.toNat < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_any_no_member" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = ms.any (fun t => t.member.isNone) ∧ (r.headD 0).toNat ≤ 1; ⊤⦄ := by
  refine triple_post (genRecCheckAnyNoMember_spec p hp n s₀ o l) ?_
  rintro r s' ⟨hl, hm, hw⟩
  exact ⟨hl, hm, anmW_ok n s₀.mem o l _ ms hw hd hb hsz⟩

end L.Ind
