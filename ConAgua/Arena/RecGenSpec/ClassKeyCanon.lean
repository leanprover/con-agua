import ConAgua.Arena.RecGenSpec.KcW

/-!
# ClassKeyCanon: `ConRon.Arena.classKeyCanon`, `ConRon.Arena.classKeyOf`, `ConRon.Arena.targetCanonParams`

The refinement theorems `targetCanonParams_refinesP`, `classKeyCanon_refines`, `classKeyOf_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- After `class_key_of_closed`. -/
def kofK2 (k2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([k2], m)
/-- After `class_key_canon`. -/
def kofK1 (k : Nat) (nP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => kofK2 (r.headD 0) (ckc2W (k + 1) m nP (rdW (m.arr64 IW) (r.headD 0 + 2))
      (rdW (m.arr64 IW) (r.headD 0 + 3)))

/-- **The model of `class_key_of(nP, po, pl, key)`** at exec fuel `k + 2`. -/
def kofW (k : Nat) (m : Mem) (nP po pl key : Word) : Option (List Word × Mem) :=
  kofK1 k nP (kcW k m po pl key)

section arms2
variable (k : Nat) (m : Mem) (nP k2 : Word) (r : List Word)
theorem kofK2_fail (h : r.headD 0 = 0) : kofK2 k2 (some (r, m)) = none := by
  simp only [kofK2]; rw [ite_eq_left h]
theorem kofK2_ok (h : ¬ r.headD 0 = 0) : kofK2 k2 (some (r, m)) = some ([k2], m) := by
  simp only [kofK2]; rw [ite_eq_right h]
theorem kofK1_some : kofK1 k nP (some (r, m)) = kofK2 (r.headD 0) (ckc2W (k + 1) m nP
    (rdW (m.arr64 IW) (r.headD 0 + 2)) (rdW (m.arr64 IW) (r.headD 0 + 3))) := rfl
end arms2
attribute [ind_grind] kofK2_fail kofK2_ok kofK1_some

/-! ## The `vcgen` specs -/

section spec
variable {p : Prog} (L : KofProg p)
include L

theorem kof_spec (k : Nat) (s₀ : St) (nP po pl key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 2)) "class_key_of" [nP, po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ kofW k s₀.mem nP po pl key = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.kof]
  simp only [callFn, classKeyOfL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      kc_spec L k, ckc2_spec L (k + 1)] <;>
    finish (gen := 20) [kofW, rdW_eq]

end spec

/-! ## The relational side -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem ckc2W_mfr : ∀ (n : Nat) (m m' : Mem) (nP o l : Word) (r : List Word),
    ckc2W n m nP o l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [ckc2W] at h
  | n + 1, m, m', nP, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ckc2W_nil n m nP o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2W_cons n m nP o l hl] at h
    obtain ⟨⟨rb, m1⟩, h1, h⟩ := of_K h (by simp only [ckc2K1])
    refine (bvbW_mfr h1).trans ?_
    by_cases hb : rb ≠ 0
    · rw [ckc2K1_open (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2K1_closed (h := hb)] at h
    obtain ⟨⟨rf, m2⟩, h2, h⟩ := of_K h (by simp only [ckc2K2])
    refine (MFr.ofFvbF h2).trans ?_
    by_cases hf : nP < rf.headD 0
    · rw [ckc2K2_open (h := hf)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2K2_closed (h := hf)] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
    rw [ckcK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ckc2W_mfr n _ _ _ _ _ _ h3

theorem ckc2W_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (nP o l : Word) (xs : List EIdx) (r : List Word),
    ckc2W n m nP o l = some (r, m') → StageR dn vis fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ b a', (xs.allM (keyClosedTest nP.toNat)).run a = .ok (b, a') ∧
      KeepPost dn vis fe decW0B m m' a' r b := by
  induction n with
  | zero => intro m m' a nP o l xs r h; simp [ckc2W] at h
  | succ n ih =>
    intro m m' a nP o l xs r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [ckc2W_nil n m nP o 0 rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl m, by simp [decW0B]⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [ckc2W_cons n m nP o l hl, hw] at h
      obtain ⟨⟨rb, m1⟩, h2, h⟩ := of_K h (by simp only [ckc2K1])
      obtain ⟨a1, hrun1, hS1, hg1, -⟩ := bvbW_stageW dn vis fe hS n coreWalkFuel CWF (.inl (Nat.le_of_eq CWF_eq)) w rb hw32 h2
      by_cases hz : rb ≠ 0
      · rw [ckc2K1_open n m1 nP o l w rb hz] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hk : rb.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
        refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
        simp only [List.allM_cons, StateT.run_bind, keyClosedTest]
        rw [show (decI w : EIdx) = decE w from rfl, hrun1]
        simp only [bind, Except.bind, hk, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
        rfl
      · rw [ckc2K1_closed n m1 nP o l w rb hz] at h
        have hk : rb.toNat = 0 := by rw [show rb = 0 by simpa using hz]; rfl
        obtain ⟨⟨rf, m2⟩, h3, h⟩ := of_K h (by simp only [ckc2K2])
        obtain ⟨kf, a2, hrun2, hS2, hg2, hkf⟩ := fvbF_ok dn vis fe CWF w hw32 m1 m2 a1 rf h3 hS1
        rw [CWF_eq] at hrun2
        have hg12 := hg1.trans hg2
        have hlt : (nP < rf.headD 0) ↔ ¬ kf ≤ nP.toNat := by
          rw [UInt64.lt_iff_toNat_lt, hkf]; omega
        have hrunT : (keyClosedTest nP.toNat (decI w)).run a = .ok (decide (kf ≤ nP.toNat), a2) := by
          simp only [keyClosedTest, StateT.run_bind]
          rw [show (decI w : EIdx) = decE w from rfl, hrun1]
          simp only [bind, Except.bind, hk, bne_self_eq_false, Bool.false_eq_true, ite_false]
          simp only [StateT.bind, StateT.run] at hrun2 ⊢
          rw [show (decE w : EIdx) = decI w from rfl, hrun2]
          rfl
        by_cases hn' : nP < rf.headD 0
        · rw [ckc2K2_open n m2 nP o l rf hn'] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hn'' := hlt.mp hn'
          refine ⟨false, a2, ?_, hS2, hg12, by simp [decW0B]⟩
          simp only [List.allM_cons, StateT.run_bind]
          rw [hrunT]
          simp only [bind, Except.bind, hn'', decide_false, Bool.false_eq_true, ite_false]
          rfl
        · rw [ckc2K2_closed n m2 nP o l rf hn'] at h
          have hn'' : kf ≤ nP.toNat := by have := mt hlt.mpr hn'; omega
          obtain ⟨⟨r4, m3⟩, h4, h⟩ := of_K h rfl
          rw [ckcK3_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          obtain ⟨b3, a3, hrun3, hS3, hg3, hd3, hd31⟩ := ih m2 m3 a2 nP (o + 1) (l - 1) xs' r4 h4 hS2
            (by rw [decHL_grow hg12 (by omega)]; exact hd') (by omega) (by have := hg12.1; omega)
          refine ⟨b3, a3, ?_, hS3, hg12.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩
          simp only [List.allM_cons, StateT.run_bind]
          rw [hrunT]
          simp only [bind, Except.bind, hn'', decide_true, ite_true]
          exact hrun3

/-- **`class_key_of`'s model simulates `classKeyOf`.** -/
theorem kofW_ok (k : Nat) (m m' : Mem) (a : AState) (nP po pl key : Word) (r : List Word)
    (pfvs : List EIdx) (ck : ClassKey) (h : kofW k m nP po pl key = some (r, m')) (hS : StageR dn vis fe m a)
    (hpf : decHL m po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop m)
    (hk : DecB (fun m => decCK m key.toNat) m ck) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.classKeyOf nP.toNat pfvs ck).run a = .ok (x, a') ∧
      DecB (fun m => decCK m (r.headD 0).toNat) m' x ∧ (r.headD 0).toNat + 4 ≤ iwTop m' ∧
      (rdW (m'.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (m'.arr64 IW) (r.headD 0 + 3)).toNat ≤ iwTop m' ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' := by
  unfold kofW at h
  obtain ⟨⟨r1, m1⟩, hc, h⟩ := of_K h rfl
  rw [kofK1_some] at h
  obtain ⟨x1, a1, hrun1, hd1, hb1, hds1, hS1, hg1, hP1⟩ := kcW_ok dn fe vis k m m1 a po pl key r1 pfvs ck hc hS hpf hpb hk hP
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hd1
  obtain ⟨-, -, -, -, hds, -, -⟩ := pos2_nk_fields hnk htop1
  obtain ⟨⟨r2, m2⟩, hcl, h⟩ := of_K h rfl
  obtain ⟨b, a2, hrun2, hS2, hg2, hb2, -⟩ := ckc2W_ok dn fe vis (k + 1) m1 m2 a1 nP _ _ nk.ds r2 hcl hS1 hds
    (by omega) hds1
  by_cases h0 : r2.headD 0 = 0
  · rw [kofK2_fail (h := h0)] at h; cases h
  rw [kofK2_ok (h := h0)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hbt : b = true := by rw [← hb2]; exact bne_iff_ne.mpr h0
  subst hbt
  refine ⟨ckOfNk nk, a2, ?_, ?_, by simpa using (by have := hg2.1; omega : (r1.headD 0).toNat + 4 ≤ iwTop m2), ?_,
    hS2, hg1.trans hg2, hP1.fr (ckc2W_mfr _ _ _ _ _ _ _ hcl)⟩
  · simp only [ConRon.Arena.classKeyOf, StateT.run_bind]
    rw [hrun1]
    simp only [except_ok_bind]
    have e : (ckOfNk nk).ds = nk.ds := rfl
    have hr2' : ((ckOfNk nk).ds.allM fun x => do
        if (← bvarB coreWalkFuel x) != 0 then pure false
        else pure ((← fvarB coreWalkFuel x) ≤ nP.toNat)).run a1 = .ok (true, a2) := hrun2
    rw [hr2']
    rfl
  · simpa using hd1.grow (decCK_mono _) hg2
  · have ek (j : Word) (hj : j.toNat < 4) :
        rdW (m2.arr64 IW) (r1.headD 0 + j) = rdW (m1.arr64 IW) (r1.headD 0 + j) := by
      simp only [rdW, word_add_toNat (show (r1.headD 0).toNat + j.toNat < 2 ^ 64 by omega)]
      rw [hg2.2.2.1 _ (by omega)]
    simp only [List.headD_cons]; rw [ek 2 (by decide), ek 3 (by decide)]; have := hg2.1; omega

end rel

/-! ## Census -/

section census
variable {p : Prog} (L : KofProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
include L

/-- **`target_canon_params` refines `targetCanonParams`** (`replace_fvars` through its `mk_app_n`
stub): the parameters a slice below the top, the walk memos well formed before and after. -/
@[refines ConRon.Arena.targetCanonParams]
theorem targetCanonParams_refinesP (k : Nat) (s₀ : St) (a₀ : AState) (pfo pfl e : Word) (pfvs : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hpf : decHL s₀.mem pfo.toNat pfl.toNat = some pfvs)
    (hpb : pfo.toNat + pfl.toNat ≤ iwTop s₀.mem) (he : H e) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (tcpP_spec L k s₀ pfo pfl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hS', hg, hP'⟩ := tcpPW_ok dn fe vis k _ _ a₀ pfo pfl e _ pfvs hm hS hpf hpb he hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres], hH, by rw [hst]; exact hS', hg, hP'⟩

/-- **`class_key_canon` refines `classKeyCanon`** (through `replace_fvars`' stub): the key decoded
below the tops, the canonical parameters a slice below the top; the canonical key a fresh record
decoded below the tops, its parameter slice below the top. -/
@[refines ConRon.Arena.classKeyCanon]
theorem classKeyCanon_refines (k : Nat) (s₀ : St) (a₀ : AState) (po pl key : Word) (pfvs : List EIdx)
    (ck : ClassKey) (hS : StageR dn vis fe s₀.mem a₀) (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs)
    (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck)
    (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "class_key_canon" [po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classKeyCanon pfvs ck) a₀ ∧
      DecB (fun m => decCK m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.classKeyCanon pfvs ck) a₀) ∧
      (r.headD 0).toNat + 4 ≤ iwTop s'.mem ∧
      (rdW (s'.mem.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (s'.mem.arr64 IW) (r.headD 0 + 3)).toNat ≤
        iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classKeyCanon pfvs ck) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (kc_spec L k s₀ po pl key) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, h1, h2, h3, h4, h5, h6⟩ := kcW_ok dn fe vis k _ _ a₀ po pl key r pfvs ck hm hS hpf hpb hk hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact h1, h2, h3, by rw [hst]; exact h4, h5, h6⟩

/-- **`class_key_of` refines `classKeyOf`** (through `replace_fvars`' and `fvar_b`'s stubs;
`bvar_b` the master's walk, at exec fuel below `coreWalkFuel`). -/
@[refines ConRon.Arena.classKeyOf]
theorem classKeyOf_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (nP po pl key : Word) (pfvs : List EIdx) (ck : ClassKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem)
    (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 2)) "class_key_of" [nP, po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀ ∧
      DecB (fun m => decCK m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀) ∧
      (r.headD 0).toNat + 4 ≤ iwTop s'.mem ∧
      (rdW (s'.mem.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (s'.mem.arr64 IW) (r.headD 0 + 3)).toNat ≤
        iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (kof_spec L k s₀ nP po pl key) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, h1, h2, h3, h4, h5, h6⟩ :=
    kofW_ok dn fe vis k _ _ a₀ nP po pl key r pfvs ck hm hS hpf hpb hk hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact h1, h2, h3, by rw [hst]; exact h4, h5, h6⟩

end census

end L.Ind

end
