import ConAgua.Arena.RecCheckSpec20

/-!
# `RecCheck`: `targetMajorOf`'s outside tests (lane `indproofs3`, helper `rec`; built by helper `rec2`)

`target_major_of_outside_closed` (`ds.allM` of the closedness test, with lane `exprops4`'s real
`bvar_b` at the twin's `coreWalkFuel`: `bvbW_stageC`; helper `recb`'s earlier spec used the stub) and
`target_major_of_outside_occ` (`ds.anyM` of `nest_occ`, now a self-recursion).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_major_of_outside_closed` -/

/-- The tail call's single result. -/
def tmK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

theorem tmK1_some (r : List Word) (m : Mem) : tmK1 (some (r, m)) = some ([r.headD 0], m) := rfl
attribute [ind_grind] tmK1_some

mutual
/-- **The model of `target_major_of_outside_closed`** (exec fuel). -/
def tmocW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, dso, dsl, nP =>
    if dsl = 0 then some ([1], m)
    else tmocK1 n dso dsl nP (rdW (m.arr64 IW) dso) (bvbW n m (rdW (m.arr64 IW) dso) CWF)
/-- After `bvar_b`. -/
def tmocK1 (n : Nat) (dso dsl nP x : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (bb, m) => if bb ≠ 0 then some ([0], m) else tmocK2 n dso dsl nP (stubM "fvar_b" m [CWF, x])
/-- After `fvar_b`. -/
def tmocK2 (n : Nat) (dso dsl nP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => if nP < rf.headD 0 then some ([0], m) else tmK1 (tmocW n m (dso + 1) (dsl - 1) nP)
end

section arms
variable (n : Nat) (m : Mem) (dso dsl nP x bb : Word) (rf : List Word)
theorem tmocW_nil (h : dsl = 0) : tmocW (n + 1) m dso dsl nP = some ([1], m) := by simp [tmocW, h]
theorem tmocW_cons (h : ¬ dsl = 0) : tmocW (n + 1) m dso dsl nP =
    tmocK1 n dso dsl nP (rdW (m.arr64 IW) dso) (bvbW n m (rdW (m.arr64 IW) dso) CWF) := by simp [tmocW, h]
theorem tmocK1_b (h : bb ≠ 0) : tmocK1 n dso dsl nP x (some (bb, m)) = some ([0], m) := by
  simp only [tmocK1]; rw [if_pos h]
theorem tmocK1_ok (h : ¬ bb ≠ 0) : tmocK1 n dso dsl nP x (some (bb, m)) =
    tmocK2 n dso dsl nP (stubM "fvar_b" m [CWF, x]) := by
  simp only [tmocK1]; rw [if_neg h]
theorem tmocK2_out (h : nP < rf.headD 0) : tmocK2 n dso dsl nP (some (rf, m)) = some ([0], m) := by
  simp only [tmocK2]; rw [if_pos h]
theorem tmocK2_ok (h : ¬ nP < rf.headD 0) : tmocK2 n dso dsl nP (some (rf, m)) =
    tmK1 (tmocW n m (dso + 1) (dsl - 1) nP) := by simp only [tmocK2]; rw [if_neg h]
end arms
attribute [ind_grind] tmocW_nil tmocW_cons tmocK1_b tmocK1_ok tmocK2_out tmocK2_ok

theorem tmoc_spec (p : Prog) (hb : BvbProg p)
    (hp : p.lookup "target_major_of_outside_closed" = some targetMajorOfOutsideClosed) (n : Nat) :
    ∀ (s₀ : St) (dso dsl nP : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_of_outside_closed" [dso, dsl, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ tmocW n s₀.mem dso dsl nP = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dso dsl nP; rw [invoke_eq _ hp]; simp only [callFn, targetMajorOfOutsideClosed]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ dso dsl nP
    rw [invoke_eq _ hp]
    simp only [callFn, targetMajorOfOutsideClosed]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvarBL_spec p hb n, stubM_spec p "fvar_b" n, ih] <;>
      finish (gen := 20) [rdW_eq]

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tmocW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {dso dsl nP : Word} {r : List Word} {xs : List EIdx},
    tmocW n m dso dsl nP = some (r, m') → StageR dn vis fe m a → HSl0 m dso dsl xs → RcMR m →
    ∃ b a', (xs.allM (keyClosedTest nP.toNat)).run a = .ok (b, a') ∧ (r.headD 0 != 0) = b ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  induction n with
  | zero => intro m m' a dso dsl nP r xs h; simp [tmocW] at h
  | succ n ih =>
  intro m m' a dso dsl nP r xs h hS hxs hP
  by_cases hl : dsl = 0
  · rw [tmocW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by have := hxs.len; simpa using this
    subst this
    exact ⟨true, a, rfl, rfl, hS, IWGrow.refl _, hP⟩
  rw [tmocW_cons (h := hl)] at h
  have hb : dso.toNat + dsl.toNat ≤ iwTop m := hxs.2.resolve_left hl
  obtain ⟨w, xs', rfl, ew, hw, hxs'⟩ := decHL_cons hxs.1 hl (hS.lt64 hb)
  obtain ⟨eo, el, hl0⟩ := slice_step hl (hS.lt64 hb)
  rw [ew] at h
  cases h1 : bvbW n m w CWF with
  | none => rw [h1] at h; simp [tmocK1] at h
  | some y =>
  obtain ⟨bb, m1⟩ := y
  rw [h1] at h
  obtain ⟨a1, run1, hS1, hg1, hf1⟩ := bvbW_stageC dn fe vis hS n w bb hw h1
  have hP1 := hP.fr hf1
  rw [decE_eq] at run1
  by_cases hbb : bb ≠ 0
  · rw [tmocK1_b (h := hbb)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e1 : (bb.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hbb (UInt64.toNat_inj.mp (by simpa using h0))
    refine ⟨false, a1, ?_, rfl, hS1, hg1, hP1⟩
    simp only [List.allM_cons, keyClosedTest, StateT.run_bind, run1, except_ok_bind, e1, if_true]; rfl
  rw [tmocK1_ok (h := hbb)] at h
  have e1 : (bb.toNat != 0) = false := by simp at hbb; simp [hbb]
  cases h2 : stubM "fvar_b" m1 [CWF, w] with
  | none => rw [h2] at h; simp [tmocK2] at h
  | some y =>
  obtain ⟨rf, m2⟩ := y
  rw [h2] at h
  obtain ⟨k2, a2, run2, hS2, hg2, hd2⟩ := fvarB_spec dn vis fe CWF w hw m1 m2 a1 rf h2 hS1
  rw [CWF_eq] at run2
  have hP2 := hP1.stub (by decide) h2
  simp only [decW0Nat] at hd2
  by_cases hc : nP < rf.headD 0
  · rw [tmocK2_out (h := hc)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e2 : decide (k2 ≤ nP.toNat) = false := by rw [UInt64.lt_iff_toNat_lt] at hc; simp; omega
    refine ⟨false, a2, ?_, rfl, hS2, hg1.trans hg2, hP2⟩
    simp only [List.allM_cons, keyClosedTest, StateT.run_bind, run1, except_ok_bind, e1, Bool.false_eq_true,
      if_false, run2, e2]; rfl
  rw [tmocK2_ok (h := hc)] at h
  have e2 : decide (k2 ≤ nP.toNat) = true := by rw [UInt64.lt_iff_toNat_lt] at hc; simp; omega
  have hg12 := hg1.trans hg2
  cases h3 : tmocW n m2 (dso + 1) (dsl - 1) nP with
  | none => rw [h3] at h; cases h
  | some y =>
  obtain ⟨r3, m3⟩ := y
  rw [h3, tmK1_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨b, a3, run3, hb3, hS3, hg3, hP3⟩ := ih h3 hS2
    (HSl0.of (by rw [decHL_grow hg12 (by rw [eo, el]; omega)]; exact hxs') (by rw [eo, el]; have := hg12.1; omega)) hP2
  refine ⟨b, a3, ?_, by simpa using hb3, hS3, hg12.trans hg3, hP3⟩
  simp only [List.allM_cons, keyClosedTest, StateT.run_bind, run1, except_ok_bind, e1, Bool.false_eq_true,
    if_false, run2, e2, if_true]
  exact run3

end rel

/-! ## `target_major_of_outside_occ` -/

mutual
/-- **The model of `target_major_of_outside_occ`** (exec fuel). -/
def tmooW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, mno, mnl, dso, dsl =>
    if dsl = 0 then some ([0], m)
    else tmooK1 n mno mnl dso dsl (noF n m mno mnl 0 0 (rdW (m.arr64 IW) dso))
/-- After `nest_occ`. -/
def tmooK1 (n : Nat) (mno mnl dso dsl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m) => if b ≠ 0 then some ([1], m) else tmK1 (tmooW n m mno mnl (dso + 1) (dsl - 1))
end

section arms
variable (n : Nat) (m : Mem) (mno mnl dso dsl b : Word)
theorem tmooW_nil (h : dsl = 0) : tmooW (n + 1) m mno mnl dso dsl = some ([0], m) := by simp [tmooW, h]
theorem tmooW_cons (h : ¬ dsl = 0) : tmooW (n + 1) m mno mnl dso dsl =
    tmooK1 n mno mnl dso dsl (noF n m mno mnl 0 0 (rdW (m.arr64 IW) dso)) := by
  simp [tmooW, h]
theorem tmooK1_hit (h : b ≠ 0) : tmooK1 n mno mnl dso dsl (some (b, m)) = some ([1], m) := by
  simp only [tmooK1]; rw [if_pos h]
theorem tmooK1_miss (h : ¬ b ≠ 0) : tmooK1 n mno mnl dso dsl (some (b, m)) = tmK1 (tmooW n m mno mnl (dso + 1) (dsl - 1)) := by
  simp only [tmooK1]; rw [if_neg h]
end arms
attribute [ind_grind] tmooW_nil tmooW_cons tmooK1_hit tmooK1_miss

theorem tmoo_spec (p : Prog) (L : K53Look p)
    (hp : p.lookup "target_major_of_outside_occ" = some targetMajorOfOutsideOcc) (n : Nat) :
    ∀ (s₀ : St) (mno mnl dso dsl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_of_outside_occ" [mno, mnl, dso, dsl]
    ⦃fun r s' => LocEq s' s₀ ∧ tmooW n s₀.mem mno mnl dso dsl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ mno mnl dso dsl; rw [invoke_eq _ hp]; simp only [callFn, targetMajorOfOutsideOcc]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ mno mnl dso dsl
    rw [invoke_eq _ hp]
    simp only [callFn, targetMajorOfOutsideOcc]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, noF_spec p L n, ih] <;>
      finish (gen := 20) [rdW_eq]

section rel2
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tmooW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {mno mnl dso dsl : Word} {r : List Word}
    {names : List NIdx} {xs : List EIdx},
    tmooW n m mno mnl dso dsl = some (r, m') → StageR dn vis fe m a →
    decHL m mno.toNat mnl.toNat = some names → mno.toNat + mnl.toNat ≤ iwTop m →
    HSl0 m dso dsl xs → RcMR m →
    ∃ b, (xs.anyM (fun x => ConRon.Arena.nestOcc names 0 0 x)).run a = .ok (b, a) ∧ (r.headD 0 != 0) = b ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ RcMR m' := by
  induction n with
  | zero => intro m m' a mno mnl dso dsl r names xs h; simp [tmooW] at h
  | succ n ih =>
  intro m m' a mno mnl dso dsl r names xs h hS hno hnob hxs hP
  by_cases hl : dsl = 0
  · rw [tmooW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by have := hxs.len; simpa using this
    subst this
    exact ⟨false, rfl, rfl, hS, IWGrow.refl _, hP⟩
  rw [tmooW_cons (h := hl)] at h
  have hb : dso.toNat + dsl.toNat ≤ iwTop m := hxs.2.resolve_left hl
  obtain ⟨w, xs', rfl, ew, hw, hxs'⟩ := decHL_cons hxs.1 hl (hS.lt64 hb)
  obtain ⟨eo, el, hl0⟩ := slice_step hl (hS.lt64 hb)
  rw [ew] at h
  cases h1 : noF n m mno mnl 0 0 w with
  | none => rw [h1] at h; simp [tmooK1] at h
  | some y =>
  obtain ⟨occ, m1⟩ := y
  rw [h1] at h
  obtain ⟨b1, run1, hb1, hS1, hg1, hP1⟩ := noF_ok dn fe vis n h1 hS hw hno hnob hP
  rw [decE_eq] at run1
  by_cases ho : occ ≠ 0
  · rw [tmooK1_hit (h := ho)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : b1 = true := by rw [← hb1]; simpa using ho
    subst this
    refine ⟨true, ?_, rfl, hS1, hg1, hP1⟩
    simp only [List.anyM_cons, StateT.run_bind, run1, except_ok_bind, if_true]; rfl
  rw [tmooK1_miss (h := ho)] at h
  have : b1 = false := by rw [← hb1]; simp at ho; simp [ho]
  subst this
  cases h3 : tmooW n m1 mno mnl (dso + 1) (dsl - 1) with
  | none => rw [h3] at h; cases h
  | some y =>
  obtain ⟨r3, m3⟩ := y
  rw [h3, tmK1_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨b, run2, hb2, hS2, hg2, hP2⟩ := ih h3 hS1 (by rw [decHL_grow hg1 hnob]; exact hno)
    (by have := hg1.1; omega)
    (HSl0.of (by rw [decHL_grow hg1 (by rw [eo, el]; omega)]; exact hxs') (by rw [eo, el]; have := hg1.1; omega)) hP1
  refine ⟨b, ?_, by simpa using hb2, hS2, hg1.trans hg2, hP2⟩
  simp only [List.anyM_cons, StateT.run_bind, run1, except_ok_bind, Bool.false_eq_true, if_false]
  exact run2

end rel2

/-! ## A fresh `TargetMajor` record, decoded below the tops -/

theorem mkTMW_recW (m : Mem) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) :
    mkTMW m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = recW m 13 [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] := by
  simp only [mkTMW, recW]
  cases allocW m 13 with
  | none => rfl
  | some x =>
    obtain ⟨q, m1⟩ := x
    simp [tmWr, wrIW, UInt64.add_assoc]

/-- A slice below the top unless empty reads the same in the cut pools of a grown memory. -/
theorem HSl0.decB {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)} (h : HSl0 m o l xs) :
    DecB (fun m => decHL m o.toNat l.toNat) m xs := by
  rcases h with ⟨hd, h0 | hb⟩
  · subst h0
    have : xs = [] := by have := decHL_length _ hd; simpa using this
    subst this; show decHL (truncM m) _ _ = _; simp [decHL, hslice?]
  · exact decHL_decB hd hb

/-- **`mk_target_major` under the stage relation**: the record decoded below the tops (its slices
decoded below the tops, `nfs` empty). -/
theorem tmRec_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a11 a12 : Word} {r : List Word} {ds pfvs : List EIdx}
    {ctors : List (IConstantVal × Nat)}
    (h : mkTMW m a0 a1 a2 a3 a4 a5 a6 a7 a8 0 0 a11 a12 = some (r, m')) (hS : StageR dn vis fe m a)
    (h0 : H a0) (h1 : H a1) (hds : HSl0 m a2 a3 ds) (hct : DecB (fun m => decPL m (decCN m) a6.toNat a7.toNat) m ctors) (hpf : HSl0 m a11 a12 pfvs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      DecB (fun m => decTM m (r.headD 0).toNat) m'
        { ind := decI a0, lvls := decI a1, ds := ds, nPc := a4.toNat, nIdx := a5.toNat, ctors := ctors,
          member := decON a8.toNat, nfs := [], pfvs := pfvs } := by
  rw [mkTMW_recW] at h
  obtain ⟨hr, hq, hget, hS', hg, hf, ht⟩ := rcFresh h hS rfl
  subst hr
  refine ⟨hS', hg, MFr.of_iw hf, ?_⟩
  simp only [List.headD_cons, List.length_cons, List.length_nil] at ht ⊢
  rw [hq]
  have hrd : ∀ j, j < 13 → (iwA (truncM m'))[iwTop m + j]? =
      ([a0, a1, a2, a3, a4, a5, a6, a7, a8, 0, 0, a11, a12] : List Word)[j]? := fun j hj => by
    rw [truncM_iw_get?, if_pos (by omega)]; exact hget j (by simpa using hj)
  have hH : ∀ {k : IdxKind} j (w : Word), j < 13 → ([a0, a1, a2, a3, a4, a5, a6, a7, a8, 0, 0, a11, a12] : List Word)[j]? = some w →
      w.toNat < 2 ^ 32 → (iwH (truncM m') (iwTop m + j) : Option (Idx k)) = some (decI w) := by
    intro _ j w hj hw hw32; simp [iwH, hd?, hrd j hj, hw, hw32]
  have hN : ∀ j (w : Word), j < 13 → ([a0, a1, a2, a3, a4, a5, a6, a7, a8, 0, 0, a11, a12] : List Word)[j]? = some w →
      iwN (truncM m') (iwTop m + j) = some w.toNat := by
    intro j w hj hw; simp [iwN, nat?, hrd j hj, hw]
  have e0 := hH (k := .name) 0 a0 (by omega) rfl h0
  have e1 := hH (k := .levels) 1 a1 (by omega) rfl h1
  have n2 := hN 2 a2 (by omega) rfl; have n3 := hN 3 a3 (by omega) rfl
  have n4 := hN 4 a4 (by omega) rfl; have n5 := hN 5 a5 (by omega) rfl
  have n6 := hN 6 a6 (by omega) rfl; have n7 := hN 7 a7 (by omega) rfl
  have n8 := hN 8 a8 (by omega) rfl; have n9 := hN 9 0 (by omega) rfl
  have n10 := hN 10 0 (by omega) rfl; have n11 := hN 11 a11 (by omega) rfl
  have n12 := hN 12 a12 (by omega) rfl
  have dds : decHL (truncM m') a2.toNat a3.toNat = some ds := (hds.decB).grow (OMono.decHL _ _) hg
  have dpf : decHL (truncM m') a11.toNat a12.toNat = some pfvs := (hpf.decB).grow (OMono.decHL _ _) hg
  have dct : decPL (truncM m') (decCN (truncM m')) a6.toNat a7.toNat = some ctors :=
    hct.grow (OMono.decPL decCN_mono _ _) hg
  show decTM (truncM m') (iwTop m) = some _
  simp only [Nat.add_zero] at e0
  simp only [decTM, decAt, e0, Option.bind_eq_bind, Option.bind_some, e1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11,
    n12, dds, dpf, dct, Nat.add_assoc, show (0 : Word).toNat = 0 from rfl]
  simp [decPL]

end L.Ind
