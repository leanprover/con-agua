import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndRealMemo
import ConAgua.Arena.IndRealIlpP

/-!
# Refinements of `IndSum`, sixth file (lane `indproofs`)

`struct_proj_bodies_go` (through `instantiate1_lift_fast`, `IndRealMemo.lean`, which needs the
walk memos `AbsOK`).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_proj_bodies_go` -/

/-- After the cons. -/
def pbK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ro, m4) => some ([1, ro.headD 0, ro.tail.headD 0], m4)
/-- After the recursion. -/
def pbK3 (n : Nat) (x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m3) =>
    if rr.headD 0 = 0 then some ([0, 0, 0], m3)
    else pbK4 (consW n m3 x (rr.tail.headD 0) (rr.tail.tail.headD 0))

mutual
/-- **The model of `struct_proj_bodies_go`.** -/
def pbW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, T, k, i, h =>
    if k = 0 then some ([1, 0, 0], m)
    else if h >>> 28 ≠ 6 then some ([0, 0, 0], m)
    else if eViewW m h = [] then none
    else pbK1 n T k i ((eViewW m h).tail.headD 0) ((eViewW m h).tail.tail.headD 0) (spaW m T i)
/-- After `struct_proj_arg_p`. -/
def pbK1 (n : Nat) (T k i x y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) =>
    if 4294967296 ≤ ra.headD 0 then none
    else pbK2 n T k i x (i1lF m1 [CWF, y, ra.headD 0, 0])
/-- After `instantiate1_lift_fast`: the recursion. -/
def pbK2 (n : Nat) (T k i x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) => pbK3 n x (pbW n m2 T (k - 1) (i + 1) (rb.headD 0))
end

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (T k i h x y : Word) (ra rb rr ro : List Word)
theorem pbW_nil (hk : k = 0) : pbW (n + 1) m T k i h = some ([1, 0, 0], m) := by simp [pbW, hk]
theorem pbW_tag (hk : k ≠ 0) (ht : h >>> 28 ≠ 6) : pbW (n + 1) m T k i h = some ([0, 0, 0], m) := by
  simp [pbW, hk, ht]
theorem pbW_empty (hk : k ≠ 0) (ht : h >>> 28 = 6) (he : eViewW m h = []) :
    pbW (n + 1) m T k i h = none := by simp [pbW, hk, ht, he]
theorem pbW_pi (hk : k ≠ 0) (ht : h >>> 28 = 6) (he : eViewW m h ≠ []) :
    pbW (n + 1) m T k i h =
      pbK1 n T k i ((eViewW m h).tail.headD 0) ((eViewW m h).tail.tail.headD 0) (spaW m T i) := by
  simp [pbW, hk, ht, he]
theorem pbK1_big (hb : 4294967296 ≤ ra.headD 0) : pbK1 n T k i x y (some (ra, m1)) = none := by
  simp only [pbK1, if_pos hb]
theorem pbK1_ok (hb : ¬ 4294967296 ≤ ra.headD 0) : pbK1 n T k i x y (some (ra, m1)) =
    pbK2 n T k i x (i1lF m1 [CWF, y, ra.headD 0, 0]) := by
  simp only [pbK1, if_neg hb]
theorem pbK2_some : pbK2 n T k i x (some (rb, m2)) = pbK3 n x (pbW n m2 T (k - 1) (i + 1) (rb.headD 0)) := by
  rw [pbK2]
theorem pbK3_none (hz : rr.headD 0 = 0) : pbK3 n x (some (rr, m3)) = some ([0, 0, 0], m3) := by
  simp only [pbK3, if_pos hz]
theorem pbK3_some (hz : rr.headD 0 ≠ 0) : pbK3 n x (some (rr, m3)) =
    pbK4 (consW n m3 x (rr.tail.headD 0) (rr.tail.tail.headD 0)) := by simp only [pbK3, if_neg hz]
theorem pbK4_some : pbK4 (some (ro, m4)) = some ([1, ro.headD 0, ro.tail.headD 0], m4) := rfl
end arms

grind_pattern [ind_grind] pbW_nil => pbW (n + 1) m T k i h
grind_pattern [ind_grind] pbW_tag => pbW (n + 1) m T k i h
grind_pattern [ind_grind] pbW_empty => pbW (n + 1) m T k i h
grind_pattern [ind_grind] pbW_pi => pbW (n + 1) m T k i h
grind_pattern [ind_grind] pbK1_big => pbK1 n T k i x y (some (ra, m1))
grind_pattern [ind_grind] pbK1_ok => pbK1 n T k i x y (some (ra, m1))
grind_pattern [ind_grind] pbK2_some => pbK2 n T k i x (some (rb, m2))
grind_pattern [ind_grind] pbK3_none => pbK3 n x (some (rr, m3))
grind_pattern [ind_grind] pbK3_some => pbK3 n x (some (rr, m3))
grind_pattern [ind_grind] pbK4_some => pbK4 (some (ro, m4))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
  (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
  (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
  (hp : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL) (hi1 : I1lF p)
include ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hp hi1

theorem pbW_spec (n : Nat) : ∀ (s₀ : St) (T k i h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_bodies_go" [T, k, i, h]
    ⦃fun r s' => LocEq s' s₀ ∧ pbW n s₀.mem T k i h = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ T k i h; rw [invoke_eq _ hp]; simp only [callFn, structProjBodiesGoL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ T k i h
    rw [invoke_eq _ hp]
    simp only [callFn, structProjBodiesGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        eView_spec p hv n, spaW_spec p hd hpf hpp hib hjf hjp hji hmp hap n,
        i1lF_spec p hi1 n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)

end spec

/-! ## The relational lemma -/

theorem spaW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a : AState)
    (T j : Word) (r : List Word) (h : spaW m T j = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ a', (structProjArgP (decI T) j.toNat).run a = .ok (decE (r.headD 0), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [spaW] at h
  cases h1 : binternW m 0 with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨b, m1⟩ := x
  rw [h1, spaK_some] at h
  cases h2 : mkProjW m1 T j b with
  | none => rw [h2] at h; cases h
  | some y =>
  obtain ⟨e, m2⟩ := y
  rw [h2, spaK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨a1, hr1, hS1, hg1⟩ := internBVar_stage hS 0 h1
  obtain ⟨a2, hr2, hS2, hg2⟩ := mkProj_stage hS1 T j b h2
  refine ⟨a2, ?_, hS2, hg1.trans hg2⟩
  simp only [structProjArgP, StateT.run_bind]
  rw [show (0 : Word).toNat = 0 from rfl] at hr1
  rw [hr1]
  exact hr2

theorem spaW_afr {m m' : Mem} {T j : Word} {r : List Word} (h : spaW m T j = some (r, m')) : AFr m m' := by
  simp only [spaW, spaK.eq_def, spaK2.eq_def] at h
  afr_auto h [binternW_afr, mkProjW_afr]

theorem tag_iff (b : Word) (hb : b.toNat < 2 ^ 32) (t : Word) (ht : t.toNat < 16) :
    (decE b).tag = t.toUInt32 ↔ b >>> 28 = t := by
  rw [decE_tag b hb]
  have key : (b >>> 28).toNat = b.toNat / 268435456 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat h
    rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, key] at this
    rw [key]
    omega
  · intro h; rw [h]

theorem eViewW_head6S (m : Mem) (h : Word) (hg : h >>> 28 = 6) (hne : eViewW m h ≠ []) :
    (eViewW m h).headD 0 = 6 := by
  revert hne; unfold eViewW
  simp only [hg, show ((6 : Word) = 0) = False from by decide, show ((6 : Word) = 1) = False from by decide,
    show ((6 : Word) = 2) = False from by decide, show ((6 : Word) = 3) = False from by decide,
    show ((6 : Word) = 4) = False from by decide, show ((6 : Word) = 5) = False from by decide,
    if_false, if_true]
  repeat' split
  all_goals simp

/-- What `struct_proj_bodies_go` returns: `(0, _, _)` for `none`, `(1, off, len)` for a slice. -/
def PBDec (m : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 = 1 ∧ decHL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

theorem pbW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (T k i h : Word) (r : List Word),
    pbW n m T k i h = some (r, m') → StageR dn vis fe m a → H h → i.toNat + k.toNat < 2 ^ 64 →
    AbsOK m →
    ∃ x a', (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PBDec m' r x ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a T k i h r hm; simp [pbW] at hm
  | succ n ih =>
    intro m m' a T k i h r hm hS hh hik hA
    by_cases hk : k = 0
    · subst hk
      rw [pbW_nil n m T 0 i h rfl] at hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨some [], a, by simp [structProjBodiesGo]; rfl, hS, IWGrow.refl m, ?_, hA⟩
      simp [PBDec, decHL, hslice?]
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hk
      · omega
    have hkm : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hk1))]; simp
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hks : k.toNat = (k.toNat - 1) + 1 := by omega
    have htf : ((decE h).tag == ETag.forallE) = true ↔ h >>> 28 = 6 := by
      rw [beq_iff_eq, show ETag.forallE = (6 : Word).toUInt32 from rfl]
      exact tag_iff h hh 6 (by decide)
    by_cases ht : h >>> 28 = 6
    · by_cases he : eViewW m h = []
      · rw [pbW_empty n m T k i h hk ht he] at hm; cases hm
      rw [pbW_pi n m T k i h hk ht he] at hm
      obtain ⟨vv, hview, hVR⟩ := eViewW_ok m a hS.1.arena.1 h he
      have h6 := eViewW_head6S m h ht he
      cases vv with
      | forallE ty body =>
        obtain ⟨-, hx32, hxe, hy32, hye⟩ := hVR
        have hx1 : (eViewW m h).getD 1 0 = (eViewW m h).tail.headD 0 := by
          cases eViewW m h with | nil => rfl | cons _ t => cases t <;> rfl
        have hy1 : (eViewW m h).getD 2 0 = (eViewW m h).tail.tail.headD 0 := by
          cases eViewW m h with
          | nil => rfl
          | cons _ t => cases t with | nil => rfl | cons _ u => cases u <;> rfl
        rw [hx1] at hx32 hxe
        rw [hy1] at hy32 hye
        generalize (eViewW m h).tail.headD 0 = x at hm hx32 hxe
        generalize (eViewW m h).tail.tail.headD 0 = y at hm hy32 hye
        cases h1 : spaW m T i with
        | none => rw [h1] at hm; simp [pbK1, pbK2, pbK3, pbK4] at hm
        | some x1 =>
        obtain ⟨ra, m1⟩ := x1
        rw [h1] at hm
        by_cases hab : 4294967296 ≤ ra.headD 0
        · rw [pbK1_big n m1 T k i x y ra hab] at hm; cases hm
        rw [pbK1_ok n m1 T k i x y ra hab] at hm
        have ha32 : (ra.headD 0).toNat < 2 ^ 32 := by
          have : ¬ (4294967296 : Nat) ≤ (ra.headD 0).toNat := hab; omega
        obtain ⟨a1, hrun1, hS1, hg1⟩ := spaW_ok dn vis fe m m1 a T i ra h1 hS
        have hA1 := spaW_afr h1 hA
        cases h2 : i1lF m1 [CWF, y, ra.headD 0, 0] with
        | none => rw [h2] at hm; simp [pbK1, pbK2, pbK3, pbK4] at hm
        | some x2 =>
        obtain ⟨rb, m2⟩ := x2
        rw [h2, pbK2_some] at hm
        obtain ⟨b', a2, ⟨hrun2, ⟨hS2, hg2, hb32, hbe⟩, hA2⟩⟩ :=
          i1lF_ok dn vis fe CWF y (ra.headD 0) 0 hy32 ha32 m1 m2 a1 rb h2 ⟨hS1, hA1⟩
        cases h3 : pbW n m2 T (k - 1) (i + 1) (rb.headD 0) with
        | none => rw [h3] at hm; simp [pbK1, pbK2, pbK3, pbK4] at hm
        | some x3 =>
        obtain ⟨rr, m3⟩ := x3
        rw [h3] at hm
        obtain ⟨x', a3, hrun3, hS3, hg3, hdec3, hA3⟩ :=
          ih m2 m3 a2 T (k - 1) (i + 1) (rb.headD 0) rr h3 hS2 hb32 (by omega) hA2
        have hg13 := (hg1.trans hg2).trans hg3
        have hview' : (view (decE h)).run a = .ok (.forallE ty body, a) := view_run _ _ _ hview
        rw [CWF_eq, show (0 : Word).toNat = 0 from rfl, ← decE_eq y, hye, ← decE_eq (ra.headD 0)] at hrun2
        rw [hi1, hkm, hbe] at hrun3
        have htwin : ∀ (xo v : Option (List EIdx)) (a' : AState),
            (structProjBodiesGo (decI T) (k.toNat - 1) (i.toNat + 1) b').run a2 = .ok (xo, a3) →
            ((match xo with | some r => pure (some (ty :: r)) | none => pure none :
              AM (Option (List EIdx))).run a3 = .ok (v, a')) →
            (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)).run a = .ok (v, a') := by
          intro xo v a' h3' hv
          rw [hks, structProjBodiesGo, ← decE_eq, if_pos (htf.mpr ht)]
          simp only [StateT.run] at hview' hrun1 hrun2 h3' hv ⊢
          simp only [bind, StateT.bind, Except.bind, hview', hrun1, hrun2, h3']
          exact hv
        cases x' with
        | none =>
          have hz : rr.headD 0 = 0 := hdec3
          rw [pbK3_none n m3 x rr hz] at hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact ⟨none, a3, htwin _ _ _ hrun3 rfl, hS3, hg13, rfl, hA3⟩
        | some l =>
          obtain ⟨h1', hdl, htl⟩ := hdec3
          rw [pbK3_some n m3 x rr (by rw [h1']; decide)] at hm
          cases h4 : consW n m3 x (rr.tail.headD 0) (rr.tail.tail.headD 0) with
          | none => rw [h4] at hm; simp [pbK1, pbK2, pbK3, pbK4] at hm
          | some x4 =>
          obtain ⟨ro, m4⟩ := x4
          rw [h4, pbK4_some] at hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          obtain ⟨hS4, hg4, hd4, ht4⟩ := consW_stage h4 hS3 htl hx32 hdl
          refine ⟨some (ty :: l), a3, htwin _ _ _ hrun3 rfl, hS4, hg13.trans hg4, ⟨rfl, ?_, ?_⟩,
            consW_afr h4 hA3⟩
          · simp only [List.tail_cons, List.headD_cons]; rw [← hxe, decE_eq]; exact hd4
          · simp only [List.tail_cons, List.headD_cons]; omega
      | _ => simp only [ViewR] at hVR <;> (rw [h6] at hVR) <;> simp at hVR
    · rw [pbW_tag n m T k i h hk ht] at hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨none, a, ?_, hS, IWGrow.refl m, rfl, hA⟩
      rw [hks, structProjBodiesGo, ← decE_eq,
        if_neg (fun e => ht (htf.mp e))]
      rfl

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
  (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
  (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
  (hp : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL) (hi1 : I1lF p)
include ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hp hi1

/-- **`struct_proj_bodies_go` refines `structProjBodiesGo`** (through the stub
`instantiate1_lift_fast`, with the walk memos `AbsOK`): `(0, _, _)` for `none`, `(1, off, len)` the
bodies' slice. -/
@[refines ConRon.Arena.structProjBodiesGo]
theorem structProjBodiesGo_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T k i h : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hh : H h) (hik : i.toNat + k.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_bodies_go" [T, k, i, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PBDec s'.mem r (AM.res (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (pbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hp hi1 n s₀ T k i h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hdec, hA'⟩ := pbW_ok dn vis fe n _ _ _ _ _ _ _ _ hm hS hh hik hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hA'⟩

end census

/-! ## `struct_proj_bodies` -/

/-- After `struct_proj_bodies_go`. -/
def spbK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m3) =>
    if rg.headD 0 = 0 then some ([0, 0, 0], m3) else some ([1, rg.tail.headD 0, rg.tail.tail.headD 0], m3)
/-- After `inst_pis_at_lift`. -/
def spbK2 (k : Nat) (T nF : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ri, m2) => if ri.headD 0 = 0 then some ([0, 0, 0], m2) else spbK3 (pbW k m2 T nF 0 (ri.tail.headD 0))
/-- After `struct_proj_ps`. -/
def spbK1 (k : Nat) (T nF cty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => spbK2 k T nF (ipalF m1 [CWF, rp.headD 0, rp.tail.headD 0, cty])
/-- **The model of `struct_proj_bodies`.** -/
def spbW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, T, nP, nF, cty => spbK1 k T nF cty (projPsW k m nP)

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (T nP nF cty : Word) (rp ri rg : List Word)
theorem spbW_succ : spbW (k + 1) m T nP nF cty = spbK1 k T nF cty (projPsW k m nP) := rfl
theorem spbK1_some : spbK1 k T nF cty (some (rp, m1)) =
    spbK2 k T nF (ipalF m1 [CWF, rp.headD 0, rp.tail.headD 0, cty]) := rfl
theorem spbK2_none (h : ri.headD 0 = 0) : spbK2 k T nF (some (ri, m2)) = some ([0, 0, 0], m2) := by
  simp only [spbK2, if_pos h]
theorem spbK2_some (h : ri.headD 0 ≠ 0) :
    spbK2 k T nF (some (ri, m2)) = spbK3 (pbW k m2 T nF 0 (ri.tail.headD 0)) := by
  simp only [spbK2, if_neg h]
theorem spbK3_none (h : rg.headD 0 = 0) : spbK3 (some (rg, m3)) = some ([0, 0, 0], m3) := by
  simp only [spbK3, if_pos h]
theorem spbK3_some (h : rg.headD 0 ≠ 0) :
    spbK3 (some (rg, m3)) = some ([1, rg.tail.headD 0, rg.tail.tail.headD 0], m3) := by
  simp only [spbK3, if_neg h]
end arms

grind_pattern [ind_grind] spbW_succ => spbW (k + 1) m T nP nF cty
grind_pattern [ind_grind] spbK1_some => spbK1 k T nF cty (some (rp, m1))
grind_pattern [ind_grind] spbK2_none => spbK2 k T nF (some (ri, m2))
grind_pattern [ind_grind] spbK2_some => spbK2 k T nF (some (ri, m2))
grind_pattern [ind_grind] spbK3_none => spbK3 (some (rg, m3))
grind_pattern [ind_grind] spbK3_some => spbK3 (some (rg, m3))

section spec2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
  (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
  (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
  (hpg : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL)
  (hgo : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hps : p.lookup "struct_ps_at" = some structPsAtL)
  (hpj : p.lookup "struct_proj_ps" = some structProjPsL)
  (hp : p.lookup "struct_proj_bodies" = some structProjBodiesL) (hi1 : I1lF p) (hipal : IpalF p)
include ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hpg hgo hps hpj hp hi1 hipal

theorem spbW_spec (k : Nat) (s₀ : St) (T nP nF cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "struct_proj_bodies" [T, nP, nF, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ spbW k s₀.mem T nP nF cty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structProjBodiesL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        projPsW_spec p ha hc hsc hpf hpp hib hgo hps hpj k, ipalF_spec p hipal k,
        pbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hpg hi1 k] <;>
      finish (gen := 20)

end spec2

/-- What `struct_proj_bodies` returns: `(0, _, _)` for `none`, `(1, off, len)` for the array. -/
def PBDecA (m : Mem) (r : List Word) : Option (Array EIdx) → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 = 1 ∧ decHL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l.toList ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

theorem spbW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (T nP nF cty : Word) (r : List Word)
    (h : spbW k m T nP nF cty = some (r, m')) (hS : StageR dn vis fe m a) (hcty : H cty)
    (hnP : 1 + nP.toNat < 2 ^ 64) (hnF : nF.toNat < 2 ^ 64) (hA : AbsOK m) :
    ∃ x a', (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PBDecA m' r x ∧ AbsOK m' := by
  cases k with
  | zero => cases h
  | succ k =>
  rw [spbW_succ] at h
  cases h1 : projPsW k m nP with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨rp, m1⟩ := x1
  rw [h1, spbK1_some] at h
  cases k with
  | zero => cases h1
  | succ k' =>
  rw [projPsW_succ] at h1
  cases h0 : psAtW k' m 1 nP with
  | none => rw [h0] at h1; cases h1
  | some x0 =>
  obtain ⟨r0, m0⟩ := x0
  rw [h0, psK3_some] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨ps, a1, hrun1, hS1, hg1, hps, -⟩ := psAtW_stage dn vis fe k' m m0 a 1 nP r0 h0 hS (by simpa using hnP)
  have hA0 : AbsOK m0 := psAtW_afr h0 hA
  simp only [List.headD_cons, List.tail_cons] at h
  cases h2 : ipalF m0 [CWF, r0.headD 0, r0.tail.headD 0, cty] with
  | none => rw [h2] at h; simp [spbK2] at h
  | some x2 =>
  obtain ⟨ri, m2⟩ := x2
  rw [h2] at h
  obtain ⟨xo, a2, hrun2, ⟨hS2, hg2, hdec2⟩, hA2⟩ :=
    ipalF_ok dn vis fe CWF (r0.headD 0) (r0.tail.headD 0) cty hcty ps m0 m2 a1 ri h2
      ⟨hS1, hA0, by simpa using hps⟩
  have hrun0 : ∀ {β : Type} (f : Option EIdx → AM β),
      (do let ps ← structProjPs nP.toNat; let r ← instPisAtLift coreWalkFuel ps (decI cty); f r).run a =
        (f xo).run a2 := by
    intro β f
    simp only [structProjPs, StateT.run_bind]
    rw [show (1 : Nat) = (1 : Word).toNat from rfl, hrun1]
    simp only [bind, Except.bind, StateT.run_bind]
    rw [CWF_eq] at hrun2
    simp only [StateT.run] at hrun2 ⊢
    rw [hrun2]
  cases xo with
  | none =>
    have hz : ri.headD 0 = 0 := hdec2
    rw [spbK2_none (k' + 1) m2 T nF ri hz] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl, hA2⟩
    simp only [structProjBodies]
    rw [hrun0]; rfl
  | some e =>
    obtain ⟨h1', he32, hee⟩ := hdec2
    rw [spbK2_some (k' + 1) m2 T nF ri (by rw [h1']; decide)] at h
    cases h3 : pbW (k' + 1) m2 T nF 0 (ri.tail.headD 0) with
    | none => rw [h3] at h; simp [spbK3] at h
    | some x3 =>
    obtain ⟨rg, m3⟩ := x3
    rw [h3] at h
    obtain ⟨x, a3, hrun3, hS3, hg3, hdec3, hA3⟩ :=
      pbW_ok dn vis fe (k' + 1) m2 m3 a2 T nF 0 (ri.tail.headD 0) rg h3 hS2 he32 (by simpa using hnF) hA2
    rw [show (0 : Word).toNat = 0 from rfl, hee] at hrun3
    cases x with
    | none =>
      have hz : rg.headD 0 = 0 := hdec3
      rw [spbK3_none m3 rg hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨none, a3, ?_, hS3, (hg1.trans hg2).trans hg3, rfl, hA3⟩
      simp only [structProjBodies]
      rw [hrun0]
      simp only [StateT.run_bind, hrun3]; rfl
    | some l =>
      obtain ⟨hl1, hdl, htl⟩ := hdec3
      rw [spbK3_some m3 rg (by rw [hl1]; decide)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨some l.toArray, a3, ?_, hS3, (hg1.trans hg2).trans hg3, ⟨rfl, by simpa using hdl,
        by simpa using htl⟩, hA3⟩
      simp only [structProjBodies]
      rw [hrun0]
      simp only [StateT.run_bind, hrun3]; rfl

section census2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
  (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
  (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
  (hpg : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL)
  (hgo : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hps : p.lookup "struct_ps_at" = some structPsAtL)
  (hpj : p.lookup "struct_proj_ps" = some structProjPsL)
  (hp : p.lookup "struct_proj_bodies" = some structProjBodiesL) (hi1 : I1lF p) (hipal : IpalF p)
include ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hpg hgo hps hpj hp hi1 hipal

/-- **`struct_proj_bodies` refines `structProjBodies`** (through the models `ipalF`,
`i1lF`). -/
@[refines ConRon.Arena.structProjBodies]
theorem structProjBodies_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T nP nF cty : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hcty : H cty) (hnP : 1 + nP.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "struct_proj_bodies" [T, nP, nF, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PBDecA s'.mem r (AM.res (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (spbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hpg hgo hps hpj hp hi1
    hipal k s₀ T nP nF cty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hdec, hA'⟩ :=
    spbW_ok dn vis fe k _ _ _ _ _ _ _ _ hm hS hcty hnP nF.toNat_lt hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hA'⟩

end census2

end L.Ind
