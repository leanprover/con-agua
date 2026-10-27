import ConAgua.Arena.IndSumSpec.PBDecA
import ConAgua.Arena.IndSumSpec.StructCtorResidOk

/-!
# StructProjBodies: `ConRon.Arena.structProjBodiesGo`, `ConRon.Arena.structProjBodies`

The refinement theorems `structProjBodiesGo_refines`, `structProjBodies_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_proj_bodies_go` -/

/-- **`struct_proj_bodies_go` is its model `pbW`** (generated). -/
l_model pbW_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
    (hp : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL) (hi1 : I1lF p)
  fns [hp ↦ pbW]
  specs [eView_spec p hv n, spaW_spec p hd hpf hpp hib hjf hjp hji hmp hap n,
    i1lF_spec p hi1 n, slCons_specW p ha hc hsc n]
  grind [ind_grind] simp []

/-! ## The relational lemma -/

theorem spaW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a : AState)
    (T j : Word) (r : List Word) (h : spaW m T j = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ a', (structProjArgP (decI T) j.toNat).run a = .ok (decE (r.headD 0), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [spaW] at h
  obtain ⟨b, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [spaK_some] at h
  obtain ⟨e, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [spaK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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
    ite_false, ite_true]
  repeat' split
  all_goals simp

/-- What `struct_proj_bodies_go` returns: `(0, _, _)` for `none`, `(1, off, len)` for a slice. -/
def PBDec (m : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 = 1 ∧ decHL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

theorem pbW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m : Mem) (a : AState) (T k i h : Word), StageR dn vis fe m a → H h →
    i.toNat + k.toNat < 2 ^ 64 → AbsOK m →
    Sim (pbW n m T k i h) (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PBDec m' r x ∧ AbsOK m') := by
  induction n with
  | zero => intro m a T k i h _ _ _ _; rw [pbW.eq_1]; exact Sim.of_none
  | succ n ih =>
    intro m a T k i h hS hh hik hA
    by_cases hk : k = 0
    · subst hk; rw [pbW.arm1 n m T 0 i h rfl]
      exact Sim.congr (Sim.ret (x := some []) ⟨hS, IWGrow.refl m, by simp [PBDec, decHL, hslice?], hA⟩)
        (by simp [structProjBodiesGo])
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
    case neg =>
      rw [pbW.arm2 n m T k i h hk ht, hks, structProjBodiesGo, ← decE_eq, ite_eq_right (fun e => ht (htf.mp e))]
      exact Sim.ret ⟨hS, IWGrow.refl m, rfl, hA⟩
    by_cases he : eViewW m h = []
    · rw [pbW.abort1 n m T k i h hk ht he]; exact Sim.of_none
    rw [pbW.arm3 n m T k i h hk ht he, hks, structProjBodiesGo, ← decE_eq, ite_eq_left (htf.mpr ht)]
    obtain ⟨vv, hview, hVR⟩ := eViewW_ok m a hS.1.arena.1 h he
    have h6 := eViewW_head6S m h ht he
    refine Sim.bind_twin (view_run _ _ _ hview) ?_
    cases vv with
    | forallE ty body =>
      obtain ⟨-, hx32, rfl, hy32, rfl⟩ := hVR
      simp only [getD1_eq', getD2_eq] at hx32 hy32 ⊢
      generalize (eViewW m h).tail.headD 0 = x at hx32 ⊢
      generalize (eViewW m h).tail.tail.headD 0 = y at hy32 ⊢
      refine Sim.bindD (dec := fun ra => decE (ra.headD 0))
        (R₁ := fun m1 a1 => StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ AbsOK m1)
        (pbW.k_struct_proj_arg_p.none ..) (fun _ _ => rfl) (fun ra m1 h1 => ?_) ?_
      · obtain ⟨a1, hr, hS1, hg1⟩ := spaW_ok dn vis fe m m1 a T i ra h1 hS
        exact ⟨_, a1, hr, rfl, hS1, hg1, spaW_afr h1 hA⟩
      rintro ra m1 a1 ⟨hS1, hg1, hA1⟩
      by_cases hab : 4294967296 ≤ ra.headD 0
      · rw [pbW.k_struct_proj_arg_p.abort1 (hc1 := hab)]; exact Sim.of_none
      rw [pbW.k_struct_proj_arg_p.arm1 (hc1 := hab)]
      have ha32 : (ra.headD 0).toNat < 2 ^ 32 := by
        have : ¬ (4294967296 : Nat) ≤ (ra.headD 0).toNat := hab; omega
      refine Sim.bindK (pbW.k_instantiate1_lift_fast.none ..) (fun _ _ => rfl) (fun r m' e =>
        i1lF_ok dn vis fe CWF y (ra.headD 0) 0 hy32 ha32 m1 m' a1 r e ⟨hS1, hA1⟩) ?_
      rintro rb _ m2 a2 ⟨⟨hS2, hg2, hb32, rfl⟩, hA2⟩
      rw [pbW.k_instantiate1_lift_fast.arm1, ← hkm, ← hi1]
      refine Sim.bindK (pbW.k_struct_proj_bodies_go.none ..) (fun _ _ => rfl)
        (ih m2 a2 T (k - 1) (i + 1) (rb.headD 0) hS2 hb32 (by omega) hA2) ?_
      rintro rr (_ | l) m3 a3 ⟨hS3, hg3, hdec3, hA3⟩
      · rw [pbW.k_struct_proj_bodies_go.arm1 (hc1 := hdec3)]
        exact Sim.ret ⟨hS3, (hg1.trans hg2).trans hg3, rfl, hA3⟩
      obtain ⟨h1', hdl, htl⟩ := hdec3
      rw [pbW.k_struct_proj_bodies_go.arm2 (hc1 := by rw [h1']; decide)]
      rcases h4 : consW n m3 x (rr.tail.headD 0) (rr.tail.tail.headD 0) with _ | ⟨ro, m4⟩
      · exact Sim.of_none
      obtain ⟨hS4, hg4, hd4, ht4⟩ := consW_stage h4 hS3 htl hx32 hdl
      exact Sim.ret ⟨hS4, ((hg1.trans hg2).trans hg3).trans hg4, ⟨rfl, by simpa [decE_eq] using hd4,
        by simp only [List.tail_cons, List.headD_cons]; omega⟩, consW_afr h4 hA3⟩
    | _ => simp only [ViewR] at hVR <;> (rw [h6] at hVR) <;> simp at hVR

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
  obtain ⟨x, a', hrun, hS', hg, hdec, hA'⟩ := pbW_ok dn vis fe n _ _ _ _ _ _ hS hh hik hA _ _ hm
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
  simp only [spbK2, ite_eq_left h]
theorem spbK2_some (h : ri.headD 0 ≠ 0) :
    spbK2 k T nF (some (ri, m2)) = spbK3 (pbW k m2 T nF 0 (ri.tail.headD 0)) := by
  simp only [spbK2, ite_eq_right h]
theorem spbK3_none (h : rg.headD 0 = 0) : spbK3 (some (rg, m3)) = some ([0, 0, 0], m3) := by
  simp only [spbK3, ite_eq_left h]
theorem spbK3_some (h : rg.headD 0 ≠ 0) :
    spbK3 (some (rg, m3)) = some ([1, rg.tail.headD 0, rg.tail.tail.headD 0], m3) := by
  simp only [spbK3, ite_eq_right h]
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
  obtain ⟨rp, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [spbK1_some] at h
  cases k with
  | zero => cases h1
  | succ k' =>
  rw [projPsW_succ] at h1
  obtain ⟨r0, m0, h0, h1⟩ := kSome_inv h1 rfl (fun _ _ => rfl)
  rw [psK3_some] at h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
  obtain ⟨ps, a1, hrun1, hS1, hg1, hps, -⟩ := psAtW_stage dn vis fe k' m m0 a 1 nP r0 h0 hS (by simpa using hnP)
  have hA0 : AbsOK m0 := psAtW_afr h0 hA
  simp only [List.headD_cons, List.tail_cons] at h
  obtain ⟨ri, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨xo, a2, hrun2, ⟨hS2, hg2, hdec2⟩, hA2⟩ :=
    ipalF_ok dn vis fe CWF (r0.headD 0) (r0.tail.headD 0) cty hcty ps m0 m2 a1 ri h2
      ⟨hS1, hA0, by simpa using hps⟩
  have hrun0 : ∀ {β : Type} (f : Option EIdx → AM β),
      (do let ps ← structProjPs nP.toNat; let r ← instPisAtLift coreWalkFuel ps (decI cty); f r).run a =
        (f xo).run a2 := by
    intro β f
    simp only [structProjPs, StateT.run_bind]
    rw [show (1 : Nat) = (1 : Word).toNat from rfl, hrun1]
    simp only [bind, Except.bind]
    rw [CWF_eq] at hrun2
    simp only [StateT.run] at hrun2 ⊢
    rw [hrun2]
  cases xo with
  | none =>
    have hz : ri.headD 0 = 0 := hdec2
    rw [spbK2_none (k' + 1) m2 T nF ri hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl, hA2⟩
    simp only [structProjBodies]
    rw [hrun0]; rfl
  | some e =>
    obtain ⟨h1', he32, hee⟩ := hdec2
    rw [spbK2_some (k' + 1) m2 T nF ri (by rw [h1']; decide)] at h
    obtain ⟨rg, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    obtain ⟨x, a3, hrun3, hS3, hg3, hdec3, hA3⟩ :=
      pbW_ok dn vis fe (k' + 1) m2 a2 T nF 0 (ri.tail.headD 0) hS2 he32 (by simpa using hnF) hA2 _ _ h3
    rw [show (0 : Word).toNat = 0 from rfl, hee] at hrun3
    cases x with
    | none =>
      have hz : rg.headD 0 = 0 := hdec3
      rw [spbK3_none m3 rg hz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a3, ?_, hS3, (hg1.trans hg2).trans hg3, rfl, hA3⟩
      simp only [structProjBodies]
      rw [hrun0]
      simp only [StateT.run_bind, hrun3]; rfl
    | some l =>
      obtain ⟨hl1, hdl, htl⟩ := hdec3
      rw [spbK3_some m3 rg (by rw [hl1]; decide)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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

end
