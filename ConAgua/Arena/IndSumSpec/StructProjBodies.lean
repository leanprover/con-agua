module

public import ConAgua.Arena.IndSumSpec.PBDecA
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndPosSpec.MatesW
public import ConAgua.Arena.IndRealIlpP
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndSumSpec.Row
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.IndSumSpec.StructProjArgP
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.ProjStore

@[expose] public section

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
  grind [ind_grind]

/-! ## The relational lemma -/

theorem spaW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a : AState)
    (T j : Word) (r : List Word) (h : spaW m T j = some (r, m')) (hS : StageR vis fe m a) :
    ∃ a', (structProjArgP (decI T) j.toNat).run a = .ok (decE (r.headD 0), a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
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

theorem eViewW_head6S (m : Mem) (h : Word) (hg : tagW h = 6) (hne : eViewW m h ≠ []) :
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
    ∀ (m : Mem) (a : AState) (T k i h : Word), StageR vis fe m a → H h →
    i.toNat + k.toNat < 2 ^ 64 → AbsOK m →
    Sim (pbW n m T k i h) (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧ PBDec m' r x ∧ AbsOK m') := by
  sorry

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
    (hS : StageR vis fe s₀.mem a₀) (hh : H h) (hik : i.toNat + k.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_bodies_go" [T, k, i, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a₀ ∧
      StageR vis fe s'.mem (AM.st (structProjBodiesGo (decI T) k.toNat i.toNat (decI h)) a₀) ∧
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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        projPsW_spec p ha hc hsc hpf hpp hib hgo hps hpj k, ipalF_spec p hipal k,
        pbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hpg hi1 k] <;>
      finish (gen := 20)

end spec2

theorem spbW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (T nP nF cty : Word) (r : List Word)
    (h : spbW k m T nP nF cty = some (r, m')) (hS : StageR vis fe m a) (hcty : H cty)
    (hnP : 1 + nP.toNat < 2 ^ 64) (hnF : nF.toNat < 2 ^ 64) (hA : AbsOK m) :
    ∃ x a', (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)).run a = .ok (x, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ PBDecA m' r x ∧ AbsOK m' := by
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
    (hS : StageR vis fe s₀.mem a₀) (hcty : H cty) (hnP : 1 + nP.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "struct_proj_bodies" [T, nP, nF, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)) a₀ ∧
      StageR vis fe s'.mem (AM.st (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)) a₀) ∧
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
