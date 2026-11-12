module

public import ConAgua.Arena.IndSumSpec.PBDecA
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
public import ConAgua.Arena.IndRealMemo
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
import ConAgua.L.WordOff
import ConAgua.Arena.IndDecStab

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
    (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL) (hi1 : I1lF p)
  fns [hp ↦ pbW]
  specs [eView_spec p hv n, i1lF_spec p hi1 n, spaW_spec p hd hpf hpp hib hjf hjp hji hmp hap n,
    slSnoc_specW p ha hc hsn n, slCons_specW p ha hc hsc n]
  grind [ind_grind]

/-! ## The relational lemma -/

theorem spaW_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a : AState)
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

/-- **`sl_snoc` keeps the stage relation** (the slice of handles `xs` grew by `x`). -/
private theorem pbSnoc_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List EIdx}
    (h : snocW n m o l x = some (r, m')) (hS : StageR vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m) (hx : x.toNat < 2 ^ 32)
    (hxs : decHL m o.toNat l.toNat = some xs) : StageR vis fe m' a := by
  have hsz := hS.iw.iwSize
  obtain ⟨-, -, -, hf, -, htop⟩ := snocW_dec h hsz hS.iw.ctl hsrc hx hxs
  refine ⟨CheckR.frame_iw hf hS.check, IWOK.of_iw hf hS.iw ?_⟩
  rw [hf.size IW]
  simp only [snocW] at h
  have h0 : l + 1 ≠ 0 := by intro e0; simp [e0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l + 1) with _ | qm
  · simp [hal] at h
  obtain ⟨hq, -, hroom⟩ := allocW_facts hal hsz
  rw [← htop, ← hq]; exact hroom

theorem pbW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m : Mem) (a : AState) (T vo vl k i h : Word) (xs : List EIdx), StageR vis fe m a → H h →
    i.toNat + k.toNat < 2 ^ 64 → AbsOK m → decHL m vo.toNat vl.toNat = some xs →
    vo.toNat + vl.toNat ≤ iwTop m →
    Sim (pbW n m T vo vl k i h) (structProjBodiesGo (decI T) xs.toArray k.toNat i.toNat (decI h)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧ PBDec m' r x ∧ AbsOK m') := by
  induction n with
  | zero => intro m a T vo vl k i h xs _ _ _ _ _ _; rw [pbW.eq_1]; exact Sim.of_none
  | succ n ih =>
    intro m a T vo vl k i h xs hS hh hik hA hxs hvt
    by_cases hk : k = 0
    · subst hk; rw [pbW.arm1 n m T vo vl 0 i h rfl]
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
    have htf : ((decE h).tag == ETag.forallE) = true ↔ tagW h = 6 := by
      rw [beq_iff_eq, show ETag.forallE = (6 : Word).toUInt32 from rfl]
      exact decE_tag_eqW h hh 6 (by decide)
    by_cases ht : tagW h = 6
    case neg =>
      rw [pbW.arm2 n m T vo vl k i h hk ht, hks, structProjBodiesGo, ← decE_eq,
        ite_eq_right (fun e => ht (htf.mp e))]
      exact Sim.ret ⟨hS, IWGrow.refl m, rfl, hA⟩
    by_cases he : eViewW m h = []
    · rw [pbW.abort1 n m T vo vl k i h hk ht he]; exact Sim.of_none
    rw [pbW.arm3 n m T vo vl k i h hk ht he, hks, structProjBodiesGo, ← decE_eq, ite_eq_left (htf.mpr ht)]
    obtain ⟨vv, hview, hVR⟩ := eViewW_ok m a hS.check.arena.base h he
    have h6 := eViewW_head6S m h ht he
    refine Sim.bind_twin (view_run _ _ _ hview) ?_
    cases vv with
    | forallE ty body =>
      obtain ⟨-, hx32, rfl, hy32, rfl⟩ := hVR
      simp only [L.getD_one, L.getD_two] at hx32 hy32 ⊢
      generalize (eViewW m h).tail.headD 0 = x at hx32 ⊢
      generalize (eViewW m h).tail.tail.headD 0 = y at hy32 ⊢
      refine Sim.bindK (pbW.k_instantiate_lift_fast.none ..) (fun _ _ => rfl) (fun r m' e =>
        i1lF_ok dn vis fe CWF x vo vl 0 hx32 xs m m' a r e ⟨hS, hA, hxs⟩) ?_
      rintro rb _ m1 a1 ⟨⟨hS1, hg1, hb32, rfl⟩, hA1⟩
      rw [pbW.k_instantiate_lift_fast.arm1]
      have hxs1 : decHL m1 vo.toNat vl.toNat = some xs := decHL_grow' hg1 hvt hxs
      refine Sim.bindD (dec := fun ra => decE (ra.headD 0))
        (R₁ := fun m2 a2 => StageR vis fe m2 a2 ∧ IWGrow m1 m2 ∧ AbsOK m2)
        (pbW.k_struct_proj_arg_p.none ..) (fun _ _ => rfl) (fun ra m2 h2 => ?_) ?_
      · obtain ⟨a2, hr, hS2, hg2⟩ := spaW_ok dn vis fe m1 m2 a1 T i ra h2 hS1
        exact ⟨_, a2, hr, rfl, hS2, hg2, spaW_afr h2 hA1⟩
      rintro ra m2 a2 ⟨hS2, hg2, hA2⟩
      by_cases hab : 4294967296 ≤ ra.headD 0
      · rw [pbW.k_struct_proj_arg_p.abort1 (hc1 := hab)]; exact Sim.of_none
      rw [pbW.k_struct_proj_arg_p.arm1 (hc1 := hab)]
      have ha32 : (ra.headD 0).toNat < 2 ^ 32 := by
        have : ¬ (4294967296 : Nat) ≤ (ra.headD 0).toNat := hab; omega
      have hxs2 : decHL m2 vo.toNat vl.toNat = some xs := decHL_grow' hg2 (by have := hg1.iw; omega) hxs1
      rcases h3 : snocW n m2 vo vl (ra.headD 0) with _ | ⟨rs, m3⟩
      · rw [pbW.k_sl_snoc.none]; exact Sim.of_none
      obtain ⟨hrs, hdec3, hg3, hf3, hl1, htop3⟩ := snocW_dec h3 hS2.iw.iwSize hS2.iw.ctl
        (by have := hg1.iw; have := hg2.iw; omega) ha32 hxs2
      have hS3 := pbSnoc_stage h3 hS2 (by have := hg1.iw; have := hg2.iw; omega) ha32 hxs2
      subst hrs
      rw [pbW.k_sl_snoc.arm1]
      simp only [List.headD_cons, List.tail_cons] at ⊢
      rw [← hkm, ← hi1, show (xs.toArray.push (decE (ra.headD 0))) = (xs ++ [decI (ra.headD 0)]).toArray
        by simp; rfl]
      refine Sim.bindK (pbW.k_struct_proj_bodies_go.none ..) (fun _ _ => rfl)
        (ih m3 a2 T _ (vl + 1) (k - 1) (i + 1) y _ hS3 hy32 (by omega) (AFr.iw hf3 hA2) hdec3
          (by omega)) ?_
      rintro rr (_ | l) m4 a4 ⟨hS4, hg4, hdec4, hA4⟩
      · rw [pbW.k_struct_proj_bodies_go.arm1 (hc1 := hdec4)]
        exact Sim.ret ⟨hS4, (((hg1.trans hg2).trans hg3).trans hg4), rfl, hA4⟩
      obtain ⟨h1', hdl, htl⟩ := hdec4
      rw [pbW.k_struct_proj_bodies_go.arm2 (hc1 := by rw [h1']; decide)]
      rcases h5 : consW n m4 (rb.headD 0) (rr.tail.headD 0) (rr.tail.tail.headD 0) with _ | ⟨ro, m5⟩
      · exact Sim.of_none
      obtain ⟨hS5, hg5, hd5, ht5⟩ := consW_stage h5 hS4 htl hb32 hdl
      exact Sim.ret ⟨hS5, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5,
        ⟨rfl, by simpa [decE_eq] using hd5, by simp only [List.tail_cons, List.headD_cons]; omega⟩,
        consW_afr h5 hA4⟩
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
  (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL) (hi1 : I1lF p)
include ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hsn hp hi1

/-- **`struct_proj_bodies_go` refines `structProjBodiesGo`** (through `instantiate_lift_fast`,
with the walk memos `AbsOK`), the values the decoded `IW` slice `(vo, vl)`: `(0, _, _)` for
`none`, `(1, off, len)` the bodies' slice. -/
@[refines ConRon.Arena.structProjBodiesGo]
theorem structProjBodiesGo_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T vo vl k i h : Word)
    (xs : List EIdx) (hS : StageR vis fe s₀.mem a₀) (hh : H h) (hik : i.toNat + k.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) (hxs : decHL s₀.mem vo.toNat vl.toNat = some xs)
    (hvt : vo.toNat + vl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_bodies_go" [T, vo, vl, k, i, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structProjBodiesGo (decI T) xs.toArray k.toNat i.toNat (decI h)) a₀ ∧
      StageR vis fe s'.mem (AM.st (structProjBodiesGo (decI T) xs.toArray k.toNat i.toNat (decI h)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PBDec s'.mem r (AM.res (structProjBodiesGo (decI T) xs.toArray k.toNat i.toNat (decI h)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (pbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hsn hp hi1 n s₀ T vo vl k i h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hdec, hA'⟩ := pbW_ok dn vis fe n _ _ _ _ _ _ _ _ xs hS hh hik hA hxs hvt _ _ hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hA'⟩

end census

/-! ## `struct_proj_bodies` -/

/-- **The model of `struct_proj_bodies`** (`spbW`). -/
l_model spbW_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
    (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hpg : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL)
    (hgo : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hps : p.lookup "struct_ps_at" = some structPsAtL)
    (hpj : p.lookup "struct_proj_ps" = some structProjPsL)
    (hp : p.lookup "struct_proj_bodies" = some structProjBodiesL) (hi1 : I1lF p) (hst : StripProg p)
  fns [hp ↦ spbW list]
  specs [stripPis_specF p hst n, projPsW_spec p ha hc hsc hpf hpp hib hgo hps hpj n,
    pbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hsn hpg hi1 n]
  grind [ind_grind]

theorem spbW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (T nP nF cty : Word) (r : List Word)
    (h : spbW k m T nP nF cty = some (r, m')) (hS : StageR vis fe m a) (hcty : H cty)
    (hnP : 1 + nP.toNat < 2 ^ 64) (hnF : nF.toNat < 2 ^ 64) (hA : AbsOK m) :
    ∃ x a', (structProjBodies (decI T) nP.toNat nF.toNat (decI cty)).run a = .ok (x, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ PBDecA m' r x ∧ AbsOK m' := by
  cases k with
  | zero => cases h
  | succ k =>
  rw [spbW.arm1] at h
  obtain ⟨rs, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨xo, a1, hrun1, hS1, hg1, hdec1⟩ := stripF_pis_ok vis fe nP cty hcty m m1 a rs h1 hS
  have hA1 : AbsOK m1 := stripF_afr h1 hA
  cases xo with
  | none =>
    have hz : rs.headD 0 = 0 := hdec1
    rw [spbW.k_strip_pis.arm1 (hc1 := hz)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a1, ?_, hS1, hg1, rfl, hA1⟩
    simp only [structProjBodies, StateT.run_bind, hrun1]; rfl
  | some pe =>
    obtain ⟨doms, e⟩ := pe
    obtain ⟨h1', -, he32, hee⟩ := hdec1
    rw [spbW.k_strip_pis.arm2 (hc1 := by rw [h1']; decide)] at h
    obtain ⟨rp, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [spbW.k_struct_proj_ps.arm1] at h
    cases k with
    | zero => cases h2
    | succ k' =>
    rw [projPsW.arm1] at h2
    obtain ⟨r0, m0, h0, h2⟩ := kSome_inv h2 rfl (fun _ _ => rfl)
    rw [projPsW.k_struct_ps_at.arm1] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    obtain ⟨ps, a2, hrun2, hS2, hg2, hps, htop⟩ :=
      psAtW_stage dn vis fe k' m1 m0 a1 1 nP r0 h0 hS1 (by simpa using hnP)
    have hA0 : AbsOK m0 := psAtW_afr h0 hA1
    simp only [List.headD_cons, List.tail_cons] at h
    have he32' : H (rs.tail.tail.tail.headD 0) := by simpa [decW0E] using he32
    obtain ⟨rg, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    obtain ⟨x, a3, hrun3, hS3, hg3, hdec3, hA3⟩ :=
      pbW_ok dn vis fe (k' + 1) m0 a2 T (r0.headD 0) (r0.tail.headD 0) nF 0 (rs.tail.tail.tail.headD 0)
        ps hS2 he32' (by simpa using hnF) hA0 hps (by omega) _ _ h3
    have hee' : decI (rs.tail.tail.tail.headD 0) = e := by simpa [decW0E] using hee
    rw [show (0 : Word).toNat = 0 from rfl, hee'] at hrun3
    have hrun0 : ∀ {β : Type} (f : Option (List EIdx) → AM β),
        (do let ps ← structProjPs nP.toNat
            let r ← structProjBodiesGo (decI T) ps.toArray nF.toNat 0 e; f r).run a1 =
          (f x).run a3 := by
      intro β f
      simp only [structProjPs, StateT.run_bind]
      rw [show (1 : Nat) = (1 : Word).toNat from rfl, hrun2]
      simp only [bind, Except.bind]
      simp only [StateT.run] at hrun3 ⊢
      rw [hrun3]
    cases x with
    | none =>
      have hz : rg.headD 0 = 0 := hdec3
      rw [spbW.k_struct_proj_bodies_go.arm1 (hc1 := hz)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a3, ?_, hS3, (hg1.trans hg2).trans hg3, rfl, hA3⟩
      simp only [structProjBodies, StateT.run_bind, hrun1, except_ok_bind]
      exact hrun0 (fun r => match r with
        | some l => pure (some l.toArray)
        | none => pure none)
    | some l =>
      obtain ⟨hl1, hdl, htl⟩ := hdec3
      rw [spbW.k_struct_proj_bodies_go.arm2 (hc1 := by rw [hl1]; decide)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨some l.toArray, a3, ?_, hS3, (hg1.trans hg2).trans hg3, ⟨rfl, by simpa using hdl,
        by simpa using htl⟩, hA3⟩
      simp only [structProjBodies, StateT.run_bind, hrun1, except_ok_bind]
      exact hrun0 (fun r => match r with
        | some l => pure (some l.toArray)
        | none => pure none)

section census2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
  (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
  (hap : p.lookup "struct_proj_arg_p" = some structProjArgPL)
  (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hpg : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL)
  (hgo : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hps : p.lookup "struct_ps_at" = some structPsAtL)
  (hpj : p.lookup "struct_proj_ps" = some structProjPsL)
  (hp : p.lookup "struct_proj_bodies" = some structProjBodiesL) (hi1 : I1lF p) (hst : StripProg p)
include ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hsn hpg hgo hps hpj hp hi1 hst

/-- **`struct_proj_bodies` refines `structProjBodies`** (through `strip_pis` and the models
`pbW`, `i1lF`). -/
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
  refine triple_post (spbW_spec p ha hc hsc hv hd hpf hpp hib hjf hjp hji hmp hap hsn hpg hgo hps hpj hp hi1
    hst k s₀ T nP nF cty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hdec, hA'⟩ :=
    spbW_ok dn vis fe k _ _ _ _ _ _ _ _ hm hS hcty hnP nF.toNat_lt hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hdec, hA'⟩

end census2

end L.Ind

end
