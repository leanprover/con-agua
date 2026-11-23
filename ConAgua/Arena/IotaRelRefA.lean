module

public import ConAgua.Arena.IotaRelRefN
public import ConAgua.Arena.IndPosSpec.NtyLook
public import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.RecLayout.CIDec
public import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Core.Walks.Spine

@[expose] public section

/-!
# The ι reading rule, part 2: the consumed annotations (lane ronsync8)

`ann_witness`, `ann_ident_body`, `ann_ident_val`, `ann_ident`, `ann_eq` against the twin's
`annWitness`, `annIdentBody`, `annIdentVal`, `annIdent`, `annEq` (the statements of
`IotaRelRef.lean`: `StageR` at the index read, con-ron's `CheckOK` at the entry index).
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- The lookups of the ι rule's comparisons (`IotaRel.lean`'s functions and their callees). -/
structure IotaRelProg (p : Prog) : Prop where
  ev : p.lookup "e_view" = some eView
  lvl : LvlCacheProg p
  lsn : p.lookup "ls_node" = some lsNode
  vll : p.lookup "view_ls_len" = some viewLsLenL
  erg : p.lookup "env_row_get" = some envRowGetL
  brg : p.lookup "base_row_get" = some baseRowGetL
  ef : p.lookup "env_find" = some envFindL
  na : NaF p
  nr : NrF p
  ele : p.lookup "expr_lvl_eq" = some exprLvlEqL
  nop : p.lookup "name_opt_param" = some nameOptParamL
  nap : p.lookup "name_auto_param" = some nameAutoParamL
  nout : p.lookup "name_out_param" = some nameOutParamL
  nsop : p.lookup "name_semi_out_param" = some nameSemiOutParamL
  nmis : p.lookup "name_missing" = some nameMissingL
  aw : p.lookup "ann_witness" = some annWitnessL

section ann
variable {p : Prog} {env : ConLeche.Env} {fe feR : IFEnv} {vis : Word}

theorem const_name_den {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx} {us : LsIdx}
    (hv : st.view h = some (.const n us)) : ∃ x, denoteN st.ns n = some x := by
  obtain ⟨rk, w⟩ := hwf
  have hs := (w.nchildOK h _ hv n (by simp [ENodeView.nchildren])).1
  obtain ⟨rkL, wL⟩ := w.lss.ls
  obtain ⟨rk', w'⟩ := wL.ns
  exact denoteN_of_viewW w' _ n (Nat.lt_succ_self _) hs

/-- The length word of a stored level list. -/
theorem lsNode_len {m : Mem} {a : AState} (hR : ArenaR m a) {us : Word} (hus : HW us)
    {ls : List ConLeche.Level} (hd : denoteLs a.store.lss (decI us) = some ls) :
    lsNodeW m us ≠ [] ∧ ((lsNodeW m us).tail.headD 0).toNat = ls.length := by
  obtain ⟨ids, hv, hdl⟩ := denoteLs_view a _ ls hd
  obtain ⟨e1, -, s1⟩ := lsNodeW_store hR hus hv
  refine ⟨by rw [e1]; simp, ?_⟩
  rw [e1]
  have h1 := congrArg List.length s1
  rw [sliceL_length, lsWords, List.length_map] at h1
  simp only [List.tail_cons, List.headD_cons]
  rw [h1]
  exact (ConRon.Bridge.denoteLList_len hdl).symm

theorem irEnvFind (P : IotaRelProg p) {n : Nat} {m m' : Mem} {w v : Word} {r : List Word}
    (h : callW p n "env_find" [w, v] m = some (r, m')) : m' = m ∧ r = findRes m v w := by
  obtain ⟨s', hs', hm, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_spec p P.erg P.brg P.ef n _ v w) h
  exact ⟨hs' ▸ hm, hr⟩

theorem irViewLsLen (P : IotaRelProg p) {n : Nat} {m m' : Mem} {us : Word} {r : List Word}
    (h : callW p n "view_ls_len" [us] m = some (r, m')) :
    m' = m ∧ r = [1, (lsNodeW m us).tail.headD 0] := by
  obtain ⟨s', hs', -, hm, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (viewLsLen_specE p P.lsn P.vll n _ us) h
  exact ⟨hs' ▸ hm, hr⟩

/-- **`ann_witness(vis, D)` refines `annWitness feR D`.** -/
theorem annWitness_rel (P : IotaRelProg p) {n : Nat} {m m' : Mem} {a : AState} {D : Word}
    {r : List Word} (hc : callW p n "ann_witness" [vis, D] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a) (hD : HW D) :
    ∃ b a', (annWitness feR (decE D)).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧
      IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (annWitness_specW p P.aw n _ vis D) hc
  rcases n with _ | n
  · rw [annWitnessW.eq_1] at hW; cases hW
  have tb := irTagB D hD
  have hR := hS.check.arena.base
  by_cases h3 : tagW D ≠ 3
  · rw [annWitnessW.arm1 _ _ _ _ _ h3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B], ConRon.Bridge.CoreStep.refl hok⟩
    simp only [annWitness, tb ETag.const 3 rfl (by decide), irOfNat3, h3, decide_false,
      Bool.false_eq_true, ite_false]; rfl
  have h3 : tagW D = 3 := Classical.not_not.mp h3
  rw [annWitnessW.arm2 _ _ _ _ _ h3] at hW
  rcases c1 : callW p n "e_view" [D] m with _ | ⟨r1, m1⟩
  · rw [c1, annWitnessW.k_e_view.eq_1] at hW; cases hW
  rw [c1, annWitnessW.k_e_view.arm1] at hW
  obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view P.ev hR c1
  subst m1
  obtain ⟨rfl, hn1, hu1⟩ := irVR_const hr1 (by rw [ht1, h3])
  obtain ⟨ls, hdl⟩ := const_lvls_den hok.state.wf hv1
  obtain ⟨hne, hlen⟩ := lsNode_len hR hu1 hdl
  rcases c2 : callW p n "view_ls_len" [r1.tail.tail.headD 0] m with _ | ⟨r2, m2⟩
  · rw [c2, annWitnessW.k_view_ls_len.eq_1] at hW; cases hW
  obtain ⟨hm2, hr2⟩ := irViewLsLen P c2
  subst m2
  have tw : (decE D).tag = ETag.const := by rw [decE_tag D hD, h3]; rfl
  have ec : (Idx.tag (decE D) == ETag.const) = true := by rw [tw]; rfl
  simp only [annWitness, ec, ite_true]
  rw [StateT.run_bind, viewConst_run', irViewConst tw hv1, except_ok_bind]
  dsimp only
  rw [StateT.run_bind, viewLsLen_run', ConRon.Bridge.Core.viewLen_of_denoteLs hdl, except_ok_bind]
  dsimp only
  have hl2 : (r2.tail.headD 0).toNat = ls.length := by rw [hr2]; simpa using hlen
  by_cases hl0 : r2.tail.headD 0 ≠ 0
  · rw [c2, annWitnessW.k_view_ls_len.arm1 _ _ _ _ _ _ _ hl0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B], ConRon.Bridge.CoreStep.refl hok⟩
    rcases ls with _ | ⟨l, ls⟩
    · exact absurd (UInt64.toNat_inj.mp (by simpa using hl2)) hl0
    · rfl
  have hl0 : r2.tail.headD 0 = 0 := Classical.not_not.mp hl0
  rw [c2, annWitnessW.k_view_ls_len.arm2 _ _ _ _ _ _ _ hl0] at hW
  have hls : ls = [] := by rw [hl0] at hl2; exact List.eq_nil_of_length_eq_zero hl2.symm
  subst hls
  simp only [List.length_nil]
  rcases c3 : callW p n "name_missing" [r1.tail.headD 0] m with _ | ⟨r3, m3⟩
  · rw [c3, annWitnessW.k_name_missing.eq_1] at hW; cases hW
  rw [c3, annWitnessW.k_name_missing.arm1] at hW
  obtain ⟨a3, hrun3, hS3, hg3, hlt3⟩ := nameMissing_rel P.nmis P.nr c3 hS hn1
  obtain ⟨xn, hxn⟩ := const_name_den hok.state.wf hv1
  obtain ⟨p3, hm3⟩ := ConRon.Bridge.Inductives.internStrN_run hok.state hxn hrun3
  have k3 := p3.toCore hok
  rw [StateT.run_bind, hrun3, except_ok_bind]
  rcases c4 : callW p n "env_find" [r3.headD 0, vis] m3 with _ | ⟨r4, m4⟩
  · rw [c4, annWitnessW.k_env_find.eq_1] at hW; cases hW
  obtain ⟨hm4, hr4⟩ := irEnvFind P c4
  subst m4
  subst hr4
  have hE := hS3.check.env
  by_cases hf0 : (findRes m3 vis (r3.headD 0)).headD 0 = 0
  · rw [c4, annWitnessW.k_env_find.arm1 _ _ _ _ hf0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a3, ?_, hS3, hg3, by simp [decW0B], k3⟩
    rw [findRes_miss hE hlt3 hf0]; rfl
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hlt3 hf0
  rw [hfind, hci]
  obtain ⟨-, -, -, hlps, hty, htye⟩ := decCV_rd_ci (erRdOK m3) (decCI_cv hci)
  by_cases hte : erRd m3 ((findRes m3 vis (r3.headD 0)).tail.headD 0 + (CI.cv + CV.type)) ≠ D
  · rw [c4, annWitnessW.k_env_find.arm2 _ _ _ _ hf0 hte] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a3, ?_, hS3, hg3, by simp [decW0B], k3⟩
    have : (ci.toConstantVal.type == decE D) = false := by
      rw [htye]; simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hte (decI_inj hty hD e)
    simp only [this, Bool.false_eq_true, ite_false]; rfl
  have hte : erRd m3 ((findRes m3 vis (r3.headD 0)).tail.headD 0 + (CI.cv + CV.type)) = D :=
    Classical.not_not.mp hte
  rw [c4, annWitnessW.k_env_find.arm3 _ _ _ _ hf0 hte] at hW
  generalize erRd m3 ((findRes m3 vis (r3.headD 0)).tail.headD 0 + (CI.cv + CV.lpsLen)) = z at hW hlps
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  refine ⟨ci.toConstantVal.levelParams.length == 0, a3, ?_, hS3, hg3, ?_, k3⟩
  · have : (ci.toConstantVal.type == decE D) = true := by
      rw [htye, hte]; exact beq_self_eq_true _
    simp only [this, ite_true]; rfl
  · rw [hlps]
    by_cases hz : z = 0
    · subst hz; simp [decW0B]
    · have : z.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
      simp [decW0B, hz, this]

end ann

end L.Ind
