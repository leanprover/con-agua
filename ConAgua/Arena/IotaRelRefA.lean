module

public import ConAgua.Arena.IotaRelRefN
public import ConAgua.Arena.IndPosSpec.NtyLook
public import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.RecLayout.CIDec
public import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Inductives.Run

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
  bvf : p.lookup "bvar_find" = some bvarFind
  bvp : p.lookup "bvar_push" = some bvarPush
  ibv : p.lookup "intern_bvar" = some internBVar
  aib : p.lookup "ann_ident_body" = some annIdentBodyL

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

theorem irVR_bvar {r : List Word} {v : ENodeView} (hr : ViewR r v) (h : r.headD 0 = 0) :
    v = .bvar (r.tail.headD 0).toNat := by
  cases v <;> simp only [ViewR, h] at hr <;> (try (exfalso; revert hr; decide)) <;>
    (try (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide))
  obtain ⟨-, h1⟩ := hr
  rw [L.getD_one] at h1; rw [h1]

theorem irNatBeq (w : Word) (k : Nat) (hk : k < 2 ^ 64) :
    (w.toNat == k) = decide (w = UInt64.ofNat k) := by
  by_cases h : w = UInt64.ofNat k
  · subst h; simp; omega
  · have : w.toNat ≠ k := fun e => h (UInt64.toNat_inj.mp (by simp; omega))
    simp [h, this]

theorem decI_beq {k : IdxKind} (x y : Word) (hx : HW x) (hy : HW y) :
    ((decI x : Idx k) == decI y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : (decI x : Idx k) ≠ decI y := fun e => h (decI_inj hx hy e)
    simp [h, this]

/-- **`ann_ident_body(vis, p, p2, arity, b)` refines `annIdentBody feR p p2 arity b`.** -/
theorem annIdentBody_rel (P : IotaRelProg p) {n : Nat} {m m' : Mem} {a : AState}
    {pw p2 ar b : Word} {r : List Word}
    (hc : callW p n "ann_ident_body" [vis, pw, p2, ar, b] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a) (hp : HW pw)
    (hp2 : HW p2) (hb : HW b) :
    ∃ x a', (annIdentBody feR (decI pw) (decI p2) ar.toNat (decE b)).run a = .ok (x, a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (annIdentBody_specW p P.aib n _ vis pw p2 ar b) hc
  rcases n with _ | n
  · rw [annIdentBodyW.eq_1] at hW; cases hW
  have hR := hS.check.arena.base
  have tb := irTagB b hb
  have hpp := decI_beq (k := .name) pw p2 hp hp2
  have r0 : ∀ {mm : Mem} {x : Bool}, x = false →
      decW0B mm [0] x := fun h => by subst h; simp [decW0B]
  simp only [annIdentBody, irNatBeq ar 1 (by decide), irNatBeq ar 2 (by decide),
    show UInt64.ofNat 1 = 1 from rfl, irOfNat2]
  by_cases ha1 : ar = 1
  · subst ha1
    simp only [eq_self_iff_true, decide_true, ite_true]
    by_cases ht0 : tagW b ≠ 0
    · rw [annIdentBodyW.arm1 _ _ _ _ _ _ _ _ rfl ht0] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
      simp only [tb ETag.bvar 0 rfl (by decide), show UInt64.ofNat 0 = 0 from rfl, ht0, decide_false,
        Bool.false_eq_true, ite_false]; rfl
    have ht0 : tagW b = 0 := Classical.not_not.mp ht0
    rw [annIdentBodyW.arm2 _ _ _ _ _ _ _ _ rfl ht0] at hW
    rcases c1 : callW p n "e_view" [b] m with _ | ⟨r1, m1⟩
    · rw [c1, annIdentBodyW.k_e_view.none] at hW; cases hW
    obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view P.ev hR c1
    subst m1
    have hv := irVR_bvar hr1 (by rw [ht1, ht0])
    subst hv
    have tw : (decE b).tag = ETag.bvar := by rw [decE_tag b hb, ht0]; rfl
    simp only [tb ETag.bvar 0 rfl (by decide), show UInt64.ofNat 0 = 0 from rfl, ht0, decide_true,
      ite_true]
    rw [StateT.run_bind, viewBVar_run', irViewBVar tw hv1, except_ok_bind]
    dsimp only
    rw [irNatBeq _ 0 (by decide), show UInt64.ofNat 0 = 0 from rfl]
    by_cases hj : r1.tail.headD 0 ≠ 0
    · rw [c1, annIdentBodyW.k_e_view.arm1 _ _ _ _ _ hj] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
      simp only [hj, decide_false, Bool.false_eq_true, ite_false]; rfl
    have hj : r1.tail.headD 0 = 0 := Classical.not_not.mp hj
    rw [c1, annIdentBodyW.k_e_view.arm2 _ _ _ _ _ hj] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨(decI pw : NIdx) == decI p2, a, ?_, hS, IWGrow.refl _, ?_, ConRon.Bridge.CoreStep.refl hok⟩
    · simp only [hj, decide_true, ite_true]; rfl
    · rw [hpp]; by_cases h : pw = p2 <;> simp [decW0B, h]
  simp only [ha1, decide_false, Bool.false_eq_true, ite_false]
  by_cases ha2 : ar ≠ 2
  · rw [annIdentBodyW.arm5 _ _ _ _ _ _ _ _ ha1 ha2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [ha2, decide_false, Bool.false_eq_true, ite_false]; rfl
  have ha2 : ar = 2 := Classical.not_not.mp ha2
  subst ha2
  simp only [eq_self_iff_true, decide_true, ite_true]
  by_cases ht5 : tagW b ≠ 5
  · rw [annIdentBodyW.arm3 _ _ _ _ _ _ _ _ ha1 rfl ht5] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [tb ETag.lam 5 rfl (by decide), irOfNat5, ht5, decide_false, Bool.false_eq_true,
      ite_false]; rfl
  have ht5 : tagW b = 5 := Classical.not_not.mp ht5
  rw [annIdentBodyW.arm4 _ _ _ _ _ _ _ _ ha1 rfl ht5] at hW
  simp only [tb ETag.lam 5 rfl (by decide), irOfNat5, ht5, decide_true, ite_true]
  rcases c1 : callW p n "e_view" [b] m with _ | ⟨r1, m1⟩
  · rw [c1, annIdentBodyW.k_e_view_2.none] at hW; cases hW
  obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view P.ev hR c1
  subst m1
  obtain ⟨hD1, hc1, hv1'⟩ := irVR_two hr1 (by rw [ht1, ht5]; simp)
  have hv1l : v1 = .lam (decE (r1.tail.headD 0)) (decE (r1.tail.tail.headD 0)) := by
    rcases hv1' with ⟨g, -⟩ | ⟨-, h⟩ | ⟨g, -⟩
    · rw [ht1, ht5] at g; exact absurd g (by decide)
    · exact h
    · rw [ht1, ht5] at g; exact absurd g (by decide)
  subst hv1l
  rw [StateT.run_bind, viewBind_run', ConRon.Bridge.viewBind_of_view hv1 (Or.inl rfl), except_ok_bind]
  dsimp only
  have tc := irTagB _ hc1
  by_cases hc0 : tagW (r1.tail.tail.headD 0) ≠ 0
  · rw [c1, annIdentBodyW.k_e_view_2.arm1 _ _ _ _ _ _ _ hc0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [tc ETag.bvar 0 rfl (by decide), show UInt64.ofNat 0 = 0 from rfl, hc0, decide_false,
      Bool.false_eq_true, ite_false]; rfl
  have hc0 : tagW (r1.tail.tail.headD 0) = 0 := Classical.not_not.mp hc0
  rw [c1, annIdentBodyW.k_e_view_2.arm2 _ _ _ _ _ _ _ hc0] at hW
  simp only [tc ETag.bvar 0 rfl (by decide), show UInt64.ofNat 0 = 0 from rfl, hc0, decide_true,
    ite_true]
  rcases c2 : callW p n "e_view" [r1.tail.tail.headD 0] m with _ | ⟨r2, m2⟩
  · rw [c2, annIdentBodyW.k_e_view_3.none] at hW; cases hW
  obtain ⟨hm2, v2, hv2, hr2, ht2⟩ := eView_callW_view P.ev hR c2
  subst m2
  have hv := irVR_bvar hr2 (by rw [ht2, hc0])
  subst hv
  have tw : (decE (r1.tail.tail.headD 0)).tag = ETag.bvar := by
    rw [decE_tag _ hc1, hc0]; rfl
  rw [StateT.run_bind, viewBVar_run', irViewBVar tw hv2, except_ok_bind]
  dsimp only
  rw [irNatBeq _ 1 (by decide), show UInt64.ofNat 1 = 1 from rfl]
  by_cases hj : r2.tail.headD 0 ≠ 1
  · rw [c2, annIdentBodyW.k_e_view_3.arm1 _ _ _ _ _ _ _ _ hj] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [hj, decide_false, Bool.false_eq_true, ite_false]; rfl
  have hj : r2.tail.headD 0 = 1 := Classical.not_not.mp hj
  simp only [hj, decide_true, ite_true, hpp]
  by_cases hpq : pw ≠ p2
  · rw [c2, annIdentBodyW.k_e_view_3.arm2 _ _ _ _ _ _ _ _ hj hpq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [hpq, decide_false, Bool.false_eq_true, ite_false]; rfl
  have hpq : pw = p2 := Classical.not_not.mp hpq
  rw [c2, annIdentBodyW.k_e_view_3.arm3 _ _ _ _ _ _ _ _ hj hpq] at hW
  simp only [hpq, decide_true, ite_true]
  rcases c3 : callW p n "intern_bvar" [0] m with _ | ⟨r3, m3⟩
  · rw [c3, annIdentBodyW.k_intern_bvar.none] at hW; cases hW
  by_cases hl3 : 4294967296 ≤ r3.headD 0
  · rw [c3, annIdentBodyW.k_intern_bvar.abort1 _ _ _ _ _ _ hl3] at hW; cases hW
  obtain ⟨s3, hs3, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internBVar_spec p P.bvf P.bvp P.ibv n _ 0) c3
  simp only at hs3 hI
  rw [hs3] at hI
  obtain ⟨a3, hrun3, hS3, hg3⟩ := internBVar_stage hS 0 hI
  obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.internBVarE_run hok.state hrun3
  have k3 := p3.toCore hok
  have hz3 : HW (r3.headD 0) := by
    have := mt UInt64.le_iff_toNat_le.mpr hl3
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; unfold HW; omega
  rw [StateT.run_bind, show internBVarE 0 = internE (.bvar (0 : Word).toNat) from rfl, hrun3,
    except_ok_bind]
  rw [decE_beq _ _ hD1 hz3]
  by_cases hDz : r1.tail.headD 0 = r3.headD 0
  · rw [c3, annIdentBodyW.k_intern_bvar.arm1 _ _ _ _ _ _ hl3 hDz] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨true, a3, by simp only [hDz, decide_true, ite_true]; rfl, hS3, hg3, by simp [decW0B], k3⟩
  rw [c3, annIdentBodyW.k_intern_bvar.arm2 _ _ _ _ _ _ hl3 hDz] at hW
  simp only [hDz, decide_false, Bool.false_eq_true, ite_false]
  rcases c4 : callW p n "ann_witness" [vis, r1.tail.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [c4, annIdentBodyW.k_ann_witness.none] at hW; cases hW
  rw [c4, annIdentBodyW.k_ann_witness.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨x4, a4, h4, hS4, hg4, hd4, k4⟩ := annWitness_rel P c4 hS3 k3.ok hD1
  exact ⟨x4, a4, h4, hS4, hg3.trans hg4, hd4, k3.trans k4⟩

end ann

end L.Ind
