module

public import ConAgua.Arena.IotaRelRefN
public import ConAgua.Arena.IndPosSpec.NtyLook
public import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.RecLayout.CIDec
public import ConAgua.Arena.DeclCanonLvl
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
  lvn : p.lookup "lv_node" = some lvNode
  aiv : p.lookup "ann_ident_val" = some annIdentValL
  ai : p.lookup "ann_ident" = some annIdentL
  aeq : p.lookup "ann_eq" = some annEqL
  lle : p.lookup "list_lvl_eq" = some listLvlEqL
  lae : p.lookup "list_ann_eq" = some listAnnEqL
  pae : p.lookup "params_ann_eq" = some paramsAnnEqL
  ipr : p.lookup "iota_parts_rel" = some iotaPartsRelL
  sleq : p.lookup "sl_eq" = some slEq
  strip : StripProg p

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
    simp only [decide_true, ite_true]
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
  simp only [decide_true, ite_true]
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

/-- **`ann_ident_val(vis, lpsO, lpsL, arity, v)` refines `annIdentVal feR lps arity v`** (the level
parameters the `EREC` slice `(lpsO, lpsL)`). -/
theorem annIdentVal_rel (P : IotaRelProg p) {n : Nat} {m m' : Mem} {a : AState}
    {lo ll ar v : Word} {r : List Word} {lps : List NIdx}
    (hc : callW p n "ann_ident_val" [vis, lo, ll, ar, v] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a)
    (hl : hslice? (erecP m) lo.toNat ll.toNat = some lps) (hv : HW v) :
    ∃ x a', (annIdentVal feR lps ar.toNat (decE v)).run a = .ok (x, a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (annIdentVal_specW p P.aiv n _ vis lo ll ar v) hc
  rcases n with _ | n
  · rw [annIdentValW.eq_1] at hW; cases hW
  have hR := hS.check.arena.base
  have tb := irTagB v hv
  obtain ⟨hlen, hget⟩ := hslice?_get hl
  have r0 : ∀ {mm : Mem} {x : Bool}, x = false → decW0B mm [0] x := fun h => by subst h; simp [decW0B]
  simp only [annIdentVal, hlen, irNatBeq ll 1 (by decide), show UInt64.ofNat 1 = 1 from rfl]
  by_cases hl1 : ll ≠ 1
  · rw [annIdentValW.arm1 _ _ _ _ _ _ _ _ hl1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [hl1, decide_false, Bool.false_eq_true, ite_false]; rfl
  have hl1 : ll = 1 := Classical.not_not.mp hl1
  simp only [hl1, decide_true, ite_true]
  by_cases ht5 : tagW v ≠ 5
  · rw [annIdentValW.arm2 _ _ _ _ _ _ _ _ hl1 ht5] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [tb ETag.lam 5 rfl (by decide), irOfNat5, ht5, decide_false, Bool.false_eq_true,
      ite_false]; rfl
  have ht5 : tagW v = 5 := Classical.not_not.mp ht5
  rw [annIdentValW.arm3 _ _ _ _ _ _ _ _ hl1 ht5] at hW
  simp only [tb ETag.lam 5 rfl (by decide), irOfNat5, ht5, decide_true, ite_true]
  rcases c1 : callW p n "e_view" [v] m with _ | ⟨r1, m1⟩
  · rw [c1, annIdentValW.k_e_view.none] at hW; cases hW
  obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view P.ev hR c1
  subst m1
  obtain ⟨hty, hb1, hv1'⟩ := irVR_two hr1 (by rw [ht1, ht5]; simp)
  have hv1l : v1 = .lam (decE (r1.tail.headD 0)) (decE (r1.tail.tail.headD 0)) := by
    rcases hv1' with ⟨g, -⟩ | ⟨-, h⟩ | ⟨g, -⟩
    · rw [ht1, ht5] at g; exact absurd g (by decide)
    · exact h
    · rw [ht1, ht5] at g; exact absurd g (by decide)
  subst hv1l
  rw [StateT.run_bind, viewBind_run', ConRon.Bridge.viewBind_of_view hv1 (Or.inl rfl), except_ok_bind]
  dsimp only
  have tt := irTagB _ hty
  by_cases ht2 : tagW (r1.tail.headD 0) ≠ 2
  · rw [c1, annIdentValW.k_e_view.arm1 _ _ _ _ _ _ _ ht2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    simp only [tt ETag.sort 2 rfl (by decide), irOfNat2, ht2, decide_false, Bool.false_eq_true,
      ite_false]; rfl
  have ht2 : tagW (r1.tail.headD 0) = 2 := Classical.not_not.mp ht2
  rw [c1, annIdentValW.k_e_view.arm2 _ _ _ _ _ _ _ ht2] at hW
  simp only [tt ETag.sort 2 rfl (by decide), irOfNat2, ht2, decide_true, ite_true]
  rcases c2 : callW p n "e_view" [r1.tail.headD 0] m with _ | ⟨r2, m2⟩
  · rw [c2, annIdentValW.k_e_view_2.none] at hW; cases hW
  obtain ⟨hm2, v2, hv2, hr2, ht2'⟩ := eView_callW_view P.ev hR c2
  subst m2
  obtain ⟨rfl, hu2⟩ := viewR_sort hr2 (by rw [ht2', ht2])
  rw [c2, annIdentValW.k_e_view_2.arm1] at hW
  have tw : (decE (r1.tail.headD 0)).tag = ETag.sort := by rw [decE_tag _ hty, ht2]; rfl
  rw [StateT.run_bind, viewSort_run', irViewSort tw hv2, except_ok_bind]
  dsimp only
  rcases c3 : callW p n "lv_node" [r2.tail.headD 0] m with _ | ⟨r3, m3⟩
  · rw [c3, annIdentValW.k_lv_node.none] at hW; cases hW
  obtain ⟨s3, hs3, hseq, hne3, hr3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvNode_spec p P.lvn n _ _) c3
  subst hseq
  simp only at hs3 hr3 hne3
  subst m3
  rw [hr3] at hne3
  obtain ⟨lv, hrunL, henc⟩ := lvView hR hu2 hne3
  rw [StateT.run_bind, hrunL, except_ok_bind]
  rw [← hr3] at henc
  cases lv with
  | param q =>
    simp only [lvEnc] at henc
    subst henc
    rw [c3, annIdentValW.k_lv_node.arm2 _ _ _ _ _ _ _ _ rfl] at hW
    simp only [List.tail_cons, List.headD_cons] at hW
    dsimp only
    obtain ⟨w0, hw0, hw0', hg0⟩ := hget 0 (by rw [hl1]; decide)
    have he0 : erRd m lo = w0 := erRd_of lo w0 (by simpa using hw0)
    have hg0' : lps.getD 0 default = decI w0 := by simp [List.getD, hg0]
    rcases c4 : callW p n "ann_ident_body"
      [vis, erRd m lo, q.word.toUInt64, ar, r1.tail.tail.headD 0] m with _ | ⟨r4, m4⟩
    · rw [c4, annIdentValW.k_ann_ident_body.none] at hW; cases hW
    rw [c4, annIdentValW.k_ann_ident_body.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [he0] at c4
    obtain ⟨x4, a4, h4, hS4, hg4, hd4, k4⟩ :=
      annIdentBody_rel P c4 hS hok hw0' (idx_word_lt32 q) hb1
    rw [decI_word] at h4
    exact ⟨x4, a4, by rw [hg0']; exact h4, hS4, hg4, hd4, k4⟩
  | zero | succ _ | max _ _ | imax _ _ =>
    simp only [lvEnc] at henc
    rw [c3, annIdentValW.k_lv_node.arm1 _ _ _ _ _ _ _ _ (by rw [henc]; simp)] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a, rfl, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩

/-- **`ann_ident(vis, n, arity)` refines `annIdent feR n arity`.** -/
theorem annIdent_rel (P : IotaRelProg p) {k : Nat} {m m' : Mem} {a : AState}
    {nw ar : Word} {r : List Word}
    (hc : callW p k "ann_ident" [vis, nw, ar] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a) (hn : HW nw) :
    ∃ x a', (annIdent feR (decI nw) ar.toNat).run a = .ok (x, a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (annIdent_specW p P.ai k _ vis nw ar) hc
  rcases k with _ | k
  · rw [annIdentW.eq_1] at hW; cases hW
  rw [annIdentW.arm1] at hW
  have r0 : ∀ {mm : Mem} {x : Bool}, x = false → decW0B mm [0] x := fun h => by subst h; simp [decW0B]
  rcases c1 : callW p k "env_find" [nw, vis] m with _ | ⟨r1, m1⟩
  · rw [c1, annIdentW.k_env_find.none] at hW; cases hW
  obtain ⟨hm1, hr1⟩ := irEnvFind P c1
  subst m1; subst hr1
  have hE := hS.check.env
  simp only [annIdent]
  by_cases hf0 : (findRes m vis nw).headD 0 = 0
  · rw [c1, annIdentW.k_env_find.arm1 _ _ _ _ _ _ hf0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    rw [findRes_miss hE hn hf0]; rfl
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hn hf0
  rw [hfind, hci]
  have hsp := decCI_splitE hci
  by_cases hk1 : erRd m ((findRes m vis nw).tail.headD 0) ≠ 1
  · rw [c1, annIdentW.k_env_find.arm2 _ _ _ _ _ _ hf0 hk1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, r0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
    have hnd := hsp.2.1 hk1
    cases ci with
    | defnInfo cv v h => exact absurd rfl (hnd cv v h)
    | _ => rfl
  have hk1 : erRd m ((findRes m vis nw).tail.headD 0) = 1 := Classical.not_not.mp hk1
  rw [c1, annIdentW.k_env_find.arm3 _ _ _ _ _ _ hf0 hk1] at hW
  obtain ⟨cv, v, hint, rfl, hcv, hv, hvw⟩ := hsp.1 hk1
  obtain ⟨-, -, hsl, -, -, -⟩ := decCV_rd_ci (erRdOK m) hcv
  dsimp only
  rcases c2 : callW p k "ann_ident_val" [vis, erRd m ((findRes m vis nw).tail.headD 0 + (CI.cv + CV.lpsOff)),
      erRd m ((findRes m vis nw).tail.headD 0 + (CI.cv + CV.lpsLen)), ar,
      erRd m ((findRes m vis nw).tail.headD 0 + CI.defnValue)] m with _ | ⟨r2, m2⟩
  · rw [c2, annIdentW.k_ann_ident_val.none] at hW; cases hW
  rw [c2, annIdentW.k_ann_ident_val.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨x2, a2, h2, hS2, hg2, hd2, k2⟩ := annIdentVal_rel P c2 hS hok hsl hvw
  exact ⟨x2, a2, by rw [hv]; exact h2, hS2, hg2, hd2, k2⟩

/-- `view_ls_len` on a stored list `us` of a constant view: the length word is the twin's. -/
theorem irLsLen (P : IotaRelProg p) {n : Nat} {m m1 : Mem} {a : AState} {us : Word} {r : List Word}
    (hR : ArenaR m a) (hus : HW us) {ls : List ConLeche.Level}
    (hdl : denoteLs a.store.lss (decI us) = some ls)
    (h : callW p n "view_ls_len" [us] m = some (r, m1)) :
    m1 = m ∧ (r.tail.headD 0).toNat = ls.length := by
  obtain ⟨hm, hr⟩ := irViewLsLen P h
  obtain ⟨-, hlen⟩ := lsNode_len hR hus hdl
  exact ⟨hm, by rw [hr]; simpa using hlen⟩

theorem irLen1 {w : Word} {k : Nat} (h : w.toNat = k) :
    (w = 1 ↔ k = 1) := by
  constructor
  · rintro rfl; simp at h; omega
  · intro e; subst e; exact UInt64.toNat_inj.mp (by simp [h])

/-- **`ann_eq(vis, s, c, fu)` refines `annEq feR fu s c`**. -/
theorem annEq_run (P : IotaRelProg p) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (sw cw fu : Word) (r : List Word),
      annEqW p n m vis sw cw fu = some (r, m') → StageR vis feR m a →
      ConRon.Bridge.CheckOK false env fe a → HW sw → HW cw →
      ∃ b a', (annEq feR fu.toNat (decE sw) (decE cw)).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧
        IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a'
  | 0, m, m', a, sw, cw, fu, r, hW, _, _, _, _ => by rw [annEqW.eq_1] at hW; cases hW
  | n + 1, m, m', a, sw, cw, fu, r, hW, hS, hok, hs, hcw => by
    by_cases hf0 : fu = 0
    · rw [annEqW.abort1 _ _ _ _ _ _ _ hf0] at hW; cases hW
    obtain ⟨k, hk⟩ : ∃ k, fu.toNat = k + 1 :=
      ⟨fu.toNat - 1, by have : fu.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h)); omega⟩
    have hk1 : (fu - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have z0 : ∀ {mm : Mem} {x : Bool}, x = false → decW0B mm [0] x := fun h => by subst h; simp [decW0B]
    rw [hk, annEq]
    rw [annEqW.arm1 _ _ _ _ _ _ _ hf0] at hW
    rcases c0 : callW p n "expr_lvl_eq" [sw, cw, CWF] m with _ | ⟨r0, m0⟩
    · rw [c0, annEqW.k_expr_lvl_eq.none] at hW; cases hW
    obtain ⟨b0, a0, h0, hS0, hg0, hd0, k0⟩ := exprLvlEq_rel P.ele P.ev P.lvl c0 hS hok hs hcw
    rw [CWF_eq] at h0
    rw [StateT.run_bind, h0, except_ok_bind]
    by_cases hz0 : r0.headD 0 ≠ 0
    · rw [c0, annEqW.k_expr_lvl_eq.arm1 _ _ _ _ _ _ _ _ hz0] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hb0 : b0 = true := by rw [← hd0.1]; exact bne_iff_ne.mpr hz0
      subst hb0
      exact ⟨true, a0, rfl, hS0, hg0, by simp [decW0B], k0⟩
    have hz0 : r0.headD 0 = 0 := Classical.not_not.mp hz0
    have hb0 : b0 = false := by have := hd0.1; rw [hz0] at this; simpa using this.symm
    subst hb0
    simp only [Bool.false_eq_true, ite_false]
    have hR0 := hS0.check.arena.base
    have tc := irTagB cw hcw
    by_cases hc4 : tagW cw ≠ 4
    · rw [c0, annEqW.k_expr_lvl_eq.arm2 _ _ _ _ _ _ _ _ hz0 hc4] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a0, ?_, hS0, hg0, z0 rfl, k0⟩
      simp only [tc ETag.app 4 rfl (by decide), irOfNat4, hc4, decide_false, Bool.false_eq_true,
        ite_false]; rfl
    have hc4 : tagW cw = 4 := Classical.not_not.mp hc4
    rw [c0, annEqW.k_expr_lvl_eq.arm3 _ _ _ _ _ _ _ _ hz0 hc4] at hW
    simp only [tc ETag.app 4 rfl (by decide), irOfNat4, hc4, decide_true, ite_true]
    -- `c = f x`
    rcases c1 : callW p n "e_view" [cw] m0 with _ | ⟨r1, m1⟩
    · rw [c1, annEqW.k_e_view.none] at hW; cases hW
    obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view P.ev hR0 c1
    subst m1
    obtain ⟨hf1, hx1, hv1'⟩ := irVR_two hr1 (by rw [ht1, hc4]; simp)
    have hv1a : v1 = .app (decE (r1.tail.headD 0)) (decE (r1.tail.tail.headD 0)) := by
      rcases hv1' with ⟨-, h⟩ | ⟨g, -⟩ | ⟨g, -⟩
      · exact h
      · rw [ht1, hc4] at g; exact absurd g (by decide)
      · rw [ht1, hc4] at g; exact absurd g (by decide)
    subst hv1a
    rw [StateT.run_bind, viewApp_run', irViewApp hv1, except_ok_bind]
    dsimp only
    have tf := irTagB _ hf1
    by_cases hf4 : tagW (r1.tail.headD 0) = 4
    · -- `f = g a`, `g` a constant: `optParam`/`autoParam`
      rw [c1, annEqW.k_e_view.arm1 _ _ _ _ _ _ _ hf4] at hW
      simp only [tf ETag.app 4 rfl (by decide), irOfNat4, hf4, decide_true, ite_true]
      rcases c2 : callW p n "e_view" [r1.tail.headD 0] m0 with _ | ⟨r2, m2⟩
      · rw [c2, annEqW.k_e_view_2.none] at hW; cases hW
      obtain ⟨hm2, v2, hv2, hr2, ht2⟩ := eView_callW_view P.ev hR0 c2
      subst m2
      obtain ⟨hg2, ha2, hv2'⟩ := irVR_two hr2 (by rw [ht2, hf4]; simp)
      have hv2a : v2 = .app (decE (r2.tail.headD 0)) (decE (r2.tail.tail.headD 0)) := by
        rcases hv2' with ⟨-, h⟩ | ⟨g, -⟩ | ⟨g, -⟩
        · exact h
        · rw [ht2, hf4] at g; exact absurd g (by decide)
        · rw [ht2, hf4] at g; exact absurd g (by decide)
      subst hv2a
      rw [StateT.run_bind, viewApp_run', irViewApp hv2, except_ok_bind]
      dsimp only
      have tg := irTagB _ hg2
      by_cases hg3 : tagW (r2.tail.headD 0) ≠ 3
      · rw [c2, annEqW.k_e_view_2.arm1 _ _ _ _ _ _ _ hg3] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        refine ⟨false, a0, ?_, hS0, hg0, z0 rfl, k0⟩
        simp only [tg ETag.const 3 rfl (by decide), irOfNat3, hg3, decide_false, Bool.false_eq_true,
          ite_false]; rfl
      have hg3 : tagW (r2.tail.headD 0) = 3 := Classical.not_not.mp hg3
      rw [c2, annEqW.k_e_view_2.arm2 _ _ _ _ _ _ _ hg3] at hW
      simp only [tg ETag.const 3 rfl (by decide), irOfNat3, hg3, decide_true, ite_true]
      rcases c3 : callW p n "e_view" [r2.tail.headD 0] m0 with _ | ⟨r3, m3⟩
      · rw [c3, annEqW.k_e_view_3.none] at hW; cases hW
      obtain ⟨hm3, v3, hv3, hr3, ht3⟩ := eView_callW_view P.ev hR0 c3
      subst m3
      obtain ⟨rfl, hn3, hu3⟩ := irVR_const hr3 (by rw [ht3, hg3])
      rw [c3, annEqW.k_e_view_3.arm1] at hW
      have tw : (decE (r2.tail.headD 0)).tag = ETag.const := by rw [decE_tag _ hg2, hg3]; rfl
      rw [StateT.run_bind, viewConst_run', irViewConst tw hv3, except_ok_bind]
      dsimp only
      obtain ⟨ls, hdl⟩ := const_lvls_den k0.ok.state.wf hv3
      rw [StateT.run_bind, viewLsLen_run', ConRon.Bridge.Core.viewLen_of_denoteLs hdl, except_ok_bind]
      dsimp only
      rcases c4 : callW p n "view_ls_len" [r3.tail.tail.headD 0] m0 with _ | ⟨r4, m4⟩
      · rw [c4, annEqW.k_view_ls_len.none] at hW; cases hW
      obtain ⟨hm4, hl4⟩ := irLsLen P hR0 hu3 hdl c4
      subst m4
      by_cases h1 : r4.tail.headD 0 ≠ 1
      · rw [c4, annEqW.k_view_ls_len.arm1 _ _ _ _ _ _ _ _ _ h1] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        refine ⟨false, a0, ?_, hS0, hg0, z0 rfl, k0⟩
        have : ls.length ≠ 1 := fun e => h1 ((irLen1 hl4).mpr e)
        rcases ls with _ | ⟨l, _ | ⟨l', ls⟩⟩
        · rfl
        · exact absurd rfl this
        · rfl
      have h1 : r4.tail.headD 0 = 1 := Classical.not_not.mp h1
      rw [c4, annEqW.k_view_ls_len.arm2 _ _ _ _ _ _ _ _ _ h1] at hW
      obtain ⟨l, rfl⟩ : ∃ l, ls = [l] := by
        have := (irLen1 hl4).mp h1
        rcases ls with _ | ⟨l, _ | ⟨l', ls⟩⟩ <;> simp at this
        exact ⟨l, rfl⟩
      simp only [List.length_singleton]
      rcases c5 : callW p n "name_opt_param" [] m0 with _ | ⟨r5, m5⟩
      · rw [c5, annEqW.k_name_opt_param.none] at hW; cases hW
      rw [c5, annEqW.k_name_opt_param.arm1] at hW
      obtain ⟨a5, h5, hS5, hg5, hl5⟩ := nameOptParam_rel P.nop P.na P.nr c5 hS0
      obtain ⟨k5, -⟩ := ConRon.Bridge.Inductives.topName_run k0.ok h5
      rw [StateT.run_bind, h5, except_ok_bind]
      rcases c6 : callW p n "name_auto_param" [] m5 with _ | ⟨r6, m6⟩
      · rw [c6, annEqW.k_name_auto_param.none] at hW; cases hW
      obtain ⟨a6, h6, hS6, hg6, hl6⟩ := nameAutoParam_rel P.nap P.na P.nr c6 hS5
      obtain ⟨k6, -⟩ := ConRon.Bridge.Inductives.topName_run k5.ok h6
      rw [StateT.run_bind, h6, except_ok_bind]
      rw [decI_beq _ _ hn3 hl5, decI_beq _ _ hn3 hl6]
      by_cases hno : r3.tail.headD 0 ≠ r5.headD 0 ∧ r3.tail.headD 0 ≠ r6.headD 0
      · rw [c6, annEqW.k_name_auto_param.arm1 _ _ _ _ _ _ _ _ _ _ hno] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        refine ⟨false, a6, ?_, hS6, hg0.trans (hg5.trans hg6), z0 rfl, k0.trans (k5.trans k6)⟩
        simp only [hno.1, hno.2, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]; rfl
      rw [c6, annEqW.k_name_auto_param.arm2 _ _ _ _ _ _ _ _ _ _ hno] at hW
      have hor : (decide (r3.tail.headD 0 = r5.headD 0) || decide (r3.tail.headD 0 = r6.headD 0)) = true := by
        by_cases e : r3.tail.headD 0 = r5.headD 0
        · rw [e]; exact Bool.or_eq_true_iff.mpr (.inl (decide_eq_true rfl))
        · have : r3.tail.headD 0 = r6.headD 0 :=
            Classical.byContradiction fun e' => hno ⟨e, e'⟩
          rw [this]; exact Bool.or_eq_true_iff.mpr (.inr (decide_eq_true rfl))
      simp only [hor, ite_true]
      rcases c7 : callW p n "ann_ident" [vis, r3.tail.headD 0, 2] m6 with _ | ⟨r7, m7⟩
      · rw [c7, annEqW.k_ann_ident.none] at hW; cases hW
      obtain ⟨b7, a7, h7, hS7, hg7, hd7, k7⟩ := annIdent_rel P c7 hS6 k6.ok hn3
      rw [show (2 : Word).toNat = 2 from rfl] at h7
      rw [StateT.run_bind, h7, except_ok_bind]
      by_cases hz7 : r7.headD 0 = 0
      · rw [c7, annEqW.k_ann_ident.arm1 _ _ _ _ _ _ _ _ hz7] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hb7 : b7 = false := by have := hd7.1; rw [hz7] at this; simpa using this.symm
        subst hb7
        exact ⟨false, a7, rfl, hS7, hg0.trans (hg5.trans (hg6.trans hg7)), z0 rfl,
          k0.trans (k5.trans (k6.trans k7))⟩
      rw [c7, annEqW.k_ann_ident.arm2 _ _ _ _ _ _ _ _ hz7] at hW
      have hb7 : b7 = true := by rw [← hd7.1]; exact bne_iff_ne.mpr hz7
      subst hb7
      simp only [ite_true]
      rcases c8 : annEqW p n m7 vis sw (r2.tail.tail.headD 0) (fu - 1) with _ | ⟨r8, m8⟩
      · rw [c8, annEqW.k_ann_eq.none] at hW; cases hW
      rw [c8, annEqW.k_ann_eq.arm1] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨b8, a8, h8, hS8, hg8, hd8, k8⟩ := annEq_run P n _ _ _ _ _ _ _ c8 hS7 k7.ok hs ha2
      rw [hk1] at h8
      exact ⟨b8, a8, h8, hS8, hg0.trans (hg5.trans (hg6.trans (hg7.trans hg8))), hd8,
        k0.trans (k5.trans (k6.trans (k7.trans k8)))⟩
    -- `f` a constant: `outParam`/`semiOutParam`
    simp only [tf ETag.app 4 rfl (by decide), irOfNat4, hf4, decide_false, Bool.false_eq_true, ite_false]
    by_cases hf3 : tagW (r1.tail.headD 0) ≠ 3
    · rw [c1, annEqW.k_e_view.arm3 _ _ _ _ _ _ _ hf4 hf3] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a0, ?_, hS0, hg0, z0 rfl, k0⟩
      simp only [tf ETag.const 3 rfl (by decide), irOfNat3, hf3, decide_false, Bool.false_eq_true,
        ite_false]; rfl
    have hf3 : tagW (r1.tail.headD 0) = 3 := Classical.not_not.mp hf3
    rw [c1, annEqW.k_e_view.arm2 _ _ _ _ _ _ _ hf4 hf3] at hW
    simp only [tf ETag.const 3 rfl (by decide), irOfNat3, hf3, decide_true, ite_true]
    rcases c3 : callW p n "e_view" [r1.tail.headD 0] m0 with _ | ⟨r3, m3⟩
    · rw [c3, annEqW.k_e_view_4.none] at hW; cases hW
    obtain ⟨hm3, v3, hv3, hr3, ht3⟩ := eView_callW_view P.ev hR0 c3
    subst m3
    obtain ⟨rfl, hn3, hu3⟩ := irVR_const hr3 (by rw [ht3, hf3])
    rw [c3, annEqW.k_e_view_4.arm1] at hW
    have tw : (decE (r1.tail.headD 0)).tag = ETag.const := by rw [decE_tag _ hf1, hf3]; rfl
    rw [StateT.run_bind, viewConst_run', irViewConst tw hv3, except_ok_bind]
    dsimp only
    obtain ⟨ls, hdl⟩ := const_lvls_den k0.ok.state.wf hv3
    rw [StateT.run_bind, viewLsLen_run', ConRon.Bridge.Core.viewLen_of_denoteLs hdl, except_ok_bind]
    dsimp only
    rcases c4 : callW p n "view_ls_len" [r3.tail.tail.headD 0] m0 with _ | ⟨r4, m4⟩
    · rw [c4, annEqW.k_view_ls_len_2.none] at hW; cases hW
    obtain ⟨hm4, hl4⟩ := irLsLen P hR0 hu3 hdl c4
    subst m4
    by_cases h1 : r4.tail.headD 0 ≠ 1
    · rw [c4, annEqW.k_view_ls_len_2.arm1 _ _ _ _ _ _ _ _ _ h1] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a0, ?_, hS0, hg0, z0 rfl, k0⟩
      have : ls.length ≠ 1 := fun e => h1 ((irLen1 hl4).mpr e)
      rcases ls with _ | ⟨l, _ | ⟨l', ls⟩⟩
      · rfl
      · exact absurd rfl this
      · rfl
    have h1 : r4.tail.headD 0 = 1 := Classical.not_not.mp h1
    rw [c4, annEqW.k_view_ls_len_2.arm2 _ _ _ _ _ _ _ _ _ h1] at hW
    obtain ⟨l, rfl⟩ : ∃ l, ls = [l] := by
      have := (irLen1 hl4).mp h1
      rcases ls with _ | ⟨l, _ | ⟨l', ls⟩⟩ <;> simp at this
      exact ⟨l, rfl⟩
    simp only [List.length_singleton]
    rcases c5 : callW p n "name_out_param" [] m0 with _ | ⟨r5, m5⟩
    · rw [c5, annEqW.k_name_out_param.none] at hW; cases hW
    rw [c5, annEqW.k_name_out_param.arm1] at hW
    obtain ⟨a5, h5, hS5, hg5, hl5⟩ := nameOutParam_rel P.nout P.na P.nr c5 hS0
    obtain ⟨k5, -⟩ := ConRon.Bridge.Inductives.topName_run k0.ok h5
    rw [StateT.run_bind, h5, except_ok_bind]
    rcases c6 : callW p n "name_semi_out_param" [] m5 with _ | ⟨r6, m6⟩
    · rw [c6, annEqW.k_name_semi_out_param.none] at hW; cases hW
    obtain ⟨a6, h6, hS6, hg6, hl6⟩ := nameSemiOutParam_rel P.nsop P.na P.nr c6 hS5
    obtain ⟨k6, -⟩ := ConRon.Bridge.Inductives.topName_run k5.ok h6
    rw [StateT.run_bind, h6, except_ok_bind]
    rw [decI_beq _ _ hn3 hl5, decI_beq _ _ hn3 hl6]
    by_cases hno : r3.tail.headD 0 ≠ r5.headD 0 ∧ r3.tail.headD 0 ≠ r6.headD 0
    · rw [c6, annEqW.k_name_semi_out_param.arm1 _ _ _ _ _ _ _ _ _ _ hno] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a6, ?_, hS6, hg0.trans (hg5.trans hg6), z0 rfl, k0.trans (k5.trans k6)⟩
      simp only [hno.1, hno.2, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]; rfl
    rw [c6, annEqW.k_name_semi_out_param.arm2 _ _ _ _ _ _ _ _ _ _ hno] at hW
    have hor : (decide (r3.tail.headD 0 = r5.headD 0) || decide (r3.tail.headD 0 = r6.headD 0)) = true := by
      by_cases e : r3.tail.headD 0 = r5.headD 0
      · rw [e]; exact Bool.or_eq_true_iff.mpr (.inl (decide_eq_true rfl))
      · have : r3.tail.headD 0 = r6.headD 0 :=
          Classical.byContradiction fun e' => hno ⟨e, e'⟩
        rw [this]; exact Bool.or_eq_true_iff.mpr (.inr (decide_eq_true rfl))
    simp only [hor, ite_true]
    rcases c7 : callW p n "ann_ident" [vis, r3.tail.headD 0, 1] m6 with _ | ⟨r7, m7⟩
    · rw [c7, annEqW.k_ann_ident_2.none] at hW; cases hW
    obtain ⟨b7, a7, h7, hS7, hg7, hd7, k7⟩ := annIdent_rel P c7 hS6 k6.ok hn3
    rw [show (1 : Word).toNat = 1 from rfl] at h7
    rw [StateT.run_bind, h7, except_ok_bind]
    by_cases hz7 : r7.headD 0 = 0
    · rw [c7, annEqW.k_ann_ident_2.arm1 _ _ _ _ _ _ _ _ hz7] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hb7 : b7 = false := by have := hd7.1; rw [hz7] at this; simpa using this.symm
      subst hb7
      exact ⟨false, a7, rfl, hS7, hg0.trans (hg5.trans (hg6.trans hg7)), z0 rfl,
        k0.trans (k5.trans (k6.trans k7))⟩
    rw [c7, annEqW.k_ann_ident_2.arm2 _ _ _ _ _ _ _ _ hz7] at hW
    have hb7 : b7 = true := by rw [← hd7.1]; exact bne_iff_ne.mpr hz7
    subst hb7
    simp only [ite_true]
    rcases c8 : annEqW p n m7 vis sw (r1.tail.tail.headD 0) (fu - 1) with _ | ⟨r8, m8⟩
    · rw [c8, annEqW.k_ann_eq.none] at hW; cases hW
    rw [c8, annEqW.k_ann_eq.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨b8, a8, h8, hS8, hg8, hd8, k8⟩ := annEq_run P n _ _ _ _ _ _ _ c8 hS7 k7.ok hs hx1
    rw [hk1] at h8
    exact ⟨b8, a8, h8, hS8, hg0.trans (hg5.trans (hg6.trans (hg7.trans hg8))), hd8,
      k0.trans (k5.trans (k6.trans (k7.trans k8)))⟩

/-- **`ann_eq(vis, s, c, fu)` refines `annEq feR fu s c`** (the call). -/
@[refines ConRon.Arena.annEq]
theorem annEq_rel (P : IotaRelProg p) {n : Nat} {m m' : Mem} {a : AState} {sw cw fu : Word}
    {r : List Word} (hc : callW p n "ann_eq" [vis, sw, cw, fu] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a) (hs : HW sw) (hcw : HW cw) :
    ∃ b a', (annEq feR fu.toNat (decE sw) (decE cw)).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧
      IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (annEq_specW p P.aeq n _ vis sw cw fu) hc
  exact annEq_run P n _ _ _ _ _ _ _ hW hS hok hs hcw

end ann

end L.Ind
