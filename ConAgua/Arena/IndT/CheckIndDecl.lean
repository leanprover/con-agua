module

public import ConAgua.Arena.IndRealPartsC2
public import ConAgua.Arena.IndT.Block
public import ConAgua.Arena.IndArmLps
public import ConAgua.Arena.IndRealIpo
public import ConAgua.Arena.IndInstallSpec.ShapeCVOfDecB
public import ConAgua.Arena.IndT.Shapeless
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.IndRealAbsT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndT.Tail
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Promote.WalkDecl

@[expose] public section

/-!
# `check_ind_decl` under `StageC` (lane `indstaget`)

`check_ind_decl`'s unified model `cidE` and its refinement `cid_ref` (both outcomes) from `StageT`
and the twin's fold invariant (`FoldOK`: `CheckOK`, the environment's coherence and denotation);
`checkIndDecl_refinesC` is its ok half (`IndArm.lean` composes it into `IndArmSpec`), the error
half the inductive arm's claim (`indArmSpecE_of`, `Verdict/IndArmTopE.lean`). Its `G` is `CtsG`.
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

open ConRon.Bridge (AM.bind_ok AM.pure_ok)

set_option experimental.vcgen true in
/-- **`check_ind_decl`'s unified model**: the basis pin, the parameters' check and the parts
(outside the verdict closure) lifted; `check_basis_decl`, `check_shapeless` and `check_block`
through their runs. -/
l_model cidE_spec (p : Prog) (hV : ValProg p) (P : CidProg p)
  fns [P.cid ↦ cidE]
  specs [callW_spec p n "basis_pin_hit", callW_spec p n "ind_params_ok", callW_spec p n "block_parts",
    cslE_spec p hV P.csf P.csl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- A former of `blockSplit`'s split is an `indInfo` of the block. -/
theorem blockSplit_formers_mem : ∀ (block : List IConstantInfo) {cvTs cs rs} (cv : IConstantVal),
    ConRon.Arena.blockSplit block = some (cvTs, cs, rs) → cv ∈ cvTs → ∃ caps, IConstantInfo.indInfo cv caps ∈ block
  | [], cvTs, cs, rs, cv, h, hm => by
    simp only [ConRon.Arena.blockSplit] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hm
    · cases h
  | ci :: rest, cvTs, cs, rs, cv, h, hm => by
    cases ci with
    | indInfo cvT caps =>
      simp only [ConRon.Arena.blockSplit] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rcases List.mem_cons.1 hm with rfl | hm
        · exact ⟨caps, List.mem_cons_self ..⟩
        · obtain ⟨caps', h'⟩ := blockSplit_formers_mem rest cv (show ConRon.Arena.blockSplit rest = some (q.1, q.2.1, q.2.2) from hq) hm
          exact ⟨caps', List.mem_cons_of_mem _ h'⟩
      · cases h
    | _ =>
      simp only [ConRon.Arena.blockSplit] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hm
      · cases h

local syntax "chase " ident ident ident : tactic
macro_rules
  | `(tactic| chase $y $k $g) => `(tactic| first
      | (obtain ⟨e, -⟩ := AM.pure_ok $y; cases e; exact $k _)
      | (obtain ⟨_, t, -, y'⟩ := AM.bind_ok $y; chase y' $k $g))

local macro "jp_fin " z:ident k:ident : tactic => `(tactic| (
  obtain ⟨_, t1, -, y1⟩ := AM.bind_ok $z
  obtain ⟨_, t2, -, y2⟩ := AM.bind_ok y1
  obtain ⟨_, t3, -, y3⟩ := AM.bind_ok y2
  obtain ⟨groups, t4, -, y4⟩ := AM.bind_ok y3
  split at y4 <;> chase y4 $k groups))

theorem blockShape?_members_mem {nPd : Nat} {block : List IConstantInfo} {s s' : AState}
    {bs : BlockShape} (h : ConRon.Arena.blockShape? nPd block s = .ok (some bs, s')) :
    ∀ ms ∈ bs.members, ∃ caps, IConstantInfo.indInfo ms.cvT caps ∈ block := by
  unfold ConRon.Arena.blockShape? at h
  cases hsp : ConRon.Arena.blockSplit block with
  | none => rw [hsp] at h; cases (AM.pure_ok h).1
  | some q =>
  obtain ⟨cvTs, cs, rs⟩ := q
  rw [hsp] at h
  rcases cvTs with _ | ⟨cvT0, cvTs'⟩
  · cases (AM.pure_ok h).1
  rcases rs with _ | ⟨⟨cvR0, mI0, rP0, rules0⟩, rs'⟩
  · cases (AM.pure_ok h).1
  dsimp only at h
  obtain ⟨cnt, s1, -, z1⟩ := AM.bind_ok h
  cases cnt with
  | none => cases (AM.pure_ok z1).1
  | some nIdxs =>
  dsimp only at z1
  obtain ⟨reserved, s2, -, z2⟩ := AM.bind_ok z1
  split at z2
  case isFalse => cases (AM.pure_ok z2).1
  have key : ∀ groups : List (List (IConstantVal × Nat)), ∀ ms ∈ (((cvT0 :: cvTs').zip nIdxs).zip groups).map
      (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape)), ∃ caps, IConstantInfo.indInfo ms.cvT caps ∈ block := by
    intro groups ms hms
    obtain ⟨⟨⟨c, n⟩, g⟩, hx, rfl⟩ := List.mem_map.1 hms
    exact blockSplit_formers_mem block c hsp (List.of_mem_zip (List.of_mem_zip hx).1).1
  obtain ⟨o, s3, -, z3⟩ := AM.bind_ok z2
  split at z3
  · obtain ⟨v, s4, -, z4⟩ := AM.bind_ok z3
    split at z4
    · jp_fin z4 key
    · obtain ⟨_, s5, -, z5⟩ := AM.bind_ok z4
      jp_fin z5 key
  · obtain ⟨_, s5, -, z5⟩ := AM.bind_ok z3
    jp_fin z5 key

/-- **The shape `blockParts?` recognises has the block's formers as its members' formers.** -/
theorem blockParts?_members_mem {nPd : Nat} {block : List IConstantInfo} {s s' : AState}
    {bs : BlockShape} (h : (ConRon.Arena.blockParts? nPd block).run s = .ok (some ⟨bs⟩, s')) :
    ∀ ms ∈ bs.members, ∃ caps, IConstantInfo.indInfo ms.cvT caps ∈ block := by
  obtain ⟨o, s1, h1, h2⟩ := AM.bind_ok h
  cases o with
  | none => cases (AM.pure_ok h2).1
  | some p =>
    obtain ⟨e, -⟩ := AM.pure_ok h2
    cases e
    exact blockShape?_members_mem h1

/-- `BlockLpsDn` at the members of the shape `blockParts?` recognises. -/
theorem BlockLpsDn.members {dn : NIdx → Option ConLeche.Name} {block : List IConstantInfo}
    (hl : BlockLpsDn dn block) {nPd : Nat} {s s' : AState} {bs : BlockShape}
    (h : (ConRon.Arena.blockParts? nPd block).run s = .ok (some ⟨bs⟩, s')) :
    ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome := fun ms hms => by
  obtain ⟨caps, hm⟩ := blockParts?_members_mem h ms hms
  exact hl ms.cvT caps hm

/-- What `check_ind_decl` gives besides the twin's run, a view `w` and the memory `m'` (from `m`):
the stage, the core's memos, the growth, the inductive arm's memos. -/
structure CidPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (w : Word) (x : IFEnv) (m' : Mem)
    (a' : AState) : Prop where
  stage : StageR dn w x m' a'
  core : CoreMemos m'
  grow : IWGrow m m'
  ind : IndMemos m'

section sims
variable {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_ind_decl` refines the `.indDecl` arm of `checkDecl`, both outcomes** under `StageT` and
the twin's fold invariant (`FoldOK`; the inner stages under `StageC`): `basis_pin_hit` (con-ron's
`basisPinHit_run`: a `PStep`), `check_basis_decl` (its refinement `cbd_ref` on the run, both
outcomes), `ind_params_ok` and `block_parts` (con-ron's `indParamsOk_spec`, `blockParts?_spec`:
`CheckOK` at `block_parts`' state, the shape's denotation), then `check_shapeless` (`csl_ref`: it
never returns) or `check_block` (`block_ref` on the run). -/
theorem cid_ref (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {o l w : Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet}
    {env : ConLeche.Env}
    (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hfB : "check_basis_decl" ∈ fsC) (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    {fsH fsM fsMc : List FnName} (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hclMc : closedA p mcFreeA mcFreeC fsMc = true) (hfMc : "check_block" ∈ fsMc)
    (hlpd : BlockLpsDn dn block) :
    RefE (CtsG p) (cidE p N m vis o l w) (checkDecl V pins fe (.indDecl block w.toNat)) a
      (fun v x a' => CidPost dn m v.1 x v.2 a') := by
  have hS := hT.stage
  have hIM := hM
  have hCM : CoreMemos m := hT.twin.memos
  replace hM : CidMemos m := ⟨hIM.stage.pos, hIM.stage.ma,
    hT.absOK hIM.i1 (L.Stubs.CrOK.crMemo hIM.cr), hIM.stage.ta⟩
  have hok : ConRon.Bridge.StateOK a := hfold.check.state
  obtain ⟨blockP, hbP⟩ : ∃ blockP, Frontend.denoteCIList a.store block = some blockP := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨b, hb, -⟩ := hx
    exact ⟨b, hb⟩
  have dnE : ∀ {st : ConRon.Arena.EStore}, ConRon.Arena.Ext a.store st →
      ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN st.ns k = some x :=
    fun hx k x e => hx.lss.ls.ns k x (hT.twin.mem.dnN k x e)
  rcases N with _ | n
  · rw [cidE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cidE.arm1]
  unfold checkDecl
  dsimp only
  -- `basis_pin_hit`
  refine RefE.bindLift (fun _ => cidE.k_basis_pin_hit.none ..) fun r1 m1 c1 => ?_
  obtain ⟨x, a1, hrun1, hS1, hg1, hx⟩ := basisPinHit_ok P.bph n dn vis fe m m1 a o l block r1 hS hok hblk c1
  refine ⟨_, _, hrun1, ?_⟩
  have hM1 := hM.call hclC (hfC _ (by simp [cidFrameCallees])) c1
  obtain ⟨hIM1, hCM1⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) c1 hIM hCM
  obtain ⟨ok1, x1, hc1, hp1, -⟩ := ConRon.Bridge.basisPinHit_run hok hbP hrun1
  have k1 := (ConRon.Bridge.Inductives.PStep.of_caches ok1 x1 hc1 hp1).toCore hfold.check
  have hblk1 := hblk.grow (decEBlk_mono _ _ _) hg1
  cases x with
  | some kind =>
    obtain ⟨hz, hk4, hkind⟩ := hx
    rw [cidE.k_basis_pin_hit.arm1 _ _ _ _ _ _ _ _ hz]
    dsimp only
    rw [← hkind]
    rw [← bind_pure (checkBasisDecl _ _)]
    refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => cidE.k_check_basis_decl.none ..)
      (checkBasisDecl_specE p P.basis P.pa P.cbd n _ vis _) (fun hG => hG.nv) (fun _ => trivial)
      (cbd_ref P.basis P.canon P.rom hdn n (by omega) hS1 (fun e => absurd hk4 (by rw [e]; decide)))
      fun r2 s2 _ _ c2 _ _ hR2 => ?_
    rw [cidE.k_check_basis_decl.arm1]
    obtain ⟨hIM2, hCM2⟩ := armMemos_call hclC hfB (callW_of_callE c2) hIM1 hCM1
    exact RefE.ret rfl ⟨by simpa using hR2.stage, hCM2, hg1.trans hR2.grow, hIM2⟩
  | none =>
  replace hx : r1.headD 0 = 0 := hx
  rw [cidE.k_basis_pin_hit.arm2 _ _ _ _ _ _ _ _ hx]
  dsimp only
  have hbE : o.toNat + l.toNat < 2 ^ 64 := by
    have := hS.iw.er; have := hS.iw.erSize; omega
  -- `ind_params_ok`
  refine RefE.bindLift (fun _ => cidE.k_ind_params_ok.none ..) fun r3 m3 c3 => ?_
  obtain ⟨s3, hs3, -, hm3, hok3, hst3, hres3, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (indParamsOk_refines p P.ps P.ev P.ipo n ⟨m1, Locals.init []⟩ a1 dn vis fe w o l block hS1 hblk1 hbE)
    (callW_mono c3 (Nat.le_succ n))
  simp only at hm3
  rw [hm3] at hs3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hst3] at hrun3
  refine ⟨_, _, hrun3, ?_⟩
  refine RefE.ofArms (fun h => cidE.k_ind_params_ok.abort1 (hc1 := h) ..) (fun h => cidE.k_ind_params_ok.arm1 (hc1 := h) ..)
    (RefE.guardThen (by decide) (fun h => by rw [← hres3, h]; rfl) (fun h => by rw [← hres3] at h; simpa using h)
      fun _ hb3 => ?_)
  have hpo3 : AM.res (indParamsOk w.toNat block) a1 = true := by simpa using hb3
  obtain ⟨st3, -⟩ := ConRon.Bridge.Inductives.indParamsOk_spec w.toNat block blockP a1 a1 _ k1.ok.state
    (ConRon.Bridge.denoteCIList_mono k1.ext _ _ hbP) (by rw [hpo3] at hrun3; exact hrun3)
  -- `block_parts`
  refine RefE.bindLift (fun _ => cidE.k_block_parts.none ..) fun r4 m4 c4 => ?_
  obtain ⟨s4, hs4, -, hok4, hR4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockParts_refinesC p hkp.closed hLC P.parts n ⟨m1, Locals.init []⟩ a1 w o l block
      (StageC.of_parts hS1 k1.ok hM1.2.2.1 (dnE k1.ext)) hM1.2.2.1
      (ConRon.Bridge.denoteCIList_mono k1.ext _ _ hbP) hblk1)
    (callW_mono c4 (by omega))
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  refine ⟨_, _, hrun4, ?_⟩
  have hM4 := hM1.call hclC (hfC _ (by simp [cidFrameCallees])) c4
  obtain ⟨hIM4, -⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) c4 hIM1 hCM1
  generalize AM.res (blockParts? w.toNat block) a1 = bp at hrun4 hR4 ⊢
  generalize AM.st (blockParts? w.toNat block) a1 = a4 at hrun4 hS4 ⊢
  have x01 := k1.ext
  obtain ⟨k4, hr4⟩ := ConRon.Bridge.Inductives.blockParts?_spec fe w.toNat block blockP a1 a4 bp k1.ok
    (ConRon.Bridge.denoteCIList_mono x01 _ _ hbP) hrun4
  have hC4 := StageC.of_parts hS4 k4.ok hM4.2.2.1 (dnE (x01.trans k4.ext))
  cases bp with
  | none =>
    have z4 : r4.headD 0 = 0 := hR4
    rw [cidE.k_block_parts.arm2 _ _ _ _ _ _ _ z4]
    have h5 := csl_ref hkp hApd hCrk n (by omega) s4.mem a4 hC4.stageT
      (hblk1.grow (decEBlk_mono _ _ _) hg4) hIM4.cr hlpd (Nat.le_trans hb (hg1.trans hg4).er)
    rcases c5 : cslE p n s4.mem vis o l with e5 | ⟨r5, m5⟩ <;> rw [c5] at h5
    · rw [cidE.k_check_shapeless.none]
      exact fun hG => h5 hG.toVerdictCtxU
    obtain ⟨_, _, _, ⟨⟩⟩ := h5
  | some bp =>
  obtain ⟨hr41, hd4, hsl4⟩ := hR4
  obtain ⟨bs⟩ := bp
  have hq4 : DecB (fun m => decBS m (r4.tail.headD 0).toNat) s4.mem bs := by
    have hd : decBP (truncM s4.mem) (r4.tail.headD 0).toNat = some ⟨bs⟩ := hd4
    simp only [decBP, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
    obtain ⟨bs', hbs', e⟩ := hd
    cases e
    exact hbs'
  obtain ⟨hP4, hma4, hA4, hta4⟩ := hM4
  simp only [ConRon.Bridge.Inductives.ROp] at hr4
  obtain ⟨bpP, -, hpP4⟩ := hr4
  obtain ⟨shP, hshP, -⟩ : ∃ shP, ConRon.Bridge.Inductives.dShape a4.store bs = some shP ∧ bpP = ⟨shP⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, Option.map_eq_some_iff] at hpP4
    obtain ⟨shP, h1, h2⟩ := hpP4
    exact ⟨shP, h1, h2.symm⟩
  have z4 : r4.headD 0 ≠ 0 := by rw [hr41]; decide
  rw [cidE.k_block_parts.arm1 _ _ _ _ _ _ _ z4]
  -- `check_block`
  have hT5 := icbE_spec p P.cb n ⟨s4.mem, Locals.init []⟩ vis o l (r4.tail.headD 0)
  have hR5 := block_ref hkp hfold.envWF hV hOpf hLC hLT hApd hCrk hIlpf hLz P.cb hcl hfs hfr hcl2 hfs2 hclR hfR
    hclT hfT n (by omega) hC4 hq4 hsl4.1 (shapeCV_of_decB hq4) (hblk1.grow (decEBlk_mono _ _ _) hg4) hP4 hma4
    hA4 hkP hkt hkr hta4 hsl4.2 hfold.coh (ConRon.Bridge.denoteFEnv_mono (x01.trans k4.ext) hfold.denote) hshP
    (ConRon.Bridge.denoteCIList_mono (x01.trans k4.ext) _ _ hbP) hfRc hclH hfH hclM hfM (hlpd.members hrun4)
  dsimp only
  rw [← bind_pure (ConRon.Arena.checkBlock _ _ _ _)]
  refine RefE.bindRun (s₀ := ⟨s4.mem, Locals.init []⟩) (fun _ => cidE.k_check_basis_decl.none ..) hT5
    (fun hG => hG.nv) id hR5 fun r5 s5 _ _ c5 _ _ hR5' => ?_
  rw [cidE.k_check_basis_decl.arm1]
  have hmc5 := mcMR.ofClosed hclMc hfMc (callW_of_callE c5) hIM4.stage.mc
  have hA5 := hR5'.abs
  have hCM5 : CoreMemos s5.mem := ⟨hA5.il, hA5.ab, hA5.wk.1⟩
  obtain ⟨mp5, hma5⟩ := hR5'.ma
  exact RefE.ret rfl ⟨hR5'.stage, hCM5, hg1.trans (hg4.trans hR5'.grow),
    ⟨⟨hR5'.rc.pos, ⟨mp5, hma5⟩, hmc5, hR5'.rc.ta⟩, hA5.i1, hA5.cr.crOK⟩⟩

include hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_ind_decl` refines the `.indDecl` arm of `checkDecl`** under `StageT` and the twin's
fold invariant: the ok half of `cid_ref`, from the call's run. -/
@[refines_part ConRon.Arena.checkDecl "the inductive arm (check_ind_decl), under StageC"]
theorem checkIndDecl_refinesC (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    {n : Nat} (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {o l w : Word} {r : List Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet}
    {env : ConLeche.Env}
    (h : callW p n "check_ind_decl" [vis, o, l, w] m = some (r, m')) (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hfB : "check_basis_decl" ∈ fsC) (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    {fsH fsM fsMc : List FnName} (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hclMc : closedA p mcFreeA mcFreeC fsMc = true) (hfMc : "check_block" ∈ fsMc)
    (hlpd : BlockLpsDn dn block) :
    ∃ fe' a', (checkDecl V pins fe (.indDecl block w.toNat)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m' := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (cidE_spec p hV P n _ vis o l w)
    (cid_ref hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hclC hfC hkP hkt
      hkr (N := n) (by omega) hdn hT hfold hblk hb hden hM hfB hfRc hclH hfH hclM hfM hclMc hfMc hlpd) h
  exact ⟨x, a', hrun, hR.stage, hR.core, hR.grow, hR.ind⟩

end sims

end L.Ind

end
