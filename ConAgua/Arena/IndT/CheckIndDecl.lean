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
import ConRon.Bridge.Inductives.Install
import ConLeche.Verify.Inductives.BlockShapeInv
import all ConAgua.Arena.IndParts

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
/-- **`check_ind_decl`'s unified model**: the basis names' hit, the parameters' check and the
shape (outside the verdict closure) lifted; `check_basis_block`, `check_shapeless` and
`check_block` through their runs. -/
l_model cidE_spec (p : Prog) (hV : CcvProg p) (P : CidProg p)
  fns [P.cid ↦ cidE]
  specs [callW_spec p n "basis_name_hit", callW_spec p n "ind_params_ok", callW_spec p n "block_shape",
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

local syntax "chase2 " ident ident : tactic
macro_rules
  | `(tactic| chase2 $y $k) => `(tactic| first
      | (obtain ⟨e, -⟩ := AM.pure_ok $y; cases e; exact $k _)
      | (obtain ⟨_, t, -, y'⟩ := AM.bind_ok $y; chase2 y' $k)
      | (split at $y:ident <;> chase2 $y $k))

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
  rcases rs with _ | ⟨⟨cvR0, x1, x2, x3, x4⟩, rs'⟩
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
      (fun a => (⟨a.1.1, a.1.1, a.1.2, a.2⟩ : MemberShape)), ∃ caps, IConstantInfo.indInfo ms.cvT caps ∈ block := by
    intro groups ms hms
    obtain ⟨⟨⟨c, n⟩, g⟩, hx, rfl⟩ := List.mem_map.1 hms
    exact blockSplit_formers_mem block c hsp (List.of_mem_zip (List.of_mem_zip hx).1).1
  chase2 z2 key

/-- The program facts `cid_ref` takes beyond `CidProg`: the basis entry points' refinements
(`basis_name_hit`), the core's write set and the level cache (`block_shape`'s refinement). -/
structure CidProg2 (p : Prog) : Prop extends CidProg p where
  bref : BasisRefs p
  hcl : CoreStageClosed p
  hL : LvlCacheProg p

section sims
variable {p : Prog} (hV : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
  (hcrf : CrfF p)

include hV hq hap hkp hcrf in
/-- **`check_ind_decl` refines the `.indDecl` arm of `checkDecl`, both outcomes** under `StageT`
and the twin's fold invariant: `basis_name_hit` (`BasisRefs.nameHit`; con-ron's
`basisNameHit_run`), then the pinned block (`check_basis_block`, its contract `CbbRef`) or
`ind_params_ok` (con-ron's `indParamsOk_spec`: the state kept), `block_shape`
(`blockShape_refinesC` under `StageC`; con-ron's `blockShape?_installS`: a `PStep`), then
`check_block` (its contract `BlockRefS`) or `check_shapeless` (`csl_ref`: it never returns).
The memos across `basis_name_hit` and `block_shape` by their write set (`armMemos_call`). -/
theorem cid_ref (P : CidProg2 p) {G : Prop} (hGU : G → VerdictCtxU p)
    {dn : NIdx → Option ConLeche.Name} (hCS : CcvSims p dn) (hcb : CbbRef p dn)
    (hbr : BlockRefS G p dn) {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1) {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {o l w : Word} {block : List IConstantInfo} {pins : List INatOpPinSet}
    {env : ConLeche.Env} (hT : StageT dn vis fe m a) (hfold : ConRon.Bridge.FoldOK env fe a)
    (hdec : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hlpd : BlockLpsDn dn block) :
    RefE G (cidE p N m vis o l w) (checkDecl V pins fe (.indDecl block w.toNat)) a
      (fun v x a' => CidPost dn m v.1 x v.2 a') := by
  have hS := hT.stage
  have hCM : CoreMemos m := hT.twin.memos
  have hok : ConRon.Bridge.StateOK a := hfold.check.state
  have hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block := decB_decEBlk_of_decCIs hdec
  obtain ⟨blockP, hbP⟩ : ∃ blockP, Frontend.denoteCIList a.store block = some blockP := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨b, hb, -⟩ := hx
    exact ⟨b, hb⟩
  rcases N with _ | n
  · rw [cidE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cidE.arm1]
  unfold checkDecl
  dsimp only
  -- `basis_name_hit`
  refine RefE.bindLift (fun _ => cidE.k_basis_name_hit.none ..) fun r1 m1 c1 => ?_
  obtain ⟨x, a1, hrun1, hT1, hg1, hx⟩ := P.bref.nameHit dn vis fe o l block n m a r1 m1
    ⟨hT, hok, hfold.check.readOK, ⟨hdec, hb⟩, blockP, hbP⟩ c1
  refine ⟨_, _, hrun1, ?_⟩
  obtain ⟨hst1, hxt1, hp1, hc1, -, -, -⟩ := ConRon.Bridge.basisNameHit_run hok hbP hrun1
  have hchk1 := hfold.check.mono hst1 hxt1 hc1 hp1
  obtain ⟨hIM1, hCM1⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) c1 hM hCM
  have hA1 : AbsOK m1 := hT1.absOK hIM1.i1 (L.Stubs.CrOK.crMemo hIM1.cr)
  have hC1 : StageC dn vis fe env m1 a1 := StageC.ofStageT hT1 hchk1
  have hbP1 := ConRon.Bridge.denoteCIList_mono hxt1 _ _ hbP
  have hBA1 : BlockAt o l block m1 := blockAt_grow ⟨hdec, hb⟩ hg1
  have hblk1 := hblk.grow (decEBlk_mono _ _ _) hg1
  cases x with
  | some kind =>
    obtain ⟨hz, hk4, hkind⟩ := hx
    rw [cidE.k_basis_name_hit.arm1 _ _ _ _ _ _ _ _ (by rw [hz]; decide)]
    dsimp only
    rw [← hkind, ← bind_pure (checkBasisBlock _ _ _)]
    refine RefE.bindE (fun _ => cidE.k_check_basis_block.none ..) (fun hG => (hGU hG).nv)
      (hcb n vis _ o l fe env m1 a1 block _ hk4 hC1 hBA1 hbP1 hIM1 hA1) fun v y a2 _ hR => ?_
    rw [cidE.k_check_basis_block.arm1]
    exact RefE.ret rfl (hR.pre hg1)
  | none =>
  replace hx : r1.headD 0 = 0 := hx
  rw [cidE.k_basis_name_hit.arm2 _ _ _ _ _ _ _ _ (by simpa using hx)]
  dsimp only
  have hS1 := hT1.stage
  have hbE : o.toNat + l.toNat < 2 ^ 64 := by
    have := hS1.iw.er; have := hS1.iw.erSize; have := hBA1.2; omega
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
      fun _ _ => ?_)
  -- `block_shape`
  refine RefE.bindLift (fun _ => cidE.k_block_shape.none ..) fun r4 m4 c4 => ?_
  obtain ⟨s4, hs4, -, hok4, hR4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockShape_refinesC p P.hcl P.hL P.parts n ⟨m1, Locals.init []⟩ a1 w o l block hC1 hA1 hbP1 hblk1)
    (callW_mono c4 (by omega))
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  refine ⟨_, _, hrun4, ?_⟩
  generalize AM.res (ConRon.Arena.blockShape? w.toNat block) a1 = x4 at hrun4 hR4 ⊢
  generalize AM.st (ConRon.Arena.blockShape? w.toNat block) a1 = a4 at hrun4 hS4 ⊢
  obtain ⟨hps4, -, hq4⟩ := ConRon.Bridge.Inductives.blockShape?_installS hchk1 hbP1 hrun4
  have hchk4 : ConRon.Bridge.CheckOK false env fe a4 :=
    ⟨hps4.ok, hchk1.caches.monoF hps4.ext hps4.cframe, hchk1.pins.mono hps4.ext hps4.pins,
      hchk1.ienv.mono hps4.ext⟩
  have hf4 := hfC "block_shape" (by simp [cidFrameCallees])
  obtain ⟨hIM4, -⟩ := armMemos_call hclC hf4 c4 hIM1 hCM1
  have hA4 : AbsOK s4.mem :=
    (CidMemos.call hclC hf4 c4 ⟨hIM1.stage.pos, hIM1.stage.ma, hA1, hIM1.stage.ta⟩).2.2.1
  have hC4 : StageC dn vis fe env s4.mem a4 := StageC.of_check hC1 hS4 hA4 hchk4 hps4.ext
  have hbP4 := ConRon.Bridge.denoteCIList_mono hps4.ext _ _ hbP1
  have hblk4 := hblk1.grow (decEBlk_mono _ _ _) hg4
  have hb4 : o.toNat + l.toNat ≤ erTop s4.mem := Nat.le_trans hBA1.2 hg4.er
  cases x4 with
  | none =>
    have z4 : r4.headD 0 = 0 := hR4
    rw [cidE.k_block_shape.arm2 _ _ _ _ _ _ _ z4]
    have h5 := csl_ref hV hq hap hkp hcrf hCS hfold.envWF n (by omega) s4.mem a4 hC4.stageT hchk4
      hblk4 hIM4.cr ⟨_, hbP4⟩ hb4
    exact RefE.lastE (f := fun v => (0, v.2)) (fun _ => cidE.k_check_shapeless.none ..)
      (fun ⟨_, _⟩ => cidE.k_check_shapeless.arm1 ..) hGU h5 fun _ _ _ _ h => h.elim
  | some bs =>
  obtain ⟨hr41, hq4', hsl4⟩ := hR4
  simp only [ConRon.Bridge.Inductives.ROp] at hq4
  obtain ⟨bsP, hpP, hdP⟩ := hq4
  rw [cidE.k_block_shape.arm1 _ _ _ _ _ _ _ (by rw [hr41]; decide)]
  dsimp only
  rw [← bind_pure (ConRon.Arena.checkBlock _ _ _ _)]
  refine RefE.bindE (fun _ => cidE.k_check_basis_block.none ..) id
    (hbr n (by omega) vis o l _ fe env s4.mem a4 a bs bsP block blockP hC4 hfold
      (hxt1.trans hps4.ext) (by rw [hps4.pins, hp1]) hq4' hsl4 hblk4 hb4 hbP4 hdP
      (ConLeche.blockShape?_declared hpP) hlpd hIM4 hA4) fun v y a5 _ hR => ?_
  rw [cidE.k_check_basis_block.arm1]
  exact RefE.ret rfl ((hR.pre hg4).pre hg1)

include hV hq hap hkp hcrf in
/-- **`check_ind_decl` refines the `.indDecl` arm of `checkDecl`** under `StageT` and the twin's
fold invariant: the ok half of `cid_ref`, from the call's run. -/
@[refines_part ConRon.Arena.checkDecl "the inductive arm (check_ind_decl), under StageT"]
theorem checkIndDecl_refinesC (P : CidProg2 p) {G : Prop} (hGU : G → VerdictCtxU p)
    {dn : NIdx → Option ConLeche.Name} (hCS : CcvSims p dn) (hcb : CbbRef p dn)
    (hbr : BlockRefS G p dn) {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    {n : Nat} (hn : n ≤ 2 ^ 62) {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {o l w : Word} {r : List Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet} {env : ConLeche.Env}
    (h : callW p n "check_ind_decl" [vis, o, l, w] m = some (r, m')) (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK env fe a)
    (hdec : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hlpd : BlockLpsDn dn block) :
    ∃ fe' a', (checkDecl V pins fe (.indDecl block w.toNat)).run a = .ok (fe', a') ∧
      StageR (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m' := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (cidE_spec p hV P.toCidProg n _ vis o l w)
    (cid_ref hV hq hap hkp hcrf P hGU hCS hcb hbr hclC hfC (N := n) (by omega) hT hfold hdec hb hden hM
      hlpd) h
  exact ⟨x, a', hrun, hR.stage, hR.core, hR.grow, hR.ind⟩

end sims

end L.Ind

end
