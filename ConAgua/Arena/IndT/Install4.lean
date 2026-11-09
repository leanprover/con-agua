module

public import ConAgua.Verdict.IndsE5
public import ConAgua.Arena.IndT.KeepC
public import ConAgua.Arena.IndT.Install3
public import ConAgua.Arena.IndInstallSpec.CbProg
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndDeclConstsFormers
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.BlockInstall
public import ConAgua.Arena.IndInstallSpec.IndsOut
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.Cons
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.Icvg
public import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndMaster
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `check_block_inds`: one model, one refinement

Stage 1 (`check_block_inds`): its unified model (`cbiE`) and its refinement for both outcomes
(`cbi_ref`; `checkBlockInds_refinesC` is its ok half), from `StageC` and con-ron's preconditions of `checkBlockInds_spec`
(the shape denotes, the environment denotes, the index is coherent), its twin side transcribed
from that spec's proof: member 0's former (`cbt_ref`, con-ron's
`checkBlockTele_specF` on its run for the answer's denotation), the other formers
(`cbts_ref`, `checkBlockTeles_specF`), the agreements (`cbag_ref`),
the shape's sort (`BlockShape.withSort_spec`), the formers' constants (L only), the formers consed
(`consBlockInds_spec`). The formers are checked at the ENTRY index, so the frame is the `CoreStep`
at `fe` (con-ron's); the stage relation after is at the returned view (`IndsOut`).
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A callee proved at every positive fuel up to a bound is simulated at every fuel up to it. -/
theorem _root_.L.Arena.Sim.callW_posB {α : Type} {p : Prog} {f : FnName} {args : List Word} {m : Mem} {op : AM α}
    {a : AState} {Q : List Word → α → Mem → AState → Prop} {N : Nat}
    (h : ∀ k, k + 1 ≤ N → Sim (callW p (k + 1) f args m) op a Q) (n : Nat) (hn : n ≤ N) :
    Sim (callW p n f args m) op a Q := by
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k => exact h k hn

/-- `block_shape_with_sort` as a `Sim` under `StageC`, its `lvl_eq_c` the real call
(`installWithSortSim`'s statement; `lvlEqC_simC` for the stub contract). -/
theorem installWithSortSimC {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (hp : p.lookup "block_shape_with_sort" = some blockShapeWithSort) (n : Nat)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {m : Mem}
    {a : AState} {pp s : Word} {bs : BlockShape} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp) (hs : H s)
    {sP : ConLeche.Level} (hsP : denoteL a.store.ls (decI s) = some sP) :
    Sim (callW p n "block_shape_with_sort" [pp, s] m) (bs.withSort (decI s)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decBS m (r.headD 0).toNat) m' x ∧ ShapeSrc m' (r.headD 0) ∧
        (RecsB m pp → RecsB m' (r.headD 0))) := by
  intro r m' e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeWithSort_specC p ha hpw hp (realCall p) (realCall_spec p) n _ pp s) e
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hS := hC.stage
  obtain ⟨bs', a', q, hrun, rfl, -, hS', hg, htopq, hcell, hD⟩ :=
    wsC_ok (realCall p) n dn fe vis m s'.mem a pp s r bs hW hS hs
      (fun m'' hg => hq.stab (decBS_mono _) m'' hg) hq9 (fun k r2 m2 h0 e2 => by
        have hF := hS.check.pins.full h0
        obtain ⟨lz, hdz⟩ := hC.stageT.twin.den.zero
        rw [hF.zeroLevel] at hdz
        obtain ⟨x, a2, hrun2, hC2, hg2, hd2, -, -⟩ :=
          lvlEqC_simC p hcl hLC k hC hA s (pinW m 53) hs hF.lv_lt.2.1 sP lz hsP hdz r2 m2 e2
        exact ⟨x, a2, hrun2, hC2.stage, hg2, hd2⟩)
  refine ⟨bs', a', hrun, hS', hg, by simpa using hD hq, ?_, fun hrb o l h1 h2 => ?_⟩
  rotate_left
  · simp only [List.headD_cons] at h1 h2
    have e2 := hcell 2 (by decide) (by decide) (by decide)
    have e3 := hcell 3 (by decide) (by decide) (by decide)
    have hp2 : iwN s'.mem (pp.toNat + 2) = iwN m (pp.toNat + 2) := iwN_grow hg (by omega)
    have hp3 : iwN s'.mem (pp.toNat + 3) = iwN m (pp.toNat + 3) := iwN_grow hg (by omega)
    have g2 : iwN s'.mem (q.toNat + 2) = iwN s'.mem (pp.toNat + 2) := by simp only [iwN, nat?, iwA, aread_apply, e2]
    have g3 : iwN s'.mem (q.toNat + 3) = iwN s'.mem (pp.toNat + 3) := by simp only [iwN, nat?, iwA, aread_apply, e3]
    rw [g2, hp2] at h1; rw [g3, hp3] at h2
    exact Nat.le_trans (hrb o l h1 h2) hg.iw
  intro o l h1 h2
  simp only [List.headD_cons] at h1 h2
  have e0 := hcell 0 (by decide) (by decide) (by decide)
  have e1 := hcell 1 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at e0
  have hp0 : iwN s'.mem pp.toNat = iwN m pp.toNat := iwN_grow hg (by omega)
  have hp1 : iwN s'.mem (pp.toNat + 1) = iwN m (pp.toNat + 1) := iwN_grow hg (by omega)
  have g0 : iwN s'.mem q.toNat = iwN s'.mem pp.toNat := by simp only [iwN, nat?, iwA, aread_apply, e0]
  have g1 : iwN s'.mem (q.toNat + 1) = iwN s'.mem (pp.toNat + 1) := by simp only [iwN, nat?, iwA, aread_apply, e1]
  rw [g0, hp0] at h1; rw [g1, hp1] at h2
  exact Nat.le_trans (hsrc o l h1 h2) hg.iw

set_option experimental.vcgen true in
/-- **`check_block_inds`' unified model**: the formers and the agreements by their unified models
(`cbtE`, `cbtsE`, `cbagE`), the shape's sort, the formers' constants and the consing (outside the
verdict closure) lifted. -/
l_model cbiE_spec (p : Prog) (hP : IndsProg p)
  fns [hP.inds ↦ cbiE]
  specs [cbtE_spec p hP.bTele n, cbtsE_spec p hP.bTele hP.bTeles n,
    cbagE_spec p hP.agreeP.agree hP.agreeP.one hP.agreeP.lvl n, callW_spec p n "block_shape_with_sort",
    callW_spec p n "block_shape_declared", callW_spec p n "cons_block_inds"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_block_inds` gives besides the environment and the shape `x` it returns (from `m`,
`a`): their layout at the returned view (`IndsOut`), `AbsOK`, the recursors' bound carried to the
new shape, the core step at the entry index. -/
structure IndsPost (env : ConLeche.Env) (fe : IFEnv) (pp : Word) (m : Mem) (a : AState)
    (r : List Word) (x : IFEnv × BlockShape) (m' : Mem) (a' : AState) : Prop where
  out : IndsOut m r x m' a'
  abs : AbsOK m'
  recs : RecsB m pp → RecsB m' (r.tail.headD 0)
  core : ConRon.Bridge.CoreStep env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hcr hCS hOpf hLC hApd hCrk in
/-- **`check_block_inds` refines `checkBlockInds`, both outcomes** under `StageC` (twin side:
con-ron's `checkBlockInds_spec`'s proof): member 0's former by `cbt_ref`, the other formers by
`cbts_ref`, the agreements by `cbag_ref` (their unified models); past them only class-`0` errors:
the shape's sort, the declared formers' slice and the consing (outside the verdict closure). -/
theorem cbi_ref (hP : IndsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp isRec : Word} {bs : BlockShape} {b : Bool}
    (hC : StageC dn vis fe env m a) (hqd : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcx : ShapeCV m pp) (hb : (isRec != 0) = b) (hA : AbsOK m)
    (hk : ∀ f ∈ indsKeepCalleesC, AbsKeep p f) {bsP : ConLeche.BlockShape}
    (hbsP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP) :
    RefE (VerdictCtxU p) (cbiE p (n + 1) m vis pp isRec) (ConRon.Arena.checkBlockInds V fe bs b) a
      (fun v x a' => IndsPost env fe pp m a v.1 x v.2 a') := by
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hqd hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hqd
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  have hkl : UInt64.ofNat bs.k = l := by rw [hlk]; exact UInt64.ofNat_toNat
  obtain ⟨hmsP, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  by_cases hl0 : l = 0
  · rw [cbiE.abort1 p n m vis pp isRec (by rw [hkw, hkl]; exact hl0)]; exact RefE.of_cls0 rfl
  rw [cbiE.arm1 p n m vis pp isRec (by rw [hkw, hkl]; exact hl0), hkw, hkl, hw0, hnpw]
  -- the members, with their formers' constant records below the tops
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left hl0
  have hoN : iwN m pp.toNat = some o.toNat := (rec2IwN_trunc ho).2
  have hlN : iwN m (pp.toNat + 1) = some l.toNat := (rec2IwN_trunc hl).2
  have hms : MemsOK m o l bs.members :=
    ⟨⟨hdm, hob'⟩, fun j hj c hc d hd => hcx o.toNat l.toNat hoN hlN j hj c hc d hd⟩
  obtain ⟨q0, ms0, rest, hmeq, hw, hqb, hmok, hrest⟩ := hms.cons hl0
  rw [hw]
  unfold ConRon.Arena.checkBlockInds
  rw [hmeq]
  rw [hmeq] at hmsP
  obtain ⟨ms0P, restP, -, hm0, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  have hnp : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  -- member 0's former
  rcases n with _ | k
  · rw [cbtE.eq_1, cbiE.k_check_block_tele.none]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hR1 := cbt_ref hq henv hV hcr hCS hApd hCrk hP.toCstProg k (by omega) hC hmok hA hm0 (vis := vis)
    (nP := UInt64.ofNat bs.nP)
  rw [hnp] at hR1
  refine RefE.bindE (fun _ => cbiE.k_check_block_tele.none ..) id hR1
    fun ⟨r1, m1⟩ ⟨cvTa0, s0⟩ a1 hr1 hT1 => ?_
  rw [cbiE.k_check_block_tele.arm1]
  obtain ⟨hC1, hg1, hcv1, hcx1, hs32, hsd⟩ := hT1.out
  obtain ⟨-, ⟨cvTa₀P, s0P⟩, ⟨h1a, h1b, hw1⟩, -⟩ := ConRon.Bridge.Inductives.checkBlockTele_specF fe
    ConRon.Bridge.CoreSpec.of_core henv bs.nP ms0 ms0P a a1 _ hC.check hm0 hr1
  dsimp only at h1a h1b hw1
  have k1 : InsAt dn vis fe env m a m1 a1 := ⟨hC1, hT1.abs, hg1, hT1.core⟩
  have hc0 := installCvDecB hcv1 hcx1
  -- the other members' formers
  have hR2 := cbts_ref hq henv hV hcr hCS hApd hCrk hP.toInstProg (UInt64.ofNat bs.nP) (k + 1) (by omega) m1 a1
    (o + 1) (l - 1) rest restP hC1 (hrest.grow hg1) k1.abs
    (ConRon.Bridge.Inductives.dMember_ext.list k1.core.ext _ _ hrestP) (vis := vis)
  rw [hnp] at hR2
  refine RefE.bindE (fun _ => cbiE.k_check_block_teles.none ..) id hR2
    fun ⟨r2, m2⟩ cvs a2 hr2 hT2 => ?_
  rw [cbiE.k_check_block_teles.arm1]
  have k2 : InsAt dn vis fe env m1 a1 m2 a2 := ⟨hT2.stage, hT2.abs, hT2.grow, hT2.core⟩
  obtain ⟨-, cvsP, ⟨h2', hw2⟩, -⟩ := ConRon.Bridge.Inductives.checkBlockTeles_specF fe
    ConRon.Bridge.CoreSpec.of_core henv bs.nP rest restP a1 a2 cvs hC1.check
    (ConRon.Bridge.Inductives.dMember_ext.list k1.core.ext _ _ hrestP) hr2
  -- the agreements
  have hsd' : decI (r1.tail.headD 0) = s0 := hsd
  rw [← hsd']
  rw [← hsd'] at h1b
  have hR3 := cbag_ref hq henv hOpf hLC hP.agreeP (UInt64.ofNat bs.nP) (r1.headD 0)
    (r1.tail.headD 0) cvTa0 hw1 (k + 1) (by omega) m2 a2 (r2.headD 0) (r2.tail.headD 0) cvs cvsP k2.stage
    k2.abs (hc0.grow (OMono.decCVp _) k2.grow) hs32 hT2.teles (ConRon.Bridge.denoteCV_ext h1a k2.core.ext)
    (ConRon.Bridge.denoteL_ext h1b k2.core.ext) h2' hw2 (vis := vis)
  rw [hnp] at hR3
  refine RefE.bindE (fun _ => cbiE.k_check_block_agree.none ..) (fun hG => hG.toVerdictCtx) hR3
    fun ⟨u3, m3⟩ _ a3 hr3 hT3 => ?_
  rw [cbiE.k_check_block_agree.arm1]
  obtain ⟨c3, -, -, -⟩ := ConRon.Bridge.Inductives.checkBlockAgree_specF fe
    ConRon.Bridge.CoreSpec.of_core henv bs.nP cvTa0 cvTa₀P (decI (r1.tail.headD 0)) s0P hw1 cvs cvsP hw2
    a2 a3 _ hT2.stage.check ⟨ConRon.Bridge.denoteCV_ext h1a k2.core.ext,
      ConRon.Bridge.denoteL_ext h1b k2.core.ext, h2'⟩ hr3
  have k3 : InsAt dn vis fe env m2 a2 m3 a3 := ⟨hT3.stage, hT3.abs, hT3.grow, c3⟩
  have k03 := (k1.trans k2).trans k3
  have hx13 := (k2.trans k3).core.ext
  -- the shape with its sort
  refine RefE.bindLift (fun _ => cbiE.k_block_shape_with_sort.none ..) fun r4 m4 c4 => ?_
  obtain ⟨p1, a4, hr4, hS4, hg4, hp1, hsrc4, hrb4⟩ := installWithSortSimC hq.closed hLC hP.alloc hP.pinWord
    hP.withSort (k + 1) k3.stage k3.abs (hqd.grow (decBS_mono _) k03.grow)
    (partsHsrc_grow k03.grow hq9 hsrc) hs32 (ConRon.Bridge.denoteL_ext h1b hx13) r4 m4 c4
  have hA4 := hk _ (by simp [indsKeepCalleesC]) _ _ _ _ _ c4 k3.abs
  obtain ⟨c4', -⟩ := ConRon.Bridge.Inductives.BlockShape.withSort_spec fe bs bsP
    (decI (r1.tail.headD 0)) s0P a3 a4 p1 k3.stage.check
    ⟨ConRon.Bridge.Inductives.dShape_ext k03.core.ext _ _ hbsP, ConRon.Bridge.denoteL_ext h1b hx13⟩ hr4
  have k4 := InsAt.cstep k3.stage hS4 hA4 hg4 c4'
  refine ⟨_, _, hr4, ?_⟩
  rw [cbiE.k_block_shape_with_sort.arm1]
  -- the declared formers (L only)
  refine RefE.onlySim (fun _ => cbiE.k_block_shape_declared.none ..) (fun _ _ h => h) fun r5 m5 c5 => ?_
  rw [cbiE.k_block_shape_declared.arm1]
  have k04 := k03.trans k4
  obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (blockShapeDeclared_spec p hP.alloc hP.fieldCopy hP.declared (k + 1) _ pp) c5
  have hqd4 := hqd.grow (decBS_mono _) k04.grow
  have hsrc4' := partsHsrc_grow k04.grow hq9 hsrc
  obtain ⟨hqd4', hq94, -⟩ := partsShapeFacts hqd4 hsrc4'
  obtain ⟨er, hdd, hg5, hf5, htop5, hroom5⟩ := declW_dec hW5 hS4.iw.iwSize hS4.iw.ctl hqd4' hq94 hsrc4'
    (shapeFacts4 hqd4)
  dsimp only at hdd htop5 hroom5 hf5 hg5
  have hS5 : StageR vis fe s5.mem a4 :=
    ⟨CheckR.frame_iw hf5 hS4.check, IWOK.of_iw hf5 hS4.iw (by rw [hf5.size IW]; exact hroom5)⟩
  have hA5 : AbsOK s5.mem := AFr.of_frame hf5 (by decide) (by decide) hA4
  subst er
  have hkb : bs.k < 2 ^ 64 := by
    have := (rdW (s5.mem.arr64 CTL) 200).toNat_lt; have h' := htop5; simp only [iwTop] at h'; omega
  have hkk : (UInt64.ofNat bs.k : Word).toNat = bs.k := UInt64.toNat_ofNat_of_lt' hkb
  have hcvs : PSlR decCVp (bs.members.map (·.declared)) (rdW (m4.arr64 CTL) 200) (UInt64.ofNat bs.k) s5.mem :=
    ⟨by rw [hkk]; exact decPLcv_decB hdd (by omega), by have := hkk; omega⟩
  simp only [List.headD_cons, List.tail_cons]
  -- the formers consed (L only; pure in the twin)
  refine RefE.onlySim (fun _ => cbiE.k_cons_block_inds.none ..) (fun _ _ h => h) fun r6 m6 c6 => ?_
  rw [cbiE.k_cons_block_inds.arm1]
  obtain ⟨-, hp9, -⟩ := partsShapeFacts hp1 hsrc4
  have hp1' := hp1.grow (decBS_mono _) hg5
  have hsrc5 := partsHsrc_grow hg5 hp9 hsrc4
  rw [hmeq] at hcvs
  obtain ⟨s6, rfl, -, hS6, hg6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (consBlockInds_refines p hP.toConsIndsProg (k + 1) _ a4 vis fe (r4.headD 0) isRec _ _ 0 p1 b _ hb hS5
      hp1' hsrc5 hcvs (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact UInt64.toNat_lt _)) c6
  have hA6 := hk _ (by simp [indsKeepCalleesC]) _ _ _ _ _ c6 hA5
  obtain ⟨-, hp9', -⟩ := partsShapeFacts hp1' hsrc5
  simp only [UInt64.toNat_zero] at hS6
  exact RefE.ret rfl ⟨⟨hS6, (k04.grow.trans hg5).trans hg6, hp1'.grow (decBS_mono _) hg6,
    partsHsrc_grow hg6 hp9' hsrc5⟩, hA6, fun hrb =>
    ((hrb4 ((hrb.grow (k1.trans k2).grow (by omega)).grow k3.grow
      (by have := (k1.trans k2).grow.1; omega))).grow (hg5.trans hg6) (by omega)), k04.core⟩


include hq henv hV hcr hCS hOpf hLC hApd hCrk in
/-- **`check_block_inds` refines `checkBlockInds`** under `StageC` (stage 1, the ok half of
`cbi_ref`): the environment with the formers pushed at the returned view and the shape with its
sort below the tops; the frame at the entry index a `CoreStep`. -/
@[refines ConRon.Arena.checkBlockInds]
theorem checkBlockInds_refinesC (hP : IndsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (pp isRec : Word) (bs : BlockShape) (b : Bool) (hC : StageC dn vis fe env s₀.mem a₀)
    (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcx : ShapeCV s₀.mem pp) (hb : (isRec != 0) = b) (hA : AbsOK s₀.mem)
    (hk : ∀ f ∈ indsKeepCalleesC, AbsKeep p f) {bsP : ConLeche.BlockShape}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_inds" [vis, pp, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockInds V fe bs b) a₀ ∧
      IndsOut s₀.mem r (AM.res (ConRon.Arena.checkBlockInds V fe bs b) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockInds V fe bs b) a₀) ∧ AbsOK s'.mem ∧
      (RecsB s₀.mem pp → RecsB s'.mem (r.tail.headD 0)) ∧
      ConRon.Bridge.CoreStep env fe a₀ (AM.st (ConRon.Arena.checkBlockInds V fe bs b) a₀); ⊤⦄ := by
  refine triple_post (RefE.triple (cbiE_spec p hP (n + 1) s₀ vis pp isRec)
    (cbi_ref hq henv hV hcr hCS hOpf hLC hApd hCrk hP n hn hC hqd hsrc hcx hb hA hk hbsP)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR.out, hR.abs, hR.recs, by rw [hst]; exact hR.core⟩

end sims


end L.Ind

end
