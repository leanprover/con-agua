module

import ConAgua.Arena.IndT.Pass
import ConAgua.Arena.IndInstallSpec.BlockRawRec
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.IcaW
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
import ConAgua.Arena.IndPartsSpec.AllCtors
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndT.Tail
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.RefWalk
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.BpRecBpassR
public import ConAgua.Arena.IndInstallSpec.CbProg
public import ConAgua.Arena.IndInstallSpec.ConsRecsTFSimOf
public import ConAgua.Arena.IndInstallSpec.OfClosed
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.IndRealLvlZ
public import ConAgua.Arena.IndT.ArmMemos
public import ConAgua.Arena.IndT.GenRec2
public import ConAgua.Arena.IndT.Sum2
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `checkBlock` under `StageC` (lane `indstaget`)

`check_block`'s unified model `icbE` and its refinement `block_ref` (both outcomes) from `StageC` at
the entry index: the iw-only steps and the names' checks keep the twin's state; the flush
(`ReadOK.flush`: `CheckOK` at the cleared caches) and the raw recursion bit (core-free, the state
kept) before the pass (`pass_ref`: `StageC` at the formers' index and what the tail takes), then the
tail (`tail_ref`). `checkBlock_refinesC` is its ok half.
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`check_block`'s unified model**: the pass, the raw recursion bit and the tail through their runs
(the ok half reads the calls' memos), the shape's and the names' steps, the duplicate checks and the
flush (outside the verdict closure) lifted. -/
l_model icbE_spec (p : Prog) (hP : CbProg p)
  fns [hP.cb ↦ icbE]
  specs [callW_spec p n "block_shape_all_ctors", callW_spec p n "block_caps_ctor_names",
    callW_spec p n "block_shape_member_names", callW_spec p n "sl_nodup", callW_spec p n "flush_caches"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_block` gives besides the twin's run, a view `w` and the memory `m'` (from `m`): the
stage, the growth, the memos of the tail, `AbsOK`, the recursors' memo, the main-arg memo. -/
structure BlockPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (w : Word) (x : IFEnv) (m' : Mem)
    (a' : AState) : Prop where
  stage : StageR w x m' a'
  grow : IWGrow m m'
  memo : HbMemo m'
  abs : AbsOK m'
  rc : RcMR m'
  ma : ∃ mp, maMR m' mp

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_block` refines `checkBlock`, both outcomes** under `StageC` (twin side con-ron's
`checkBlock_bridge_of`): the iw-only steps and the names' checks keep the twin's state; the flush
(`ReadOK.flush`: `CheckOK` at the cleared caches) and the raw recursion bit (core-free, the state
kept), then the pass (`pass_ref` on the run: `StageC` at the formers' index and what the tail takes)
and the tail (`tail_ref` on the run). -/
theorem block_ref (hP : CbProg p) {fs fs2 : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (N : Nat)
    (hN : N ≤ 2 ^ 62 + 1)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsrc : ShapeSrc m p0)
    (hcx : ShapeCV m p0) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hPm : PosMR m) (hma : ∃ mp, maMR m mp) (hA : AbsOK m)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    (hta : ∃ mp, taMR m mp) (hrb : RecsB m p0)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a.store fe = some env)
    {shP : ConLeche.BlockShape} (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some shP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a.store block = some blockP)
    {fsH fsM : List FnName} (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH)
    (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    RefE (CtsG p) (icbE p N m vis bO bL p0) (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a
      (fun v x a' => BlockPost dn m v.1 x v.2 a') := by
  have hS := hC.stage
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr⟩ := partsShapeFacts hq hsrc
  rcases N with _ | n
  · rw [icbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn : n ≤ 2 ^ 62 := by omega
  rw [icbE.arm1]
  -- the constructors
  refine RefE.onlySim (fun _ => icbE.k_block_shape_all_ctors.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  rw [icbE.k_block_shape_all_ctors.arm1]
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeAllCtors_spec p hP.ha hP.cp hP.nco hP.acc hP.acg hP.ac n _ p0) c1
  simp only at hs1 hW1
  subst hs1
  obtain ⟨cq, tot, rfl, hdc, hg1, hf1, htop1, hroom1⟩ := acW_ok _ _ _ p0 _ bs hW1 hq hS.iw.iwSize hS.iw.ctl
  have hS1 := stage_frame_iw hS hf1 (by omega)
  have hP1 := hPm.fr (MFr.of_iw hf1)
  obtain ⟨mp0, hmp0⟩ := hma
  have hma1 := maMR_mfr (MFr.of_iw hf1) hmp0
  have hA1 : AbsOK s1.mem := AFr.of_frame hf1 (by decide) (by decide) hA
  obtain ⟨tp0, htp0⟩ := hta
  have hta1 : ∃ mp, taMR s1.mem mp := ⟨tp0, taMR_mfr (MFr.of_iw hf1) (by simp) (by simp) htp0⟩
  simp only [List.headD_cons, List.tail_cons]
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  -- the constructors' names
  have hdc1 : decPL s1.mem (decCN s1.mem) cq.toNat tot.toNat = some bs.allCtors :=
    hdc.get (OMono.decPL (fun q => decCN_mono q) _ _)
  refine RefE.onlySim (fun _ => icbE.k_block_caps_ctor_names.none ..) (fun _ _ h => h) fun r2 m2 c2 => ?_
  rw [icbE.k_block_caps_ctor_names.arm1]
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.ha hP.mnc hP.bccn n _ cq tot) c2
  simp only at hs2 hW2
  subst hs2
  have hcsd : decPL (truncM s1.mem) (decCN (truncM s1.mem)) cq.toNat tot.toNat = some bs.allCtors := hdc
  have hlen := decPL_length _ hcsd
  obtain ⟨hr2, hd2, hg2, hf2, ht2⟩ := ctorNamesW_dec hW2 hS1.iw.iwSize hS1.iw.ctl (Nat.le_of_eq htop1)
    (bs.allCtors.map (·.1)) (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get tot.toNat cq.toNat bs.allCtors hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := rec2IwN_trunc hv
      obtain ⟨hvlt2, hva'⟩ := rec2IwN_trunc hva
      have hj' : j < bs.allCtors.length := by omega
      have hy' : bs.allCtors[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS2 : StageR vis fe s2.mem a := stage_frame_iw hS1 hf2 (by
    have := ctorNamesW_room hW2 hS1.iw.iwSize; simp only [iwTop] at this ht2 ⊢; omega)
  subst hr2
  simp only [List.map_map] at hd2
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hma2 := maMR_mfr (MFr.of_iw hf2) hma1
  have hA2 : AbsOK s2.mem := AFr.of_frame hf2 (by decide) (by decide) hA1
  have hta2 : ∃ mp, taMR s2.mem mp :=
    let ⟨mp, h⟩ := hta1; ⟨mp, taMR_mfr (MFr.of_iw hf2) (by simp) (by simp) h⟩
  have hg12 := hg1.trans hg2
  have hT2 : iwTop s2.mem < 2 ^ 64 := (rdW (s2.mem.arr64 CTL) 200).toNat_lt
  -- the members' names
  have hq2 := hq.grow (decBS_mono _) hg12
  have hsrc2 := partsHsrc_grow hg12 hq9 hsrc
  obtain ⟨hqd2, hq92, hptr2⟩ := partsShapeFacts hq2 hsrc2
  refine RefE.onlySim (fun _ => icbE.k_block_shape_member_names.none ..) (fun _ _ h => h) fun r3 m3 c3 => ?_
  rw [icbE.k_block_shape_member_names.arm1]
  obtain ⟨s3, hs3, hr3, hdn3, hg3, hf3, ht3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.ha hP.mnc hP.bsmn n _ p0 bs hqd2 (by omega) hS2.iw.iwSize
      hS2.iw.ctl hsrc2 (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr2 o l j v h1 h2 h3 h4))) c3
  obtain ⟨s3', hs3', -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.ha hP.mnc hP.bsmn n _ p0) c3
  have hroom := memberNamesW_room hW3 hS2.iw.iwSize
  rw [partsShapeK hqd2 hq92] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd2).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hs3 hr3 hdn3 hg3 hf3 ht3
  subst hs3
  have hS3 : StageR vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    rw [← ht3]; simp only [iwTop] at hroom ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons]
  have hP3 := hP2.fr (MFr.of_iw hf3)
  have hma3 := maMR_mfr (MFr.of_iw hf3) hma2
  have hA3 : AbsOK s3.mem := AFr.of_frame hf3 (by decide) (by decide) hA2
  have hta3 : ∃ mp, taMR s3.mem mp :=
    let ⟨mp, h⟩ := hta2; ⟨mp, taMR_mfr (MFr.of_iw hf3) (by simp) (by simp) h⟩
  -- the two `sl_nodup`s
  have hcn3 : (decHL s3.mem (rdW (s1.mem.arr64 CTL) 200).toNat tot.toNat : Option (List NIdx)) =
      some (bs.allCtors.map (fun x => x.1.name)) := by
    rw [decHL_grow3 hg3 (by omega), hd2]; rfl
  obtain ⟨wc, hslc, hwc, hwcl⟩ := slR_of_decHL s3.mem _ _ _ hcn3 (by rw [ht2]; exact hT2)
  rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at hslc
  obtain ⟨wm, hslm, hwm, hwml⟩ := slR_of_decHL s3.mem _ _ _ hdn3
    (by rw [ht3]; exact (rdW (s3.mem.arr64 CTL) 200).toNat_lt)
  rw [UInt64.ofNat_toNat] at hslm
  refine RefE.onlySim (fun _ => icbE.k_sl_nodup.none ..) (fun _ _ h => h) fun r4 m4 c4 => ?_
  rw [icbE.k_sl_nodup.arm1]
  obtain ⟨s4, hs4, -, hm4, hnd1⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup n _ _ _ wc hslc hwcl) c4
  simp only at hs4 hm4 hnd1
  subst hs4
  rw [hm4]
  refine RefE.onlySim (fun _ => icbE.k_sl_nodup_2.none ..) (fun _ _ h => h) fun r5 m5 c5 => ?_
  obtain ⟨s5, hs5, -, hm5, hnd2⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup n _ _ _ wm hslm hwml) c5
  simp only at hs5 hm5 hnd2
  subst hs5
  rw [← hwc] at hnd1
  rw [← hwm] at hnd2
  unfold ConRon.Arena.checkBlock
  refine RefE.ofArms (fun h => icbE.k_sl_nodup_2.abort1 (hc1 := h) ..) (fun h => icbE.k_sl_nodup_2.arm1 (hc1 := h) ..)
    (RefE.guardThen (by decide) (fun h => by simpa [← hnd1, ← hnd2] using h)
      (fun h => by simpa [← hnd1, ← hnd2] using h) fun _ _ => ?_)
  rw [hm5]
  -- the flush
  have hg13 := hg12.trans hg3
  refine RefE.bindLift (fun _ => icbE.k_flush_caches.none ..) fun r6 m6 c6 => ⟨_, _, flushCaches_run a, ?_⟩
  rw [icbE.k_flush_caches.arm1]
  obtain ⟨s6, hs6, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (flushCaches_spec p hP.pass.flush n _) c6
  simp only at hs6 hfok hfm
  subst hs6
  obtain ⟨hS6, hg6⟩ := flush_stage hS3 hfok
  have hfr6 : MFr [] [] s3.mem s6.mem := by
    rw [hfm]; exact MFr.of_frame (flushMem_frame s3.mem) (by simp) (by
      intro x hx; left; have := flushCtl_lt x hx; omega)
  rw [← hfm] at hS6 hg6
  have hP6 := hP3.fr hfr6
  have hma6 := maMR_mfr hfr6 hma3
  have hA6 : AbsOK s6.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame s3.mem) (by decide) (by decide) hA3
  have hta6 : ∃ mp, taMR s6.mem mp :=
    let ⟨mp, h⟩ := hta3; ⟨mp, taMR_mfr hfr6 (by simp) (by simp) h⟩
  have hg16 := hg13.trans hg6
  -- the raw recursion bit
  have hq6 := hq.grow (decBS_mono _) hg16
  have hsrc6 := partsHsrc_grow hg16 hq9 hsrc
  rcases c7 : callE p n "block_raw_rec" [p0] s6.mem with e7 | ⟨r7, m7⟩
  · rw [icbE.k_block_raw_rec.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) c7
  rw [icbE.k_block_raw_rec.arm1]
  have d7 := callW_of_callE c7
  rcases n with _ | k
  · rw [callW_zero] at d7; cases d7
  obtain ⟨s7, hs7, -, hok7, hst7, hr7, hma7, hS7, hg7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (blockRawRec_refines p hP.ma hP.ha hP.mnc hP.bsmn hP.pdm hP.brm hP.brg hP.brr k _ _ dn vis fe p0 bs
      _ hS6 hq6 hsrc6 hma6) d7
  simp only at hs7 hst7 hr7 hma7 hS7 hg7
  subst hs7
  have hP7 := PosMR.ofClosed hcl hfr d7 hP6
  have hA7 : AbsOK s7.mem := hkr _ _ _ _ _ d7 hA6
  have hrun7 := AM.run_of_ok _ _ hok7
  rw [hst7] at hrun7
  refine RefE.bind_right hrun7 ?_
  generalize AM.res (ConRon.Arena.blockRawRec ⟨bs⟩) { a with caches := Caches.empty } = raw at hrun7 hr7 ⊢
  subst hr7
  have hg17 := hg16.trans hg7
  have hta7 := taMR.ofClosed hclT (hfT _ (by decide)) d7 hta6
  obtain ⟨cf, -, -⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V) hC.check.toR
    (show ConRon.Arena.flushCaches a = .ok ((), { a with caches := Caches.empty }) from rfl)
  have hC7 := StageC.of_parts hS7 cf hA7 hC.mem.dnN
  -- the pass
  have hq7 := hq.grow (decBS_mono _) hg17
  have hsrc7 := partsHsrc_grow hg17 hq9 hsrc
  have hcx7 := hcx.grow hg17 hq9 hsrc hptr
  have hT8 := icpE_spec p hP.pass (k + 1) ⟨s7.mem, Locals.init []⟩ vis p0 ([if raw then (1 : Word) else 0].headD 0)
  have hR8 := pass_ref hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP.pass hcl hfs (k + 1) hn hC7 hq7 hsrc7 hcx7
    (isRec := [if raw then (1 : Word) else 0].headD 0) (b := raw) (by cases raw <;> rfl) hP7 hA7 hkP hcoh hden hshP hlpsDn
  refine RefE.bindRun (s₀ := ⟨s7.mem, Locals.init []⟩) (fun _ => icbE.k_check_block_pass.none ..) hT8
    (fun hG => hG.nv) id hR8 fun r8 s8 x8 a8 c8 _ hrun8 hR8' => ?_
  rw [icbE.k_check_block_pass.arm1]
  have d8 := callW_of_callE c8
  obtain ⟨env₁, hC8, qP, i8, hcoh8, hden8, henv₁, hqP, hTw, henv₂, hMs⟩ := hR8'.twin
  have hma8 := maMR.ofClosed hclM (hfM _ (by simp)) d8 hma7
  have hg18 := hg17.trans hR8'.grow
  have hta8 := taMR.ofClosed hclT (hfT _ (by decide)) d8 hta7
  have hrb8 := hR8'.recs (hrb.grow hg17 (by omega))
  -- the tail
  have hT9 := ictlE_spec p hP.tail (k + 1) ⟨s8.mem, Locals.init []⟩ bO bL (r8.headD 0)
  have hR9 := tail_ref hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP.tail hP.cbr hfs2 hcl2 (k + 1) hclR hfR
    (by omega) hC8 hR8'.bpass (hblk.grow (decEBlk_mono _ _ _) hg18) hR8'.pos.hbOK hR8'.abs hkt ⟨hR8'.pos, hta8⟩
    hrb8 hR8'.classes hcoh8 hden8 hqP (ConRon.Bridge.denoteCIList_mono i8.ext _ _ hbP) hTw henv₂ hMs hfRc hclH hfH
  rw [← bind_pure (ConRon.Arena.checkBlockTail V block x8)]
  refine RefE.bindRun (s₀ := ⟨s8.mem, Locals.init []⟩) (fun _ => icbE.k_check_block_tail.none ..) hT9
    (fun hG => hG.nv) (fun hG => hG.toVerdictCtxU) hR9 fun r9 s9 x9 a9 c9 _ _ hR9' => ?_
  rw [icbE.k_check_block_tail.arm1]
  exact RefE.ret rfl ⟨hR9'.stage, hg18.trans hR9'.grow, hR9'.memo, hR9'.abs, hR9'.rc,
    maMR.ofClosed hclM (hfM _ (by simp)) (callW_of_callE c9) hma8⟩

include hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_block(vis, block.off, block.len, p0)` refines `checkBlock` under `StageC`**
(`checkBlock_refines`'s, from `StageC` at the entry index and con-ron's `checkBlock_bridge_of`
preconditions: the environment's coherence and denotation, the shape's and the block's
denotations). -/
@[refines ConRon.Arena.checkBlock]
theorem checkBlock_refinesC (hP : CbProg p) {fs fs2 : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (n : Nat) (hn : n + 4 ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (hC : StageC dn vis fe env s₀.mem a₀) (hq : DecB (fun m => decBS m p0.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem p0) (hcx : ShapeCV s₀.mem p0)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block)
    (hPm : PosMR s₀.mem) (hma : ∃ mp, maMR s₀.mem mp) (hA : AbsOK s₀.mem)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec") (hta : ∃ mp, taMR s₀.mem mp)
    (hrb : RecsB s₀.mem p0)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a₀.store fe = some env)
    {shP : ConLeche.BlockShape} (hshP : ConRon.Bridge.Inductives.dShape a₀.store bs = some shP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a₀.store block = some blockP)
    {fsH fsM : List FnName} (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH)
    (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 5)) "check_block" [vis, bO, bL, p0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀ ∧
      StageR (r.headD 0) (AM.res (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem ∧ AbsOK s'.mem ∧ RcMR s'.mem ∧ (∃ mp, maMR s'.mem mp); ⊤⦄ := by
  refine triple_post (RefE.triple (icbE_spec p hP (n + 5) s₀ vis bO bL p0)
    (block_ref hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT (n + 5)
      (by omega) hC hq hsrc hcx hblk hPm hma hA hkP hkt hkr hta hrb hcoh hden hshP hbP hfRc hclH hfH hclM hfM
      hlpsDn)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR'.stage, hR'.grow, hR'.memo, hR'.abs, hR'.rc, hR'.ma⟩

end sims

end L.Ind
