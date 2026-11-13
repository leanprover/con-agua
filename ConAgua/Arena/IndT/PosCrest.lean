module

import ConRon.Bridge.Core.Walks.Cached
public import ConAgua.Arena.IndPosSpec.OneK
public import ConAgua.Arena.IndT.PosDefs
public import ConAgua.Verdict.PosE3Cm
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.TwinStep
public import ConAgua.Verdict.VCtx
import ConAgua.L.WordOff

@[expose] public section

/-!
# `nest_ctors_crest`: one refinement for both outcomes

`crest_ref` refines `crestT` (the head of `oneK`, split off by `oneK_eq`) by `ncrE` (unified):
its twin side transcribed from con-ron's `nestCtors_spec` (the cons case's head), the level
instantiation (`instLPFast_cstep`), the crest (`nestCrest_spec`, well scoped by
`WScoped_nestCrest`), its type (`inferC_rsim`) and that type's sort (`ensureSortC_rsim`), whose
errors are the core stubs' claims. It serves `oneRef_step` (`PosOne.lean`) through the run.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A core entry point keeps the stage's memos but the `hb` memo (`CoreFr.mfr`). -/
theorem coreF_mfr {p : Prog} (hq : KnotStageProg p) {f : FnName} (hf : f ∈ stageCoreFns) {n : Nat}
    {args r : List Word} {m m' : Mem} (h : realCall p n f args m = some (r, m')) :
    MFr [HBM] [214, 215] m m' :=
  (callW_coreFrame hq.closed hf h).mfr

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat) (prog : List NestHole)

/-- The head of `oneK` (`nest_ctors_crest`): the crest, typed. -/
def crestT (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (cv : IConstantVal) : AM EIdx :=
  if !nameNodup cv.levelParams then
    fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor has a duplicate universe level parameter (official: duplicate universe level parameter)")
  else do
    let cty ← instLPFast coreWalkFuel cv.levelParams us cv.type
    match ← ConRon.Arena.nestCrest names us ds holes cty with
    | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does not bind the parameters (official: ill-formed constructor)")
    | some crest => do
      let ty ← inferTypeCore mode fe checkFuel hi crest
      let _ ← ensureSortCore mode fe checkFuel hi ty
      pure crest

/-- The rest of `oneK` after the crest. -/
def oneRest {β : Type} (root : Bool) (hi : Nat) (us : LsIdx) (ds : List EIdx) (cv : IConstantVal) (nF : Nat)
    (ns : NestState) (K : List NestFieldKind × EIdx → NestState → AM β) (crest : EIdx) : AM β :=
  walkK mode fe ctx fuel prog root hi nF crest ns fun ks _nds cur ns2 closed => do
    let u4 ← (List.range nF).anyM (u4F ks closed)
    if u4 then
      fail (.invalid "nested positivity: non valid occurrence of the datatypes being declared (a later field or the result depends on a recursive or nested field)")
    else do
      roK ctx hi cur fun resOk =>
        if !resOk then
          fail (.invalid "nested positivity: invalid return type — a constructor's result index mentions the block")
        else do
          let nf ← ConRon.Arena.nestCtorNf ctx prog us ds cv closed
          let ns3 := { ns2 with ctorNfs := ns2.ctorNfs.push nf }
          K (ks, closed) ns3

theorem oneK_eq {β : Type} (root : Bool) (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) (cv : IConstantVal) (nF : Nat) (ns : NestState)
    (K : List NestFieldKind × EIdx → NestState → AM β) :
    oneK mode fe ctx fuel prog root hi us ds names holes cv nF ns K =
      crestT mode fe hi us ds names holes cv >>= oneRest mode fe ctx fuel prog root hi us ds cv nF ns K := by
  unfold oneK crestT
  split
  · funext s; rfl
  · simp only [bind_assoc]
    congr 1; funext cty
    congr 1; funext x
    split
    · funext s; rfl
    · simp only [bind_assoc, pure_bind]
      rfl

end twin

/-- What `nest_ctors_crest` gives besides the crest `crest` (from `m`, the twin from `a`): the stage,
the growth, the result word, the frames, the twin's step, the crest denoting a term well scoped at
the frame's depth. -/
structure CrestPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (a : AState) (m : Mem) (hi w : Word) (m' : Mem) (crest : EIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  hw : H w
  dec : decI w = crest
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'
  den : ∃ crestP, denoteE a'.store crest = some crestP ∧ ConLeche.Expr.WScoped hi.toNat crestP

section crest
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
  (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hIlpf henv in
/-- **`nest_ctors_crest` refines `crestT` (the head of `oneK`), both outcomes**, under `StageC`
and con-ron's preconditions of the constructor's head (`nestCtors_spec`'s): the level parameters
and the duplicate check, the level instantiation (`instLPFast_cstep`), the crest
(`nestCrest_spec`, well scoped by `WScoped_nestCrest`), its type (`inferC_rsim`) and that type's
sort (`ensureSortC_rsim`); the errors of the last two are the core stubs' claims. -/
theorem crest_ref {k : Nat} (hn : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    {no nl us dO dL hO hL cv hi : Word} {names : List NIdx}
    {ds holes : List EIdx} {cvv : IConstantVal} (hC : StageC dn vis fe env m a)
    (hus : H us) (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hnn : dL.toNat + names.length < 2 ^ 64)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hcv : decCVp m cv.toNat = some cvv) (hP : PosMR m) (hA : AbsOK m)
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {namesP : List ConLeche.Name}
    {holesP : List ConLeche.Expr} {cvP : ConLeche.ConstantVal}
    (hpre : CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hcl : cvP.type.hasFvar = false) :
    RefE (VerdictCtx p) (ncrE p k m vis no nl us dO dL hO hL cv hi)
      (crestT V fe hi.toNat (decI us) ds names holes cvv) a
      (fun v crest a' => CrestPost dn vis fe env a m hi v.1 v.2 crest a') := by
  have hS := hC.stage
  cases k with
  | zero => rw [ncrE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  rw [ncrE.arm1]
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨hcvn, hcvl, hcvt⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  -- the level parameters (L only)
  refine RefE.onlySim (fun _ => ncrE.k_cv_lps.none ..) (fun _ _ h => h) fun r1 m1 hlp => ?_
  rw [ncrE.k_cv_lps.arm1]
  obtain ⟨hS1, hg1, hE1, hdec1, ht1⟩ := L.Ind.cvLpsW_stage hlp hS hcv
  have hA1 : AbsOK m1 := erToIwW_afr (show erToIwW _ m _ _ = some (r1, m1) from hlp) hA
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
  obtain ⟨ws, hws, hwsd, hwH⟩ := slR_of_decHL m1 _ _ _ hdec1 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  -- the duplicate check
  rcases hnd : nodupW k m1 (r1.headD 0) (r1.tail.headD 0) with _ | b
  · rw [liftE_none, ncrE.k_sl_nodup.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hb := nodupW_ok k m1 _ _ b ws hws hnd
  have hnod : nameNodup cvv.levelParams = decide ws.Nodup := by rw [hwsd, nameNodup_map ws hwH]
  unfold crestT
  refine RefE.ofArms (fun h => ncrE.k_sl_nodup.abort1 (hc1 := h) ..) (fun h => ncrE.k_sl_nodup.arm1 (hc1 := h) ..)
    (RefE.guardThen (by decide) (fun h => by grind) (fun h => by grind) fun _ _ => ?_)
  -- the instantiated type
  obtain ⟨-, -, hty⟩ := decCV_eq_some.mp hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have e3 : (cv + CV.type).toNat = cv.toNat + CV.type.toNat := L.toNat_add_of_lt _ _ (by have := erecP_lt64 hwt; omega)
  have hrdt : rdW (m1.arr64 (tierA EREC ((cv + CV.type) >>> 40))) (cv + CV.type &&& 1099511627775) = wt := by
    change erRd m1 (cv + CV.type) = wt
    rw [erRd_frame (erToIwW_iwFr (show erToIwW _ m _ _ = some (r1, m1) from hlp)) (by decide) (by decide)]
    exact (erRd_of_erecP (a := cv + CV.type) (by rw [e3]; exact hwt)).1
  rw [hrdt]
  refine RefE.bindLift (fun _ => ncrE.k_inst_lp_fast.none ..) fun r2 m2 hil => ?_
  obtain ⟨cty, a1, hrun1, ⟨hS2, hg2, hcH, hcd⟩, ⟨A2, C2, hA2s, hC2s, hfr2⟩, hAF2⟩ :=
    IlpRd.realC hIlpf hC k CWF _ _ _ _ cvv.levelParams m1 m2 a r2 hus hwtH ⟨rfl, erToIwW_iwFr hlp⟩ hS1 hdec1 hil
  rw [CWF_eq, ← hwtd] at hrun1
  refine ⟨_, _, hrun1, ?_⟩
  rw [ncrE.k_inst_lp_fast.arm1]
  have hA2 : AbsOK m2 := hAF2 hA1
  obtain ⟨c1, hctyP⟩ := ConRon.Bridge.Inductives.instLPFast_cstep hC.check hcvl hpre.hus hcvt hrun1
  have hC2 : StageC dn vis fe env m2 a1 := hC.of_cstep hS2 hA2 c1
  -- the crest
  have hg12 := hg1.trans hg2
  refine RefE.bindLift (fun _ => ncrE.k_nest_crest.none ..) fun r3 m3 hpc0 => ?_
  cases k with
  | zero => simp [pcrWf] at hpc0
  | succ k =>
  cases k with
  | zero => simp [pcrWf] at hpc0
  | succ k =>
  cases k with
  | zero => simp [pcrWf] at hpc0
  | succ k =>
  simp only [pcrWf] at hpc0
  have hP2 : PosMR m2 := (hP.fr (posmemo_cvLpsW_mfr hlp)).fr (MFr.of_frame hfr2 hA2s hC2s)
  obtain ⟨M, G, g, hR⟩ := hP2.rf
  obtain ⟨mp2, hM2⟩ := hP2.rp
  obtain ⟨x, a2, hrun2, hx, ⟨M', G', hS3, hg3, hR3, -⟩, hM3⟩ := pcrW_ok fe vis k m2 m3 a1 no nl us dO dL hO hL
    (r2.headD 0) r3 names ds holes M G g hpc0 hS2 hcH hus
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hdec) (by omega)
    (by have := hg12.iw; omega) hnn mp2 hM2
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hds) (by have := hg12.iw; omega)
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hho) (by have := hg12.iw; omega) hR
  rw [hcd] at hrun2
  refine ⟨_, _, hrun2, ?_⟩
  have hA3 : AbsOK m3 := pcrW_afr hpc0 hA2
  obtain ⟨p2, ho⟩ := ConRon.Bridge.Inductives.nestCrest_spec names namesP (decI us) usP ds dsP holes holesP cty _
    a1 a2 x hC2.check.state hC2.check.pins
    ⟨ConRon.Bridge.denoteNListE_ext c1.ext _ _ hpre.hnames, ConRon.Bridge.denoteLs_ext hpre.hus c1.ext,
      ConRon.Bridge.denoteEList_ext c1.ext _ _ hpre.hds, ConRon.Bridge.denoteEList_ext c1.ext _ _ hpre.hholes,
      hctyP⟩ hrun2
  cases x with
  | none =>
    simp only [decOE] at hx
    rw [ncrE.k_nest_crest.abort1 _ _ _ _ _ _ hx]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  | some crest =>
  obtain ⟨hx1, hxH, hxd⟩ := hx
  rw [ncrE.k_nest_crest.arm1 _ _ _ _ _ _ (by rw [hx1]; decide)]
  obtain ⟨crestP, hcrestP, hcrest⟩ := ho
  have hwc : ConLeche.Expr.WScoped hi.toNat crestP :=
    ConLeche.WScoped_nestCrest (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl) hpre.hlen
      (fun y hy => (List.mem_append.mp hy).elim (hpre.wds y) (hpre.wholes y)) hcrestP
  have hP3 : PosMR m3 := hP2.setCr (pcrW_mfr hpc0) hM3 ⟨M', G', g, hR3⟩
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 p2
  have hxH' : H (r3.tail.headD 0) := by simpa using hxH
  have hxd' : decI (r3.tail.headD 0) = crest := by simpa [decE_eq] using hxd
  subst hxd'
  -- its type
  refine RefE.bindCall (fun _ => ncrE.k_infer_type_core.none ..)
    (fun hV e h5 => hV.core.inferTypeCore (k + 1 + 1 + 1) (by omega) hC3.stageT hi _ hxH' e h5)
    (inferC_rsim hq henv (k + 1 + 1 + 1) (by omega) hC3 hA3 hi _ hxH' hcrest hwc)
    fun r4 m4 ty a3 c5 hrun3 ⟨hC4, hg4, ⟨htyH, htyd⟩, hA4, c4, tyP, htyP, hwty⟩ => ?_
  dsimp only at hC4 hg4 htyH htyd hA4
  rw [ncrE.k_infer_type_core.arm1]
  subst htyd
  have hP4 : PosMR m4 := hP3.ofCore hq.closed (by decide) (callW_of_callE c5)
  -- its sort
  refine RefE.bindCall (fun _ => ncrE.k_ensure_sort_core.none ..)
    (fun hV e h6 => hV.core.ensureSortCore (k + 1 + 1 + 1) (by omega) hC4.stageT hi _ htyH e h6)
    (ensureSortC_rsim hq henv (k + 1 + 1 + 1) (by omega) hC4 hA4 hi _ htyH htyP hwty)
    fun r5 m5 so a4 c6 hrun4 ⟨hC5, hg5, _, hA5, c5', _⟩ => ?_
  dsimp only at hC5 hg5 hA5
  rw [ncrE.k_ensure_sort_core.arm1]
  exact RefE.ret rfl ⟨hC5, ((hg12.trans hg3).trans hg4).trans hg5, hxH', rfl,
    hP4.ofCore hq.closed (by decide) (callW_of_callE c6), hA5,
    ((c1.trans (p2.toCore hC2.check)).trans c4).trans c5',
    crestP, ConRon.Bridge.denote_ext hcrest (c4.ext.trans c5'.ext), hwc⟩

end crest

end L.Ind
