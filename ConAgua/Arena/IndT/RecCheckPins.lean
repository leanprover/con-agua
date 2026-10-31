import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.RecClassSpec.ReadProg
import ConAgua.Verdict.IndBPins
import ConAgua.Arena.IndPosSpec.NestCrest

/-!
# `target_major_pins`: one refinement for both outcomes

`tmp_ref` refines `targetMajorPins` with `tmpE` (`Verdict/IndBPins`) for both outcomes, from
`StageC`, `AbsOK` and the inputs' denotations con-ron's `targetMajorPins_spec` asks (the
parameters' denotations and their scoping at the rule prefix), the twin side transcribed from that
spec's proof: `targetPinTys` (`tpt_ref`), the head's intern (`internConstE_run`), `mkAppN`
(`mkAppN_run`), `inferTypeCore` (`inferC_rsim`, the core stubs' claim). Its post carries the
frame (`MFr`) for `class_majors`' `PosMR`; `tptE_mfr` is `target_pin_tys`' frame.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section mfr
variable {p : Prog} (hq : KnotStageProg p)

include hq in
theorem coreC_mfr {n : Nat} {args r : List Word} {m m' : Mem}
    (h : realCall p n "infer_type_core" args m = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (run_memFrame hq.closed (by decide) (run_of_callW h)).1 coreStageA_stage coreStageC_stage

include hq in
theorem tptE_mfr : ∀ (n : Nat) (m m' : Mem) (vis d xo xl v : Word),
    tptE p n m vis d xo xl = .ok (v, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by rw [tptE.eq_def] at h; cases h
  | n + 1, m, m', vis, d, xo, xl, v, h => by
    by_cases hl : xl = 0
    · rw [tptE.arm1 p n m vis d xo xl hl] at h
      cases h; exact MFr.refl _ _ _
    rw [tptE.arm2 p n m vis d xo xl hl] at h
    rcases h1 : callE p n "infer_type_core" [vis, d, rdW (m.arr64 IW) xo] m with e1 | ⟨r1, m1⟩ <;>
      rw [h1] at h
    · rw [tptE.k_infer_type_core.none] at h; cases h
    rw [tptE.k_infer_type_core.arm1] at h
    refine (coreC_mfr hq (callW_of_callE h1)).trans ?_
    rcases h2 : tptE p n m1 vis d (xo + 1) (xl - 1) with e2 | ⟨v2, m2⟩ <;> rw [h2] at h
    · rw [tptE.k_target_pin_tys.none] at h; cases h
    rw [tptE.k_target_pin_tys.arm1] at h
    cases h
    exact tptE_mfr n _ _ _ _ _ _ _ h2

end mfr

/-- What `target_major_pins` gives besides the twin's run (from `m`): the stage invariant, the
growth, the abstraction memos, the frame. -/
structure TmpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  mfr : MFr [] [] m m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_major_pins` refines `targetMajorPins .verified`, both outcomes** (twin side: con-ron's
`targetMajorPins_spec`'s proof): `tpt_ref`, the head's intern (`internConstE_run`), `mkAppN`
(`mkAppN_run`), `inferC_rsim` (the core stubs' claim). -/
theorem tmp_ref (N : Nat) (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {rP Mp : Word}
    {M : TargetMajor} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hM : DecB (fun m => decTM m Mp.toNat) m M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    RefE (VerdictCtx p) (tmpE p N m vis rP Mp) (ConRon.Arena.targetMajorPins V fe rP.toNat M) a
      (fun v _ a' => TmpPost dn vis fe env m v.2 a') := by
  obtain _ | N := N
  · rw [tmpE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hS := hC.stage
  have hsz := hS.iw.iwSize
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨k, hk, hmem⟩ := decTM_member hM0
  obtain ⟨hind, hlv, hdsd, -, -, -, hmemP, -, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hMP
  have hrk := iwN_rdW_at (w := Mp) (k := 8) hk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  by_cases hk8 : rdW (m.arr64 IW) (Mp + 8) ≠ 0
  · rw [tmpE.arm1 p N m vis rP Mp hk8]
    have hk0' : k ≠ 0 := by intro e; apply hk8; rw [hrk.1, e]; rfl
    have hmem' : M.member = some (k - 1) := by rw [hmem]; simp [decON, hk0']
    exact RefE.ret (by simp [ConRon.Arena.targetMajorPins, hmem']; rfl)
      ⟨hC, IWGrow.refl m, hA, MFr.refl _ _ _⟩
  rw [tmpE.arm2 p N m vis rP Mp (by simpa using hk8)]
  have hk00 : k = 0 := by
    have : rdW (m.arr64 IW) (Mp + 8) = 0 := by simpa using hk8
    rw [hrk.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' hrk.2] at this
  have hmem' : M.member = none := by rw [hmem, hk00]; rfl
  have hw := hds (by rw [← hmemP, hmem'])
  obtain ⟨o, l, hoT, hlT, hdT⟩ := decTM_ds (show decTM (truncM m) Mp.toNat = some M from hM)
  obtain ⟨hoi, ho⟩ := iwN_truncM_get hoT
  obtain ⟨hli, hl⟩ := iwN_truncM_get hlT
  have hdsm : decHL m o l = some M.ds := (OMono.decHL o l).mono _ _ _ (IWGrow.refl m).truncExt hdT
  have ro := iwN_rdW_at (w := Mp) (k := 2) ho hsz
  have rl := iwN_rdW_at (w := Mp) (k := 3) hl hsz
  rw [show UInt64.ofNat 2 = (2 : Word) from rfl] at ro
  rw [show UInt64.ofNat 3 = (3 : Word) from rfl] at rl
  rw [ro.1, rl.1]
  have hoo := UInt64.toNat_ofNat_of_lt' ro.2
  have hll := UInt64.toNat_ofNat_of_lt' rl.2
  rw [ConRon.Arena.targetMajorPins]
  simp only [hmem']
  -- the pins of the parameters
  have hds0 : HSl0 m (UInt64.ofNat o) (UInt64.ofNat l) M.ds := by
    refine ⟨by rw [hoo, hll]; exact hdsm, ?_⟩
    by_cases hl0 : l = 0
    · exact .inl (by rw [hl0]; rfl)
    · exact .inr (by rw [hoo, hll]; exact decHL_truncM_bound hdT hl0)
  have hR1 := tpt_ref hq henv N (by omega) hC hA hds0 hdsd hw
  rcases h1 : tptE p N m vis rP (UInt64.ofNat o) (UInt64.ofNat l) with e1 | ⟨v1, m1⟩ <;>
    rw [h1] at hR1
  · rw [tmpE.k_target_pin_tys.none]; exact RefE.bind_left hR1
  rw [tmpE.k_target_pin_tys.arm1]
  obtain ⟨_, a1, hrun1, hR⟩ := hR1
  dsimp only at hR
  have hC1 := hR.stage
  have hg1 := hR.grow
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetPinTys_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv rP.toNat M.ds MP.ds hw a a1 () hC.check hdsd hrun1
  refine RefE.bind_right hrun1 ?_
  have hS1 := hC1.stage
  have hM1 : decTM m1 Mp.toNat = some M := hM.stab (decTM_mono _) m1 hg1
  obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := Mp) (k := 0) (by simpa using decTM_ind hM1) hS1.iw.iwSize
  obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := Mp) (k := 1) (decTM_lvls' hM1) hS1.iw.iwSize
  rw [show Mp + UInt64.ofNat 0 = Mp by simp] at hwi
  rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
  rw [hwi, hwu]
  refine RefE.bindLift (fun _ => rfl) fun hd m2 h2 => ?_
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 wi wu hwiH hwuH h2
  rw [hwiE, hwuE] at hrun2
  obtain ⟨p2, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run c1.ok.state
    (ConRon.Bridge.denoteN_ext hind c1.ext) (ConRon.Bridge.denoteLs_ext hlv c1.ext) hrun2
  have hA2 := ceinternW_afr h2 hR.abs
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hS2 hA2 p2
  have c2 := c1.trans (p2.toCore c1.ok)
  refine ⟨_, _, (by unfold ConRon.Arena.internConstE; exact hrun2), ?_⟩
  dsimp only [tmpE.k_intern_const]
  refine RefE.abort0 rfl fun hbig => ?_
  have hdH : H hd := by
    have : hd.toNat < (4294967296 : Word).toNat :=
      Nat.lt_of_not_le fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simpa [H] using this
  have hg12 := hg1.trans hg2
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.iw.iw
  have e2 : rdW (m2.arr64 IW) (Mp + 2) = UInt64.ofNat o := by
    rw [← ro.1]; simp only [rdW]
    rw [show (Mp + 2).toNat = Mp.toNat + 2 by rw [UInt64.toNat_add]; simp; omega, hg12.iwGet _ hoi]
  have e3 : rdW (m2.arr64 IW) (Mp + 3) = UInt64.ofNat l := by
    rw [← rl.1]; simp only [rdW]
    rw [show (Mp + 3).toNat = Mp.toNat + 3 by rw [UInt64.toNat_add]; simp; omega, hg12.iwGet _ hli]
  rw [e2, e3]
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 h3 => ?_
  have hds2 : decHL m2 (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat = some M.ds := by
    rw [hoo, hll]; exact (OMono.decHL o l).mono _ _ _ hg12.truncExt hdT
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := mknF_ok dn vis fe hd _ _ hdH M.ds m2 m3 a2 r3 h3 ⟨hS2, hds2⟩
  have hrun3' : (ConRon.Arena.mkAppN (decE hd) M.ds) a2 = .ok (x3, a3) := hrun3
  obtain ⟨p3, happ⟩ := ConRon.Bridge.Inductives.mkAppN_run M.ds MP.ds c2.ok.state hhd
    (ConRon.Bridge.denoteEList_ext c2.ext _ _ hdsd) hrun3'
  have hA3 := mknF_afr h3 hA2
  have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [tmpE.k_mk_app_n_f]
  rw [← hx3.2] at happ ⊢
  refine RefE.bindCall (fun _ => rfl)
    (fun hV _ h4 => hV.core.inferTypeCore N (by omega) hC3.stageT rP (r3.headD 0) hx3.1 _ h4)
    (inferC_rsim hq henv N (by omega) hC3 hA3 rP (r3.headD 0) hx3.1 happ
      (ConLeche.Expr.WScoped.mkAppN (by simp [ConLeche.Expr.WScoped]) hw))
    fun r4 m4 _ a4 h4 _ ⟨hC4, hg4, _, hA4, _⟩ => ?_
  refine RefE.ret rfl ⟨hC4, (hg12.trans hg3).trans hg4, hA4, ?_⟩
  exact (((tptE_mfr hq _ _ _ _ _ _ _ _ h1).trans (ceinternW_mfr h2)).trans (MFr.ofMknF h3)).trans
    (coreC_mfr hq (callW_of_callE h4))

include hq henv in
/-- **`target_major_pins` refines `targetMajorPins`** under `StageC` (`tmp_ref`'s ok half; the
knot's `infer_type_core`; the major's denotation and its parameters' scoping as con-ron's
`targetMajorPins_spec` asks). -/
@[refines ConRon.Arena.targetMajorPins]
theorem targetMajorPins_refinesC (hp : TmpProg p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (rP Mp : Word) (M : TargetMajor) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hM : DecB (fun m => decTM m Mp.toNat) s₀.mem M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a₀.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, Mp]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tmpE_spec p hp N s₀ vis rP Mp)
    (tmp_ref hq henv N hN hC hA hM hMP hds)) ?_
  rintro r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
