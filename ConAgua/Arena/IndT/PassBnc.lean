module

public import ConAgua.Arena.IndT.PassCS
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndInstallSpec.Pos3Init
public import ConAgua.Arena.IndInstallSpec.NhW
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Arena.IndPosSpec.NestHoles
import ConAgua.Arena.IndT.BncAfr
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndInstall
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.IndT.Lift
public import ConAgua.Arena.CrOKFrame
import ConAgua.L.WordOff

@[expose] public section

/-!
# `block_nest_ctx`' contract (lane `ronsync2`, stage 3)

`block_nest_ctx(p)` (`IndInstall.lean`): the formers' slice (`block_shape_formers`), the first
former's telescope opened (`open_pis_at_fvars_f`), the context record (`block_shape_nest_ctx`), the
members' holes (`nest_holes`). Its unified model `bncE`, the refinement `bnc_ref` against con-ron's
`blockNestCtx`, the contract `bncRefS_of`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

set_option experimental.vcgen true in
/-- **`block_nest_ctx`'s unified model**: every callee lifted. -/
l_model bncE_spec (p : Prog) (hP : PosBlkProg p)
  fns [hP.bnc ↦ bncE list]
  specs [callW_spec p n "block_shape_formers", callW_spec p n "open_pis_at_fvars_f",
    callW_spec p n "block_shape_nest_ctx", callW_spec p n "nest_holes"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- A lifted callee's error has class `0`. -/
theorem liftE_err_cls {α : Type} {x : Option α} {e : Err} (h : liftE x = .error e) : e.cls = 0 := by
  cases x <;> cases h; simp

/-- **Every error of `block_nest_ctx`'s model has class `0`** (aborts, lifted callees, fuel). -/
theorem bncE_cls {p : Prog} {n : Nat} {m : Mem} {pp : Word} {e : Err} (h : bncE p n m pp = .error e) :
    e.cls = 0 := by
  unfold bncE at h
  simp only [bncE.k_block_shape_formers, bncE.k_open_pis_at_fvars_f, bncE.k_block_shape_nest_ctx,
    bncE.k_nest_holes] at h
  repeat' split at h
  all_goals (cases h <;> first | simp | exact liftE_err_cls ‹_›)

/-- **`block_nest_ctx`'s ok run is `blockNestCtx`'s** (from `StageC`, `AbsOK`, the shape decoded
below the tops; con-ron's `blockNestCtx_spec` for the core step): the stage after, the context
decoded, the holes' slice. -/
theorem bnc_ok {p : Prog} (hP : PosBlkProg p) (hOpf : OpfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) {n : Nat} {m : Mem}
    {a : AState} {pp : Word} {bs : BlockShape} {bsP : ConLeche.BlockShape}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hsl : ShapeSl m pp) (hdP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hT : ∀ cv ∈ bsP.formers, ConLeche.Expr.WScoped 0 cv.type)
    {r : List Word} {m' : Mem} (hx : bncE p n m pp = .ok (r, m')) :
    ∃ x a', (ConRon.Arena.blockNestCtx bs).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ AbsOK m' ∧ IWGrow m m' ∧
      DecB (fun m => decCtx m (r.headD 0).toNat) m' x.1 ∧
      UCtx dn vis fe m' (r.headD 0) x.1 ∧
      (decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat : Option (List EIdx)) = some x.2 ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧
      x.1.hiAt 0 < 2 ^ 64 ∧ x.1.params.length + x.1.names.length < 2 ^ 64 := by
  have hS := hC.stage
  have hsrc := hsl.1
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  rcases n with _ | n
  · simp [bncE] at hx
  unfold bncE at hx
  simp only [bncE.k_block_shape_formers] at hx
  -- the formers
  rcases h1 : callW p n "block_shape_formers" [pp] m with _ | ⟨r1, m1⟩
  · rw [h1] at hx; simp at hx
  rw [h1, liftE_some] at hx
  simp only at hx
  have hf1 : formersW n m pp = some (r1, m1) := by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (blockShapeFormers_spec p hP.nck.alloc hP.nck.fieldCopy hP.nck.formers n _ pp) h1
    rw [← hs]; exact hW
  obtain ⟨hq', hq9, hptr⟩ := partsShapeFacts hq hsrc
  obtain ⟨hr1, hd1, hg1, hfr1, ht1, hroom1⟩ := formersW_dec hf1 hS.iw.iwSize hS.iw.ctl hq' hq9 hsrc
    (fun o l j v h1 h2 h3 h4 => by have := hptr o l j v h1 h2 h3 h4; omega)
  have hS1 : StageR vis fe m1 a := stage_frame_iw hS hfr1 hroom1
  have hA1 : AbsOK m1 := formersW_afr hf1 hA
  subst hr1
  simp only [List.headD_cons, List.tail_cons] at hx
  -- the shape's words
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hkT : (UInt64.ofNat bs.k : Word).toNat = bs.k := UInt64.toNat_ofNat_of_lt' hkb
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg1 hq hq9
  have hk1 : rdW (m1.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [rdW_iw_grow hg1 (by rw [UInt64.toNat_add]; simp; omega), hkw]
  rw [hnpw, hk1] at hx
  by_cases hk0 : (UInt64.ofNat bs.k : Word) = 0
  · simp only [hk0, ite_true] at hx; cases hx
  simp only [hk0, ite_false] at hx
  by_cases hov : UInt64.ofNat bs.nP + UInt64.ofNat bs.k < (UInt64.ofNat bs.nP : Word)
  · simp only [hov, ite_true] at hx; cases hx
  simp only [hov, ite_false] at hx
  -- the first former
  have hcv : PSlR decCVp bs.formers (rdW (m.arr64 CTL) 200) (UInt64.ofNat bs.k) m1 :=
    ⟨by rw [hkT]; exact decPLcv_decB hd1 (by omega), by rw [hkT]; omega⟩
  obtain ⟨pc, cv0, cvs, hfm, hw, hpb, hcv0, -⟩ := partsPSl_cons hcv hk0
  obtain ⟨htyl, htye⟩ := partsCVType hcv0 (UInt64.toNat_ofNat_of_lt' hpb)
  rw [hw, show rdW (m1.arr64 (tierA EREC ((UInt64.ofNat pc + 3 : Word) >>> 40)))
    ((UInt64.ofNat pc + 3 : Word) &&& 1099511627775) = erRd m1 (UInt64.ofNat pc + 3) from rfl] at hx
  -- `open_pis_at_fvars_f`
  rcases h2 : callW p n "open_pis_at_fvars_f" [UInt64.ofNat bs.nP, erRd m1 (UInt64.ofNat pc + 3), 0] m1
    with _ | ⟨r2, m2⟩
  · rw [h2] at hx; simp [bncE.k_open_pis_at_fvars_f] at hx
  rw [h2, liftE_some] at hx
  simp only [bncE.k_open_pis_at_fvars_f] at hx
  obtain ⟨x2, a2, hrun2, ⟨⟨hS2, hg2, hd2⟩, -⟩, hA2⟩ := opfSimRA hOpf htyl hS1 hA1 r2 m2 h2
  rw [htye, UInt64.toNat_ofNat_of_lt' hnpb, show (0 : Word).toNat = 0 from rfl] at hrun2
  have hk2 : rdW (m2.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [rdW_iw_grow hg2 (by have := hg1.iw; rw [UInt64.toNat_add]; simp; omega), hk1]
  rw [hk2] at hx
  cases x2 with
  | none =>
    have h0 : r2.headD 0 = 0 := hd2
    simp only [h0, ite_true] at hx; cases hx
  | some pq =>
  obtain ⟨fvs, body⟩ := pq
  obtain ⟨h21, hfv, -⟩ := hd2
  obtain ⟨hfd, hfb⟩ := hfv
  simp only [h21, show (1 : Word) ≠ 0 by decide, ite_false] at hx
  have g1 : r2.getD 1 0 = r2.tail.headD 0 := by rcases r2 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r2.getD (1 + 1) 0 = r2.tail.tail.headD 0 := by
    rcases r2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  by_cases hov2 : r2.tail.tail.headD 0 + UInt64.ofNat bs.k < r2.tail.tail.headD 0
  · simp only [hov2, ite_true] at hx; cases hx
  simp only [hov2, ite_false] at hx
  -- `block_shape_nest_ctx`
  rcases n with _ | n
  · simp [callW_zero, bncE.k_block_shape_nest_ctx] at hx
  rcases h3 : callW p (n + 1) "block_shape_nest_ctx" [pp, r2.tail.headD 0, r2.tail.tail.headD 0] m2
    with _ | ⟨r3, m3⟩
  · rw [h3] at hx; simp [bncE.k_block_shape_nest_ctx] at hx
  rw [h3, liftE_some] at hx
  simp only [bncE.k_block_shape_nest_ctx] at hx
  have hc3 : nckW n m2 pp (r2.tail.headD 0) (r2.tail.tail.headD 0) = some (r3, m3) := by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (nck_spec p hP.nck n _ pp (r2.tail.headD 0) (r2.tail.tail.headD 0)) h3
    rw [← hs]; exact hW
  have g12 := hg1.trans hg2
  obtain ⟨hok3, hd3, hS3, hg3, hin3, hsl3⟩ := nckW_ok n ⟨m2, Locals.init []⟩ ⟨m3, Locals.init []⟩ a2 dn vis
    fe pp (r2.tail.headD 0) (r2.tail.tail.headD 0) bs fvs hS2 (hq.grow (decBS_mono _) g12)
    (partsHsrc_grow g12 hq9 hsrc) hfd hfb r3 hc3
  have hA3 : AbsOK m3 := nckW_afr hc3 hA2
  have hrun3 := partsRunOfOk hok3
  generalize hc : AM.res (bs.nestCtx fvs) a2 = c at hrun3 hd3
  generalize ha3 : AM.st (bs.nestCtx fvs) a2 = a3 at hrun3 hS3
  have hnc : c.nP = bs.nP ∧ c.names = bs.memberNames ∧ c.params = fvs := by
    have h' : (bs.nestCtx fvs) a2 = .ok (c, a3) := hrun3
    unfold ConRon.Arena.BlockShape.nestCtx at h'
    obtain ⟨lv, a', -, h'⟩ := ConRon.Bridge.AM.bind_ok h'
    obtain ⟨rfl, -⟩ := ConRon.Bridge.AM.pure_ok h'
    exact ⟨rfl, rfl, rfl⟩
  have hpn : c.params.length + c.names.length < 2 ^ 64 := by
    have := L.toNat_add_of_not_lt hov2
    rw [hkT] at this
    have := (r2.tail.tail.headD 0 + UInt64.ofNat bs.k : Word).toNat_lt
    rw [hnc.2.2, hnc.2.1, decHL_length _ hfd]
    simp only [BlockShape.memberNames, List.length_map]
    have : bs.k = bs.members.length := rfl
    omega
  have hhi : c.hiAt 0 < 2 ^ 64 := by
    have := L.toNat_add_of_not_lt hov
    rw [UInt64.toNat_ofNat_of_lt' hnpb, hkT] at this
    have := (UInt64.ofNat bs.nP + UInt64.ofNat bs.k : Word).toNat_lt
    simp only [NestCtx.hiAt, hnc.1, hnc.2, BlockShape.memberNames, List.length_map]
    have : bs.k = bs.members.length := rfl
    omega
  -- `nest_holes`
  rcases h4 : callW p (n + 1) "nest_holes" [r3.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [h4] at hx; simp [bncE.k_nest_holes] at hx
  rw [h4, liftE_some] at hx
  simp only [bncE.k_nest_holes] at hx
  have hc4 : nhW n m3 (r3.headD 0) = some ([r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0], m4) := by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (nestHoles_spec p hP.nh n _ (r3.headD 0)) h4
    rw [← hs]; exact hW
  obtain ⟨holes, a4, hrun4, hR4, hS4, hg4⟩ := nhW_sim n hS3 (hd3.get (decCtx_mono _)) hin3 hsl3 hhi _ _ hc4
  have hA4 : AbsOK m4 := nhW_afr hc4 hA3
  cases holes with
  | none =>
    have h0 : r4.headD 0 = 0 := hR4
    simp only [h0, ite_true] at hx; cases hx
  | some hs =>
  obtain ⟨h41, hd4, hb4⟩ := hR4
  simp only [List.headD_cons, List.tail_cons] at h41 hd4 hb4
  simp only [h41, show (1 : Word) ≠ 0 by decide, ite_false, Except.ok.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  have hrun : (ConRon.Arena.blockNestCtx bs).run a = .ok ((c, hs), a4) := by
    unfold ConRon.Arena.blockNestCtx
    rw [hfm]
    simp only [unwrapOr, StateT.run_bind]
    simp only [StateT.run_pure, except_ok_bind, hrun2]
    simp only [pure_bind, except_ok_bind, hrun3, hrun4, StateT.run_pure]
    rfl
  obtain ⟨core, -⟩ := ConRon.Bridge.Inductives.blockNestCtx_spec fe henv bs bsP hT a a4 (c, hs) hC.check hdP hrun
  have hd34 := hd3.grow (decCtx_mono _) hg4
  refine ⟨(c, hs), a4, hrun, hC.of_cstep hS4 hA4 core, hA4, (g12.trans hg3).trans hg4, hd34,
    ⟨hd34.get (decCtx_mono _), (CtxIn.grow hin3 hg4).2, hsl3.grow hin3 hg4⟩, hd4, hb4, hhi, hpn⟩

/-- **`block_nest_ctx`'s contract** (`BncRefS`): `bnc_ok` through the call (every error of class
`0`: `bncE_cls`); the memos by `callW_indMemos` (`block_nest_ctx` is in `imFns`). -/
theorem bncRefS_of {p : Prog} {dn : NIdx → Option ConLeche.Name} (hP : PosBlkProg p) (hOpf : OpfF p)
    (hCrk : CrKeep p) (hl : IndLeaves p) : BncRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a pp bs bsP hB henv hqd hsl hdP hT
  have h : RefE (VerdictCtxU p) (bncE p n m pp) (ConRon.Arena.blockNestCtx bs) a
      (fun rm x a' => StageC dn vis fe env rm.2 a' ∧ AbsOK rm.2 ∧ IWGrow m rm.2 ∧
        DecB (fun m => decCtx m (rm.1.headD 0).toNat) rm.2 x.1 ∧
        UCtx dn vis fe rm.2 (rm.1.headD 0) x.1 ∧
        (decHL rm.2 (rm.1.tail.headD 0).toNat (rm.1.tail.tail.headD 0).toNat : Option (List EIdx)) =
          some x.2 ∧
        (rm.1.tail.headD 0).toNat + (rm.1.tail.tail.headD 0).toNat ≤ iwTop rm.2 ∧
        x.1.hiAt 0 < 2 ^ 64 ∧ x.1.params.length + x.1.names.length < 2 ^ 64) := by
    rcases hx : bncE p n m pp with e | ⟨r, m'⟩
    · exact RefE.of_cls0 (bncE_cls hx)
    · exact bnc_ok hP hOpf henv hB.c hB.abs hqd hsl hdP hT hx
  have h2 := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (bncE_spec p hP n _ pp) (fun hG => hG.nv) h
  refine RefE.callOk h2 fun ⟨r, m'⟩ x a' hc hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  obtain ⟨hC', hA', hg, hd, hU, hho, hhb, hhi, hpn⟩ := hR
  exact ⟨⟨hC', callW_indMemos hCrk.closed hl (im_mem _ rfl) (callW_of_callE hc) hB.ind, hA'⟩, hg, hd, hU,
    hho, hhb, hhi, hpn⟩

end L.Ind

end
