import ConAgua.Verdict.DeclValE
import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosE3Cm
import ConAgua.Arena.IndT.PosOne

/-!
# `nest_ctors_crest`'s and `nest_ctors_one`'s error claims (lane `verdicts-b`, helper `ia2`,
fork `kn2b`)

`crestE_claim`: `p2ctW_okC`'s proof (`PosCrest.lean`) on the error model `ncrE`, the claim on the
fragment `oneK` (whatever its continuation): the duplicate level parameters and the crest not
binding the parameters reject as the twin does, the crest's type and its sort are the core stubs'
claims (`CoreStubsE`); the other callees are outside the verdict closure.
`oneOKE_step`: `oneOKC_step`'s proof on `noE`: the crest's error by `crestE_claim`, the walk's by the
block's `WalkOKE` at `n`, the later-use (U4) and result-head sites as the twin's `fail`s.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section crest
variable {p : Prog} (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include L hq hIlpf hnv hcE henv in
/-- **`nest_ctors_crest`'s error claim**: the fragment `oneK` fails, whatever comes after the crest. -/
theorem crestE_claim {k : Nat} (hn : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    {no nl us dO dL hO hL cv hi : Word} {names : List NIdx}
    {ds holes : List EIdx} {cvv : IConstantVal} {e : Err}
    (he : callE p k "nest_ctors_crest" [vis, no, nl, us, dO, dL, hO, hL, cv, hi] m = .error e)
    (hC : StageC dn vis fe env m a)
    (hus : H us) (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hnn : dL.toNat + names.length < 2 ^ 64)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hcv : decCVp m cv.toNat = some cvv) (hcv3 : cv.toNat + 3 < 2 ^ 64) (hP : PosMR m) (hA : AbsOK m)
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {namesP : List ConLeche.Name}
    {holesP : List ConLeche.Expr} {cvP : ConLeche.ConstantVal}
    (hpre : CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hcl : cvP.type.hasFvar = false)
    (c : NestCtx) (fu : Nat) (prog : List NestHole) (root : Bool) (nF : Nat) (NS : NestState) {β : Type}
    (K : List NestFieldKind × EIdx → NestState → AM β) :
    ErrClaim (oneK V fe c fu prog root hi.toNat (decI us) ds names holes cvv nF NS K) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (ncrE_spec p L.ct.hp k ⟨m, Locals.init []⟩ vis no nl us dO dL hO hL cv hi)
    he (Err.code_ne_of_cls hk0)
  simp only at he
  have hS := hC.stage
  cases k with
  | zero => rw [ncrE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ k =>
  rw [ncrE.arm1] at he
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hcvn, hcvl, hcvt⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  -- the level parameters
  cases c1 : callE p k "cv_lps" [cv] m with
  | error e1 =>
    rw [c1, ncrE.k_cv_lps.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hlp⟩ := triple_of_callW (cvLps_spec p L.ct.ha L.ct.hc L.ct.he L.ct.hcv k ⟨m, Locals.init []⟩ cv)
    (callW_of_callE c1)
  simp only at hlp
  rw [hs1] at hlp
  rw [c1, ncrE.k_cv_lps.arm1] at he
  obtain ⟨hS1, hg1, hE1, hdec1, ht1⟩ := pos2_cvLpsW_stage hlp hS hcv hcv3
  have hA1 : AbsOK m1 := erToIwW_afr (show erToIwW _ m _ _ = some (r1, m1) from hlp) hA
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨ws, hws, hwsd, hwH⟩ := slR_of_decHL m1 _ _ _ hdec1 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  -- the duplicate check
  cases c2 : callE p k "sl_nodup" [r1.headD 0, r1.tail.headD 0] m1 with
  | error e2 =>
    rw [c2, ncrE.k_sl_nodup.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c2
  | ok q2 =>
  obtain ⟨r2, m2'⟩ := q2
  obtain ⟨s2, hs2, -, hm2, hnd⟩ := triple_of_callW (slNodup_spec p L.ct.hsc L.ct.hnd k ⟨m1, Locals.init []⟩ _ _)
    (callW_of_callE c2)
  simp only at hm2 hnd
  have hm2' : m1 = m2' := by rw [← hs2, hm2]
  subst hm2'
  rw [c2] at he
  have hb := nodupW_ok k m1 _ _ _ ws hws hnd
  by_cases hb0 : r2.headD 0 = 0
  · rw [ncrE.k_sl_nodup.abort1 p k vis no nl us dO dL hO hL cv hi _ _ r2 m1 hb0] at he; cases he
    have hnod : nameNodup cvv.levelParams = false := by
      rw [hwsd, nameNodup_map ws hwH]
      by_cases hn : ws.Nodup
      · rw [ite_eq_left hn] at hb; rw [hb] at hb0; exact absurd hb0 (by decide)
      · simp [hn]
    simp only [oneK, hnod, Bool.not_false, ite_true]
    exact ErrClaim.fail _ _ (by decide)
  rw [ncrE.k_sl_nodup.arm1 p k vis no nl us dO dL hO hL cv hi _ _ r2 m1 hb0] at he
  have hnod : nameNodup cvv.levelParams = true := by
    rw [hwsd, nameNodup_map ws hwH]
    by_cases hn : ws.Nodup
    · simp [hn]
    · rw [ite_eq_right hn] at hb; exact absurd hb hb0
  simp only [oneK, hnod, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the instantiated type
  obtain ⟨-, -, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have e3 : (cv + 3).toNat = cv.toNat + 3 := word_add_toNat (by simp; omega)
  have hrdt : rdW (m1.arr64 EREC) (cv + 3) = wt := by
    rw [hE1]; simp only [erA] at hwt; simp [rdW, e3, hwt]
  rw [hrdt] at he
  cases c3 : callE p k "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, us, wt] m1 with
  | error e3 =>
    rw [c3, ncrE.k_inst_lp_fast.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c3
  | ok q3 =>
  obtain ⟨r2, m2⟩ := q3
  rw [c3, ncrE.k_inst_lp_fast.arm1] at he
  have hil : realCall p k "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, us, wt] m1 = some (r2, m2) :=
    callW_of_callE c3
  obtain ⟨cty, a1, hrun1, ⟨hS2, hg2, hcH, hcd⟩, ⟨A2, C2, hA2s, hC2s, hfr2⟩, hAF2⟩ :=
    IlpRd.realC hIlpf hC k CWF _ _ _ _ cvv.levelParams m1 m2 a r2 hus hwtH ⟨rfl, erToIwW_iwFr hlp⟩ hS1 hdec1 hil
  rw [CWF_eq, ← hwtd] at hrun1
  have hA2 : AbsOK m2 := hAF2 hA1
  obtain ⟨c1', hctyP⟩ := ConRon.Bridge.Inductives.instLPFast_cstep hC.check hcvl hpre.hus hcvt hrun1
  have hC2 : StageC dn vis fe env m2 a1 := hC.of_cstep hS2 hA2 c1'
  refine ErrClaim.bind_right hrun1 ?_
  -- the crest
  have hg12 := hg1.trans hg2
  cases c4 : callE p k "nest_crest" [no, nl, us, dO, dL, hO, hL, r2.headD 0] m2 with
  | error e4 =>
    rw [c4, ncrE.k_nest_crest.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨r3, m3⟩ := q4
  obtain ⟨s4, hs4, -, hpc0⟩ := triple_of_callW (nestCrest_spec' p L.ct.cr k ⟨m2, Locals.init []⟩ no nl us dO dL hO hL
    (r2.headD 0)) (callW_of_callE c4)
  simp only at hpc0
  rw [hs4] at hpc0
  rw [c4] at he
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
  obtain ⟨x, a2, hrun2, hx, ⟨M', G', hS3, hg3, hR3, -⟩, hM3⟩ := pcrW_ok dn fe vis k m2 m3 a1 no nl us dO dL hO hL
    (r2.headD 0) r3 names ds holes M G g hpc0 hS2 hcH hus
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hdec) (by omega)
    (by have := hg12.1; omega) hnn mp2 hM2
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hds) (by have := hg12.1; omega)
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hho) (by have := hg12.1; omega) hR
  rw [hcd] at hrun2
  have hA3 : AbsOK m3 := pcrW_afr hpc0 hA2
  obtain ⟨p2, ho⟩ := ConRon.Bridge.Inductives.nestCrest_spec names namesP (decI us) usP ds dsP holes holesP cty _
    a1 a2 x hC2.check.state hC2.check.pins
    ⟨ConRon.Bridge.denoteNListE_ext c1'.ext _ _ hpre.hnames, ConRon.Bridge.denoteLs_ext hpre.hus c1'.ext,
      ConRon.Bridge.denoteEList_ext c1'.ext _ _ hpre.hds, ConRon.Bridge.denoteEList_ext c1'.ext _ _ hpre.hholes,
      hctyP⟩ hrun2
  refine ErrClaim.bind_right hrun2 ?_
  cases x with
  | none =>
    simp only [decOE] at hx
    rw [ncrE.k_nest_crest.abort1 p _ vis hi r3 m3 hx] at he; cases he
    exact ErrClaim.fail _ _ (by decide)
  | some crest =>
  obtain ⟨hx1, hxH, hxd⟩ := hx
  rw [ncrE.k_nest_crest.arm1 p _ vis hi r3 m3 (by rw [hx1]; decide)] at he
  obtain ⟨crestP, hcrestP, hcrest⟩ := ho
  have hwc : ConLeche.Expr.WScoped hi.toNat crestP :=
    ConLeche.WScoped_nestCrest (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl) hpre.hlen
      (fun y hy => (List.mem_append.mp hy).elim (hpre.wds y) (hpre.wholes y)) hcrestP
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 p2
  have hxH' : H (r3.tail.headD 0) := by simpa using hxH
  have hxd' : decI (r3.tail.headD 0) = crest := by simpa [decE_eq] using hxd
  -- its type
  cases c5 : callE p (k + 1 + 1 + 1) "infer_type_core" [vis, hi, r3.tail.headD 0] m3 with
  | error e5 =>
    rw [c5, ncrE.k_infer_type_core.none] at he; cases he
    have h5 := hcE.inferTypeCore (k + 1 + 1 + 1) (by omega) hC3.stageT hi (r3.tail.headD 0) hxH' _ c5
    rw [hxd'] at h5
    exact ErrClaim.bind_left h5
  | ok q5 =>
  obtain ⟨r4, m4⟩ := q5
  rw [c5, ncrE.k_infer_type_core.arm1] at he
  obtain ⟨ty, a3, hrun3, hC4, hg4, hdec4, hA4, c4', tyP, htyP, hwty⟩ :=
    inferC_rsim hq henv (k + 1 + 1 + 1) (by omega) hC3 hA3 hi (r3.tail.headD 0) hxH'
      (by rw [hxd']; exact hcrest) hwc _ (callW_of_callE c5)
  obtain ⟨htyH, htyd⟩ := hdec4
  rw [hxd'] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  -- its sort
  cases c6 : callE p (k + 1 + 1 + 1) "ensure_sort_core" [vis, hi, r4.headD 0] m4 with
  | error e6 =>
    rw [c6, ncrE.k_ensure_sort_core.none] at he; cases he
    have h6 := hcE.ensureSortCore (k + 1 + 1 + 1) (by omega) hC4.stageT hi (r4.headD 0) htyH _ c6
    rw [htyd] at h6
    exact ErrClaim.bind_left h6
  | ok q6 =>
    obtain ⟨r5, m5⟩ := q6
    rw [c6, ncrE.k_ensure_sort_core.arm1] at he; cases he

end crest

/-- A twin run equal to another's, from another state. -/
theorem ErrClaim.of_runEq2 {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    {x : Except CheckError (α × AState)} (h : T.run a = x) (h2 : ∀ ce, T'.run a' = .error ce → x = .error ce)
    (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, by rw [h]; exact h2 ce hce, hc⟩

section one
variable {p : Prog} (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include L hq hIlpf hnv hcE henv in
theorem oneOKE_step (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (ihC : NbOKC p dn vis fe env n)
    (ihE : NbOKE p dn vis fe env n) : OneOKE p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hWalk, -⟩ := ihC
  obtain ⟨-, -, -, -, -, -, -, -, -, hWalkE, -⟩ := ihE
  have hSp := nbSpec_all L (realCall p) (realCall_spec p) n
  intro m a ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS ctxP progP
    usP dsP namesP holesP cvP nsP hC hW hCc hcv hcv3 hns hP hA hc hctx hprog hpre hcvP hcl hnsP e he β K
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (noE_spec p L.pone (n + 1) ⟨m, Locals.init []⟩ vis ctx root fu po pl hi us dO dL
    no nl hO hL cv nF ns) he (Err.code_ne_of_cls hk0)
  simp only at he
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [noE.arm1] at he
  -- the crest, typed
  cases c1 : callE p n "nest_ctors_crest" [vis, no, nl, us, dO, dL, hO, hL, cv, hi] m with
  | error e1 =>
    rw [c1, noE.k_nest_ctors_crest.none] at he; cases he
    exact crestE_claim L hq hIlpf hnv hcE dn vis fe henv (by omega) c1 hC hCc.hus hCc.hnames hCc.hnamesb hCc.hnn
      (hCc.hds.get (OMono.decHL _ _)) hCc.hdsb hCc.hholes hCc.hholesb ((erecP_ext m).decCV hcv) hcv3 hP hA hpre
      hcvP hcl c fu.toNat prog (decide (root ≠ 0)) nF.toNat NS K
  | ok q1 =>
  obtain ⟨rc0, m1⟩ := q1
  obtain ⟨s1, hs1, -, hct⟩ := triple_of_callW (nestCtorsCrest_spec p L.ct (realCall p) (realCall_spec p) n
    ⟨m, Locals.init []⟩ vis no nl us dO dL hO hL cv hi) (callW_of_callE c1)
  simp only at hct
  rw [hs1] at hct
  rw [c1, noE.k_nest_ctors_crest.arm1] at he
  obtain ⟨cty, a1, crest, a2, ty, a3, so, a4, hnod, hrun1, hrun2, hrun3, hrun4, hC1, hg1, hcrH, hcrd, hP1, hA1, c1',
      crestP, hcrP, hwc⟩ :=
    p2ctW_okC hq hIlpf dn vis fe henv (by omega) hct hC hCc.hus hCc.hnames hCc.hnamesb hCc.hnn
      (hCc.hds.get (OMono.decHL _ _)) hCc.hdsb hCc.hholes hCc.hholesb ((erecP_ext m).decCV hcv) hcv3 hP hA hpre
      hcvP hcl
  simp only [List.headD_cons] at hcrH hcrd
  have hS1 := hC1.stage
  simp only [oneK, hnod, Bool.not_true, Bool.false_eq_true, ite_false]
  refine ErrClaim.bind_right hrun1 (ErrClaim.bind_right hrun2 ?_)
  refine ErrClaim.bind_right hrun3 (ErrClaim.bind_right hrun4 ?_)
  rw [← hcrd]
  -- the walk
  cases c2 : callE p n "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, rc0.headD 0, ns] m1 with
  | error e2 =>
    rw [c2, noE.k_nest_ctors_walk.none] at he; cases he
    exact hWalkE m1 a4 ctx root fu po pl hi nF (rc0.headD 0) ns c prog NS ctxP progP crestP nsP hC1 (hW.grow hg1)
      hcrH (hns.grow hg1 htop) hP1 hA1 hc (dCtx_ext _ c1'.ext _ _ hctx) (dProg_ext c1'.ext _ _ hprog)
      (by rw [hcrd]; exact hcrP) (dState_ext c1'.ext _ _ hnsP) hwc _ c2 _
  | ok q2 =>
  obtain ⟨rw, m2⟩ := q2
  obtain ⟨s2, hs2, -, hwk⟩ := triple_of_callW (hSp.2.2.2.2.2.2.2.2.2.1 ⟨m1, Locals.init []⟩ vis ctx root fu po pl hi
    nF (rc0.headD 0) ns) (callW_of_callE c2)
  simp only at hwk
  rw [hs2] at hwk
  rw [c2, noE.k_nest_ctors_walk.arm1] at he
  obtain ⟨ks, nds, cur, ns2, closed, a5, hW5, hC2, hg2, hks, hksb, hksl, hcurH, hcurd, hclH, hcld, hns2, hP2, hA2,
      c2', ndsP, curP, nsP2, hndsP, hcurP, hns2P, hclP, hwnds, hwcur⟩ :=
    hWalk m1 m2 a4 ctx root fu po pl hi nF (rc0.headD 0) ns c prog NS _ ctxP progP crestP nsP hwk hC1 (hW.grow hg1)
      hcrH (hns.grow hg1 htop) hP1 hA1 hc (dCtx_ext _ c1'.ext _ _ hctx) (dProg_ext c1'.ext _ _ hprog)
      (by rw [hcrd]; exact hcrP) (dState_ext c1'.ext _ _ hnsP) hwc
  simp only [List.headD_cons, List.tail_cons] at hks hksb hcurH hcurd hclH hcld hns2
  have hS2 := hC2.stage
  refine ErrClaim.of_runEq2 (hW5 _) (fun ce h => h) ?_
  -- U4
  have hkl : (rw.tail.headD 0).toNat = nF.toNat := by rw [← hks.length, hksl]
  have hksT : decKL (truncM m2) (rw.headD 0).toNat nF.toNat = some ks := by rw [← hkl]; exact hks
  cases c3 : callE p n "nest_ctors_u4" [rw.headD 0, nF, rw.tail.tail.tail.headD 0, 0] m2 with
  | error e3 =>
    rw [c3, noE.k_nest_ctors_u4.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c3
  | ok q3 =>
  obtain ⟨ru0, m3⟩ := q3
  obtain ⟨s3, hs3, -, hu⟩ := triple_of_callW (nestCtorsU4_spec p L.usl L.hu4 n ⟨m2, Locals.init []⟩ _ _ _ _)
    (callW_of_callE c3)
  simp only at hu
  rw [hs3] at hu
  rw [c3] at he
  obtain ⟨bu, a6, hrun6, hS3, hg3, hru, hP3⟩ := u4W_ok dn vis fe (m0 := m2) _ nF _ ks hclH hksT n m2 m3 a5 0 _
    hu hS2 (IWGrow.refl _) (by simp) hP2
  have hA3 := u4W_afr _ _ _ _ _ _ _ _ hu hA2
  have p6 : PStep a5 a6 := u4_pstep _ hC2.check.state (by rw [hcld]; exact hclP) hrun6
  have hr6 : ((List.range nF.toNat).anyM (u4F ks closed)).run a5 = .ok (bu, a6) := by
    rw [List.range_eq_range', ← hcld]; simpa using hrun6
  simp only [List.headD_cons] at hru
  refine ErrClaim.bind_right hr6 ?_
  cases bu with
  | true =>
    rw [noE.k_nest_ctors_u4.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hru]; decide)] at he; cases he
    simp only [ite_true]
    exact ErrClaim.fail _ _ (by decide)
  | false =>
  rw [noE.k_nest_ctors_u4.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hru]; decide)] at he
  simp only [Bool.false_eq_true, ite_false]
  -- the result's head
  have hU3 := (((hW.grow hg1).grow hg2).grow hg3).u
  cases c4 : callE p n "nest_ctors_res_ok" [ctx, hi, rw.tail.tail.headD 0] m3 with
  | error e4 =>
    rw [c4, noE.k_nest_ctors_res_ok.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨rr0, m4⟩ := q4
  obtain ⟨s4, hs4, -, hro⟩ := triple_of_callW (nestCtorsResOk_spec p L.nit.no L.nit.hoa L.hrh L.nt.ad L.hro n
    ⟨m3, Locals.init []⟩ ctx hi _) (callW_of_callE c4)
  simp only at hro
  rw [hs4] at hro
  rw [c4] at he
  obtain ⟨bo, a7, hrun7, hS4, hg4, hrr, hP4⟩ := roW_ok dn vis fe hro hS3 hU3 hcurH hP3
  simp only [List.headD_cons] at hrr
  rw [hcurd] at hrun7
  refine ErrClaim.of_runEq2 (hrun7 _) (fun ce h => h) ?_
  cases bo with
  | false =>
    rw [noE.k_nest_ctors_res_ok.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hrr]; rfl)] at he; cases he
    simp only [Bool.not_false, ite_true]
    exact ErrClaim.fail _ _ (by decide)
  | true =>
  rw [noE.k_nest_ctors_res_ok.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hrr]; decide)] at he
  -- the rest: outside the verdict closure
  cases c5 : callE p n "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, rw.tail.tail.tail.headD 0] m4 with
  | error e5 =>
    rw [c5, noE.k_nest_ctor_nf.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, noE.k_nest_ctor_nf.arm1] at he
  cases c6 : callE p n "sl_snoc" [rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 4),
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 5), r5.headD 0] m5 with
  | error e6 =>
    rw [c6, noE.k_sl_snoc.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, noE.k_sl_snoc.arm1] at he
  cases c7 : callE p n "rec6" [rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0),
      rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 1), rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 2),
      rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 3), r6.headD 0, r6.tail.headD 0] m6 with
  | error e7 =>
    rw [c7, noE.k_rec6.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c7
  | ok q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [c7, noE.k_rec6.arm1] at he; cases he

end one

end L.Ind
