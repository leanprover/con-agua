import ConAgua.Verdict.IndBTmt
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinement of `target_major_of_outside` (lane `verdicts-b`, helper `ib`)

Mirrors `tmoW_simC` (`IndT/RecGenTmf`): the rejects are the twin's `fail`s (Quot, not a stored
inductive, too few arguments, the closedness test, the occurrence test); the tail's claim is
`tmoTail_claim`; every other callee is `closedNV`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmoE_spec (p : Prog) (hf : p.lookup "target_major_of_outside" = some targetMajorOfOutside)
  fns [hf ↦ tmoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hP : TmoOProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
  (hLC : LvlCacheProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) {env : ConLeche.Env}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hP hIlpf hcore hLC hnv in
/-- **`target_major_of_outside`'s model error claim** (`tmoW_simC`'s hypotheses). -/
theorem tmoE_claim (n : Nat) {m : Mem} {a : AState}
    {pp pfo pfl I us ao al mno mnl : Word} {bs : BlockShape} {pfvs args : List EIdx} {ws : List Word}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hq9 : pp.toNat + 9 ≤ iwTop m)
    (hws : SlR m mno mnl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hwsb : ∀ i < mnl.toNat, mno.toNat + i < iwTop m) (hnames : ws.map (fun w => (decI w : NIdx)) = bs.memberNames)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs) (hI : H I) (hus : H us) (hPm : PosMR m)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {IP : ConLeche.Name}
    (hIP : denoteN a.store.ns (decI I) = some IP) {usP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI us) = some usP) {argsP : List ConLeche.Expr}
    (hargsP : Frontend.denoteEList a.store args = some argsP) :
    ∀ e, tmoE p (n + 1) m vis pp pfo pfl I us ao al mno mnl = .error e →
      ErrClaim (tmoOutT fe bs pfvs args (decI I) (decI us)) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [tmoE.arm1] at he
  unfold tmoOutT
  -- `pin_at`
  cases h1 : callE p n "pin_at" [47] m with
  | error e1 =>
    rw [h1, tmoE.k_pin_at.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Arena.pinAt_specW p hP.pin n _ 47) (callW_of_callE h1)
  obtain ⟨hm1, hr1, hqH, hrun1⟩ := L.Arena.pinAtW_ok (a := a) hW1 hS.1.pins
  have hm1' : s1.mem = m := hm1
  simp only at hr1 hqH hrun1
  subst hs1
  subst hr1
  refine ErrClaim.bind_right hrun1 ?_
  rw [h1, hm1'] at he
  by_cases hIq : I = pinW m (1 + (47 : Word).toNat)
  · rw [tmoE.k_pin_at.abort1 p n vis pp pfo pfl I us ao al mno mnl [pinW m (1 + (47 : Word).toNat)] m hIq] at he
    cases he
    simp only [hIq, beq_self_eq_true, ite_true]
    exact ErrClaim.fail _ _ (by decide)
  rw [tmoE.k_pin_at.arm1 p n vis pp pfo pfl I us ao al mno mnl [pinW m (1 + (47 : Word).toNat)] m hIq] at he
  have hne : ((decI I : NIdx) == decI (pinW m (1 + (47 : Word).toNat))) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; rw [clsDecI_inj hI hqH]; exact hIq
  simp only [hne, Bool.false_eq_true, ite_false]
  -- `target_ctors_of`
  cases h2 : callE p n "target_ctors_of" [vis, I] m with
  | error e2 =>
    rw [h2, tmoE.k_target_ctors_of.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero =>
      obtain ⟨e', he', -⟩ := callE_zero p "target_ctors_of" [vis, I] m
      rw [h2] at he'; cases he'
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tco_spec p hP.nt hP.tco k _ vis I)
    (callW_of_callE h2)
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero => simp [ntWf, tcoPK] at hW2
    | succ k => exact ⟨k, rfl⟩
  rcases hnt : ntW k' m vis I with _ | y
  · rw [show ntWf (k' + 1) _ vis I = ntW k' _ vis I from rfl, hnt] at hW2; simp [tcoPK] at hW2
  obtain ⟨r, m'⟩ := y
  rw [show ntWf (k' + 1) _ vis I = ntW k' _ vis I from rfl, hnt, tcoPK_some] at hW2
  obtain ⟨rfl, hm'⟩ := Prod.mk.inj (Option.some.inj hW2)
  obtain ⟨x, a', hrun, hS2, hg2, hout⟩ := ntW_ok dn fe vis I hI k' m m' a r hnt hS
  have hf : MFr [] [] m m' := ntWf_mfr (k := k' + 1) (show ntWf (k' + 1) m vis I = some (r, m') from hnt)
  have hA2 : AbsOK m' := ntWf_afr (k := k' + 1) (show ntWf (k' + 1) m vis I = some (r, m') from hnt) hA
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.targetCtorsOf_spec (env := env) fe (decI I) IP a a' x
    hC.check.state ⟨hC.check.ienv.toS, hIP⟩ hrun
  have hC2 := hC.of_pstep hS2 hA2 p2
  have hm2 : m2 = m' := hs2.symm.trans hm'.symm
  rw [hm2] at h2
  have hP2 : PosMR m' := hPm.fr hf
  have hg2 : IWGrow m m' := hg2
  refine ErrClaim.bind_right hrun ?_
  rcases x with _ | ⟨nPc, cs⟩
  · have hz : r.headD 0 = 0 := by simpa [NcOut] using hout
    rw [h2, tmoE.k_target_ctors_of.abort1 p _ vis pp pfo pfl I us ao al mno mnl
      [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] _ (by simpa using hz)] at he
    cases he
    exact ErrClaim.fail _ _ (by decide)
  obtain ⟨h1, hnP, hcl, hcb, hcsat⟩ := hout
  have hne0 : r.headD 0 ≠ 0 := by rw [h1]; decide
  have hagT : decHL (truncM m) ao.toNat al.toNat = some args := hag
  have hal' := decHL_length _ hagT
  by_cases hal : al < r.tail.headD 0
  · rw [h2, tmoE.k_target_ctors_of.abort2 p _ vis pp pfo pfl I us ao al mno mnl
      [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] _ (by simpa using hne0)
      (by simpa using hal)] at he
    cases he
    have hlt : al.toNat < nPc := by have := UInt64.lt_iff_toNat_lt.mp hal; omega
    refine ErrClaim.ite_pos ?_ (ErrClaim.fail _ _ (by decide))
    simp only [bne_iff_ne, ne_eq, List.length_take]; omega
  rw [h2, tmoE.k_target_ctors_of.arm1 p _ vis pp pfo pfl I us ao al mno mnl
      [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] _ (by simpa using hne0)
      (by simpa using hal)] at he
  simp only [List.tail_cons, List.headD_cons] at he
  have hnal : nPc ≤ al.toNat := by
    have : ¬ al.toNat < (r.tail.headD 0).toNat := fun h => hal (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hlen : (args.take nPc).length = nPc := by simp; omega
  refine ErrClaim.ite_neg (by simp only [hlen, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]) ?_
  have hT2 : iwTop m' < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have htake : DecB (fun m => decHL m ao.toNat (r.tail.headD 0).toNat) m (args.take nPc) := by
    show decHL (truncM m) _ _ = _
    rw [hnP, decHL_take hagT _ hnal]
  have htake2 : decHL m' ao.toNat (r.tail.headD 0).toNat = some (args.take nPc) :=
    htake.stab (OMono.decHL _ _) m' hg2
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg2 hq hq9
  -- the closedness test
  cases h3 : callE p (k' + 1 + 1) "target_major_of_outside_closed"
      [ao, r.tail.headD 0, rdW (m'.arr64 IW) (pp + 4)] m' with
  | error e3 =>
    rw [h3, tmoE.k_target_major_of_outside_closed.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨m', Locals.init []⟩)
    (tmoc_spec p hP.bvb hP.hf hP.tmoc (k' + 1 + 1) _ ao (r.tail.headD 0) (rdW (m'.arr64 IW) (pp + 4)))
    (callW_of_callE h3)
  obtain ⟨b, a3, hrun3, hS3, hg3, hb3, -⟩ := ckc2W_ok dn fe vis (k' + 1 + 1) m' s3.mem a' _ ao _ _ r3 hW3 hS2 htake2
    (by have := hg2.1; omega) (by have := hg2.1; omega)
  rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb] at hrun3
  have hA3 : AbsOK s3.mem := ckc2W_afr _ _ _ _ _ _ _ hW3 hA2
  obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.allM_E_pstep (fun _ => True) (fun _ h => h)
    (fun e eP s₀ s' b hok _ he hrun => ConRon.Bridge.Inductives.RC.closed1_run hok he hrun)
    _ _ a' a3 b hC2.check.state trivial
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext p2.ext _ _ hargsP) nPc) hrun3
  refine ErrClaim.bind_right hrun3 ?_
  cases b
  · have hz : r3.headD 0 = 0 := by simpa using hb3
    rw [h3, tmoE.k_target_major_of_outside_closed.abort1 p _ vis pp pfo pfl I us ao mno mnl _ _ _ r3 m3 hz] at he
    cases he
    exact ErrClaim.ite_pos (by simp) (ErrClaim.fail _ _ (by decide))
  have h0 : r3.headD 0 ≠ 0 := by simpa using hb3
  rw [h3, tmoE.k_target_major_of_outside_closed.arm1 p _ vis pp pfo pfl I us ao mno mnl _ _ _ r3 m3 h0] at he
  refine ErrClaim.ite_neg (by simp) ?_
  subst hs3
  have hP3 : PosMR s3.mem := hP2.fr (ckc2W_mfr _ _ _ _ _ _ _ hW3)
  have hC3 := hC2.of_pstep hS3 hA3 p3
  have hg03 := hg2.trans hg3
  -- the occurrence test
  rw [← hnames]
  cases h4 : callE p (k' + 1 + 1) "target_major_of_outside_occ" [mno, mnl, ao, r.tail.headD 0] s3.mem with
  | error e4 =>
    rw [h4, tmoE.k_target_major_of_outside_occ.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (oc_spec p hP.occ (k' + 1 + 1) _ mno mnl ao (r.tail.headD 0)) (callW_of_callE h4)
  have hT3 : iwTop s3.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  obtain ⟨b, a4, hrun4, hb4, hS4', hg4', hP4'⟩ := ocW_sim hP.no mno mnl ws hwlt (k' + 1 + 1) s3.mem a3 ao _
    (args.take nPc) hS3 (slR_grow hg03 hT hws hwsb)
    (fun i hi => Nat.lt_of_lt_of_le (hwsb i hi) hg03.1) (htake.stab (OMono.decHL _ _) s3.mem hg03)
    (by have := hg03.1; omega) hP3 r4 s4.mem hW4
  have hA4 : AbsOK s4.mem := ocW_afr hP.no _ _ _ _ _ _ _ _ hW4 hA3
  have hx3 := (p2.trans p3).ext
  have hnm : Frontend.denoteNList a3.store.ns (ws.map (fun w => (decI w : NIdx))) = some pP.memberNames := by
    rw [hnames]; exact ConRon.Bridge.denoteNListE_ext hx3 _ _
      (ConRon.Bridge.Inductives.BlockShape.memberNames_spec hshP)
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.anyM_E_pstep
    (fun st => Frontend.denoteNList st.ns (ws.map (fun w => (decI w : NIdx))) = some pP.memberNames)
    (fun hx h => ConRon.Bridge.denoteNListE_ext hx _ _ h)
    (fun e eP s₀ s' b hok hq he hrun => ConRon.Bridge.Inductives.nestOcc_spec _ pP.memberNames 0 0 e eP
      s₀ s' b hok ⟨hq, he⟩ hrun)
    _ _ a3 a4 b hC3.check.state hnm
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx3 _ _ hargsP) nPc) hrun4
  refine ErrClaim.bind_right hrun4 ?_
  cases b
  · have hz : r4.headD 0 = 0 := by simpa using hb4
    rw [h4, tmoE.k_target_major_of_outside_occ.abort1 p _ vis pp pfo pfl I us ao _ _ _ r4 m4 hz] at he
    cases he
    exact ErrClaim.ite_neg (by simp) (ErrClaim.bind_left (ErrClaim.fail _ _ (by decide)))
  have h0 : r4.headD 0 ≠ 0 := by simpa using hb4
  rw [h4, tmoE.k_target_major_of_outside_occ.arm1 p _ vis pp pfo pfl I us ao _ _ _ r4 m4 h0] at he
  refine ErrClaim.ite_pos (by simp) ?_
  subst hs4
  have hC4 := hC3.of_pstep hS4' hA4 p4
  have hg04 := hg03.trans hg4'
  have hx4 := (p2.trans (p3.trans p4)).ext
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  have hcsd := csAt_decB hcsat hcb
  rw [← hcl] at hcsd
  -- the tail
  cases h5 : callE p (k' + 1 + 1) "target_major_of_outside_tail"
      [vis, pp, pfo, pfl, I, us, ao, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] s4.mem with
  | error e5 =>
    rw [h5, tmoE.k_target_major_of_outside_tail.none] at he
    cases he
    subst hnP
    exact CoreSpecE.of_callE (tmoTail_claim hP.tmt hIlpf hcore hLC hnv (k' + 1 + 1) ⟨s4.mem, Locals.init []⟩ a4
      pp pfo pfl I us ao _ _ _ bs pfvs (args.take (r.tail.headD 0).toNat) cs hC4 hA4
      (hq.grow (decBS_mono _) hg04) (by show _ ≤ iwTop s4.mem; have := hg04.1; omega) hI hus
      (htake.grow (OMono.decHL _ _) hg04) (by have := hagb; omega)
      (hcsd.grow (OMono.decPL decCN_mono _ _) (hg3.trans hg4')) (hpf.grow (OMono.decHL _ _) hg04) hP4'
      (ConRon.Bridge.denoteN_ext hIP hx4) (ConRon.Bridge.denoteLs_ext husP hx4)
      (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx4 _ _ hargsP) _)
      (ConRon.Bridge.denoteL_ext hsP hx4)) h5
  | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, tmoE.k_target_major_of_outside_tail.arm1] at he
    cases he

include hP hIlpf hcore hLC hnv in
/-- **`target_major_of_outside`'s error claim** (every fuel; `tmoW_simC`'s hypotheses). -/
theorem tmo_claim (N : Nat) {s₀ : St} {a : AState}
    {pp pfo pfl I us ao al mno mnl : Word} {bs : BlockShape} {pfvs args : List EIdx} {ws : List Word}
    (hS : StageR dn vis fe s₀.mem a) (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hq9 : pp.toNat + 9 ≤ iwTop s₀.mem)
    (hws : SlR s₀.mem mno mnl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hwsb : ∀ i < mnl.toNat, mno.toNat + i < iwTop s₀.mem) (hnames : ws.map (fun w => (decI w : NIdx)) = bs.memberNames)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) s₀.mem args) (hagb : ao.toNat + al.toNat ≤ iwTop s₀.mem)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs) (hI : H I) (hus : H us) (hPm : PosMR s₀.mem)
    (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {IP : ConLeche.Name}
    (hIP : denoteN a.store.ns (decI I) = some IP) {usP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI us) = some usP) {argsP : List ConLeche.Expr}
    (hargsP : Frontend.denoteEList a.store args = some argsP) :
    CoreSpecE p N "target_major_of_outside" [vis, pp, pfo, pfl, I, us, ao, al, mno, mnl]
      (tmoOutT fe bs pfvs args (decI I) (decI us)) s₀ a := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tmoE_claim hP hIlpf hcore hLC hnv n hS hq hq9 hws hwlt hwsb hnames hag hagb hpf hI hus hPm hC hA
      hshP hIP husP hargsP e
      (triple_of_callE_err (tmoE_spec p hP.out (n + 1) s₀ vis pp pfo pfl I us ao al mno mnl) hc
        (Err.code_ne_of_cls hk0))

end sims

end L.Ind
