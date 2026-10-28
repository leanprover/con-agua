import ConAgua.Verdict.DeclValE
import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosE3Cm
import ConAgua.Arena.IndT.PosOne
/-!
# `nest_ctors_one`'s error claim

`oneOKE_step`: `oneOKC_step`'s proof on `noE`: the crest's error by `crest_ref` (`PosCrest.lean`,
its error half), the walk's by the block's `WalkOKE` at `n`, the later-use (U4) and result-head
sites as the twin's `fail`s.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

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
    rw [oneK_eq]
    exact ErrClaim.bind_left (RefE.run_err (ncrE_spec p L.ct n ⟨m, Locals.init []⟩ vis no nl us dO dL hO hL cv hi)
      hnv ⟨hnv, hcE⟩ (crest_ref hq hIlpf dn vis fe henv (by omega) hC hCc.hus hCc.hnames hCc.hnamesb hCc.hnn
        (hCc.hds.get (OMono.decHL _ _)) hCc.hdsb hCc.hholes hCc.hholesb ((erecP_ext m).decCV hcv) hcv3 hP hA hpre
        hcvP hcl) c1)
  | ok q1 =>
  obtain ⟨rc0, m1⟩ := q1
  rw [c1, noE.k_nest_ctors_crest.arm1] at he
  obtain ⟨s1, hs1, -, crest, a4, hcr, hR1⟩ := RefE.run_ok (ncrE_spec p L.ct n ⟨m, Locals.init []⟩ vis no nl us dO dL
      hO hL cv hi)
    (crest_ref hq hIlpf dn vis fe henv (by omega) hC hCc.hus hCc.hnames hCc.hnamesb hCc.hnn
      (hCc.hds.get (OMono.decHL _ _)) hCc.hdsb hCc.hholes hCc.hholesb ((erecP_ext m).decCV hcv) hcv3 hP hA hpre
      hcvP hcl) c1
  rw [hs1] at hR1; dsimp only at hR1
  obtain ⟨hC1, hg1, hcrH, hcrd, hP1, hA1, c1', crestP, hcrP, hwc⟩ := hR1
  have hS1 := hC1.stage
  rw [oneK_eq]
  refine ErrClaim.bind_right hcr ?_
  unfold oneRest
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
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c3
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
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c4
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
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, noE.k_nest_ctor_nf.arm1] at he
  cases c6 : callE p n "sl_snoc" [rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 4),
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 5), r5.headD 0] m5 with
  | error e6 =>
    rw [c6, noE.k_sl_snoc.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, noE.k_sl_snoc.arm1] at he
  cases c7 : callE p n "rec6" [rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0),
      rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 1), rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 2),
      rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 3), r6.headD 0, r6.tail.headD 0] m6 with
  | error e7 =>
    rw [c7, noE.k_rec6.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c7
  | ok q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [c7, noE.k_rec6.arm1] at he; cases he

end one

end L.Ind
