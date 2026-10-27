import ConAgua.Verdict.IndBAgree
import ConAgua.Verdict.IndBRec1
import ConAgua.Verdict.IndBFields
import ConAgua.Arena.IndT.RecGen27
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
set_option linter.unusedSectionVars false

/-!
# Error refinement of `class_ctor_of` (lane `verdicts-b`, helper `ib`)

The non-`closedNV` callees are `class_minor_slot`, `class_fields_of`, `class_fields_agree` (their
claims); the aborts are code `0`. The twin side transcribes `cxoW_okC`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cxoE_spec (p : Prog) (hf : p.lookup "class_ctor_of" = some classCtorOfL)
  fns [hf ↦ cxoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section rel
variable {p : Prog} (hq : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CxoProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) {vis : Word} (hTka : TkaE p dn vis fe env)
include hq henv P hIlpf hOpf hnv hTka

/-- **`class_ctor_of`'s model error claim** (`cxoW_okC`'s hypotheses; the model at fuel `n + 1`). -/
theorem cxoE_claim (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {m : Mem} {a : AState} {q fto ftl rd mo ml c cA : Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cA' : IConstantVal × Nat}
    (hC : StageC dn vis fe env m a)
    (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcA : DecB (fun m => decCN m cA.toNat) m cA') (_hlp : CtorLp m cA) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {cAP : ConLeche.ConstantVal × Nat}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) (hcAP : ConRon.Bridge.Inductives.dCtor a.store cA' = some cAP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ∀ e, cxoE p (n + 1) m vis q fto ftl rd mo ml c cA = .error e →
      ErrClaim (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hcAP
  obtain ⟨cvP, hcvP, rfl⟩ := hcAP
  have hname := ConRon.Bridge.denoteCV_name hcvP
  have hbsD : DecB (fun m => decBS m q.toNat) m bs := hbs.1
  have hq9 : q.toNat + 9 ≤ iwTop m := by have := hbs.ptop; omega
  have hq64 := hS.lt64 hq9
  rw [cxoE.arm1] at he
  -- `target_major_at`
  cases h1 : callE p n "target_major_at" [mo, ml, c] m with
  | error e1 =>
    rw [h1, cxoE.k_target_major_at.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cxoE.k_target_major_at.arm1] at he
  obtain ⟨s1, rfl, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetMajorAt_spec p P.ha P.pw P.mtm P.tmd P.tma P.na n _ mo ml c) (callW_of_callE h1)
  obtain ⟨tm, a1, run1, hS1, hg1, hTM⟩ := rec3TMA_sim dn vis fe n m a mo ml c ms hS hms hmsb _ hw1
  dsimp only at hS1 hg1 hTM
  have hP1 := hP.fr (tmaW_mfr hw1)
  have hA1 := tmaW_afr hw1 hA
  obtain ⟨q1, hmP⟩ := ConRon.Bridge.Inductives.targetMajorAt_spec ms MsP c.toNat a a1 tm hC.check.state
    hC.check.pins hmsP run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  obtain ⟨-, -, hmdsP, -, -, -, -, hnfsP, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hmP
  have hk1 := callW_keepW (callW_of_callE h1)
  have hsz1 := hS1.2.2.2.1
  obtain ⟨⟨no, nl, h9, h10, hno, hnl, hnfs⟩, hds, hmw13⟩ := decTM_slices hTM hsz1
  obtain ⟨ca, hca, hca3, hcv, hnmH, hnmD, hnF, hnFb, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg1) hsz1
  obtain ⟨cam, hcam, hca3m, -, -, -, -, -, hcAt⟩ := decCN_words hcA hsz
  rw [h9, h10, hca] at he
  refine ErrClaim.bind_right run1 ?_
  -- `class_ctor_of_nfs`
  cases h2 : callE p n "class_ctor_of_nfs" [UInt64.ofNat no, UInt64.ofNat nl,
      rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca)] s1.mem with
  | error e2 =>
    rw [h2, cxoE.k_class_ctor_of_nfs.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
    cases n with
    | zero =>
      obtain ⟨e', he', -⟩ := callE_zero p "class_ctor_of_nfs" [UInt64.ofNat no, UInt64.ofNat nl,
        rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca)] s1.mem
      rw [h2] at he'; cases he'
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (cnf_spec p P.ha P.cnf n _ (UInt64.ofNat no) (UInt64.ofNat nl) (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca)))
    (callW_of_callE h2)
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hf2, hes⟩ := cnfF_ok _ _ _ tm.nfs n hw2 hS1 (by
    rw [UInt64.toNat_ofNat_of_lt' hno, UInt64.toNat_ofNat_of_lt' hnl]; exact hnfs) hnmH
  rw [hnmD] at hes
  have hP2 := hP1.fr hf2
  have hA2 := cnfF_afr hw2 hA1
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  have hk2 := callW_keepW (callW_of_callE h2)
  have hg12 := hg1.trans hg2
  by_cases hel : r2.tail.headD 0 = 0
  · rw [h2, cxoE.k_class_ctor_of_nfs.abort1 p (n + 1) vis q fto ftl rd mo ml c cA _ _ r2 _ hel] at he
    cases he
    exact absurd (by decide) hk0
  rw [h2, cxoE.k_class_ctor_of_nfs.arm1 p (n + 1) vis q fto ftl rd mo ml c cA _ _ r2 _ hel] at he
  obtain ⟨e0', es', hes_eq, he0, -⟩ := hes.uncons hel hS2.2.2.2.1
  rw [hes_eq] at hes
  have hEP := ConRon.Bridge.Inductives.filter_nfs hC1.check.state.wf
    (ConRon.Bridge.denoteN_ext hname q1.ext) _ _ hnfsP
  rw [hes_eq] at hEP
  obtain ⟨e0P, EsP', hEsP, he0P, hEsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hEP
  rw [hEsP] at hEP
  have he0ty := (ConRon.Bridge.Inductives.RC.dCtorNf_inv he0P).2.2.2
  have hsz2 := hS2.2.2.2.1
  generalize hE0 : rdW (s2.mem.arr64 IW) (r2.headD 0) = e0w at he he0
  obtain ⟨htyH, htyD⟩ := decNCN_ty he0 hsz2
  have hca64 : ca < 2 ^ 64 := by
    have := (rdW (s1.mem.arr64 CTL) 129).toNat_lt; simp only [erTop] at hca3; omega
  have hcaT : (UInt64.ofNat ca : Word).toNat = ca := UInt64.toNat_ofNat_of_lt' hca64
  have hcaeq : cam = ca := by
    have hcm64 : cam < 2 ^ 64 := by
      have := (rdW (m.arr64 CTL) 129).toNat_lt; simp only [erTop] at hca3m; omega
    have e := hca
    rw [rdW_grow hg1 (by omega), hcam] at e
    have := congrArg UInt64.toNat e
    rwa [UInt64.toNat_ofNat_of_lt' hcm64, hcaT] at this
  subst hcaeq
  have hER2 : rdW (s2.mem.arr64 EREC) (UInt64.ofNat cam) = rdW (s1.mem.arr64 EREC) (UInt64.ofNat cam) :=
    rdW_er_grow hg2 (by rw [hcaT]; omega)
  rw [hER2] at he
  -- `class_minor_slot`
  cases h3 : callE p (n + 1) "class_minor_slot" [rd, c, rdW (s1.mem.arr64 EREC) (UInt64.ofNat cam)] s2.mem with
  | error e3 =>
    rw [h3, cxoE.k_class_minor_slot.none] at he
    cases he
    have hsz5' : (s2.mem.arr64 IW).size + 5 < 2 ^ 64 := by
      have h12 := hk2 IW; have h11 := hk1 IW; rw [h12, h11]; exact hsz5
    have := CoreSpecE.of_callE (classMinorSlot_claim hnv P.cmsg P.cms n ⟨s2.mem, Locals.init []⟩ a1 rd c _ R
      (hR.stab (decCR_mono _) s2.mem hg12) hnmH hsz5') h3
    rw [hnmD] at this
    dsimp only
    rw [hes_eq]
    dsimp only
    exact ErrClaim.bind_left this
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cxoE.k_class_minor_slot.arm1] at he
  obtain ⟨s3, rfl, -, hm3, hw3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classMinorSlot_spec p P.cmsg P.cms n _ rd c (rdW (s1.mem.arr64 EREC) (UInt64.ofNat cam)))
    (callW_of_callE h3)
  rw [hm3] at he
  have hsz5' : (s2.mem.arr64 IW).size + 5 < 2 ^ 64 := by
    have h12 := hk2 IW; have h11 := hk1 IW; rw [h12, h11]; exact hsz5
  obtain ⟨s, ihs, hhits, -, hihs⟩ := cms_decB n hw3 (hR.grow (decCR_mono _) hg12) hnmH hsz5'
  have hrun3 : (ConRon.Arena.classMinorSlot R c.toNat cA'.1.name).run a1 = .ok ((s, ihs), a1) := by
    have hits := hitsFrom_eq c.toNat (decI (rdW (s1.mem.arr64 EREC) (UInt64.ofNat cam))) 0 R.slots
    simp only [Nat.zero_add] at hits
    rw [← hnmD]
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits, hhits]
    rfl
  dsimp only
  rw [hes_eq]
  dsimp only
  refine ErrClaim.bind_right hrun3 ?_
  dsimp only
  -- `open_pis_at_fvars_f`
  obtain ⟨ca2, hca2, -, -, -, -, hnF2, -, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg12) hsz2
  have hq4 : rdW (s2.mem.arr64 IW) (q + 4) = UInt64.ofNat bs.nP := (partsShapeWords hg12 hbsD hq9).1
  have hq1 : rdW (s2.mem.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
    have e : (q + 1 : Word) = UInt64.ofNat (q.toNat + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    rw [e]; exact decBS_k ((hbsD.grow (decBS_mono _) hg12).get (decBS_mono _)) (by omega)
  have hsum : (UInt64.ofNat bs.nP + UInt64.ofNat bs.k : Word) = UInt64.ofNat (bs.nP + bs.k) := by
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add] <;> omega
  dsimp only at he
  rw [hnF2, hq4, hq1, hsum] at he
  cases h4 : callE p (n + 1) "open_pis_at_fvars_f" [UInt64.ofNat cA'.snd, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)] s2.mem with
  | error e4 =>
    rw [h4, cxoE.k_open_pis_at_fvars_f.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, rfl, -, hw4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (opfF_spec p hOpf (n + 1) _ [UInt64.ofNat cA'.2, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)]) (callW_of_callE h4)
  obtain ⟨ox, a4, run4, ⟨hS4, hg4, hd4⟩, hA4⟩ := opfF_ok dn vis fe _ _ (UInt64.ofNat (bs.nP + bs.k)) htyH
    _ _ a1 r4 hw4 ⟨hS2, hA2⟩
  have hP4 := hP2.fr (MFr.ofOpfF hw4)
  rw [UInt64.toNat_ofNat_of_lt' hnFb, UInt64.toNat_ofNat_of_lt' hnpk, htyD] at run4
  obtain ⟨q4, ho4⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC2.check.state he0ty run4
  have hC4 := hC2.of_pstep hS4 hA4 q4
  have hk4 := callW_keepW (callW_of_callE h4)
  refine ErrClaim.bind_right run4 ?_
  rcases ox with _ | ⟨fvs, body⟩
  · rw [h4, cxoE.k_open_pis_at_fvars_f.abort1 p (n + 1) vis q fto ftl mo ml cA _ _ _ _ e0w _ _ r4 _ hd4] at he
    cases he
    exact absurd (by decide) hk0
  obtain ⟨h41, ⟨hdl, hbl⟩, -⟩ := hd4
  obtain ⟨fvsP, -, -, hfvsP, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho4
  have q14 := q1.trans q4
  have h0 : ¬ r4.headD 0 = 0 := by rw [h41]; decide
  rw [h4, cxoE.k_open_pis_at_fvars_f.arm1 p (n + 1) vis q fto ftl mo ml cA _ _ _ _ e0w _ _ r4 _ h0] at he
  simp only [getD_one, show (1 + 1 : Nat) = 2 from rfl, getD_two] at hdl hbl
  have hg24 := hg4
  have hg14 := hg12.trans hg4
  -- `class_fields_of`
  obtain ⟨mp0, hM0⟩ := hP4.pos.no
  have hihB := hihs.grow (OMono.decPL (fun q => decNN_mono q) _ _) hg24
  have hib : (r3.tail.headD 0).toNat + (r3.tail.tail.headD 0).toNat < 2 ^ 64 := by
    rcases decB_decPL_bound hihB with h0 | h0
    · rw [h0]; exact (r3.tail.headD 0).toNat_lt
    · exact hS4.lt64 h0
  cases h5 : callE p (n + 1) "class_fields_of" [q, r3.tail.headD 0, r3.tail.tail.headD 0, 0,
      r4.tail.headD 0, r4.tail.tail.headD 0] s4.mem with
  | error e5 =>
    rw [h5, cxoE.k_class_fields_of.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classFieldsOf_claim P.cfo hnv (n + 1) ⟨s4.mem, Locals.init []⟩ a4 q
      (r3.tail.headD 0) (r3.tail.tail.headD 0) 0 (r4.tail.headD 0) (r4.tail.tail.headD 0) bs ihs fvs mp0 hS4
      (hbs.grow hg14) (DecB.stab (OMono.decPL (fun q => decNN_mono q) _ _) hihB) hib hdl hbl
      (by simpa using (r4.tail.tail.headD 0).toNat_lt) hM0) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, cxoE.k_class_fields_of.arm1] at he
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hsp5, ⟨mp5, hM5⟩, hf5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classFieldsOf_refines p P.cfo (n + 1) _ a4 dn vis fe q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
      (r4.tail.headD 0) (r4.tail.tail.headD 0) bs ihs fvs mp0 hS4 (hbs.grow hg14)
      (DecB.stab (OMono.decPL (fun q => decNN_mono q) _ _) hihB) hib hdl hbl
      (by simpa using (r4.tail.tail.headD 0).toNat_lt) hM0) (callW_of_callE h5)
  simp only at hs5 hS5 hg5 hsp5 hM5 hf5; subst hs5
  obtain ⟨s5', hs5', -, hw5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classFieldsOf_spec p P.cfo (n + 1) _ q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
      (r4.tail.headD 0) (r4.tail.tail.headD 0)) (callW_of_callE h5)
  simp only at hs5' hw5; rw [hs5'] at hw5
  have hA5 := cfoW_afr hw5 hA4
  have hP5 := hP4.setNo hf5 ⟨mp5, hM5⟩
  have run5 := AM.run_of_ok _ a4 hok5
  generalize hx5 : AM.res (ConRon.Arena.classFieldsOf bs ihs (0 : Word).toNat fvs) a4 = kinds at run5 hsp5
  generalize ha5 : AM.st (ConRon.Arena.classFieldsOf bs ihs (0 : Word).toNat fvs) a4 = a5 at run5 hS5
  obtain ⟨q5, -⟩ := ConRon.Bridge.Inductives.classFieldsOf_spec bs pP cvP.name ihs fvs fvsP 0 a4 a5 kinds
    hC4.check.state ⟨ConRon.Bridge.Inductives.dShape_ext q14.ext _ _ hsh, hfvsP⟩ run5
  have hC5 := hC4.of_pstep hS5 hA5 q5
  have q15 := q14.trans q5
  have hg15 := hg14.trans hg5
  have hk5 := callW_keepW (callW_of_callE h5)
  refine ErrClaim.bind_right run5 ?_
  -- `class_fields_agree`
  cases h6 : callE p (n + 1) "class_fields_agree" [vis, q, fto, ftl, mo, ml, r4.tail.headD 0,
      r4.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0, 0, r5.headD 0, r5.tail.headD 0] s5.mem with
  | error e6 =>
    rw [h6, cxoE.k_class_fields_agree.none] at he
    cases he
    exact ErrClaim.bind_left (CoreSpecE.of_callE (classFieldsAgree_claim hq henv P.toCfaProg hnv hTka q fto ftl mo ml
      (r4.tail.headD 0) (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) (r5.headD 0) (r5.tail.headD 0) bs
      formerTys ms fvs (e0' :: es') kinds (n + 1) (by omega) ⟨s5.mem, Locals.init []⟩ a5 0 hC5 hA5
      (hbs.grow hg15) (by rw [decHL_grow hg15 hftb]; exact hft)
      (Nat.le_trans hftb hg15.1) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg15)
      hmsb (by rw [decHL_grow hg5 hbl]; exact hdl) (Nat.le_trans hbl hg5.1)
      (hes.grow (fun q => decNCN_mono q) (hg4.trans hg5)) hsp5.toSPL
      (by simpa using (r5.tail.headD 0).toNat_lt) hP5
      (ConRon.Bridge.Inductives.dShape_ext q15.ext _ _ hsh) (denoteEList_ext q15.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext.list q15.ext _ _ hmsP) (denoteEList_ext q5.ext _ _ hfvsP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list (q4.trans q5).ext _ _ hEP) hformer hMs) h6)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, cxoE.k_class_fields_agree.arm1] at he
  cases h7 : callE p (n + 1) "target_ctor_at" [r1.headD 0, UInt64.ofNat cam] m6 with
  | error e7 =>
    rw [h7, cxoE.k_target_ctor_at.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7, cxoE.k_target_ctor_at.arm1] at he
  cases h8 : callE p (n + 1) "inst_pis_with" [rdW (m7.arr64 IW) (r1.headD 0 + 2), rdW (m7.arr64 IW) (r1.headD 0 + 3),
      r7.headD 0] m7 with
  | error e8 =>
    rw [h8, cxoE.k_inst_pis_with.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h8
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  by_cases hz8 : r8.headD 0 = 0
  · rw [h8, cxoE.k_inst_pis_with.abort1 p (n + 1) _ _ _ _ _ r8 _ hz8] at he
    cases he
    exact absurd (by decide) hk0
  rw [h8, cxoE.k_inst_pis_with.arm1 p (n + 1) _ _ _ _ _ r8 _ hz8] at he
  cases h9 : callE p (n + 1) "rec6" [UInt64.ofNat cam, rdW (m8.arr64 IW) (cA + 1), r5.headD 0, r5.tail.headD 0,
      r8.tail.headD 0, rdW (m8.arr64 IW) (e0w + 4)] m8 with
  | error e9 =>
    rw [h9, cxoE.k_rec6.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h9
  | ok q9 =>
  rw [h9, cxoE.k_rec6.arm1] at he
  cases he

/-- **`class_ctor_of`'s error claim** (every fuel; `classCtorOf_refinesC`'s hypotheses). -/
theorem classCtorOf_claim (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl rd mo ml c cA : Word) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor) (cA' : IConstantVal × Nat)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcA : DecB (fun m => decCN m cA.toNat) s₀.mem cA') (hlp : CtorLp s₀.mem cA) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {cAP : ConLeche.ConstantVal × Nat}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hcAP : ConRon.Bridge.Inductives.dCtor a₀.store cA' = some cAP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    CoreSpecE p N "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, cA]
      (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact cxoE_claim hq henv P hIlpf hOpf dn fe hnv hTka n hN hC hA hbs hft hftb hR hms hmsb hcA hlp hnpk
      hsz5 hP hsh hftP hmsP hcAP hformer hMs e
      (triple_of_callE_err (cxoE_spec p P.cxo (n + 1) s₀ vis q fto ftl rd mo ml c cA) hc (Err.code_ne_of_cls hk0))

end rel

end L.Ind
