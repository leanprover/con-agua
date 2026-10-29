import ConAgua.Verdict.IndBFields
import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.IndT.RecGen24
import ConAgua.Arena.RecCheckSpec.TargetMajorAt
import ConAgua.Arena.RecGenSpec.DecTMSlices
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndT.RecGen27Models

/-!
# `class_ctor_of`, `class_ctors_of`, `classes_ctors`: one model, one refinement each

The unified models (`cxoE`, `cosE`, `ccsE`, in `RecGen27Models.lean`) and their refinements for both outcomes (`cxo_ref`,
`cos_ref`, `ccs_ref`; the loops `cosLoop_ref`, `ccsLoop_ref`), under `StageC` and the inputs' denotations con-ron's `classCtorOf_spec` asks; its twin side
transcribed from that spec's proof: `targetMajorAt` (`targetMajorAt_spec`), the entries' filter and
the minor slot (state kept), `openPisAtFvarsF` (`openPisAtFvarsF_run`), `classFieldsOf`
(`classFieldsOf_spec`), `classFieldsAgree` (`cfa_ref` through the run, con-ron's spec on its run),
`targetCtorAt` (`targetCtorAt_spec`, a `CSpec`), `instPisWith` (`instPisWith_spec`), the record (L
only).
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

/-- Across the real `open_pis_at_fvars_f` (its write set, `opfF_frame`). -/
theorem MFr.ofOpfF {m m' : Mem} {args r : List Word} (h : opfF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (opfF_frame h)
    (by decide)
    (by simp [opfC, instListC, mkC, instC, liftC])

theorem cnfW_afr : ∀ (k : Nat) (m m' : Mem) (nfo nfl nm q j rp r : Word),
    cnfW k m nfo nfl nm q j rp = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [cnfW] at h
  | k + 1, m, m', nfo, nfl, nm, q, j, rp, r, h => by
    by_cases hj : j < nfl
    · by_cases h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (nfo + j)) = nm
      · by_cases h2 : (q + rp).toNat < (m.arr64 IW).size
        · rw [cnfW_hit (h := hj) (h1 := h1) (h2 := h2)] at h
          exact (set64IW_afr _ _ _).trans (cnfW_afr k _ _ _ _ _ _ _ _ _ h)
        · rw [cnfW_oob (h := hj) (h1 := h1) (h2 := h2)] at h; cases h
      · rw [cnfW_miss (h := hj) (h1 := h1)] at h
        exact cnfW_afr k _ _ _ _ _ _ _ _ _ h
    · rw [cnfW_exit (h := hj)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _

theorem cnfF_afr {n : Nat} {m m' : Mem} {nfo nfl nm : Word} {r : List Word}
    (h : cnfF n m nfo nfl nm = some (r, m')) : AFr m m' := by
  simp only [cnfF] at h
  obtain ⟨⟨q, m1⟩, hal, h⟩ := of_K h rfl
  rw [cnfK1_some] at h
  obtain ⟨⟨rp, m2⟩, hl, h⟩ := of_K h rfl
  rw [cnfK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr hal).trans (cnfW_afr _ _ _ _ _ _ _ _ _ _ hl)

/-- What `class_ctor_of` gives besides the constructor record `x` it returns (from `m`). -/
structure CxoPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (w : Word) (m' : Mem) (x : ClassCtor) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  cc : StabA (iwTop m) (fun m => decCC m w.toNat) m' x
  rc : RcMR m'
  abs : AbsOK m'

/-- What a loop filling a result slice `qo[0..l)` gives (from `m0`, with the records `acc` already
written): the stage, the growth and the array sizes from `m0`, the slice's records decoded by `D`. -/
structure SlotsLoopPost {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (D : Mem → Nat → Option α) (m0 : Mem) (l qo : Word) (acc : List α) (m' : Mem)
    (xs : List α) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m0 m'
  keep : KeepW m0 m'
  top : iwTop m0 + l.toNat ≤ iwTop m'
  rc : RcMR m'
  abs : AbsOK m'
  slots : ∃ ps', decNL m' qo.toNat l.toNat = some ps' ∧
    FA2 (fun p x => StabA (iwTop m0 + l.toNat) (fun m => D m p) m' x) ps' (acc ++ xs)

/-- What a function returning a fresh slice `[off, len]` of records decoded by `D` gives (from `m`). -/
structure SlotsPost {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (D : Mem → Nat → Option α) (m : Mem) (r : List Word) (m' : Mem) (xs : List α)
    (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  slots : SPLA (iwTop m) D m' (r.headD 0).toNat (r.tail.headD 0).toNat xs
  rc : RcMR m'
  abs : AbsOK m'

section rel
variable {p : Prog} (hq : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CxoProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include hq henv P hIlpf hOpf

/-- **`class_ctor_of` refines `classCtorOf`, both outcomes** (twin side: con-ron's
`classCtorOf_spec`'s proof; `class_minor_slot` by `cms_ref`, `class_fields_of` by `cfo_ref` and
`class_fields_agree` by `cfa_ref` through their runs). -/
theorem cxo_ref (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {m : Mem} {a : AState} {vis q fto ftl rd mo ml c cA : Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cA' : IConstantVal × Nat}
    (hC : StageC dn vis fe env m a)
    (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcA : DecB (fun m => decCN m cA.toNat) m cA') (hlp : CtorLp m cA) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {cAP : ConLeche.ConstantVal × Nat}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) (hcAP : ConRon.Bridge.Inductives.dCtor a.store cA' = some cAP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (cxoE p (n + 1) m vis q fto ftl rd mo ml c cA)
      (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a
      (fun v x a' => CxoPost dn vis fe env m v.1 v.2 x a') := by
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hcAP
  obtain ⟨cvP, hcvP, rfl⟩ := hcAP
  have hname := ConRon.Bridge.denoteCV_name hcvP
  have hbsD : DecB (fun m => decBS m q.toNat) m bs := hbs.1
  have hq9 : q.toNat + 9 ≤ iwTop m := by have := hbs.ptop; omega
  have hq64 := hS.lt64 hq9
  rw [cxoE.arm1]
  -- `target_major_at`
  rcases c1 : callW p n "target_major_at" [mo, ml, c] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, cxoE.k_target_major_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cxoE.k_target_major_at.arm1]
  obtain ⟨s1, rfl, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetMajorAt_spec p P.ha P.pw P.mtm P.tmd P.tma P.na n _ mo ml c) c1
  obtain ⟨tm, a1, run1, hS1, hg1, hTM⟩ := rec3TMA_sim dn vis fe n m a mo ml c ms hS hms hmsb _ hw1
  dsimp only at hS1 hg1 hTM
  have hP1 := hP.fr (tmaW_mfr hw1)
  have hA1 := tmaW_afr hw1 hA
  obtain ⟨q1, hmP⟩ := ConRon.Bridge.Inductives.targetMajorAt_spec ms MsP c.toNat a a1 tm hC.check.state
    hC.check.pins hmsP run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  obtain ⟨-, -, hmdsP, -, -, -, -, hnfsP, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hmP
  have hk1 := callW_keepW c1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨⟨no, nl, h9, h10, hno, hnl, hnfs⟩, hds, hmw13⟩ := decTM_slices hTM hsz1
  obtain ⟨ca, hca, hca3, hcv, hnmH, hnmD, hnF, hnFb, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg1) hsz1
  obtain ⟨cam, hcam, hca3m, -, -, -, -, -, hcAt⟩ := decCN_words hcA hsz
  rw [h9, h10, hca]
  refine RefE.bind_right run1 ?_
  -- `class_ctor_of_nfs`
  rcases c2 : callW p n "class_ctor_of_nfs" [UInt64.ofNat no, UInt64.ofNat nl,
      rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca)] s1.mem with _ | ⟨r2, m2⟩
  · rw [liftE_none, cxoE.k_class_ctor_of_nfs.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  rcases n with _ | n
  · obtain ⟨_, _, hf⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (invoke_exec_zero p _ _ _) c2
    exact hf.elim
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (cnf_spec p P.ha P.cnf n _ (UInt64.ofNat no) (UInt64.ofNat nl) (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))) c2
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hf2, hes⟩ := cnfF_ok _ _ _ tm.nfs n hw2 hS1 (by
    rw [UInt64.toNat_ofNat_of_lt' hno, UInt64.toNat_ofNat_of_lt' hnl]; exact hnfs) hnmH
  rw [hnmD] at hes
  have hP2 := hP1.fr hf2
  have hA2 := cnfF_afr hw2 hA1
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  have hk2 := callW_keepW c2
  have hg12 := hg1.trans hg2
  by_cases hel : r2.tail.headD 0 = 0
  · rw [cxoE.k_class_ctor_of_nfs.abort1 p (n + 1) vis q fto ftl rd mo ml c cA _ _ r2 _ hel]
    exact RefE.of_cls0 rfl
  rw [cxoE.k_class_ctor_of_nfs.arm1 p (n + 1) vis q fto ftl rd mo ml c cA _ _ r2 _ hel]
  -- the class's entries: the first
  obtain ⟨e0', es', hes_eq, he0, -⟩ := hes.uncons hel hS2.2.2.2.1
  rw [hes_eq] at hes
  have hEP := ConRon.Bridge.Inductives.filter_nfs hC1.check.state.wf
    (ConRon.Bridge.denoteN_ext hname q1.ext) _ _ hnfsP
  rw [hes_eq] at hEP
  obtain ⟨e0P, EsP', hEsP, he0P, hEsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hEP
  rw [hEsP] at hEP
  have he0ty := (ConRon.Bridge.Inductives.RC.dCtorNf_inv he0P).2.2.2
  have hsz2 := hS2.2.2.2.1
  generalize hE0 : rdW (s2.mem.arr64 IW) (r2.headD 0) = e0w at he0 ⊢
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
  subst cam
  have hER2 : rdW (s2.mem.arr64 EREC) (UInt64.ofNat ca) = rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca) :=
    rdW_er_grow hg2 (by rw [hcaT]; omega)
  rw [hER2]
  -- `class_minor_slot`
  have hsz5' : (s2.mem.arr64 IW).size + 5 < 2 ^ 64 := by rw [hk2 IW, hk1 IW]; exact hsz5
  have h3 := cms_ref P.cmsg (n + 1) (a := a1) (c := c) ((hR.grow (decCR_mono _) hg12).get (decCR_mono _)) hnmH hsz5'
  rcases h3' : classMinorSlotE p (n + 1) s2.mem rd c (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))
    with e3 | ⟨r3, m3⟩ <;> rw [h3'] at h3
  · rw [cxoE.k_class_minor_slot.none]
    rw [hnmD] at h3
    dsimp only
    rw [hes_eq]
    dsimp only
    exact RefE.bind_left fun hG => h3 hG.nv
  rw [cxoE.k_class_minor_slot.arm1]
  obtain ⟨⟨s, ihs⟩, a3, hrun3, hR3⟩ := h3
  have hm3 := hR3.mem
  have ha3 := hR3.st
  have hihs := hR3.ihsB (hR.grow (decCR_mono _) hg12)
  dsimp only at hm3 ha3 hihs
  subst hm3
  rw [hnmD, ha3] at hrun3
  dsimp only
  rw [hes_eq]
  dsimp only
  refine RefE.bind_right hrun3 ?_
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
  rw [hnF2, hq4, hq1, hsum]
  rcases c4 : callW p (n + 1) "open_pis_at_fvars_f" [UInt64.ofNat cA'.snd, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)] s2.mem with _ | ⟨r4, m4⟩
  · rw [liftE_none, cxoE.k_open_pis_at_fvars_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s4, rfl, -, hw4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (opfF_spec p hOpf (n + 1) _ [UInt64.ofNat cA'.2, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)]) c4
  obtain ⟨ox, a4, run4, ⟨hS4, hg4, hd4⟩, hA4⟩ := opfF_ok dn vis fe _ _ (UInt64.ofNat (bs.nP + bs.k)) htyH
    _ _ a1 r4 hw4 ⟨hS2, hA2⟩
  have hP4 := hP2.fr (MFr.ofOpfF hw4)
  rw [UInt64.toNat_ofNat_of_lt' hnFb, UInt64.toNat_ofNat_of_lt' hnpk, htyD] at run4
  obtain ⟨q4, ho4⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC2.check.state he0ty run4
  have hC4 := hC2.of_pstep hS4 hA4 q4
  have hk4 := callW_keepW c4
  refine RefE.bind_right run4 ?_
  rcases ox with _ | ⟨fvs, body⟩
  · rw [cxoE.k_open_pis_at_fvars_f.abort1 p (n + 1) vis q fto ftl mo ml cA _ _ _ _ e0w _ _ r4 _ hd4]
    exact RefE.of_cls0 rfl
  obtain ⟨h41, ⟨hdl, hbl⟩, -⟩ := hd4
  obtain ⟨fvsP, -, -, hfvsP, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho4
  have q14 := q1.trans q4
  have h0 : ¬ r4.headD 0 = 0 := by rw [h41]; decide
  rw [cxoE.k_open_pis_at_fvars_f.arm1 p (n + 1) vis q fto ftl mo ml cA _ _ _ _ e0w _ _ r4 _ h0]
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
  have hT5 := cfoE_spec p P.cfo (n + 1) ⟨s4.mem, Locals.init []⟩ q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
    (r4.tail.headD 0) (r4.tail.tail.headD 0)
  have hR5 := cfo_ref (i := 0) (p := p) dn vis fe bs ihs (n + 1) hS4 (hbs.grow hg14)
    (DecB.stab (OMono.decPL (fun q => decNN_mono q) _ _) hihB) hib hdl hbl
    (by simpa using (r4.tail.tail.headD 0).toNat_lt) hM0 (a := a4)
  rcases h5 : callE p (n + 1) "class_fields_of" [q, r3.tail.headD 0, r3.tail.tail.headD 0, 0,
      r4.tail.headD 0, r4.tail.tail.headD 0] s4.mem with e5 | ⟨r5, m5⟩
  · rw [cxoE.k_class_fields_of.none]
    exact RefE.bind_left fun hG => RefE.run_err hT5 hG.nv hG.nv hR5 h5
  rw [cxoE.k_class_fields_of.arm1]
  obtain ⟨s5, hs5, -, kinds, a5, run5, hS5, hg5, hsp5, ⟨mp5, hM5⟩, hf5, hA5⟩ := RefE.run_ok hT5 hR5 h5
  subst hs5
  replace hA5 := hA5 hA4
  have hP5 := hP4.setNo hf5 ⟨mp5, hM5⟩
  obtain ⟨q5, -⟩ := ConRon.Bridge.Inductives.classFieldsOf_spec bs pP cvP.name ihs fvs fvsP 0 a4 a5 kinds
    hC4.check.state ⟨ConRon.Bridge.Inductives.dShape_ext q14.ext _ _ hsh, hfvsP⟩ run5
  have hC5 := hC4.of_pstep hS5 hA5 q5
  have q15 := q14.trans q5
  have hg15 := hg14.trans hg5
  have hk5 := callW_keepW (callW_of_callE h5)
  refine RefE.bind_right run5 ?_
  -- `class_fields_agree`
  have hT6 := cfaE_spec p P.toCfaProg (n + 1) ⟨s5.mem, Locals.init []⟩ vis q fto ftl mo ml (r4.tail.headD 0)
    (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) 0 (r5.headD 0) (r5.tail.headD 0)
  have hR6 := cfa_ref hq henv P.toCfaProg vis q fto ftl mo ml (r4.tail.headD 0)
      (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) (r5.headD 0) (r5.tail.headD 0) bs formerTys ms fvs
      (e0' :: es') kinds (n + 1) (by omega) _ a5 0 hC5 hA5 (hbs.grow hg15) (by rw [decHL_grow hg15 hftb]; exact hft)
      (Nat.le_trans hftb hg15.1) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg15)
      hmsb (by rw [decHL_grow hg5 hbl]; exact hdl) (Nat.le_trans hbl hg5.1)
      (hes.grow (fun q => decNCN_mono q) (hg4.trans hg5)) hsp5.toSPL
      (by simpa using (r5.tail.headD 0).toNat_lt) hP5
      (ConRon.Bridge.Inductives.dShape_ext q15.ext _ _ hsh) (denoteEList_ext q15.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext.list q15.ext _ _ hmsP) (denoteEList_ext q5.ext _ _ hfvsP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list (q4.trans q5).ext _ _ hEP) hformer hMs
  rcases h6 : callE p (n + 1) "class_fields_agree" [vis, q, fto, ftl, mo, ml, r4.tail.headD 0,
      r4.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0, 0, r5.headD 0, r5.tail.headD 0] s5.mem with e6 | ⟨r6, m6⟩
  · rw [cxoE.k_class_fields_agree.none]
    exact RefE.bind_left fun hG => RefE.run_err hT6 hG.nv hG hR6 h6
  rw [cxoE.k_class_fields_agree.arm1]
  obtain ⟨s6, hs6, -, u6, a6, run6, hR6'⟩ := RefE.run_ok hT6 hR6 h6
  subst hs6
  have hC6 := hR6'.stage
  have hg6 := hR6'.grow
  have hP6 := hR6'.rc
  have hA6 := hR6'.abs
  simp only [show (0 : Word).toNat = 0 from rfl] at run5 run6
  obtain ⟨cs6, -⟩ := ConRon.Bridge.Inductives.classFieldsAgree_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys formerTysP ms MsP fvs fvsP (e0' :: es') (e0P :: EsP') cvP.name hformer hMs kinds 0
    a5 _ () hC5.check
    ⟨ConRon.Bridge.Inductives.dShape_ext q15.ext _ _ hsh, denoteEList_ext q15.ext _ _ hftP,
      ConRon.Bridge.Inductives.dMajor_ext.list q15.ext _ _ hmsP, denoteEList_ext q5.ext _ _ hfvsP,
      ConRon.Bridge.Inductives.dCtorNf_ext.list (q4.trans q5).ext _ _ hEP⟩ run6
  have cs16 := (q15.toCore hC.check).trans cs6
  have hS6 := hC6.stage
  have hg16 := hg15.trans hg6
  have hk6 := callW_keepW (callW_of_callE h6)
  refine RefE.bind_right run6 ?_
  -- `target_ctor_at`
  rcases c7 : callW p (n + 1) "target_ctor_at" [r1.headD 0, UInt64.ofNat ca] s6.mem with _ | ⟨r7, m7⟩
  · rw [liftE_none, cxoE.k_target_ctor_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cxoE.k_target_ctor_at.arm1]
  have hgm6 := hg16
  have hg26 : IWGrow s1.mem s6.mem := hg2.trans (hg4.trans (hg5.trans hg6))
  have hca3' : ca + 3 < 2 ^ 64 := by
    have := (rdW (s1.mem.arr64 CTL) 129).toNat_lt; simp only [erTop] at hca3; omega
  have hkm6 : KeepW m s6.mem := hk1.trans (hk2.trans (hk4.trans (hk5.trans hk6)))
  have hlp6 : (rdW (s6.mem.arr64 EREC) (UInt64.ofNat ca + 2)).toNat = 0 ∨
      (rdW (s6.mem.arr64 EREC) (UInt64.ofNat ca + 1)).toNat +
      (rdW (s6.mem.arr64 EREC) (UInt64.ofNat ca + 2)).toNat ≤ (s6.mem.arr64 EREC).size := by
    have e1 : (UInt64.ofNat ca + 1 : Word).toNat = ca + 1 := by rw [UInt64.toNat_add]; simp <;> omega
    have e2 : (UInt64.ofNat ca + 2 : Word).toNat = ca + 2 := by rw [UInt64.toNat_add]; simp <;> omega
    rw [rdW_er_grow hgm6 (by rw [e2]; omega), rdW_er_grow hgm6 (by rw [e1]; omega), hkm6 EREC]
    have := hlp; simp only [CtorLp] at this; rw [hcam] at this; exact this
  obtain ⟨s7, rfl, -, hw7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (targetCtorAt_spec p P.ha P.erc P.eri P.cvl P.tca (realCall p) (realCall_spec p) n _ (r1.headD 0)
      (UInt64.ofNat ca)) c7
  obtain ⟨t7, a7, run7, hS7, hg7, ht7H, ht7D, hA7f⟩ := tcW_ok dn vis fe n _ _ a6 (r1.headD 0) (UInt64.ofNat ca)
    tm cA'.1 r7 (realCall p) (IlpRd.realC hIlpf hC6) hS6 ((hTM.grow (decTM_mono _) hg26).get (decTM_mono _))
      (by rw [hcaT]; exact (hcv.grow (OMono.decCVp _) hg26).get (OMono.decCVp _)) hmw13 (by rw [hcaT]; omega)
      hlp6 hw7
  rw [← ht7D] at run7
  have hP7 := hP6.fr (tcW_mfr (IlpFr.real hIlpf) hw7)
  have hA7 := hA7f hA6
  obtain ⟨cs7, ht0P⟩ := ConRon.Bridge.Inductives.targetCtorAt_spec fe tm _ cA'.1 cvP a6 a7 _ hC6.check
    ⟨ConRon.Bridge.Inductives.dMajor_ext ((q4.trans q5).ext.trans cs6.ext) _ _ hmP,
      ConRon.Bridge.Inductives.dExt_denoteCV cs16.ext _ _ hcvP⟩ run7
  have hC7 := hC6.of_cstep hS7 hA7 cs7
  have hg17 := hg16.trans hg7
  refine RefE.bind_right run7 ?_
  -- `inst_pis_with`
  have hsz7 := hS7.2.2.2.1
  obtain ⟨-, hds7, -⟩ := decTM_slices (hTM.grow (decTM_mono _) (hg26.trans hg7)) hsz7
  rcases c8 : callW p (n + 1) "inst_pis_with" [rdW (s7.mem.arr64 IW) (r1.headD 0 + 2),
      rdW (s7.mem.arr64 IW) (r1.headD 0 + 3), r7.headD 0] s7.mem with _ | ⟨r8, m8⟩
  · rw [liftE_none, cxoE.k_inst_pis_with.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s8, rfl, -, hw8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (instPisWith_spec p P.hv P.ipw P.hi1 (n + 1) _ _ _ _) c8
  obtain ⟨ox, a8, run8, hS8, hg8, hd8⟩ := instW_ok0 (n + 1) hw8 hS7 ht7H hds7
  have hP8 := hP7.fr (instW_mfr _ _ _ _ _ _ _ hw8)
  have hA8 := instW_afr _ _ _ _ _ _ _ hw8 hA7
  obtain ⟨q8, -⟩ := ConRon.Bridge.Inductives.instPisWith_spec tm.ds _ _ _ a7 a8 ox hC7.check.state
    ⟨denoteEList_ext ((q4.trans q5).ext.trans (cs6.ext.trans cs7.ext)) _ _ hmdsP, ht0P⟩ run8
  have hC8 := hC7.of_pstep hS8 hA8 q8
  have hg18 := hg17.trans hg8
  refine RefE.bind_right run8 ?_
  rcases ox with _ | tyD
  · rw [cxoE.k_inst_pis_with.abort1 p (n + 1) _ _ _ _ _ r8 _ hd8]; exact RefE.of_cls0 rfl
  obtain ⟨h81, h8H, h8D⟩ := hd8
  have h0 : ¬ r8.headD 0 = 0 := by rw [h81]; decide
  rw [cxoE.k_inst_pis_with.arm1 p (n + 1) _ _ _ _ _ r8 _ h0]
  -- `rec6`
  have hsz8 := hS8.2.2.2.1
  obtain ⟨ca8, hca8, -, hcv8, -, -, hnF8, -, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg18) hsz8
  obtain ⟨hty8H, hty8D⟩ := decNCN_ty (he0.grow (decNCN_mono _) (hg4.trans (hg5.trans (hg6.trans (hg7.trans hg8)))))
    hsz8
  rw [hnF8]
  rcases c9 : callW p (n + 1) "rec6" [UInt64.ofNat ca, UInt64.ofNat cA'.2, r5.headD 0, r5.tail.headD 0,
      r8.tail.headD 0, rdW (s8.mem.arr64 IW) (e0w + 4)] s8.mem with _ | ⟨r9, m9⟩
  · rw [liftE_none, cxoE.k_rec6.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cxoE.k_rec6.arm1]
  obtain ⟨s9, hs9, -, hw9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (rec6_specW p P.ha P.r6 (n + 1) _ _ _ _ _ _ _) c9
  simp only at hs9 hw9; subst hs9
  obtain ⟨hS9, hg9, hq9', ht9, hget9⟩ := posRecW_stage hw9 hS8 (by simp)
  have hP9 := hP8.fr (posRecW_mfr hw9)
  have hA9 := posRecW_afr hw9 hA8
  refine RefE.ret (y := ⟨cA'.1, cA'.2, kinds, tyD, e0'.ty⟩) (a' := a8) rfl
    ⟨hC8.of_pstep hS9 hA9 (PStep.refl hC8.check.state), hg18.trans hg9, ?_, hP9, hA9⟩
  have := rec6_decCC (m := s8.mem) (q := r9.headD 0) (cvw := UInt64.ofNat ca) (nFw := UInt64.ofNat cA'.2)
    (ko := r5.headD 0) (kl := r5.tail.headD 0) (tyD := r8.tail.headD 0) (tyN := rdW (s8.mem.arr64 IW) (e0w + 4))
    (fun j hj => by simpa using hget9 j (by simpa using hj)) (by simp at ht9; omega)
    (by rw [hq9']; exact hg18.1) hg9
    (by rw [hcaT]; exact hcv.grow (OMono.decCVp _) (hg26.trans (hg7.trans hg8)))
    ((hsp5.mono hg14.1).grow (AgreeA.of_grow (hg6.trans (hg7.trans hg8)))) h8H hty8H
  rw [h8D, hty8D, UInt64.toNat_ofNat_of_lt' hnFb] at this
  exact this

end rel

/-- **`class_ctor_of` refines `classCtorOf`** under `StageC` (the knot's core calls; the inputs'
denotations and scoping as con-ron's `classCtorOf_spec` asks; `open_pis_at_fvars_f`, `inst_lp_fast`
through their stub contracts). -/
@[refines ConRon.Arena.classCtorOf]
theorem classCtorOf_refinesC {p : Prog} (hq : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CxoProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl rd mo ml c cA : Word) (bs : BlockShape)
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
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, cA]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      StabA (iwTop s₀.mem) (fun m => decCC m (r.headD 0).toNat) s'.mem
        (AM.res (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a₀) ∧ RcMR s'.mem ∧
      AbsOK s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (RefE.triple (cxoE_spec p P (n + 1) s₀ vis q fto ftl rd mo ml c cA)
    (cxo_ref hq henv P hIlpf hOpf dn fe n hn hC hA hbs hft hftb hR hms hmsb hcA hlp hnpk hsz5 hP hsh hftP
      hmsP hcAP hformer hMs)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR'.stage, hR'.grow, by rw [hres]; exact hR'.cc, hR'.rc, hR'.abs⟩

section cos
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CosProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl rd mo ml c ao al qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (cAs : List (IConstantVal × Nat)) (m0 : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {rdP : ConLeche.ClassRead}
include hkp henv P hIlpf hOpf

/-- **`class_ctors_of`' loop refines `classCtorsOf`, both outcomes** (twin side: con-ron's
`classCtorsOf_spec`'s list induction; each constructor by `cxo_ref` through the call's run, the
extension after it from con-ron's `classCtorOf_spec` on its run). -/
theorem cosLoop_ref (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m0 cAs) (hlp : CtorsLp m0 ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64) (hq : qo.toNat = iwTop m0)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (k : Nat) (hk' : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (j : Word) (acc : List ClassCtor) (ps : List Nat)
      (csP : List (ConLeche.ConstantVal × Nat)),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m →
    KeepW m0 m → iwTop m0 + al.toNat ≤ iwTop m → j ≤ al → decNL m qo.toNat j.toNat = some ps →
    FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p) m x) ps acc → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ConRon.Bridge.Inductives.dClassRead a.store R = some rdP → ms.mapM (dMajor a.store) = some MsP →
    dCtors a.store (cAs.drop j.toNat) = some csP →
    RefE (VerdictCtx p) (cosE.loop1 p k m vis q fto ftl rd mo ml c ao al qo j)
      (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat (cAs.drop j.toNat)) a
      (fun m' xs a' => SlotsLoopPost dn vis fe env decCC m0 al qo acc m' xs a') := by
  have hcAs0 : decPL (truncM m0) (decCN (truncM m0)) ao.toNat al.toNat = some cAs := hcAs
  have hlen := decPL_length _ hcAs0
  induction k with
  | zero => intros; rw [cosE.loop1.eq_def]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a j acc ps csP hC hA hg hk htop hja hps hfa hP hsh hftP hrdP hmsP hcsP
  have hS := hC.stage
  have hjk : j.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hja
  by_cases hj : j < al
  rotate_left
  · rw [cosE.loop1.arm2 p k m vis q fto ftl rd mo ml c ao al qo j hj]
    have h1 : al.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have hje : j.toNat = al.toNat := by omega
    rw [List.drop_eq_nil_of_le (by omega)]
    exact RefE.ret rfl ⟨hC, hg, hk, htop, hP, hA, ps, by rw [← hje]; exact hps, by simpa using hfa⟩
  have hjl : j.toNat < al.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := al.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [cosE.loop1.arm1 p k m vis q fto ftl rd mo ml c ao al qo j hj]
  have hsz := hS.2.2.2.1
  -- the constructor record
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m0) hcAs0 j.toNat hjl
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hsz0 : (m0.arr64 IW).size < 2 ^ 64 := by omega
  have hrd0 := iwN_rdW_at (w := ao) (k := j.toNat) hv0 hsz0
  have hnj : ao + UInt64.ofNat j.toNat = ao + j := by simp
  rw [hnj] at hrd0
  have hT0 := (rdW (m0.arr64 CTL) 200).toNat_lt
  have hajt : (ao + j).toNat = ao.toNat + j.toNat := by
    simp only [iwTop] at hvt; rw [UInt64.toNat_add]; simp <;> omega
  have hrd : rdW (m.arr64 IW) (ao + j) = UInt64.ofNat v := by
    rw [rdW_grow hg (by rw [hajt]; exact hvt), hrd0.1]
  rw [hrd]
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd0.2
  have hcA0 : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m0 cAs[j.toNat] := by
    rw [hvT]; rw [← hlen] at hjl; exact hdv
  have hlp0 : CtorLp m0 (UInt64.ofNat v) := by
    have := hlp j.toNat hjl; rw [hnj, hrd0.1] at this; exact this
  rw [List.drop_eq_getElem_cons (by rw [hlen]; omega)] at hcsP
  obtain ⟨cAP, csP', rfl, hcAP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classCtorsOf]
  -- `class_ctor_of`
  rcases k with _ | k
  · obtain ⟨e', he', h0⟩ := callE_zero p "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat v] m
    rw [he', cosE.k_class_ctor_of.none]; exact RefE.of_cls0 h0
  have hT1 := cxoE_spec p P.toCxoProg (k + 1) ⟨m, Locals.init []⟩ vis q fto ftl rd mo ml c (UInt64.ofNat v)
  have hR1 := cxo_ref hkp henv P.toCxoProg hIlpf hOpf dn fe k (by omega) hC hA (hbs.grow hg)
    (by rw [decHL_grow hg hftb]; exact hft) (Nat.le_trans hftb hg.1)
    (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg) hmsb
    (hcA0.grow (decCN_mono _) hg) (hlp0.grow hcA0 hsz0 hg hk) hnpk (by rw [hk IW]; exact hsz5) hP
    hsh hftP hmsP hcAP hformer hMs (vis := vis) (q := q) (fto := fto) (ftl := ftl) (rd := rd) (mo := mo)
    (ml := ml) (c := c)
  rcases h1 : callE p (k + 1) "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat v] m with
    e1 | ⟨r1, m1⟩
  · rw [cosE.k_class_ctor_of.none]
    exact RefE.bind_left fun hG => RefE.run_err hT1 hG.nv hG hR1 h1
  rw [cosE.k_class_ctor_of.arm1]
  obtain ⟨s1, hs1, -, x1, a1, run1, hR1'⟩ := RefE.run_ok hT1 hR1 h1
  subst hs1
  have hC1 := hR1'.stage
  have hg1 := hR1'.grow
  have hd1 := hR1'.cc
  have hP1 := hR1'.rc
  have hA1 := hR1'.abs
  dsimp only at hC1 hg1 hd1 hP1 hA1
  obtain ⟨cs1, -⟩ := ConRon.Bridge.Inductives.classCtorOf_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv
    bs pP formerTys formerTysP R rdP ms MsP c.toNat cAs[j.toNat] cAP hformer hMs a _ _ hC.check
    ⟨hsh, hftP, hrdP, hmsP, hcAP⟩ run1
  have hS1 := hC1.stage
  have hk1 := callW_keepW (callW_of_callE h1)
  -- the slot write
  have hsz1 := hS1.2.2.2.1
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqj : (qo + j).toNat = qo.toNat + j.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hb0 : iwTop m0 + al.toNat ≤ iwTop m := htop
  have hS2 := hS1.set_iw (qo + j) (r1.headD 0)
  have hAb2 := set64IW_afr s1.mem (qo + j) (r1.headD 0) hA1
  have hC2 := hC1.of_pstep hS2 hAb2 (PStep.refl hC1.check.state)
  have hg2 : IWGrow m0 (s1.mem.set64 IW (qo + j) (r1.headD 0)) := (hg.trans hg1).set_iw _ _ (by omega)
  have hk2 : KeepW m0 (s1.mem.set64 IW (qo + j) (r1.headD 0)) := (hk.trans hk1).set64 _ _ _
  have hA2 : AgreeA (iwTop m0 + al.toNat) s1.mem (s1.mem.set64 IW (qo + j) (r1.headD 0)) :=
    AgreeA.set_iw _ _ (by omega)
  have hps1 : decNL s1.mem qo.toNat j.toNat = some ps := by
    rw [decNL_grow hg1 (by omega)]; exact hps
  have hqb : (qo + j).toNat < (s1.mem.arr64 IW).size := by
    have := hS1.2.1; have := hg1.1; omega
  have hps2 := decNL_write s1.mem qo.toNat j.toNat (qo + j) (r1.headD 0) ps hqj (by omega) hps1
  have hfa2 : FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p)
      (s1.mem.set64 IW (qo + j) (r1.headD 0)) x) (ps ++ [(r1.headD 0).toNat]) (acc ++ [x1]) :=
    FA2.snoc (FA2.imp (fun _ _ hq => (hq.grow (AgreeA.of_grow hg1)).grow hA2) hfa)
      ((hd1.mono hb0).grow hA2)
  refine RefE.bind_right run1 ?_
  have ih' := ih (by omega) _ a1 (j + 1)
    (acc ++ [x1]) (ps ++ [(r1.headD 0).toNat]) csP' hC2 hAb2 hg2 hk2
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg1.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [hj1]; exact hps2) hfa2 (hP1.fr (MFr.set_iw _ _ _))
    (ConRon.Bridge.Inductives.dShape_ext cs1.ext _ _ hsh) (denoteEList_ext cs1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dClassRead_ext cs1.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hmsP)
    (by rw [hj1]; exact ConRon.Bridge.Inductives.dCtors_ext cs1.ext _ _ hcsP')
  rw [hj1] at ih'
  exact RefE.tail (k := fun x => x) (f := id) (fun _ => rfl) (fun _ => rfl) id
    (fun xs a' h => ⟨x1 :: xs, by simp only [StateT.run_bind, h]; rfl,
      fun _ hR => ⟨hR.stage, hR.grow, hR.keep, hR.top, hR.rc, hR.abs, by
        obtain ⟨ps', h1, h2⟩ := hR.slots; exact ⟨ps', h1, by simpa using h2⟩⟩⟩)
    (fun ce h => by simp only [StateT.run_bind, h]; rfl) ih'

end cos

section cosf
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CosProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include hkp henv P hIlpf hOpf

/-- **`class_ctors_of` refines `classCtorsOf`, both outcomes** (`cosLoop_ref` over the fresh result
slice). -/
theorem cos_ref (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {m : Mem} {a : AState} {vis q fto ftl rd mo ml c ao al : Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cAs : List (IConstantVal × Nat)}
    (hC : StageC dn vis fe env m a)
    (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m cAs) (hlp : CtorsLp m ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {rdP : ConLeche.ClassRead} {csP : List (ConLeche.ConstantVal × Nat)}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store R = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) (hcsP : dCtors a.store cAs = some csP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (cosE p (n + 1) m vis q fto ftl rd mo ml c ao al)
      (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a
      (fun v xs a' => SlotsPost dn vis fe env decCC m v.1 v.2 xs a') := by
  rw [cosE.arm1]
  rcases h1 : callW p n "iw_alloc" [al] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, cosE.k_iw_alloc.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cosE.k_iw_alloc.arm1]
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (iwAlloc_specW p P.ha n ⟨m, Locals.init []⟩ al) h1
  dsimp only at hs1 hal
  subst hs1
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hC.stage
  have hf1 := allocW_mfr hal
  have hA1 := allocW_afr hal hA
  have h := cosLoop_ref hkp henv P hIlpf hOpf dn fe vis q fto ftl rd mo ml c ao al (r1.headD 0) bs formerTys R ms
    cAs m hbs hft hftb hR hms hmsb hcAs hlp hnpk hsz5 hq hformer hMs (n + 1) hn s1.mem a 0 [] [] csP
    (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hA1 hg1 (KeepW.of_mfr hf1) (by omega) UInt64.zero_le
    (by simp [decNL]) .nil (hP.fr hf1) hsh hftP hrdP hmsP (by simpa using hcsP)
  simp only [UInt64.toNat_zero, List.drop_zero] at h
  rcases hl : cosE.loop1 p (n + 1) s1.mem vis q fto ftl rd mo ml c ao al (r1.headD 0) 0 with e' | m2 <;>
    rw [hl] at h
  · rw [cosE.k_loop1.none]; exact h
  rw [cosE.k_loop1.arm1]
  obtain ⟨xs, a', run, hR'⟩ := h
  obtain ⟨ps', hps', hfa'⟩ := hR'.slots
  have ht' := hR'.top
  simp only [List.nil_append] at hfa'
  exact RefE.ret run ⟨hR'.stage, hR'.grow, ⟨.inr (by simp only [List.headD_cons]; omega), by simp only [List.headD_cons, List.tail_cons]; omega, ps', hps',
    FA2.imp (fun _ _ hq => hq.mono (by omega)) hfa'⟩, hR'.rc, hR'.abs⟩

end cosf

/-- **`class_ctors_of` refines `classCtorsOf`** under `StageC` (the knot's core calls; the inputs'
denotations and scoping as con-ron's `classCtorsOf_spec` asks). -/
@[refines ConRon.Arena.classCtorsOf]
theorem classCtorsOf_refinesC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CosProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl rd mo ml c ao al : Word) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor) (cAs : List (IConstantVal × Nat))
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) s₀.mem cAs) (hlp : CtorsLp s₀.mem ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {rdP : ConLeche.ClassRead} {csP : List (ConLeche.ConstantVal × Nat)}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store R = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP) (hcsP : dCtors a₀.store cAs = some csP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, ao, al]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      SPLA (iwTop s₀.mem) decCC s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat
        (AM.res (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a₀) ∧ RcMR s'.mem ∧
      AbsOK s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (RefE.triple (cosE_spec p P (n + 1) s₀ vis q fto ftl rd mo ml c ao al)
    (cos_ref hkp henv P hIlpf hOpf dn fe n hn hC hA hbs hft hftb hR hms hmsb hcAs hlp hnpk hsz5 hP hsh hftP
      hrdP hmsP hcsP hformer hMs)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR'.stage, hR'.grow, by rw [hres]; exact hR'.slots, hR'.rc, hR'.abs⟩

section ccs
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl rd mo ml qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (m0 : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {rdP : ConLeche.ClassRead}
include hkp henv P hIlpf hOpf

/-- **`classes_ctors`' loop refines `classesCtors`, both outcomes** (twin side: con-ron's
`classesCtors_spec`'s list induction; each class by `cos_ref` through the call's run, the extension
after it from con-ron's `classCtorsOf_spec` on its run). -/
theorem ccsLoop_ref (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp m0 mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64)
    (hq : qo.toNat = iwTop m0) (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (k : Nat) (hk' : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (c : Word) (acc : List (List ClassCtor)) (ps : List Nat)
      (lP : List ConLeche.TargetMajor),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m →
    KeepW m0 m → iwTop m0 + ml.toNat ≤ iwTop m → c ≤ ml → decNL m qo.toNat c.toNat = some ps →
    FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p) m x) ps acc →
    RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ConRon.Bridge.Inductives.dClassRead a.store R = some rdP → ms.mapM (dMajor a.store) = some MsP →
    (ms.drop c.toNat).mapM (dMajor a.store) = some lP →
    RefE (VerdictCtx p) (ccsE.loop1 p k m vis q fto ftl rd mo ml qo c)
      (ConRon.Arena.classesCtors V fe bs formerTys R ms c.toNat (ms.drop c.toNat)) a
      (fun m' xss a' => SlotsLoopPost dn vis fe env (fun m p => decLH m (decPL m (decCC m)) p) m0 ml qo acc
        m' xss a') := by
  have hms0 : decPL (truncM m0) (decTM (truncM m0)) mo.toNat ml.toNat = some ms := hms
  have hlen := decPL_length _ hms0
  have hsz0 : (m0.arr64 IW).size < 2 ^ 64 := by omega
  induction k with
  | zero => intros; rw [ccsE.loop1.eq_def]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a c acc ps lP hC hA hg hk htop hcm hps hfa hP hsh hftP hrdP hmsP hlP
  have hS := hC.stage
  have hck : c.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hcm
  by_cases hc : c < ml
  rotate_left
  · rw [ccsE.loop1.arm2 p k m vis q fto ftl rd mo ml qo c hc]
    have h1 : ml.toNat ≤ c.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hc
    have hce : c.toNat = ml.toNat := by omega
    rw [List.drop_eq_nil_of_le (by omega)]
    exact RefE.ret (by simp only [ConRon.Arena.classesCtors]; rfl)
      ⟨hC, hg, hk, htop, hP, hA, ps, by rw [← hce]; exact hps, by simpa using hfa⟩
  have hcl : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hc
  have := ml.toNat_lt
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [ccsE.loop1.arm1 p k m vis q fto ftl rd mo ml qo c hc]
  -- the class record and its constructors
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m0) hms0 c.toNat hcl
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hrd0 := iwN_rdW_at (w := mo) (k := c.toNat) hv0 hsz0
  have hnc : mo + UInt64.ofNat c.toNat = mo + c := by simp
  rw [hnc] at hrd0
  have hmc : (mo + c).toNat < iwTop m0 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : rdW (m.arr64 IW) (mo + c) = UInt64.ofNat v := by rw [rdW_grow hg hmc, hrd0.1]
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd0.2
  have hTM0 : DecB (fun m => decTM m v) m0 ms[c.toNat] := by rw [← hlen] at hcl; exact hdv
  obtain ⟨o, l, ho, hl, hv7, hcts⟩ := decTM_ctors hTM0
  have r6 := iwN_rdW_at (w := UInt64.ofNat v) (k := 6) (by rw [hvT]; exact ho) hsz0
  have r7 := iwN_rdW_at (w := UInt64.ofNat v) (k := 7) (by rw [hvT]; exact hl) hsz0
  simp only [show UInt64.ofNat 6 = (6 : Word) from rfl, show UInt64.ofNat 7 = (7 : Word) from rfl] at r6 r7
  have hv6t : (UInt64.ofNat v + 6 : Word).toNat < iwTop m0 := by rw [UInt64.toNat_add, hvT]; simp; omega
  have hv7t : (UInt64.ofNat v + 7 : Word).toNat < iwTop m0 := by rw [UInt64.toNat_add, hvT]; simp; omega
  rw [hrd, rdW_grow hg hv6t, rdW_grow hg hv7t, r6.1, r7.1]
  have hoT : (UInt64.ofNat o : Word).toNat = o := UInt64.toNat_ofNat_of_lt' r6.2
  have hlT : (UInt64.ofNat l : Word).toNat = l := UInt64.toNat_ofNat_of_lt' r7.2
  have hcts' : DecB (fun m => decPL m (decCN m) (UInt64.ofNat o : Word).toNat (UInt64.ofNat l : Word).toNat) m0
      ms[c.toNat].ctors := by rw [hoT, hlT]; exact hcts
  have hlp0 := hlp c.toNat hcl v o l hv0 ho hl
  have hol : (UInt64.ofNat o : Word).toNat + (UInt64.ofNat l : Word).toNat < 2 ^ 64 := by
    rcases decB_decPL_bound hcts with h0 | h0
    · rw [hoT, hlT, h0]; omega
    · rw [hoT, hlT]; have := (rdW (m0.arr64 CTL) 200).toNat_lt; simp only [iwTop] at h0; omega
  rw [List.drop_eq_getElem_cons (by rw [hlen]; omega)] at hlP
  obtain ⟨mP, lP', rfl, hmP, hlP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hlP
  have hmc := (ConRon.Bridge.Inductives.dMajor_inv hmP).2.2.2.2.2.1
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classesCtors]
  -- `class_ctors_of`
  rcases k with _ | k'
  · obtain ⟨e', he', h0⟩ := callE_zero p "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c,
      UInt64.ofNat o, UInt64.ofNat l] m
    rw [he', ccsE.k_class_ctors_of.none]; exact RefE.of_cls0 h0
  have hT1 := cosE_spec p P.toCosProg (k' + 1) ⟨m, Locals.init []⟩ vis q fto ftl rd mo ml c (UInt64.ofNat o)
    (UInt64.ofNat l)
  have hR1 := cos_ref hkp henv P.toCosProg hIlpf hOpf dn fe k' (by omega) hC hA (hbs.grow hg)
    (by rw [decHL_grow hg hftb]; exact hft) (Nat.le_trans hftb hg.1) (hR.grow (decCR_mono _) hg)
    (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg) hmsb
    (hcts'.grow (OMono.decPL (fun q => decCN_mono q) _ _) hg) (hlp0.grow hcts' hsz0 hg hk) hnpk
    (by rw [hk IW]; exact hsz5) hP hsh hftP hrdP hmsP hmc hformer hMs (vis := vis) (c := c)
  rcases h1 : callE p (k' + 1) "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat o,
      UInt64.ofNat l] m with e1 | ⟨r1, m1⟩
  · rw [ccsE.k_class_ctors_of.none]
    exact RefE.bind_left fun hG => RefE.run_err hT1 hG.nv hG hR1 h1
  rw [ccsE.k_class_ctors_of.arm1]
  obtain ⟨s1, hs1, -, x1, a1, run1, hR1'⟩ := RefE.run_ok hT1 hR1 h1
  subst hs1
  have hC1 := hR1'.stage
  have hg1 := hR1'.grow
  have hd1 := hR1'.slots
  have hP1 := hR1'.rc
  have hA1 := hR1'.abs
  dsimp only at hC1 hg1 hd1 hP1 hA1
  obtain ⟨cs1, -⟩ := ConRon.Bridge.Inductives.classCtorsOf_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv
    bs pP formerTys formerTysP R rdP ms MsP c.toNat hformer hMs ms[c.toNat].ctors mP.ctors a _ _ hC.check
    ⟨hsh, hftP, hrdP, hmsP, hmc⟩ run1
  have hS1 := hC1.stage
  have hk1 := callW_keepW (callW_of_callE h1)
  refine RefE.bind_right run1 ?_
  -- `rec2`
  rcases c2 : callW p (k' + 1) "rec2" [r1.headD 0, r1.tail.headD 0] s1.mem with _ | ⟨r2, m2⟩
  · rw [liftE_none, ccsE.k_rec2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ccsE.k_rec2.arm1]
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (rec2_specW p P.ha (k' + 1) P.r2 _ (r1.headD 0) (r1.tail.headD 0)) c2
  simp only at hs2 hw2; subst hs2
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hr2, hget2, hg2, hf2, ht2, hroom2⟩ := recW_post hw2 hS1.2.2.2.2.2 hsz1 rfl
  have hS2 := stage_frame_iw hS1 hf2 (by simp at ht2 hroom2; omega)
  have hk2 : KeepW s1.mem s2.mem := KeepW.of_mfr (MFr.of_iw hf2)
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hAb2 := AFr.iw hf2 hA1
  have hC2 := hC1.of_pstep hS2 hAb2 (PStep.refl hC1.check.state)
  have hb0 : iwTop m0 + ml.toNat ≤ iwTop m := htop
  have hhdr : StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) (r2.headD 0).toNat) s2.mem x1 := by
    rw [hr2]
    have hw0 : iwN s2.mem (rdW (s1.mem.arr64 CTL) 200).toNat = some (r1.headD 0).toNat := by
      have e0 := hget2 0 (by simp); rw [Nat.add_zero] at e0
      simp only [iwN, nat?, iwA, e0]; rfl
    have hw1 : iwN s2.mem ((rdW (s1.mem.arr64 CTL) 200).toNat + 1) = some (r1.tail.headD 0).toNat := by
      have e1 := hget2 1 (by simp)
      simp only [iwN, nat?, iwA, e1]; rfl
    have ht2' : iwTop s2.mem = iwTop s1.mem + 2 := by simpa using ht2
    exact stabA_decLH hw0 hw1 (Nat.le_trans hb0 hg1.1) (by rw [ht2']; exact Nat.le_refl _)
      ((hd1.mono (by omega)).grow (AgreeA.of_grow hg2))
  -- the slot write
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqc : (qo + c).toNat = qo.toNat + c.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hqb : (qo + c).toNat < (s2.mem.arr64 IW).size := by
    have := hS2.2.1; have := hg1.1; have := hg2.1; omega
  have hg12 := hg1.trans hg2
  have hS3 := hS2.set_iw (qo + c) (r2.headD 0)
  have hAb3 := set64IW_afr s2.mem (qo + c) (r2.headD 0) hAb2
  have hC3 := hC2.of_pstep hS3 hAb3 (PStep.refl hC2.check.state)
  have hg3 : IWGrow m0 (s2.mem.set64 IW (qo + c) (r2.headD 0)) := ((hg.trans hg12)).set_iw _ _ (by omega)
  have hk3 : KeepW m0 (s2.mem.set64 IW (qo + c) (r2.headD 0)) := (hk.trans (hk1.trans hk2)).set64 _ _ _
  have hA3 : AgreeA (iwTop m0 + ml.toNat) s2.mem (s2.mem.set64 IW (qo + c) (r2.headD 0)) :=
    AgreeA.set_iw _ _ (by omega)
  have hps2 : decNL s2.mem qo.toNat c.toNat = some ps := by rw [decNL_grow hg12 (by omega)]; exact hps
  have hps3 := decNL_write s2.mem qo.toNat c.toNat (qo + c) (r2.headD 0) ps hqc (by omega) hps2
  have hfa3 : FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p)
      (s2.mem.set64 IW (qo + c) (r2.headD 0)) x) (ps ++ [(r2.headD 0).toNat]) (acc ++ [x1]) :=
    FA2.snoc (FA2.imp (fun _ _ hq => (hq.grow (AgreeA.of_grow hg12)).grow hA3) hfa) (hhdr.grow hA3)
  have ih' := ih (by omega) _ a1 (c + 1)
    (acc ++ [x1]) (ps ++ [(r2.headD 0).toNat]) lP' hC3 hAb3 hg3 hk3
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg12.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [hc1]; exact hps3) hfa3 (hP2.fr (MFr.set_iw _ _ _))
    (ConRon.Bridge.Inductives.dShape_ext cs1.ext _ _ hsh) (denoteEList_ext cs1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dClassRead_ext cs1.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hmsP)
    (by rw [hc1]; exact ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hlP')
  rw [hc1] at ih'
  exact RefE.tail (k := fun x => x) (f := id) (fun _ => rfl) (fun _ => rfl) id
    (fun xss a' h => ⟨x1 :: xss, by simp only [StateT.run_bind, h]; rfl,
      fun _ hR => ⟨hR.stage, hR.grow, hR.keep, hR.top, hR.rc, hR.abs, by
        obtain ⟨ps', h1, h2⟩ := hR.slots; exact ⟨ps', h1, by simpa using h2⟩⟩⟩)
    (fun ce h => by simp only [StateT.run_bind, h]; rfl) ih'

end ccs

section ccsf
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include hkp henv P hIlpf hOpf

/-- **`classes_ctors` refines `classesCtors`, both outcomes** (`ccsLoop_ref` over the fresh result
slice). -/
theorem ccs_ref (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {m : Mem} {a : AState} {vis q fto ftl rd mo ml : Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    (hC : StageC dn vis fe env m a)
    (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp m mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64)
    (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {rdP : ConLeche.ClassRead}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store R = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (ccsE p (n + 1) m vis q fto ftl rd mo ml)
      (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a
      (fun v xss a' => SlotsPost dn vis fe env (fun m p => decLH m (decPL m (decCC m)) p) m v.1 v.2 xss a') := by
  rw [ccsE.arm1]
  rcases h1 : callW p n "iw_alloc" [ml] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, ccsE.k_iw_alloc.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ccsE.k_iw_alloc.arm1]
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (iwAlloc_specW p P.ha n ⟨m, Locals.init []⟩ ml) h1
  dsimp only at hs1 hal
  subst hs1
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hC.stage
  have hf1 := allocW_mfr hal
  have hA1 := allocW_afr hal hA
  have h := ccsLoop_ref hkp henv P hIlpf hOpf dn fe vis q fto ftl rd mo ml (r1.headD 0) bs formerTys R ms m
    hbs hft hftb hR hms hmsb hlp hnpk hsz5 hq hformer hMs (n + 1) hn s1.mem a 0 [] [] MsP
    (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hA1 hg1 (KeepW.of_mfr hf1) (by omega) UInt64.zero_le
    (by simp [decNL]) .nil (hP.fr hf1) hsh hftP hrdP hmsP (by simpa using hmsP)
  simp only [UInt64.toNat_zero, List.drop_zero] at h
  rcases hl : ccsE.loop1 p (n + 1) s1.mem vis q fto ftl rd mo ml (r1.headD 0) 0 with e' | m2 <;>
    rw [hl] at h
  · rw [ccsE.k_loop1.none]; exact h
  rw [ccsE.k_loop1.arm1]
  obtain ⟨xss, a', run, hR'⟩ := h
  obtain ⟨ps', hps', hfa'⟩ := hR'.slots
  have ht' := hR'.top
  simp only [List.nil_append] at hfa'
  exact RefE.ret run ⟨hR'.stage, hR'.grow, ⟨.inr (by simp only [List.headD_cons]; omega),
    by simp only [List.headD_cons, List.tail_cons]; omega, ps', hps',
    FA2.imp (fun _ _ hq => hq.mono (by omega)) hfa'⟩, hR'.rc, hR'.abs⟩

end ccsf

/-- **`classes_ctors` refines `classesCtors`** under `StageC` (the knot's core calls; the inputs'
denotations and scoping as con-ron's `classesCtors_spec` asks). -/
@[refines ConRon.Arena.classesCtors]
theorem classesCtors_refinesC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl rd mo ml : Word) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem) (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp s₀.mem mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {rdP : ConLeche.ClassRead}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store R = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_ctors" [vis, q, fto, ftl, rd, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      SPLA (iwTop s₀.mem) (fun m p => decLH m (decPL m (decCC m)) p) s'.mem (r.headD 0).toNat
        (r.tail.headD 0).toNat (AM.res (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a₀) ∧
      RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (RefE.triple (ccsE_spec p P (n + 1) s₀ vis q fto ftl rd mo ml)
    (ccs_ref hkp henv P hIlpf hOpf dn fe n hn hC hA hbs hft hftb hR hms hmsb hlp hnpk hsz5 hP hsh hftP
      hrdP hmsP hformer hMs)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR'.stage, hR'.grow, by rw [hres]; exact hR'.slots, hR'.rc, hR'.abs⟩

/-- **`classes_ctors`' error claim** (every fuel; `classesCtors_refinesC`'s hypotheses), from
`ccs_ref`. -/
theorem classesCtors_claim {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    {vis : Word} (hcE : CoreStubsE p) (q fto ftl rd mo ml : Word)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {rdP : ConLeche.ClassRead}
    (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem) (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp s₀.mem mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem)
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store R = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    CoreSpecE p N "classes_ctors" [vis, q, fto, ftl, rd, mo, ml]
      (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    exact RefE.coreSpecE (ccsE_spec p P (n + 1) s₀ vis q fto ftl rd mo ml) hnv ⟨hnv, hcE⟩
      (ccs_ref hkp henv P hIlpf hOpf dn fe n hN hC hA hbs hft hftb hR hms hmsb hlp hnpk hsz5 hP hsh hftP
        hrdP hmsP hformer hMs)

end L.Ind

end
