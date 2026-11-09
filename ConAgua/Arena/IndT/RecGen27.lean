module

import ConRon.Bridge.Inductives.FieldTele
import ConAgua.Verdict.IndBFields
public import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.IndT.RecGen24
import ConAgua.Arena.RecCheckSpec.TargetMajorAt
import ConAgua.Arena.RecGenSpec.DecTMSlices
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.IndT.RecGen27Models
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealOpf3
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.RecClassSpec.ClassNPcOf
public import ConAgua.Arena.TwinStep
public import ConAgua.Verdict.VCtx

@[expose] public section

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
    (hcA : DecB (fun m => decCN m cA.toNat) m cA') (hnpk : bs.nP + bs.k < 2 ^ 64)
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
  have hsz := hS.iw.iwSize
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hcAP
  obtain ⟨cvP, hcvP, rfl⟩ := hcAP
  have hname := ConRon.Bridge.denoteCV_name hcvP
  have hbsD : DecB (fun m => decBS m q.toNat) m bs := hbs.1
  have hq9 : q.toNat + 9 ≤ iwTop m := by have := hbs.ptop; omega
  have hq64 := hS.lt64 hq9
  rw [cxoE.arm1]
  -- `target_major_at`
  refine RefE.bindSim (fun _ => cxoE.k_target_major_at.none ..) (tma_step P.toCfaProg (RcAt.refl hC hA hP) rfl
    hms hmsb hmsP) fun r1 tm m1 a1 c1 _ ⟨k1, hTM, hmP⟩ => ?_
  rw [cxoE.k_target_major_at.arm1]
  obtain ⟨-, -, hmdsP, -, -, -, -, hnfsP, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hmP
  have hk1 := callW_keepW c1
  have hsz1 := k1.stage.stage.iw.iwSize
  obtain ⟨⟨no, nl, h9, h10, hno, hnl, hnfs⟩, hds, hmw13⟩ := decTM_slices hTM hsz1
  obtain ⟨ca, hca, hca3, hcv, hnmH, hnmD, hnF, hnFb, -⟩ := decCN_wordsE (hcA.grow (decCN_mono _) k1.grow) hsz1
  obtain ⟨cam, hcam, hca3m, -, -, -, -, -, hcAt⟩ := decCN_wordsE hcA hsz
  rw [h9, h10, hca]
  -- `class_ctor_of_nfs`
  refine RefE.onlySim (fun _ => cxoE.k_class_ctor_of_nfs.none ..) (fun _ _ h => h) fun r2 m2 c2 => ?_
  rcases n with _ | n
  · obtain ⟨_, _, hf⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (invoke_exec_zero p _ _ _) c2
    exact hf.elim
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (cnf_spec p P.ha P.cnf n _ (UInt64.ofNat no) (UInt64.ofNat nl) (erRd m1 (UInt64.ofNat ca))) c2
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hf2, hes⟩ := cnfF_ok _ _ _ tm.nfs n hw2 k1.stage.stage (by
    rw [UInt64.toNat_ofNat_of_lt' hno, UInt64.toNat_ofNat_of_lt' hnl]; exact hnfs) hnmH
  rw [hnmD] at hes
  have k2 := RcAt.pstep k1.stage hS2 (cnfF_afr hw2 k1.abs) (k1.rc.fr hf2) hg2 (PStep.refl k1.stage.check.state)
  have hk2 := callW_keepW c2
  have hg12 := k1.grow.trans hg2
  refine RefE.ofArms (fun h => cxoE.k_class_ctor_of_nfs.abort1 (hc1 := h) ..)
    (fun h => cxoE.k_class_ctor_of_nfs.arm1 (hc1 := h) ..) (RefE.abort0 rfl fun hel => ?_)
  -- the class's entries: the first
  obtain ⟨e0', es', hes_eq, he0, -⟩ := hes.uncons hel hS2.iw.iwSize
  rw [hes_eq] at hes
  have hEP := ConRon.Bridge.Inductives.filter_nfs k1.stage.check.state.wf
    (ConRon.Bridge.denoteN_ext hname k1.core.ext) _ _ hnfsP
  rw [hes_eq] at hEP
  obtain ⟨e0P, EsP', hEsP, he0P, hEsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hEP
  rw [hEsP] at hEP
  have he0ty := (ConRon.Bridge.Inductives.RC.dCtorNf_inv he0P).2.2.2
  have hsz2 := hS2.iw.iwSize
  generalize hE0 : rdW (s2.mem.arr64 IW) (r2.headD 0) = e0w at he0 ⊢
  obtain ⟨htyH, htyD⟩ := decNCN_ty he0 hsz2
  have hca64 : ca < 2 ^ 64 := by
    omega
  have hcaT : (UInt64.ofNat ca : Word).toNat = ca := UInt64.toNat_ofNat_of_lt' hca64
  have hcaeq : cam = ca := by
    have hcm64 : cam < 2 ^ 64 := by
      omega
    have e := hca
    rw [rdW_grow k1.grow (by omega), hcam] at e
    have := congrArg UInt64.toNat e
    rwa [UInt64.toNat_ofNat_of_lt' hcm64, hcaT] at this
  subst cam
  have hER2 : erRd s2.mem (UInt64.ofNat ca) = erRd m1 (UInt64.ofNat ca) := by
    have hcv2 : decCVp s2.mem ca = some cA'.1 := (hcv.grow (OMono.decCVp _) hg2).get (OMono.decCVp _)
    obtain ⟨hnm2, -, -⟩ := decCV_some (a := erA s2.mem) (q := ca) hcv2
    obtain ⟨w, hw, hwH, hwD⟩ := erH_rdW hnm2 hca64
    rw [hw]; exact (decI_inj_iff hwH hnmH).mp (hwD.trans hnmD.symm)
  rw [show rdW (s2.mem.arr64 (tierA EREC (UInt64.ofNat ca >>> 40))) (UInt64.ofNat ca &&& 1099511627775) =
    erRd s2.mem (UInt64.ofNat ca) from rfl, hER2]
  -- `class_minor_slot`
  have hsz5' : (s2.mem.arr64 IW).size + 5 < 2 ^ 64 := by rw [hk2 IW, hk1 IW]; exact hsz5
  have h3 := cms_ref P.cmsg (n + 1) (a := a1) (c := c) ((hR.grow (decCR_mono _) hg12).get (decCR_mono _)) hnmH hsz5'
  rw [hnmD] at h3
  dsimp only
  rw [hes_eq]
  dsimp only
  refine RefE.bindE (fun _ => cxoE.k_class_minor_slot.none ..) (fun hG => hG.nv) h3
    fun ⟨r3, m3⟩ ⟨s, ihs⟩ a3 hrun3 hR3 => ?_
  rw [cxoE.k_class_minor_slot.arm1]
  have hm3 := hR3.mem
  have ha3 := hR3.st
  have hihs := hR3.ihsB (hR.grow (decCR_mono _) hg12)
  dsimp only at hm3 ha3 hihs
  subst hm3 a3
  dsimp only
  -- `open_pis_at_fvars_f`
  obtain ⟨ca2, hca2, -, -, -, -, hnF2, -, -⟩ := decCN_wordsE (hcA.grow (decCN_mono _) hg12) hsz2
  have hq4 : rdW (s2.mem.arr64 IW) (q + 4) = UInt64.ofNat bs.nP := (partsShapeWords hg12 hbsD hq9).1
  have hq1 : rdW (s2.mem.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
    have e : (q + 1 : Word) = UInt64.ofNat (q.toNat + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    rw [e]; exact decBS_k ((hbsD.grow (decBS_mono _) hg12).get (decBS_mono _)) (by omega)
  have hsum : (UInt64.ofNat bs.nP + UInt64.ofNat bs.k : Word) = UInt64.ofNat (bs.nP + bs.k) := by
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add] <;> omega
  rw [hnF2, hq4, hq1, hsum]
  refine RefE.bindLift (fun _ => cxoE.k_open_pis_at_fvars_f.none ..) fun r4 m4 c4 => ?_
  obtain ⟨s4, rfl, -, hw4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (opfF_spec p hOpf (n + 1) _ [UInt64.ofNat cA'.2, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)]) c4
  obtain ⟨ox, a4, run4, ⟨hS4, hg4, hd4⟩, hA4⟩ := opfF_ok (vis := vis) (fe := fe) _ _ (UInt64.ofNat (bs.nP + bs.k)) htyH
    _ _ a1 r4 hw4 ⟨hS2, k2.abs⟩
  rw [UInt64.toNat_ofNat_of_lt' hnFb, UInt64.toNat_ofNat_of_lt' hnpk, htyD] at run4
  obtain ⟨q4, ho4⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run k2.stage.check.state he0ty run4
  have k4 := RcAt.pstep k2.stage hS4 hA4 (k2.rc.fr (MFr.ofOpfF hw4)) hg4 q4
  have hk4 := callW_keepW c4
  refine ⟨_, _, run4, ?_⟩
  rcases ox with _ | ⟨fvs, body⟩
  · rw [cxoE.k_open_pis_at_fvars_f.abort1 (hc1 := hd4)]; exact RefE.of_cls0 rfl
  obtain ⟨h41, ⟨hdl, hbl⟩, -⟩ := hd4
  obtain ⟨fvsP, -, -, hfvsP, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho4
  rw [cxoE.k_open_pis_at_fvars_f.arm1 (hc1 := by rw [h41]; decide)]
  simp only [getD_one, show (1 + 1 : Nat) = 2 from rfl, getD_two] at hdl hbl
  have k14 := k1.trans (k2.trans k4)
  -- `class_fields_of`
  obtain ⟨mp0, hM0⟩ := k4.rc.pos.no
  have hihB := hihs.grow (OMono.decPL (fun q => decNN_mono q) _ _) hg4
  have hib : (r3.tail.headD 0).toNat + (r3.tail.tail.headD 0).toNat < 2 ^ 64 := by
    rcases decB_decPL_bound hihB with h0 | h0
    · rw [h0]; exact (r3.tail.headD 0).toNat_lt
    · exact hS4.lt64 h0
  refine RefE.bindRun (s₀ := ⟨s4.mem, Locals.init []⟩) (fun _ => cxoE.k_class_fields_of.none ..)
    (cfoE_spec p P.cfo (n + 1) ⟨s4.mem, Locals.init []⟩ q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
      (r4.tail.headD 0) (r4.tail.tail.headD 0)) (fun hG => hG.nv) (fun hG => hG.nv)
    (cfo_ref (i := 0) (p := p) dn vis fe bs ihs (n + 1) hS4 (hbs.grow k14.grow)
      (DecB.stab (OMono.decPL (fun q => decNN_mono q) _ _) hihB) hib hdl hbl
      (by simpa using (r4.tail.tail.headD 0).toNat_lt) hM0 (a := a4))
    fun r5 s5 kinds a5 h5 _ run5 ⟨hS5, hg5, hsp5, ⟨mp5, hM5⟩, hf5, hA5⟩ => ?_
  rw [cxoE.k_class_fields_of.arm1]
  obtain ⟨q5, -⟩ := ConRon.Bridge.Inductives.classFieldsOf_spec bs pP cvP.name ihs fvs fvsP 0 a4 a5 kinds
    k4.stage.check.state ⟨ConRon.Bridge.Inductives.dShape_ext k14.core.ext _ _ hsh, hfvsP⟩ run5
  have k5 := RcAt.pstep k4.stage hS5 (hA5 k4.abs) (k4.rc.setNo hf5 ⟨mp5, hM5⟩) hg5 q5
  have k15 := k14.trans k5
  have hk5 := callW_keepW (callW_of_callE h5)
  -- `class_fields_agree`
  refine RefE.bindRun (s₀ := ⟨s5.mem, Locals.init []⟩) (fun _ => cxoE.k_class_fields_agree.none ..)
    (cfaE_spec p P.toCfaProg (n + 1) ⟨s5.mem, Locals.init []⟩ vis q fto ftl mo ml (r4.tail.headD 0)
      (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) 0 (r5.headD 0) (r5.tail.headD 0)) (fun hG => hG.nv) id
    (cfa_ref hq henv P.toCfaProg vis q fto ftl mo ml (r4.tail.headD 0)
      (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) (r5.headD 0) (r5.tail.headD 0) bs formerTys ms fvs
      (e0' :: es') kinds (n + 1) (by omega) _ a5 0 k5.stage k5.abs (hbs.grow k15.grow)
      (by rw [decHL_grow k15.grow hftb]; exact hft) (Nat.le_trans hftb k15.grow.iw)
      (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) k15.grow)
      hmsb (by rw [decHL_grow hg5 hbl]; exact hdl) (Nat.le_trans hbl hg5.iw)
      (hes.grow (fun q => decNCN_mono q) (hg4.trans hg5)) hsp5.toSPL
      (by simpa using (r5.tail.headD 0).toNat_lt) k5.rc
      (ConRon.Bridge.Inductives.dShape_ext k15.core.ext _ _ hsh) (denoteEList_ext k15.core.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext.list k15.core.ext _ _ hmsP) (denoteEList_ext k5.core.ext _ _ hfvsP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list (k4.trans k5).core.ext _ _ hEP) hformer hMs)
    fun r6 s6 u6 a6 h6 _ run6 hR6' => ?_
  rw [cxoE.k_class_fields_agree.arm1]
  obtain ⟨cs6, -⟩ := ConRon.Bridge.Inductives.classFieldsAgree_spec fe (ConRon.Bridge.CoreSpec.of_core)
    henv bs pP formerTys formerTysP ms MsP fvs fvsP (e0' :: es') (e0P :: EsP') cvP.name hformer hMs kinds 0
    a5 _ () k5.stage.check
    ⟨ConRon.Bridge.Inductives.dShape_ext k15.core.ext _ _ hsh, denoteEList_ext k15.core.ext _ _ hftP,
      ConRon.Bridge.Inductives.dMajor_ext.list k15.core.ext _ _ hmsP, denoteEList_ext k5.core.ext _ _ hfvsP,
      ConRon.Bridge.Inductives.dCtorNf_ext.list (k4.trans k5).core.ext _ _ hEP⟩ run6
  have k6 := RcAt.cstep k5.stage hR6'.stage.stage hR6'.abs hR6'.rc hR6'.grow cs6
  have k16 := k15.trans k6
  have hk6 := callW_keepW (callW_of_callE h6)
  -- `target_ctor_at`
  have hg26 : IWGrow m1 s6.mem := (k2.trans (k4.trans (k5.trans k6))).grow
  have hca3' : ca + 3 < 2 ^ 64 := hca3
  have hkm6 : KeepW m s6.mem := hk1.trans (hk2.trans (hk4.trans (hk5.trans hk6)))
  refine RefE.bindLift (fun _ => cxoE.k_target_ctor_at.none ..) fun r7 m7 c7 => ?_
  rw [cxoE.k_target_ctor_at.arm1]
  obtain ⟨s7, rfl, -, hw7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (targetCtorAt_spec p P.ha P.erc P.eri P.cvl P.tca (realCall p) (realCall_spec p) n _ (r1.headD 0)
      (UInt64.ofNat ca)) c7
  obtain ⟨t7, a7, run7, hS7, hg7, ht7H, ht7D, hA7f⟩ := tcW_ok dn vis fe n _ _ a6 (r1.headD 0) (UInt64.ofNat ca)
    tm cA'.1 r7 (realCall p) (IlpRd.realC hIlpf k6.stage) k6.stage.stage
      ((hTM.grow (decTM_mono _) hg26).get (decTM_mono _))
      (by rw [hcaT]; exact (hcv.grow (OMono.decCVp _) hg26).get (OMono.decCVp _)) hmw13 (by rw [hcaT]; omega)
      hw7
  rw [← ht7D] at run7
  obtain ⟨cs7, ht0P⟩ := ConRon.Bridge.Inductives.targetCtorAt_spec fe tm _ cA'.1 cvP a6 a7 _ k6.stage.check
    ⟨ConRon.Bridge.Inductives.dMajor_ext (k2.trans (k4.trans (k5.trans k6))).core.ext _ _ hmP,
      ConRon.Bridge.Inductives.dExt_denoteCV k16.core.ext _ _ hcvP⟩ run7
  have k7 := RcAt.cstep k6.stage hS7 (hA7f k6.abs) (k6.rc.fr (tcW_mfr (IlpFr.real hIlpf) hw7)) hg7 cs7
  refine ⟨_, _, run7, ?_⟩
  -- `inst_pis_with`
  have hsz7 := hS7.iw.iwSize
  obtain ⟨-, hds7, -⟩ := decTM_slices (hTM.grow (decTM_mono _) (hg26.trans hg7)) hsz7
  refine RefE.bindLift (fun _ => cxoE.k_inst_pis_with.none ..) fun r8 m8 c8 => ?_
  obtain ⟨s8, rfl, -, hw8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (instPisWith_spec p P.hv P.ipw P.hi1 (n + 1) _ _ _ _) c8
  obtain ⟨ox, a8, run8, hS8, hg8, hd8⟩ := instW_ok0 (dn := dn) (n + 1) hw8 hS7 ht7H hds7
  obtain ⟨q8, -⟩ := ConRon.Bridge.Inductives.instPisWith_spec tm.ds _ _ _ a7 a8 ox k7.stage.check.state
    ⟨denoteEList_ext (k2.trans (k4.trans (k5.trans (k6.trans k7)))).core.ext _ _ hmdsP, ht0P⟩ run8
  have k8 := RcAt.pstep k7.stage hS8 (instW_afr _ _ _ _ _ _ _ hw8 k7.abs) (k7.rc.fr (instW_mfr _ _ _ _ _ _ _ hw8))
    hg8 q8
  have k18 := k16.trans (k7.trans k8)
  refine ⟨_, _, run8, ?_⟩
  rcases ox with _ | tyD
  · rw [cxoE.k_inst_pis_with.abort1 (hc1 := hd8)]; exact RefE.of_cls0 rfl
  obtain ⟨h81, h8H, h8D⟩ := hd8
  rw [cxoE.k_inst_pis_with.arm1 (hc1 := by rw [h81]; decide)]
  -- `rec6`
  have hsz8 := hS8.iw.iwSize
  obtain ⟨ca8, hca8, -, hcv8, -, -, hnF8, -, -⟩ := decCN_wordsE (hcA.grow (decCN_mono _) k18.grow) hsz8
  obtain ⟨hty8H, hty8D⟩ := decNCN_ty (he0.grow (decNCN_mono _) (k4.trans (k5.trans (k6.trans (k7.trans k8)))).grow)
    hsz8
  rw [hnF8]
  refine RefE.onlySim (fun _ => cxoE.k_rec6.none ..) (fun _ _ h => h) fun r9 m9 c9 => ?_
  rw [cxoE.k_rec6.arm1]
  obtain ⟨s9, hs9, -, hw9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (rec6_specW p P.ha P.r6 (n + 1) _ _ _ _ _ _ _) c9
  simp only at hs9 hw9; subst hs9
  obtain ⟨hS9, hg9, hq9', ht9, hget9⟩ := posRecW_stage hw9 hS8 (by simp)
  have hA9 := posRecW_afr hw9 k8.abs
  refine RefE.ret (y := ⟨cA'.1, cA'.2, kinds, tyD, e0'.ty⟩) (a' := a8) rfl
    ⟨k8.stage.of_pstep hS9 hA9 (PStep.refl k8.stage.check.state), k18.grow.trans hg9, ?_,
      k8.rc.fr (posRecW_mfr hw9), hA9⟩
  have := rec6_decCC (m := s8.mem) (q := r9.headD 0) (cvw := UInt64.ofNat ca) (nFw := UInt64.ofNat cA'.2)
    (ko := r5.headD 0) (kl := r5.tail.headD 0) (tyD := r8.tail.headD 0) (tyN := rdW (s8.mem.arr64 IW) (e0w + 4))
    (fun j hj => by simpa using hget9 j (by simpa using hj)) (by simp at ht9; omega)
    (by rw [hq9']; exact k18.grow.iw) hg9
    (by rw [hcaT]; exact hcv.grow (OMono.decCVp _) (hg26.trans (hg7.trans hg8)))
    ((hsp5.mono k14.grow.iw).grow (AgreeA.of_grow (k6.trans (k7.trans k8)).grow)) h8H hty8H
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
    (hcA : DecB (fun m => decCN m cA.toNat) s₀.mem cA') (hnpk : bs.nP + bs.k < 2 ^ 64)
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
    (cxo_ref hq henv P hIlpf hOpf dn fe n hn hC hA hbs hft hftb hR hms hmsb hcA hnpk hsz5 hP hsh hftP
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
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m0 cAs) 
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
  sorry

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
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m cAs) 
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
  sorry

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
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) s₀.mem cAs) 
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
    (cos_ref hkp henv P hIlpf hOpf dn fe n hn hC hA hbs hft hftb hR hms hmsb hcAs hnpk hsz5 hP hsh hftP
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
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64)
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
  sorry

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
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64)
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
  sorry

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
    (hnpk : bs.nP + bs.k < 2 ^ 64)
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
    (ccs_ref hkp henv P hIlpf hOpf dn fe n hn hC hA hbs hft hftb hR hms hmsb hnpk hsz5 hP hsh hftP
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
    (hnpk : bs.nP + bs.k < 2 ^ 64)
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
      (ccs_ref hkp henv P hIlpf hOpf dn fe n hN hC hA hbs hft hftb hR hms hmsb hnpk hsz5 hP hsh hftP
        hrdP hmsP hformer hMs)

end L.Ind

end
