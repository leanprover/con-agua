import ConAgua.Arena.IndT.RecGen24
import ConAgua.Arena.RecCheckSpec.TargetMajorAt
import ConAgua.Arena.RecGenSpec.DecTMSlices
import ConAgua.Arena.RecGenSpec.ClassFieldsOf

/-!
# `classCtorOf`, `classCtorsOf`, `classesCtors` under `StageC` (lane `indstaget`, helper `pds`)

`class_ctor_of`'s model (`cxoW`, the callees through the program's `callW`) and the two loops above
it, from `StageC` and the inputs' denotations con-ron's `classCtorOf_spec` asks; its twin side
transcribed from that spec's proof: `targetMajorAt` (`targetMajorAt_spec`), the entries' filter and
the minor slot (state kept), `openPisAtFvarsF` (`openPisAtFvarsF_run`), `classFieldsOf`
(`classFieldsOf_spec`), `classFieldsAgree` (`classFieldsAgree_refinesC`, con-ron's spec on its run),
`targetCtorAt` (`targetCtorAt_spec`, a `CSpec`), `instPisWith` (`instPisWith_spec`), the record (L
only).
-/


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
    (by simp [opfA, instListA, mkA, instA, liftA, SPN, IW, FVREC, FVSLOT, FVLP])
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

theorem cfgW_afr : ∀ (n : Nat) (m m' : Mem) (mo ml io il i fo fl : Word) (r : List Word),
    cfgW n m mo ml io il i fo fl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [cfgW] at h
  | n + 1, m, m', mo, ml, io, il, i, fo, fl, r, h => by
    by_cases hl : fl = 0
    · rw [cfgW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [cfgW_cons (h := hl)] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
    rw [cfgK1_some] at h
    refine (ftdF_afr h1).trans ?_
    obtain ⟨⟨occ, m2⟩, h2, h⟩ := of_K h rfl
    rw [cfgK2_some] at h
    refine (noConstWf_afr h2).trans ?_
    -- after the kind: the record, the rest, the cons
    have tail : ∀ (r5 : List Word) (m5 : Mem), recW m2 1 [0] = some (r5, m5) ∨
        (∃ r4 m4 cls, piBW n m2 CWF (r1.headD 0) = some (r4, m4) ∧ recW m4 3 [1, cls, r4.tail.headD 0] =
          some (r5, m5)) → AFr m2 m5 := by
      rintro r5 m5 (h5 | ⟨r4, m4, cls, h4, h5⟩)
      · exact recW_afr h5
      · exact (piBW_afr _ _ _ _ _ _ h4).trans (recW_afr h5)
    obtain ⟨⟨hc, cls⟩, h3, h⟩ := of_K h rfl
    have fin : ∀ (o5 : Option (List Word × Mem)), (∀ r5 m5, o5 = some (r5, m5) → AFr m2 m5) →
        cfgK5 n (fun m5 => cfgW n m5 mo ml io il (i + 1) (fo + 1) (fl - 1)) o5 = some (r, m') →
        AFr m2 m' := by
      intro o5 hA5 h5
      obtain ⟨⟨r5, m5⟩, rfl, h5⟩ := of_K h5 (by simp only [cfgK5])
      rw [cfgK5_some] at h5
      obtain ⟨⟨r6, m6⟩, h6, h5⟩ := of_K h5 rfl
      rw [cfgK7_some] at h5
      obtain ⟨⟨r7, m7⟩, h7, h5⟩ := of_K h5 rfl
      rw [cfgK6_some] at h5
      cases h5; exact ((hA5 r5 m5 rfl).trans (cfgW_afr n _ _ _ _ _ _ _ _ _ _ h6)).trans (consW_afr h7)
    by_cases c0 : occ = 0 ∧ hc = 0
    · rw [cfgK3_ord (h := c0)] at h
      exact fin _ (fun r5 m5 e => tail r5 m5 (.inl e)) h
    by_cases c1 : occ ≠ 0 ∧ hc = 1
    · rw [cfgK3_rec (h0 := c0) (h := c1)] at h
      obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl
      rw [cfgK4_some] at h
      exact fin _ (fun r5 m5 e => tail r5 m5 (.inr ⟨r4, m4, cls, h4, e⟩)) h
    · rw [cfgK3_bad (h0 := c0) (h := c1)] at h; cases h

theorem cfoW_afr {n : Nat} {m m' : Mem} {q io il i fo fl : Word} {r : List Word}
    (h : cfoW n m q io il i fo fl = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [cfoW] at h
  rw [cfoW.arm1] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [cfoW.k_block_shape_member_names.arm1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
  rw [cfoW.k_class_fields_of_go.arm1] at h
  cases h; exact (memberNamesW_afr h1).trans (cfgW_afr _ _ _ _ _ _ _ _ _ _ _ h2)

section rel
variable {p : Prog} (hq : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CxoProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include hq henv P hIlpf hOpf

/-- **`class_ctor_of`'s model under `StageC`** (twin side: con-ron's `classCtorOf_spec`'s proof). -/
theorem cxoW_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState} {vis q fto ftl rd mo ml c cA : Word} {r : List Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cA' : IConstantVal × Nat}
    (h : cxoW p n m vis q fto ftl rd mo ml c cA = some (r, m')) (hC : StageC dn vis fe env m a)
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
    ∃ x a', (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA').run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        StabA (iwTop m) (fun m => decCC m (r.headD 0).toNat) m' x ∧ RcMR m' ∧ AbsOK m' := by
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hcAP
  obtain ⟨cvP, hcvP, rfl⟩ := hcAP
  have hname := ConRon.Bridge.denoteCV_name hcvP
  have hbsD : DecB (fun m => decBS m q.toNat) m bs := hbs.1
  have hq9 : q.toNat + 9 ≤ iwTop m := by have := hbs.ptop; omega
  have hq64 := hS.lt64 hq9
  unfold cxoW at h
  -- `target_major_at`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [cxoK1_some] at h
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
  rw [h9, h10, hca] at h
  -- `class_ctor_of_nfs`
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
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
  -- the first entry
  have hel : ¬ (r2.tail.headD 0 = 0) := fun hel => by rw [cxoK2_bad (h := hel)] at h; cases h
  rw [cxoK2_ok (h := hel)] at h
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
  generalize hE0 : rdW (s2.mem.arr64 IW) (r2.headD 0) = e0w at h he0
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
  rw [hER2] at h
  -- `class_minor_slot`
  obtain ⟨⟨r3, m3⟩, c3, h⟩ := of_K h rfl
  rw [cxoK3_some] at h
  obtain ⟨s3, rfl, -, hm3, hw3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classMinorSlot_spec p P.cmsg P.cms n _ rd c (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))) c3
  rw [hm3] at h
  have hsz5' : (s2.mem.arr64 IW).size + 5 < 2 ^ 64 := by rw [hk2 IW, hk1 IW]; exact hsz5
  obtain ⟨s, ihs, hhits, -, hihs⟩ := cms_decB n hw3 (hR.grow (decCR_mono _) hg12) hnmH hsz5'
  have hrun3 : (ConRon.Arena.classMinorSlot R c.toNat cA'.1.name).run a1 = .ok ((s, ihs), a1) := by
    have hits := hitsFrom_eq c.toNat (decI (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))) 0 R.slots
    simp only [Nat.zero_add] at hits
    rw [← hnmD]
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits, hhits]
    rfl
  -- `open_pis_at_fvars_f`
  obtain ⟨ca2, hca2, -, -, -, -, hnF2, -, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg12) hsz2
  have hq4 : rdW (s2.mem.arr64 IW) (q + 4) = UInt64.ofNat bs.nP := (partsShapeWords hg12 hbsD hq9).1
  have hq1 : rdW (s2.mem.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
    have e : (q + 1 : Word) = UInt64.ofNat (q.toNat + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    rw [e]; exact decBS_k ((hbsD.grow (decBS_mono _) hg12).get (decBS_mono _)) (by omega)
  have hsum : (UInt64.ofNat bs.nP + UInt64.ofNat bs.k : Word) = UInt64.ofNat (bs.nP + bs.k) := by
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add] <;> omega
  rw [hnF2, hq4, hq1, hsum] at h
  obtain ⟨⟨r4, m4⟩, c4, h⟩ := of_K h rfl
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
  rcases ox with _ | ⟨fvs, body⟩
  · rw [cxoK4_bad (h := hd4)] at h; cases h
  obtain ⟨h41, ⟨hdl, hbl⟩, -⟩ := hd4
  obtain ⟨fvsP, -, -, hfvsP, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho4
  have q14 := q1.trans q4
  have h0 : ¬ r4.headD 0 = 0 := by rw [h41]; decide
  rw [cxoK4_ok (h := h0)] at h
  simp only [getD_one, show (1 + 1 : Nat) = 2 from rfl, getD_two] at hdl hbl
  have hg24 := hg4
  have hg14 := hg12.trans hg4
  -- `class_fields_of`
  obtain ⟨mp0, hM0⟩ := hP4.pos.no
  obtain ⟨⟨r5, m5⟩, c5, h⟩ := of_K h rfl
  rw [cxoK5_some] at h
  have hihB := hihs.grow (OMono.decPL (fun q => decNN_mono q) _ _) hg24
  have hib : (r3.tail.headD 0).toNat + (r3.tail.tail.headD 0).toNat < 2 ^ 64 := by
    rcases decB_decPL_bound hihB with h0 | h0
    · rw [h0]; exact (r3.tail.headD 0).toNat_lt
    · exact hS4.lt64 h0
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hsp5, ⟨mp5, hM5⟩, hf5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classFieldsOf_refines p P.cfo (n + 1) _ a4 dn vis fe q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
      (r4.tail.headD 0) (r4.tail.tail.headD 0) bs ihs fvs mp0 hS4 (hbs.grow hg14)
      (DecB.stab (OMono.decPL (fun q => decNN_mono q) _ _) hihB) hib hdl hbl
      (by simpa using (r4.tail.tail.headD 0).toNat_lt) hM0) c5
  simp only at hs5 hS5 hg5 hsp5 hM5 hf5; subst hs5
  obtain ⟨s5', hs5', -, hw5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classFieldsOf_spec p P.cfo (n + 1) _ q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
      (r4.tail.headD 0) (r4.tail.tail.headD 0)) c5
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
  have hk5 := callW_keepW c5
  -- `class_fields_agree`
  obtain ⟨⟨r6, m6⟩, c6, h⟩ := of_K h rfl
  rw [cxoK6_some] at h
  obtain ⟨s6, hs6, -, hok6, hC6, hg6, hP6, hA6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (classFieldsAgree_refinesC hq henv P.toCfaProg vis q fto ftl mo ml (r4.tail.headD 0)
      (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) (r5.headD 0) (r5.tail.headD 0) bs formerTys ms fvs
      (e0' :: es') kinds (n + 1) (by omega) _ a5 0 hC5 hA5 (hbs.grow hg15) (by rw [decHL_grow hg15 hftb]; exact hft)
      (Nat.le_trans hftb hg15.1) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg15)
      hmsb (by rw [decHL_grow hg5 hbl]; exact hdl) (Nat.le_trans hbl hg5.1)
      (hes.grow (fun q => decNCN_mono q) (hg4.trans hg5)) hsp5.toSPL
      (by simpa using (r5.tail.headD 0).toNat_lt) hP5
      (ConRon.Bridge.Inductives.dShape_ext q15.ext _ _ hsh) (denoteEList_ext q15.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext.list q15.ext _ _ hmsP) (denoteEList_ext q5.ext _ _ hfvsP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list (q4.trans q5).ext _ _ hEP) hformer hMs) c6
  simp only at hs6 hC6 hg6 hP6 hA6; subst hs6
  have run6 := AM.run_of_ok _ a5 hok6
  obtain ⟨cs6, -⟩ := ConRon.Bridge.Inductives.classFieldsAgree_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys formerTysP ms MsP fvs fvsP (e0' :: es') (e0P :: EsP') cvP.name hformer hMs kinds 0
    a5 _ () hC5.check
    ⟨ConRon.Bridge.Inductives.dShape_ext q15.ext _ _ hsh, denoteEList_ext q15.ext _ _ hftP,
      ConRon.Bridge.Inductives.dMajor_ext.list q15.ext _ _ hmsP, denoteEList_ext q5.ext _ _ hfvsP,
      ConRon.Bridge.Inductives.dCtorNf_ext.list (q4.trans q5).ext _ _ hEP⟩ run6
  have cs16 := (q15.toCore hC.check).trans cs6
  generalize ha6 : AM.st (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs (e0' :: es') (0 : Word).toNat
    kinds) a5 = a6 at run6 hC6 cs6 cs16
  have hS6 := hC6.stage
  have hg16 := hg15.trans hg6
  have hk6 := callW_keepW c6
  -- `target_ctor_at`
  obtain ⟨⟨r7, m7⟩, c7, h⟩ := of_K h rfl
  rw [cxoK7_some] at h
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
  have hk7 := callW_keepW c7
  have hg17 := hg16.trans hg7
  -- `inst_pis_with`
  have hsz7 := hS7.2.2.2.1
  obtain ⟨-, hds7, -⟩ := decTM_slices (hTM.grow (decTM_mono _) (hg26.trans hg7)) hsz7
  obtain ⟨⟨r8, m8⟩, c8, h⟩ := of_K h rfl
  obtain ⟨s8, rfl, -, hw8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (instPisWith_spec p P.hv P.ipw P.hi1 (n + 1) _ _ _ _) c8
  obtain ⟨ox, a8, run8, hS8, hg8, hd8⟩ := instW_ok0 (n + 1) hw8 hS7 ht7H hds7
  have hP8 := hP7.fr (instW_mfr _ _ _ _ _ _ _ hw8)
  have hA8 := instW_afr _ _ _ _ _ _ _ hw8 hA7
  obtain ⟨q8, -⟩ := ConRon.Bridge.Inductives.instPisWith_spec tm.ds _ _ _ a7 a8 ox hC7.check.state
    ⟨denoteEList_ext ((q4.trans q5).ext.trans (cs6.ext.trans cs7.ext)) _ _ hmdsP, ht0P⟩ run8
  have hC8 := hC7.of_pstep hS8 hA8 q8
  have hg18 := hg17.trans hg8
  rcases ox with _ | tyD
  · rw [cxoK8_bad (h := hd8)] at h; cases h
  obtain ⟨h81, h8H, h8D⟩ := hd8
  have h0 : ¬ r8.headD 0 = 0 := by rw [h81]; decide
  rw [cxoK8_ok (h := h0)] at h
  -- `rec6`
  have hsz8 := hS8.2.2.2.1
  obtain ⟨ca8, hca8, -, hcv8, -, -, hnF8, -, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg18) hsz8
  obtain ⟨hty8H, hty8D⟩ := decNCN_ty (he0.grow (decNCN_mono _) (hg4.trans (hg5.trans (hg6.trans (hg7.trans hg8)))))
    hsz8
  rw [hnF8] at h
  obtain ⟨⟨r9, m9⟩, c9, h⟩ := of_K h rfl
  rw [cxoK9_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s9, hs9, -, hw9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (rec6_specW p P.ha P.r6 (n + 1) _ _ _ _ _ _ _) c9
  simp only at hs9 hw9; subst hs9
  obtain ⟨hS9, hg9, hq9', ht9, hget9⟩ := posRecW_stage hw9 hS8 (by simp)
  have hP9 := hP8.fr (posRecW_mfr hw9)
  have hA9 := posRecW_afr hw9 hA8
  refine ⟨⟨cA'.1, cA'.2, kinds, tyD, e0'.ty⟩, a8, ?_, hC8.of_pstep hS9 hA9 (PStep.refl hC8.check.state),
    hg18.trans hg9, ?_, hP9, hA9⟩
  · simp only [ConRon.Arena.classCtorOf, StateT.run_bind, run1, except_ok_bind]
    rw [hes_eq]
    simp only [show (0 : Word).toNat = 0 from rfl] at run5 run6
    simp only [StateT.run_bind, hrun3, except_ok_bind, run4, run5, run6, run7, run8]
    rfl
  · have := rec6_decCC (m := s8.mem) (q := r9.headD 0) (cvw := UInt64.ofNat ca) (nFw := UInt64.ofNat cA'.2)
      (ko := r5.headD 0) (kl := r5.tail.headD 0) (tyD := r8.tail.headD 0) (tyN := rdW (s8.mem.arr64 IW) (e0w + 4))
      (fun j hj => by simpa using hget9 j (by simpa using hj)) (by simp at ht9; omega)
      (by rw [hq9']; exact hg18.1) hg9
      (by rw [hcaT]; exact hcv.grow (OMono.decCVp _) (hg26.trans (hg7.trans hg8)))
      ((hsp5.mono hg14.1).grow (AgreeA.of_grow (hg6.trans (hg7.trans hg8)))) h8H hty8H
    simp only [List.headD_cons]
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
  refine triple_post (cxo_spec p P.cxo n s₀ vis q fto ftl rd mo ml c cA) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', run, hC', hg, hd, hP', hA'⟩ := cxoW_okC hq henv P hIlpf hOpf dn fe n (by omega) hm hC hA hbs hft hftb
    hR hms hmsb hcA hlp hnpk hsz5 hP hsh hftP hmsP hcAP hformer hMs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hres]; exact hd, hP', hA'⟩

section cos
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CosProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl rd mo ml c ao al qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (cAs : List (IConstantVal × Nat)) (m0 : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {rdP : ConLeche.ClassRead}
include hkp henv P hIlpf hOpf

/-- **`class_ctors_of`' loop under `StageC`** (twin side: con-ron's `classCtorsOf_spec`'s list
induction, the extension after one constructor from con-ron's `classCtorOf_spec` on its run). -/
theorem cosW_okC (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m0 cAs) (hlp : CtorsLp m0 ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64) (hq : qo.toNat = iwTop m0)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (k : Nat) (hk' : k ≤ 2 ^ 62) :
    ∀ (m m' : Mem) (a : AState) (j : Word) (acc : List ClassCtor) (ps : List Nat)
      (csP : List (ConLeche.ConstantVal × Nat)),
    cosW p k m vis q fto ftl rd mo ml c ao al qo j = some m' → StageC dn vis fe env m a → AbsOK m →
    IWGrow m0 m →
    KeepW m0 m → iwTop m0 + al.toNat ≤ iwTop m → j ≤ al → decNL m qo.toNat j.toNat = some ps →
    FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p) m x) ps acc → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ConRon.Bridge.Inductives.dClassRead a.store R = some rdP → ms.mapM (dMajor a.store) = some MsP →
    dCtors a.store (cAs.drop j.toNat) = some csP →
    ∃ xs a', (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat (cAs.drop j.toNat)).run a = .ok (xs, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m0 m' ∧ KeepW m0 m' ∧ iwTop m0 + al.toNat ≤ iwTop m' ∧ RcMR m' ∧
      AbsOK m' ∧
      ∃ ps', decNL m' qo.toNat al.toNat = some ps' ∧
        FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p) m' x) ps' (acc ++ xs) := by
  have hcAs0 : decPL (truncM m0) (decCN (truncM m0)) ao.toNat al.toNat = some cAs := hcAs
  have hlen := decPL_length _ hcAs0
  induction k with
  | zero => intro m m' a j acc ps csP h; simp [cosW] at h
  | succ k ih =>
  intro m m' a j acc ps csP h hC hA hg hk htop hja hps hfa hP hsh hftP hrdP hmsP hcsP
  have hS := hC.stage
  have hjk : j.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hja
  by_cases hj : j < al
  rotate_left
  · rw [cosW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : al.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have hje : j.toNat = al.toNat := by omega
    rw [List.drop_eq_nil_of_le (by omega)]
    refine ⟨[], a, rfl, hC, hg, hk, htop, hP, hA, ps, by rw [← hje]; exact hps, by simpa using hfa⟩
  have hjl : j.toNat < al.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := al.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [cosW_step (h := hj)] at h
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
  rw [hrd] at h
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd0.2
  have hcA0 : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m0 cAs[j.toNat] := by
    rw [hvT]; rw [← hlen] at hjl; exact hdv
  have hlp0 : CtorLp m0 (UInt64.ofNat v) := by
    have := hlp j.toNat hjl; rw [hnj, hrd0.1] at this; exact this
  rw [List.drop_eq_getElem_cons (by rw [hlen]; omega)] at hcsP
  obtain ⟨cAP, csP', rfl, hcAP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  -- `class_ctor_of`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  obtain ⟨s1, hs1, -, hok1, hC1, hg1, hd1, hP1, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classCtorOf_refinesC hkp henv P.toCxoProg hIlpf hOpf k (by omega) _ a dn fe vis q fto ftl rd mo ml c (UInt64.ofNat v) bs
      formerTys R ms cAs[j.toNat] hC hA (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft) (Nat.le_trans hftb hg.1)
      (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg) hmsb
      (hcA0.grow (decCN_mono _) hg) (hlp0.grow hcA0 hsz0 hg hk) hnpk (by rw [hk IW]; exact hsz5) hP
      hsh hftP hmsP hcAP hformer hMs) c1
  simp only at hs1 hC1 hg1 hd1 hP1 hA1; subst hs1
  have run1 := AM.run_of_ok _ a hok1
  obtain ⟨cs1, -⟩ := ConRon.Bridge.Inductives.classCtorOf_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv
    bs pP formerTys formerTysP R rdP ms MsP c.toNat cAs[j.toNat] cAP hformer hMs a _ _ hC.check
    ⟨hsh, hftP, hrdP, hmsP, hcAP⟩ run1
  generalize hx1 : AM.res (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cAs[j.toNat]) a = x1 at run1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cAs[j.toNat]) a = a1 at run1 hC1 cs1
  have hS1 := hC1.stage
  have hk1 := callW_keepW c1
  -- the slot write
  have hsz1 := hS1.2.2.2.1
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqj : (qo + j).toNat = qo.toNat + j.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hqb : (qo + j).toNat < (s1.mem.arr64 IW).size := by
    have := hS1.2.1; have := hg1.1; omega
  rw [cosK_ok (h := hqb)] at h
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
  have hps2 := decNL_write s1.mem qo.toNat j.toNat (qo + j) (r1.headD 0) ps hqj (by omega) hps1
  have hfa2 : FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p)
      (s1.mem.set64 IW (qo + j) (r1.headD 0)) x) (ps ++ [(r1.headD 0).toNat]) (acc ++ [x1]) :=
    FA2.snoc (FA2.imp (fun _ _ hq => (hq.grow (AgreeA.of_grow hg1)).grow hA2) hfa)
      ((hd1.mono hb0).grow hA2)
  obtain ⟨xs, a', run2, hC', hg', hk', ht', hP', hA', ps', hps', hfa'⟩ := ih (by omega) _ m' a1 (j + 1)
    (acc ++ [x1]) (ps ++ [(r1.headD 0).toNat]) csP' h hC2 hAb2 hg2 hk2
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg1.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [hj1]; exact hps2) hfa2 (hP1.fr (MFr.set_iw _ _ _))
    (ConRon.Bridge.Inductives.dShape_ext cs1.ext _ _ hsh) (denoteEList_ext cs1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dClassRead_ext cs1.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hmsP)
    (by rw [hj1]; exact ConRon.Bridge.Inductives.dCtors_ext cs1.ext _ _ hcsP')
  refine ⟨x1 :: xs, a', ?_, hC', hg', hk', ht', hP', hA', ps', hps', by simpa using hfa'⟩
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classCtorsOf]
  rw [hj1] at run2
  simp only [StateT.run_bind, run1, except_ok_bind, run2]
  rfl

end cos

section cosf
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CosProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include hkp henv P hIlpf hOpf

/-- `cosW_okC` from the fresh result slice. -/
theorem cosF_okC (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {m m' : Mem} {a : AState} {vis q fto ftl rd mo ml c ao al : Word} {r : List Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cAs : List (IConstantVal × Nat)}
    (h : cosF p n m vis q fto ftl rd mo ml c ao al = some (r, m')) (hC : StageC dn vis fe env m a)
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
    ∃ xs a', (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs).run a = .ok (xs, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
      SPLA (iwTop m) decCC m' (r.headD 0).toNat (r.tail.headD 0).toNat xs ∧ RcMR m' ∧ AbsOK m' := by
  rw [cosF_eq] at h
  obtain ⟨⟨qo, m1⟩, hal, h⟩ := of_K h rfl
  rw [cosK1_some] at h
  obtain ⟨m2, hl, h⟩ := of_K h rfl
  rw [cosK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hC.stage
  have hf1 := allocW_mfr hal
  have hA1 := allocW_afr hal hA
  obtain ⟨xs, a', run, hC', hg', -, ht', hP', hA', ps', hps', hfa'⟩ := cosW_okC hkp henv P hIlpf hOpf dn fe vis q fto ftl rd
    mo ml c ao al qo bs formerTys R ms cAs m hbs hft hftb hR hms hmsb hcAs hlp hnpk hsz5 hq hformer hMs
    (n + 1) (by omega) m1 m2 a 0 [] [] csP hl (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hA1 hg1
    (KeepW.of_mfr hf1) (by omega) UInt64.zero_le (by simp [decNL]) .nil (hP.fr hf1) hsh hftP hrdP hmsP
    (by simpa using hcsP)
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hfa'
  refine ⟨xs, a', run, hC', hg', ⟨.inr (by simp; omega), by simp; omega, ps', hps',
    FA2.imp (fun _ _ hq => hq.mono (by omega)) hfa'⟩, hP', hA'⟩

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
  refine triple_post (cos_spec p P.ha P.cos n s₀ vis q fto ftl rd mo ml c ao al) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', run, hC', hg, hd, hP', hA'⟩ := cosF_okC hkp henv P hIlpf hOpf dn fe n (by omega) hm hC hA hbs hft hftb
    hR hms hmsb hcAs hlp hnpk hsz5 hP hsh hftP hrdP hmsP hcsP hformer hMs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hres]; exact hd, hP', hA'⟩

section ccs
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl rd mo ml qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (m0 : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {rdP : ConLeche.ClassRead}
include hkp henv P hIlpf hOpf

/-- **`classes_ctors`' loop under `StageC`** (twin side: con-ron's `classesCtors_spec`'s list
induction, the extension after one class from con-ron's `classCtorsOf_spec` on its run). -/
theorem ccsW_okC (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp m0 mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64)
    (hq : qo.toNat = iwTop m0) (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (k : Nat) (hk' : k ≤ 2 ^ 62) :
    ∀ (m m' : Mem) (a : AState) (c : Word) (acc : List (List ClassCtor)) (ps : List Nat)
      (lP : List ConLeche.TargetMajor),
    ccsW p k m vis q fto ftl rd mo ml qo c = some m' → StageC dn vis fe env m a → AbsOK m → IWGrow m0 m →
    KeepW m0 m → iwTop m0 + ml.toNat ≤ iwTop m → c ≤ ml → decNL m qo.toNat c.toNat = some ps →
    FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p) m x) ps acc →
    RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ConRon.Bridge.Inductives.dClassRead a.store R = some rdP → ms.mapM (dMajor a.store) = some MsP →
    (ms.drop c.toNat).mapM (dMajor a.store) = some lP →
    ∃ xss a', (ConRon.Arena.classesCtors V fe bs formerTys R ms c.toNat (ms.drop c.toNat)).run a =
        .ok (xss, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m0 m' ∧ KeepW m0 m' ∧ iwTop m0 + ml.toNat ≤ iwTop m' ∧ RcMR m' ∧
      AbsOK m' ∧
      ∃ ps', decNL m' qo.toNat ml.toNat = some ps' ∧
        FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p) m' x) ps'
          (acc ++ xss) := by
  have hms0 : decPL (truncM m0) (decTM (truncM m0)) mo.toNat ml.toNat = some ms := hms
  have hlen := decPL_length _ hms0
  have hsz0 : (m0.arr64 IW).size < 2 ^ 64 := by omega
  induction k with
  | zero => intro m m' a c acc ps lP h; simp [ccsW] at h
  | succ k ih =>
  intro m m' a c acc ps lP h hC hA hg hk htop hcm hps hfa hP hsh hftP hrdP hmsP hlP
  have hS := hC.stage
  have hck : c.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hcm
  by_cases hc : c < ml
  rotate_left
  · rw [ccsW_exit (h := hc)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : ml.toNat ≤ c.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hc
    have hce : c.toNat = ml.toNat := by omega
    rw [List.drop_eq_nil_of_le (by omega)]
    refine ⟨[], a, ?_, hC, hg, hk, htop, hP, hA, ps, by rw [← hce]; exact hps, by simpa using hfa⟩
    simp only [ConRon.Arena.classesCtors]; rfl
  have hcl : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hc
  have := ml.toNat_lt
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [ccsW_step (h := hc)] at h
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
  rw [hrd, rdW_grow hg hv6t, rdW_grow hg hv7t, r6.1, r7.1] at h
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
  -- `class_ctors_of`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [ccsK1_some] at h
  rcases k with _ | k'
  · obtain ⟨_, _, hf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (invoke_exec_zero p _ _ _) c1
    exact hf.elim
  obtain ⟨s1, hs1, -, hok1, hC1, hg1, hd1, hP1, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classCtorsOf_refinesC hkp henv P.toCosProg hIlpf hOpf (k' + 1) (by omega) _ a dn fe vis q fto ftl rd mo ml c
      (UInt64.ofNat o) (UInt64.ofNat l) bs formerTys R ms ms[c.toNat].ctors hC hA (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft)
      (Nat.le_trans hftb hg.1) (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg)
      hmsb (hcts'.grow (OMono.decPL (fun q => decCN_mono q) _ _) hg) (hlp0.grow hcts' hsz0 hg hk) hnpk
      (by rw [hk IW]; exact hsz5) hP hsh hftP hrdP hmsP hmc hformer hMs) c1
  simp only at hs1 hC1 hg1 hd1 hP1 hA1; subst hs1
  have run1 := AM.run_of_ok _ a hok1
  obtain ⟨cs1, -⟩ := ConRon.Bridge.Inductives.classCtorsOf_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv
    bs pP formerTys formerTysP R rdP ms MsP c.toNat hformer hMs ms[c.toNat].ctors mP.ctors a _ _ hC.check
    ⟨hsh, hftP, hrdP, hmsP, hmc⟩ run1
  generalize hx1 : AM.res (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat ms[c.toNat].ctors) a = x1 at run1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat ms[c.toNat].ctors) a = a1 at run1 hC1 cs1
  have hS1 := hC1.stage
  have hk1 := callW_keepW c1
  -- `rec2`
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
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
  rw [ccsK2_ok (h := hqb)] at h
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
  obtain ⟨xss, a', run2, hC', hg', hk', ht', hP', hA', ps', hps', hfa'⟩ := ih (by omega) _ m' a1 (c + 1)
    (acc ++ [x1]) (ps ++ [(r2.headD 0).toNat]) lP' h hC3 hAb3 hg3 hk3
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg12.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [hc1]; exact hps3) hfa3 (hP2.fr (MFr.set_iw _ _ _))
    (ConRon.Bridge.Inductives.dShape_ext cs1.ext _ _ hsh) (denoteEList_ext cs1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dClassRead_ext cs1.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hmsP)
    (by rw [hc1]; exact ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hlP')
  refine ⟨x1 :: xss, a', ?_, hC', hg', hk', ht', hP', hA', ps', hps', by simpa using hfa'⟩
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classesCtors]
  rw [hc1] at run2
  simp only [StateT.run_bind, run1, except_ok_bind, run2]
  rfl

end ccs

section ccsf
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include hkp henv P hIlpf hOpf

/-- `ccsW_okC` from the fresh result slice. -/
theorem ccsF_okC (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {m m' : Mem} {a : AState} {vis q fto ftl rd mo ml : Word} {r : List Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    (h : ccsF p n m vis q fto ftl rd mo ml = some (r, m')) (hC : StageC dn vis fe env m a)
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
    ∃ xss a', (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms).run a = .ok (xss, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
      SPLA (iwTop m) (fun m p => decLH m (decPL m (decCC m)) p) m' (r.headD 0).toNat (r.tail.headD 0).toNat xss ∧
      RcMR m' ∧ AbsOK m' := by
  rw [ccsF_eq] at h
  obtain ⟨⟨qo, m1⟩, hal, h⟩ := of_K h rfl
  rw [ccsK3_some] at h
  obtain ⟨m2, hl, h⟩ := of_K h rfl
  rw [ccsK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hC.stage
  have hf1 := allocW_mfr hal
  have hA1 := allocW_afr hal hA
  obtain ⟨xss, a', run, hC', hg', -, ht', hP', hA', ps', hps', hfa'⟩ := ccsW_okC hkp henv P hIlpf hOpf dn fe vis q fto ftl rd
    mo ml qo bs formerTys R ms m hbs hft hftb hR hms hmsb hlp hnpk hsz5 hq hformer hMs (n + 1) hn m1 m2 a 0
    [] [] MsP hl (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hA1 hg1
    (KeepW.of_mfr hf1) (by omega) UInt64.zero_le (by simp [decNL]) .nil (hP.fr hf1) hsh hftP hrdP hmsP
    (by simpa using hmsP)
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hfa'
  refine ⟨xss, a', run, hC', hg', ⟨.inr (by simp; omega), by simp; omega, ps', hps',
    FA2.imp (fun _ _ hq => hq.mono (by omega)) hfa'⟩, hP', hA'⟩

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
  refine triple_post (ccs_spec p P.ha P.ccs n s₀ vis q fto ftl rd mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xss, a', run, hC', hg, hd, hP', hA'⟩ := ccsF_okC hkp henv P hIlpf hOpf dn fe n (by omega) hm hC hA hbs hft
    hftb hR hms hmsb hlp hnpk hsz5 hP hsh hftP hrdP hmsP hformer hMs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hres]; exact hd, hP', hA'⟩

end L.Ind
