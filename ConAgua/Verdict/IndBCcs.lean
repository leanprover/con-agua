import ConAgua.Verdict.IndBCos

/-!
# Error refinement of `classes_ctors` (lane `verdicts-b`, helper `ib`)

The loop calls `class_ctors_of` (`classCtorsOf_claim`); `rec2` is `closedNV`. The next iteration's
hypotheses are those of `ccsW_okC` less the result-slice invariants.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ccsE_spec (p : Prog) (hf : p.lookup "classes_ctors" = some classesCtorsL)
  fns [hf ↦ ccsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section ccs
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) {vis : Word} (hTka : TkaE p dn vis fe env)
  (q fto ftl rd mo ml qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (m0 : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {rdP : ConLeche.ClassRead}
include hkp henv P hIlpf hOpf hnv hTka

/-- **`classes_ctors`' loop error claim** (`ccsW_okC`'s hypotheses, the result-slice invariants
dropped). -/
theorem ccsE_claim (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp m0 mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64)
    (hq : qo.toNat = iwTop m0) (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (k : Nat) (hk' : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (c : Word) (lP : List ConLeche.TargetMajor),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m →
    KeepW m0 m → iwTop m0 + ml.toNat ≤ iwTop m → c ≤ ml → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ConRon.Bridge.Inductives.dClassRead a.store R = some rdP → ms.mapM (dMajor a.store) = some MsP →
    (ms.drop c.toNat).mapM (dMajor a.store) = some lP →
    ∀ e, ccsE.loop1 p k m vis q fto ftl rd mo ml qo c = .error e →
      ErrClaim (ConRon.Arena.classesCtors V fe bs formerTys R ms c.toNat (ms.drop c.toNat)) a e := by
  have hms0 : decPL (truncM m0) (decTM (truncM m0)) mo.toNat ml.toNat = some ms := hms
  have hlen := decPL_length _ hms0
  have hsz0 : (m0.arr64 IW).size < 2 ^ 64 := by omega
  induction k with
  | zero =>
    intro m a c lP hC hA hg hk htop hcm hP hsh hftP hrdP hmsP hlP e he
    rw [ccsE.loop1.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a c lP hC hA hg hk htop hcm hP hsh hftP hrdP hmsP hlP e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hck : c.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hcm
  by_cases hc : c < ml
  rotate_left
  · rw [ccsE.loop1.arm2 p k m vis q fto ftl rd mo ml qo c hc] at he
    cases he
  have hcl : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hc
  have := ml.toNat_lt
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [ccsE.loop1.arm1 p k m vis q fto ftl rd mo ml qo c hc] at he
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
  rw [hrd, rdW_grow hg hv6t, rdW_grow hg hv7t, r6.1, r7.1] at he
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
  cases h1 : callE p k "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat o, UInt64.ofNat l] m with
  | error e1 =>
    rw [h1, ccsE.k_class_ctors_of.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classCtorsOf_claim hkp henv P.toCosProg hIlpf hOpf dn fe hnv hTka q fto ftl rd mo ml c
      (UInt64.ofNat o) (UInt64.ofNat l) k (by omega) ⟨m, Locals.init []⟩ a bs formerTys R ms ms[c.toNat].ctors
      hC hA (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft)
      (Nat.le_trans hftb hg.1) (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg)
      hmsb (hcts'.grow (OMono.decPL (fun q => decCN_mono q) _ _) hg) (hlp0.grow hcts' hsz0 hg hk) hnpk
      (by rw [hk IW]; exact hsz5) hP hsh hftP hrdP hmsP hmc hformer hMs) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, ccsE.k_class_ctors_of.arm1] at he
  obtain ⟨s1, hs1, -, hok1, hC1, hg1, hd1, hP1, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classCtorsOf_refinesC hkp henv P.toCosProg hIlpf hOpf k (by omega) _ a dn fe vis q fto ftl rd mo ml c
      (UInt64.ofNat o) (UInt64.ofNat l) bs formerTys R ms ms[c.toNat].ctors hC hA (hbs.grow hg)
      (by rw [decHL_grow hg hftb]; exact hft)
      (Nat.le_trans hftb hg.1) (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg)
      hmsb (hcts'.grow (OMono.decPL (fun q => decCN_mono q) _ _) hg) (hlp0.grow hcts' hsz0 hg hk) hnpk
      (by rw [hk IW]; exact hsz5) hP hsh hftP hrdP hmsP hmc hformer hMs) (callW_of_callE h1)
  simp only at hs1 hC1 hg1 hd1 hP1 hA1; subst hs1
  have run1 := AM.run_of_ok _ a hok1
  obtain ⟨cs1, -⟩ := ConRon.Bridge.Inductives.classCtorsOf_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv
    bs pP formerTys formerTysP R rdP ms MsP c.toNat hformer hMs ms[c.toNat].ctors mP.ctors a _ _ hC.check
    ⟨hsh, hftP, hrdP, hmsP, hmc⟩ run1
  generalize hx1 : AM.res (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat ms[c.toNat].ctors) a = x1 at run1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat ms[c.toNat].ctors) a = a1 at run1 hC1 cs1
  have hS1 := hC1.stage
  have hk1 := callW_keepW (callW_of_callE h1)
  refine ErrClaim.bind_right run1 ?_
  -- `rec2`
  cases h2 : callE p k "rec2" [r1.headD 0, r1.tail.headD 0] s1.mem with
  | error e2 =>
    rw [h2, ccsE.k_rec2.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, ccsE.k_rec2.arm1] at he
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero =>
      obtain ⟨e', he', -⟩ := callE_zero p "rec2" [r1.headD 0, r1.tail.headD 0] s1.mem
      rw [h2] at he'; cases he'
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (rec2_specW p P.ha (k' + 1) P.r2 _ (r1.headD 0) (r1.tail.headD 0)) (callW_of_callE h2)
  simp only at hs2 hw2; subst hs2
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hr2, hget2, hg2, hf2, ht2, hroom2⟩ := recW_post hw2 hS1.2.2.2.2.2 hsz1 rfl
  have hS2 := stage_frame_iw hS1 hf2 (by simp at ht2 hroom2; omega)
  have hk2 : KeepW s1.mem s2.mem := KeepW.of_mfr (MFr.of_iw hf2)
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hAb2 := AFr.iw hf2 hA1
  have hC2 := hC1.of_pstep hS2 hAb2 (PStep.refl hC1.check.state)
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqc : (qo + c).toNat = qo.toNat + c.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hg12 := hg1.trans hg2
  have hS3 := hS2.set_iw (qo + c) (r2.headD 0)
  have hAb3 := set64IW_afr s2.mem (qo + c) (r2.headD 0) hAb2
  have hC3 := hC2.of_pstep hS3 hAb3 (PStep.refl hC2.check.state)
  have hg3 : IWGrow m0 (s2.mem.set64 IW (qo + c) (r2.headD 0)) := ((hg.trans hg12)).set_iw _ _ (by omega)
  have hk3 : KeepW m0 (s2.mem.set64 IW (qo + c) (r2.headD 0)) := (hk.trans (hk1.trans hk2)).set64 _ _ _
  have := ih (by omega) _ a1 (c + 1) lP' hC3 hAb3 hg3 hk3
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg12.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (hP2.fr (MFr.set_iw _ _ _))
    (ConRon.Bridge.Inductives.dShape_ext cs1.ext _ _ hsh) (denoteEList_ext cs1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dClassRead_ext cs1.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hmsP)
    (by rw [hc1]; exact ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hlP') e he
  rw [hc1] at this
  exact ErrClaim.bind_left this

/-- **`classes_ctors`' error claim** (every fuel; `classesCtors_refinesC`'s hypotheses). -/
theorem classesCtors_claim (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (bs : BlockShape)
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
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have he := triple_of_callE_err (ccsE_spec p P.ccs (n + 1) s₀ vis q fto ftl rd mo ml) hc
      (Err.code_ne_of_cls hk0)
    rw [ccsE.arm1] at he
    cases h1 : callE p n "iw_alloc" [ml] s₀.mem with
    | error e1 =>
      rw [h1, ccsE.k_iw_alloc.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q1 =>
      obtain ⟨r1, m1⟩ := q1
      rw [h1, ccsE.k_iw_alloc.arm1] at he
      obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (iwAlloc_specW p P.ha n s₀ ml) (callW_of_callE h1)
      obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hC.stage
      have hf1 := allocW_mfr hal
      have hA1 := allocW_afr hal hA
      subst hs1
      cases hl : ccsE.loop1 p (n + 1) s1.mem vis q fto ftl rd mo ml (r1.headD 0) 0 with
      | error e' =>
        rw [hl, ccsE.k_loop1.none] at he
        cases he
        have := ccsE_claim hkp henv P hIlpf hOpf dn fe hnv hTka q fto ftl rd mo ml (r1.headD 0) bs formerTys R ms
          s₀.mem hbs hft hftb hR hms hmsb hlp hnpk hsz5 hq hformer hMs (n + 1) (by omega) s1.mem a₀ 0 MsP
          (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hA1 hg1 (KeepW.of_mfr hf1) (by omega) UInt64.zero_le
          (hP.fr hf1) hsh hftP hrdP hmsP (by simpa using hmsP) _ hl
        simpa using this
      | ok m' =>
        rw [hl, ccsE.k_loop1.arm1] at he
        cases he

end ccs

end L.Ind
