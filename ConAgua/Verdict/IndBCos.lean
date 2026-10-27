import ConAgua.Verdict.IndBCtor
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# Error refinement of `class_ctors_of` (lane `verdicts-b`, helper `ib`)

The loop calls `class_ctor_of` (`classCtorOf_claim`); the result slots are written below the pool's
top as in `cosW_okC`, whose invariants the next iteration's hypotheses need.
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

l_model cosE_spec (p : Prog) (hf : p.lookup "class_ctors_of" = some classCtorsOfL)
  fns [hf ↦ cosE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section cos
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CosProg p) (hIlpf : IlpfF p) (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) {vis : Word} (hTka : TkaE p dn vis fe env)
  (q fto ftl rd mo ml c ao al qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (cAs : List (IConstantVal × Nat)) (m0 : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {rdP : ConLeche.ClassRead}
include hkp henv P hIlpf hOpf hnv hTka

/-- **`class_ctors_of`' loop error claim** (`cosW_okC`'s hypotheses; the invariants about the result
slice dropped). -/
theorem cosE_claim (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m0 cAs) (hlp : CtorsLp m0 ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64) (hq : qo.toNat = iwTop m0)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (k : Nat) (hk' : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (j : Word) (csP : List (ConLeche.ConstantVal × Nat)),
    StageC dn vis fe env m a → AbsOK m →
    IWGrow m0 m →
    KeepW m0 m → iwTop m0 + al.toNat ≤ iwTop m → j ≤ al → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ConRon.Bridge.Inductives.dClassRead a.store R = some rdP → ms.mapM (dMajor a.store) = some MsP →
    dCtors a.store (cAs.drop j.toNat) = some csP →
    ∀ e, cosE.loop1 p k m vis q fto ftl rd mo ml c ao al qo j = .error e →
      ErrClaim (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat (cAs.drop j.toNat)) a e := by
  have hcAs0 : decPL (truncM m0) (decCN (truncM m0)) ao.toNat al.toNat = some cAs := hcAs
  have hlen := decPL_length _ hcAs0
  induction k with
  | zero =>
    intro m a j csP hC hA hg hk htop hja hP hsh hftP hrdP hmsP hcsP e he
    rw [cosE.loop1.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a j csP hC hA hg hk htop hja hP hsh hftP hrdP hmsP hcsP e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hjk : j.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hja
  by_cases hj : j < al
  rotate_left
  · rw [cosE.loop1.arm2 p k m vis q fto ftl rd mo ml c ao al qo j hj] at he
    cases he
  have hjl : j.toNat < al.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := al.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [cosE.loop1.arm1 p k m vis q fto ftl rd mo ml c ao al qo j hj] at he
  have hsz := hS.2.2.2.1
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
  rw [hrd] at he
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd0.2
  have hcA0 : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m0 cAs[j.toNat] := by
    rw [hvT]; rw [← hlen] at hjl; exact hdv
  have hlp0 : CtorLp m0 (UInt64.ofNat v) := by
    have := hlp j.toNat hjl; rw [hnj, hrd0.1] at this; exact this
  rw [List.drop_eq_getElem_cons (by rw [hlen]; omega)] at hcsP
  obtain ⟨cAP, csP', rfl, hcAP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classCtorsOf]
  -- `class_ctor_of`
  cases h1 : callE p k "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat v] m with
  | error e1 =>
    rw [h1, cosE.k_class_ctor_of.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classCtorOf_claim hkp henv P.toCxoProg hOpf dn fe hnv hTka k (by omega)
      ⟨m, Locals.init []⟩ a q fto ftl rd mo ml c (UInt64.ofNat v) bs
      formerTys R ms cAs[j.toNat] hC hA (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft) (Nat.le_trans hftb hg.1)
      (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg) hmsb
      (hcA0.grow (decCN_mono _) hg) (hlp0.grow hcA0 hsz0 hg hk) hnpk (by rw [hk IW]; exact hsz5) hP
      hsh hftP hmsP hcAP hformer hMs) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cosE.k_class_ctor_of.arm1] at he
  obtain ⟨s1, hs1, -, hok1, hC1, hg1, hd1, hP1, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classCtorOf_refinesC hkp henv P.toCxoProg hIlpf hOpf k (by omega) _ a dn fe vis q fto ftl rd mo ml c (UInt64.ofNat v) bs
      formerTys R ms cAs[j.toNat] hC hA (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft) (Nat.le_trans hftb hg.1)
      (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg) hmsb
      (hcA0.grow (decCN_mono _) hg) (hlp0.grow hcA0 hsz0 hg hk) hnpk (by rw [hk IW]; exact hsz5) hP
      hsh hftP hmsP hcAP hformer hMs) (callW_of_callE h1)
  simp only at hs1 hC1 hg1 hd1 hP1 hA1; subst hs1
  have run1 := AM.run_of_ok _ a hok1
  obtain ⟨cs1, -⟩ := ConRon.Bridge.Inductives.classCtorOf_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv
    bs pP formerTys formerTysP R rdP ms MsP c.toNat cAs[j.toNat] cAP hformer hMs a _ _ hC.check
    ⟨hsh, hftP, hrdP, hmsP, hcAP⟩ run1
  generalize hx1 : AM.res (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cAs[j.toNat]) a = x1 at run1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cAs[j.toNat]) a = a1 at run1 hC1 cs1
  have hS1 := hC1.stage
  have hk1 := callW_keepW (callW_of_callE h1)
  have hsz1 := hS1.2.2.2.1
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqj : (qo + j).toNat = qo.toNat + j.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hS2 := hS1.set_iw (qo + j) (r1.headD 0)
  have hAb2 := set64IW_afr s1.mem (qo + j) (r1.headD 0) hA1
  have hC2 := hC1.of_pstep hS2 hAb2 (PStep.refl hC1.check.state)
  have hg2 : IWGrow m0 (s1.mem.set64 IW (qo + j) (r1.headD 0)) := (hg.trans hg1).set_iw _ _ (by omega)
  have hk2 : KeepW m0 (s1.mem.set64 IW (qo + j) (r1.headD 0)) := (hk.trans hk1).set64 _ _ _
  refine ErrClaim.bind_right run1 ?_
  have := ih (by omega) _ a1 (j + 1) csP' hC2 hAb2 hg2 hk2
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg1.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (hP1.fr (MFr.set_iw _ _ _))
    (ConRon.Bridge.Inductives.dShape_ext cs1.ext _ _ hsh) (denoteEList_ext cs1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dClassRead_ext cs1.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cs1.ext _ _ hmsP)
    (by rw [hj1]; exact ConRon.Bridge.Inductives.dCtors_ext cs1.ext _ _ hcsP') e he
  rw [hj1] at this
  exact ErrClaim.bind_left this

/-- **`class_ctors_of`' error claim** (every fuel; `classCtorsOf_refinesC`'s hypotheses). -/
theorem classCtorsOf_claim (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor)
    (cAs : List (IConstantVal × Nat))
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) s₀.mem cAs) (hlp : CtorsLp s₀.mem ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem)
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store R = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP) {csP : List (ConLeche.ConstantVal × Nat)}
    (hcsP : dCtors a₀.store cAs = some csP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    CoreSpecE p N "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, ao, al]
      (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have he := triple_of_callE_err (cosE_spec p P.cos (n + 1) s₀ vis q fto ftl rd mo ml c ao al) hc
      (Err.code_ne_of_cls hk0)
    rw [cosE.arm1] at he
    cases h1 : callE p n "iw_alloc" [al] s₀.mem with
    | error e1 =>
      rw [h1, cosE.k_iw_alloc.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
    | ok q1 =>
      obtain ⟨r1, m1⟩ := q1
      rw [h1, cosE.k_iw_alloc.arm1] at he
      obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (iwAlloc_specW p P.ha n s₀ al) (callW_of_callE h1)
      obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hC.stage
      have hf1 := allocW_mfr hal
      have hA1 := allocW_afr hal hA
      subst hs1
      cases hl : cosE.loop1 p (n + 1) s1.mem vis q fto ftl rd mo ml c ao al (r1.headD 0) 0 with
      | error e' =>
        rw [hl, cosE.k_loop1.none] at he
        cases he
        refine cosE_claim hkp henv P hIlpf hOpf dn fe hnv hTka q fto ftl rd mo ml c ao al (r1.headD 0) bs formerTys R ms
          cAs s₀.mem hbs hft hftb hR hms hmsb hcAs hlp hnpk hsz5 hq hformer hMs (n + 1) (by omega) s1.mem a₀ 0 csP
          (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hA1 hg1 (KeepW.of_mfr hf1) (by omega) UInt64.zero_le
          (hP.fr hf1) hsh hftP hrdP hmsP (by simpa using hcsP) _ ?_
        exact hl
      | ok m' =>
        rw [hl, cosE.k_loop1.arm1] at he
        cases he

end cos

end L.Ind
