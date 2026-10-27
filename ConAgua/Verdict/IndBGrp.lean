import ConAgua.Verdict.IndBGrpM
import ConAgua.Verdict.IndBGck
import ConAgua.Verdict.IndBRec3
import ConAgua.Verdict.IndBRecPins
import ConAgua.Verdict.IndBCcs
import ConAgua.Verdict.IndBStream

/-!
# Error refinement of `gen_rec_check_prep` (lane `verdicts-b`, helper `ib`)

Mirrors `grpAW_okC`/`grpBW_okC`/`grpCW_okC` (the three parts of `grpW_okC`). The claims used are
`targetRecPins_claim`, `classStreamRecs_claim`, `classesCtors_claim`, `classRecTysOk_claim`;
`classes_nfs`' claim is a hypothesis (`ClassesNfsE`: the generator cannot produce its model, the
function has nested loops), `block_large_elim_allowed` and the rest are `closedNV`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor dClassGen dRec)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`classes_nfs`' error claim** (hypothesis; `classesNfs_refinesLpC`'s hypotheses). -/
def ClassesNfsE (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor},
    StageC dn vis fe env s₀.mem a₀ → AbsOK s₀.mem → BSOK s₀.mem q.toNat bs →
    decHL s₀.mem fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop s₀.mem →
    PSlR decNCN tbl tblo tbll s₀.mem → PSlR decTM ms mo ml s₀.mem → RcMR s₀.mem →
    ClassesLp s₀.mem mo ml →
    dShape a₀.store bs = some pP → Frontend.denoteEList a₀.store formerTys = some formerTysP →
    tbl.mapM (dCtorNf a₀.store) = some tblP → ms.mapM (dMajor a₀.store) = some MsP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    (∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) →
    CoreSpecE p n "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
      (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) s₀ a₀

theorem grc_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | a :: l, _, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact grc_mapM_mem hys x hx

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p) (hCcv : CcvE p)

include hkp henv hApd hCrk hnv hcE hU in
/-- **`gen_rec_check_prep`'s third part, error claim** (`grpCW_okC`'s hypotheses): the generator
record, its prefix, the recursor types. -/
theorem grpCE_claim (P : GrcProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL rd cRo cRl m2o m2l fo fl co cl el : Word}
    {bs : BlockShape} {params : List EIdx} {rdv : ConRon.Arena.ClassRead} {ms2 : List TargetMajor}
    {ctors : List (List ConRon.Arena.ClassCtor)} {ftc : List EIdx} {elim : LIdx} {cvRis : List IConstantVal}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (hrd : DecB (fun m => decCR m rd.toNat) m rdv) (hms2 : PSlR decTM ms2 m2o m2l m)
    (hct : DecB (fun m => decPL m (decLH m (decPL m (decCC m))) co.toNat cl.toNat) m ctors)
    (hft : decHL m fo.toNat fl.toNat = some ftc) (hftb : fo.toNat + fl.toNat ≤ iwTop m)
    (hel : el.toNat < 2 ^ 32) (hel' : (decI el : LIdx) = elim)
    (hcv : DecB (fun m => decPL m (decCVp m) cRo.toNat cRl.toNat) m cvRis)
    (hns : bs.nP + rdv.slots.length < 2 ^ 64) (hA : AbsOK m)
    {pP : ConLeche.BlockShape} {gP0 : ConLeche.ClassGen} {cvRisP : List ConLeche.ConstantVal}
    (hsh : dShape a.store bs = some pP)
    (hg0 : dClassGen a.store ⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, []⟩ = some gP0)
    (hcvP : cvRis.mapM (Frontend.denoteCV a.store) = some cvRisP)
    (hwRis : ∀ cv ∈ cvRisP, ConLeche.Expr.WScoped 0 cv.type) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) (hP : RcMR m) :
    ∀ e, grpE.k_iw_alloc p n vis pp pO pL rd cRo cRl m2o m2l co cl fo fl el
        (callE p n "iw_alloc" [14] m) = .error e →
      ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k) a e := by
  intro e he β k
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hc : 200 < (m.arr64 CTL).size := hS.2.2.2.2.2
  have hp8 := hbs.ptop
  have hrecsP0 := (ConRon.Bridge.Inductives.dShape_inv hsh).2.1
  obtain ⟨hrd3, hslD, hrcD, hrcb, -⟩ := crWords hrd
  unfold grcTwinC
  -- `iw_alloc(14)`
  cases h1 : callE p n "iw_alloc" [14] m with
  | error e1 =>
    rw [h1, grpE.k_iw_alloc.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, grpE.k_iw_alloc.arm1] at he
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p P.ia n _ 14)
    (callW_of_callE h1)
  simp only at hs1 hal; subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  obtain ⟨hS1, -, hqtop, -⟩ := allocW_stage hal hS
  generalize hgq : r1.headD 0 = g at he hq hqtop hroom
  have h14 : (14 : Word).toNat = 14 := rfl
  rw [h14] at hroom
  have he' : grpE.k_class_gen_prefix_binders p n vis pp rd cRo cRl g (callE p n "class_gen_prefix_binders" [g]
      (grpG3 (grpG2b (grpG2 (grpG1 s1.mem g pp pO pL m2o m2l) g fo fl rd) g rd co) g cl el)) =
      Except.error e := he
  rw [grpGs_eq s1.mem g pp pO pL m2o m2l fo fl rd co cl el (by omega) (by omega)] at he'
  have e4 : rdW (s1.mem.arr64 IW) (pp + 4) = UInt64.ofNat bs.nP := by
    rw [hm1, allocMem_IW]; exact (partsShapeWords (IWGrow.refl m) hbs.1 (by omega)).1
  have er0 : rdW (s1.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := by rw [hm1, allocMem_IW]
  have er1 : rdW (s1.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) := by rw [hm1, allocMem_IW]
  rw [e4, er0, er1] at he'
  generalize hws : [UInt64.ofNat bs.nP, pO, pL, m2o, m2l, fo, fl, rdW (m.arr64 IW) rd,
    rdW (m.arr64 IW) (rd + 1), co, cl, el, (0 : Word), 0] = ws at he'
  have hS1G : StageR dn vis fe (wrIW s1.mem g ws) a := StageR.wrIW hS1 g ws
  have hwl : ws.length = 14 := by rw [← hws]; rfl
  obtain ⟨hget, hgG, hfG, htopG⟩ := recMem_post m ws 14 (by rw [hwl]; rfl) hc (by rw [hwl, ← hq]; omega) hsz
  rw [← hm1, ← hq] at hget hgG htopG hfG
  have hAG := AFr.iw hfG hA
  have hPG := hP.fr (MFr.of_iw hfG)
  have hgt : g.toNat = iwTop m := hqtop
  have htG : iwTop (wrIW s1.mem g ws) = iwTop m + 14 := by
    simp only [iwTop]; rw [htopG, UInt64.toNat_add, h14, Nat.mod_eq_of_lt (by omega)]
    simp only [iwTop] at hgt; omega
  have hnP : bs.nP < 2 ^ 64 := (partsShapeWords (IWGrow.refl m) hbs.1 (by omega)).2.1
  have hparD := decHL_decB hpar hparb
  have hftD := decHL_decB hft hftb
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m := by
    obtain ⟨-, hrecs, -, -, -, -, -⟩ := decBS_some (show decBS (truncM m) pp.toNat = some bs from hbs.1)
    exact bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hcomp : ∀ m'', IWGrow m m'' →
      DecB (fun x => (decHL x pO.toNat pL.toNat : Option (List EIdx))) m'' params ∧
      DecB (fun x => decPL x (decTM x) m2o.toNat m2l.toNat) m'' ms2 ∧
      DecB (fun x => (decHL x fo.toNat fl.toNat : Option (List EIdx))) m'' ftc ∧
      DecB (fun x => decPL x (decCS x) (rdW (m.arr64 IW) rd).toNat (rdW (m.arr64 IW) (rd + 1)).toNat) m'' rdv.slots ∧
      DecB (fun x => decPL x (decLH x (decPL x (decCC x))) co.toNat cl.toNat) m'' ctors := by
    intro m'' hg
    exact ⟨hparD.grow (OMono.decHL _ _) hg, hms2.1.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg,
      hftD.grow (OMono.decHL _ _) hg, hslD.grow (OMono.decPL decCS_mono _ _) hg,
      hct.grow (OMono.decPL decCC_lh_mono _ _) hg⟩
  generalize hmG : wrIW s1.mem g ws = mG at hS1G hget hgG htopG htG he' hAG hPG
  obtain ⟨cP, cM, cF, cS, cC⟩ := hcomp mG hgG
  have hsl1 : rd.toNat + 1 < iwTop m := by omega
  have hG0 : DecB (fun x => decCG x g.toNat) mG
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, []⟩ : ConRon.Arena.ClassGen) := by
    subst hws
    exact cgRec_decB (fun j hj => hget j (by simpa using hj)) (by omega) (UInt64.toNat_ofNat_of_lt' hnP) cP cM cF
      cS cC hel hel' (by show decHL (truncM mG) (0 : Word).toNat (0 : Word).toNat = some []; simp [decHL, hslice?])
  have hCG : StageC dn vis fe env mG a := hC.of_pstep hS1G hAG (PStep.refl hC.check.state)
  -- the prefix
  cases h2 : callE p n "class_gen_prefix_binders" [g] mG with
  | error e2 =>
    rw [h2, grpE.k_class_gen_prefix_binders.none] at he'
    cases he'
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hgp⟩ := triple_of_callW (s₀ := ⟨mG, Locals.init []⟩) (prefixBinders_spec p P.pb n _ g)
    (callW_of_callE h2)
  simp only at hs2 hgp; subst hs2
  obtain ⟨x2, a2, hrun2, hC2, ⟨⟨⟨hS2, hg2, hd2⟩, hA2⟩, hfr2⟩, hR2, p9⟩ :=
    RSim.liftPP hCG (gpbW_simF dn vis fe n mG a g _ hS1G hG0 hns hAG)
      (fun _ _ _ hh => ⟨hh.1.1.1, hh.1.2⟩)
      (ConRon.Bridge.Inductives.ClassGen.prefixBinders_spec _ gP0) hg0 (r2, s2.mem) hgp
  dsimp only at hS2 hg2 hd2 hfr2 hA2 hC2
  have c19 := p9.toCore hC.check
  have hk2 := callW_keepW (callW_of_callE h2)
  have hP2 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE h2) hPG
  refine ErrClaim.bind_right hrun2 ?_
  have h0 : ¬ (r2.headD 0 = 0) := fun h0 => by
    rw [h2, grpE.k_class_gen_prefix_binders.abort1 p n vis pp rd cRo cRl g r2 _ h0] at he'
    cases he'
    exact absurd (by decide) hk0
  rw [h2, grpE.k_class_gen_prefix_binders.arm1 p n vis pp rd cRo cRl g r2 _ h0] at he'
  rcases x2 with _ | pre
  · exact absurd hd2 h0
  obtain ⟨preP, -, hpreP⟩ := hR2
  obtain ⟨-, hpreD, hpreb⟩ := hd2
  have hfr := hfr2 pre rfl
  simp only []
  generalize ho : r2.tail.headD 0 = o at he' hpreD hpreb hfr
  generalize hl : r2.tail.tail.headD 0 = l at he' hpreD hpreb
  have hgs : g.toNat + 14 ≤ (s2.mem.arr64 IW).size := by
    rw [hk2 IW, ← hmG, wrIW_size, hm1, allocMem_IW]; omega
  have e12 : (g + 12).toNat = g.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have e13 : (g + 13).toNat = g.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  have hgP : IWGrow m (grpPMem s2.mem g o l) :=
    ((hgG.trans hg2).set_iw _ _ (by rw [e12]; omega)).set_iw _ _ (by rw [e13]; omega)
  have hSP : StageR dn vis fe (grpPMem s2.mem g o l) a2 := (hS2.set_iw _ _).set_iw _ _
  have hAP : AbsOK (grpPMem s2.mem g o l) :=
    AFr.set64 _ IW (by decide) (by decide) _ _ (AFr.set64 _ IW (by decide) (by decide) _ _ hA2)
  have hPP : RcMR (grpPMem s2.mem g o l) := by
    simp only [grpPMem]; exact (hP2.fr (MFr.set_iw _ _ _)).fr (MFr.set_iw _ _ _)
  have hCP : StageC dn vis fe env (grpPMem s2.mem g o l) a2 := hC2.of_pstep hSP hAP (PStep.refl hC2.check.state)
  have htP : iwTop (grpPMem s2.mem g o l) = iwTop s2.mem := by simp only [grpPMem, iwTop_set_iw]
  have hgetP : ∀ j (hj : j < 14), ((grpPMem s2.mem g o l).arr64 IW)[g.toNat + j]? =
      [UInt64.ofNat bs.nP, pO, pL, m2o, m2l, fo, fl, rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), co, cl, el,
        o, l][j]? := by
    intro j hj
    simp only [grpPMem]
    rw [set64IW_get, set64IW_get]
    by_cases j13 : j = 13
    · subst j13; rw [ite_eq_left ⟨e13.symm, by rw [size_set64]; omega⟩]; rfl
    rw [ite_eq_right (by omega)]
    by_cases j12 : j = 12
    · subst j12; rw [ite_eq_left ⟨e12.symm, by omega⟩]; rfl
    rw [ite_eq_right (by omega), hg2.2.2.1 _ (by omega), hget j (by rw [hwl]; omega), ← hws]
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
  have hpreP' : DecB (fun x => (decHL x o.toNat l.toNat : Option (List EIdx))) (grpPMem s2.mem g o l) pre := by
    refine decHL_decB ?_ (by rw [htP]; exact hpreb)
    simp only [grpPMem]
    rw [decHL_set_out (by rw [e13]; omega), decHL_set_out (by rw [e12]; omega)]
    exact hpreD
  obtain ⟨dP, dM, dF, dS, dC⟩ := hcomp _ hgP
  have hG : DecB (fun x => decCG x g.toNat) (grpPMem s2.mem g o l)
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ : ConRon.Arena.ClassGen) :=
    cgRec_decB hgetP (by rw [htP]; have := hg2.1; rw [htG] at this; omega) (UInt64.toNat_ofNat_of_lt' hnP) dP dM dF dS dC hel hel'
      hpreP'
  have hgPd : dClassGen a2.store (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ : ConRon.Arena.ClassGen) =
      some { gP0 with pre := preP } :=
    ConRon.Bridge.Inductives.dClassGen_pre (ConRon.Bridge.Inductives.dClassGen_ext p9.ext _ _ hg0) hpreP
  -- `class_rec_tys_ok`
  have rP : ∀ k, k < 9 → rdW ((grpPMem s2.mem g o l).arr64 IW) (pp + UInt64.ofNat k) =
      rdW (m.arr64 IW) (pp + UInt64.ofNat k) := fun k hk =>
    partsRdIW_grow hgP (by rw [UInt64.toNat_add]; simp; omega)
  have rR : ∀ k, k < 4 → rdW ((grpPMem s2.mem g o l).arr64 IW) (rd + UInt64.ofNat k) =
      rdW (m.arr64 IW) (rd + UInt64.ofNat k) := fun k hk =>
    partsRdIW_grow hgP (by rw [UInt64.toNat_add]; simp; omega)
  have he'' : grpE.k_class_rec_tys_ok p g (callE p n "class_rec_tys_ok" [vis, g,
      rdW ((grpPMem s2.mem g o l).arr64 IW) (pp + 1), rdW ((grpPMem s2.mem g o l).arr64 IW) (pp + 2),
      rdW ((grpPMem s2.mem g o l).arr64 IW) (pp + 3), cRo, cRl,
      rdW ((grpPMem s2.mem g o l).arr64 IW) (rd + 2), rdW ((grpPMem s2.mem g o l).arr64 IW) (rd + 3)]
      (grpPMem s2.mem g o l)) = Except.error e := he'
  rw [show (pp + 1 : Word) = pp + UInt64.ofNat 1 from rfl, show (pp + 2 : Word) = pp + UInt64.ofNat 2 from rfl,
    show (pp + 3 : Word) = pp + UInt64.ofNat 3 from rfl, show (rd + 2 : Word) = rd + UInt64.ofNat 2 from rfl,
    show (rd + 3 : Word) = rd + UInt64.ofNat 3 from rfl, rP 1 (by omega), rP 2 (by omega), rP 3 (by omega),
    rR 2 (by omega), rR 3 (by omega)] at he''
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some (show decBS (truncM m) pp.toNat = some bs from hbs.1)).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hkw : rdW (m.arr64 IW) (pp + UInt64.ofNat 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
  rw [hkw] at he''
  have hrcs := hrecsP.1.grow (OMono.decPL decRS_mono _ _) hgP
  have hrecs2 := ConRon.Bridge.Inductives.dRec_ext.list c19.ext _ _ hrecsP0
  have hcv2 := ConRon.Bridge.Inductives.dExt_denoteCV.list c19.ext _ _ hcvP
  cases h3 : callE p n "class_rec_tys_ok" [vis, g, UInt64.ofNat bs.k, rdW (m.arr64 IW) (pp + UInt64.ofNat 2),
      rdW (m.arr64 IW) (pp + UInt64.ofNat 3), cRo, cRl, rdW (m.arr64 IW) (rd + UInt64.ofNat 2),
      rdW (m.arr64 IW) (rd + UInt64.ofNat 3)] (grpPMem s2.mem g o l) with
  | error e3 =>
    rw [h3, grpE.k_class_rec_tys_ok.none] at he''
    cases he''
    have := CoreSpecE.of_callE (classRecTysOk_claim hkp hApd hCrk hnv hcE hU henv P.rts n hn
      ⟨grpPMem s2.mem g o l, Locals.init []⟩ a2 g (UInt64.ofNat bs.k) _ _ cRo cRl _ _ _ bs.recs cvRis rdv.recCls hCP hG
      hns hrcs (rec3RecsOK_of_decB hrcs (Nat.le_trans hrecsP.2 hgP.1)) (hcv.grow (OMono.decPL
        (fun q => OMono.decCVp q) _ _) hgP) (hrcD.grow (OMono.decNL _ _) hgP) hAP hgPd hrecs2 hcv2 hwRis) h3
    rw [UInt64.toNat_ofNat_of_lt' hkb] at this
    exact ErrClaim.bind_left this
  | ok q3 =>
  rw [h3, grpE.k_class_rec_tys_ok.arm1] at he''
  cases he''


include hkp henv hApd hCrk hIlpf hnv hcE hU in
/-- **`gen_rec_check_prep`'s second and third parts, error claim** (`grpBW_okC`'s hypotheses, the
model from the formers' types on). -/
theorem grpBE_claim (P : GrcProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL tO tL rd mO mL cO cL cRo cRl : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {cvRis : List IConstantVal}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m) (hlp : ClassesLp m mO mL)
    (hcvR : DecB (fun m => decPL m (decCVp m) cRo.toNat cRl.toNat) m cvRis)
    (hns : bs.nP + rdv.slots.length < 2 ^ 64) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor}
    {cvTasP cvRisP : List ConLeche.ConstantVal}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M)
    (hcvRP : cvRis.mapM (Frontend.denoteCV a.store) = some cvRisP)
    (hwRis : ∀ cv ∈ cvRisP, ConLeche.Expr.WScoped 0 cv.type) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR)
    (hNfs : ClassesNfsE p dn vis fe env) (hTka : TkaE p dn vis fe env) :
    ∀ e, grpE.j1 p n vis pp pO pL tO tL rd mO mL cO cL cRo cRl m = .error e →
      ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
          grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k)) a e := by
  intro e he β k
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hT64 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hp8 := hbs.ptop
  obtain ⟨hrd3, hslD, hrcD, hrcb, hslb⟩ := crWords hrd
  obtain ⟨-, -, hnPe, -, -, hlargeP, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh
  have hformer : ∀ t ∈ cvTasP.map (·.type), ConLeche.Expr.WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  have hftP := ConRon.Bridge.Inductives.GR.types_denote hcvTP
  rw [grpE.j1.arm1] at he
  unfold grcTwinB
  -- the formers' types
  cases h1 : callE p n "gen_rec_check_former_tys" [cO, cL] m with
  | error e1 =>
    rw [h1, grpE.k_gen_rec_check_former_tys.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, grpE.k_gen_rec_check_former_tys.arm1] at he
  obtain ⟨s1, hs1, -, hS1, hg1, hf1, hft1, hftb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (genRecCheckFormerTys_refines P.ia P.gft n _ a cO cL cvTas hS hcv) (callW_of_callE h1)
  simp only at hs1 hS1 hg1 hf1 hft1 hftb1; subst hs1
  have hP1 := hP.fr hf1
  have hk1 := callW_keepW (callW_of_callE h1)
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ (callW_of_callE h1) hA
  have hC1 : StageC dn vis fe env s1.mem a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  -- `classes_nfs`
  cases h2 : callE p n "classes_nfs" [vis, pp, r1.headD 0, r1.tail.headD 0, tO, tL, mO, mL] s1.mem with
  | error e2 =>
    rw [h2, grpE.k_classes_nfs.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (hNfs n hn ⟨s1.mem, Locals.init []⟩ a pp _ _ tO tL mO mL bs (cvTas.map (·.type)) tbl ms
      hC1 hA1 (hbs.grow hg1) hft1 hftb1 (htbl.grow (fun q => decNCN_mono q) hg1)
      (hms.grow (fun q => decTM_mono q) hg1) hP1 (hlp.grow hms hg1 hk1 hsz) hsh hftP htblP hmsP hformer hMsT) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, grpE.k_classes_nfs.arm1] at he
  obtain ⟨s2, hs2, -, hok2, hms2, hC2, hg2, hP2, hA2, hlp2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classesNfs_refinesLpC hkp henv P.cns n hn _ a dn fe vis pp _ _ tO tL mO mL bs (cvTas.map (·.type)) tbl ms
      hC1 hA1 (hbs.grow hg1) hft1 hftb1 (htbl.grow (fun q => decNCN_mono q) hg1)
      (hms.grow (fun q => decTM_mono q) hg1) hP1 (hlp.grow hms hg1 hk1 hsz) hsh hftP htblP hmsP hformer hMsT)
    (callW_of_callE h2)
  simp only at hs2 hms2 hC2 hg2 hP2 hA2 hlp2; subst hs2
  have hk2 := callW_keepW (callW_of_callE h2)
  have hrun2 := AM.run_of_ok _ a hok2
  obtain ⟨c4, Ms2P, ⟨hms2P, hMs2⟩, -⟩ := ConRon.Bridge.Inductives.classesNfs_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs pP _ _ tbl tblP hformer ms MsP hMsT a _ _ hC1.check
    ⟨hsh, hftP, htblP, hmsP⟩ hrun2
  generalize AM.res (ConRon.Arena.classesNfs V fe bs (cvTas.map (·.type)) tbl ms) a = ms2 at hrun2 hms2 hms2P
  generalize AM.st (ConRon.Arena.classesNfs V fe bs (cvTas.map (·.type)) tbl ms) a = a2 at hrun2 hC2 hms2P c4
  have hS2 := hC2.stage
  have hg12 := hg1.trans hg2
  refine ErrClaim.bind_right hrun2 ?_
  -- `classes_ctors`
  have hsz2 : (s2.mem.arr64 IW).size = (m.arr64 IW).size := by rw [hk2 IW, hk1 IW]
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext c4.ext _ _ hsh
  have hftP2 := ConRon.Bridge.denoteEList_ext c4.ext _ _ hftP
  have hrdP2 := ConRon.Bridge.Inductives.dClassRead_ext c4.ext _ _ hrdP
  cases h3 : callE p n "classes_ctors" [vis, pp, r1.headD 0, r1.tail.headD 0, rd, r2.headD 0, r2.tail.headD 0]
      s2.mem with
  | error e3 =>
    rw [h3, grpE.k_classes_ctors.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classesCtors_claim hkp henv P.ccs hIlpf P.opf dn fe hnv hTka pp (r1.headD 0)
      (r1.tail.headD 0) rd (r2.headD 0) (r2.tail.headD 0) n hn ⟨s2.mem, Locals.init []⟩ a2 bs
      (cvTas.map (·.type)) rdv ms2 hC2 hA2 (hbs.grow hg12) (by rw [decHL_grow3 hg2 hftb1]; exact hft1)
      (Nat.le_trans hftb1 hg2.1) (hrd.grow (decCR_mono _) hg12) hms2.1 (hS2.lt64 hms2.2) (hlp2 hk2) hnpk
      (by rw [hsz2]; exact hsz5) hP2 hsh2 hftP2 hrdP2 hms2P hformer hMs2) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, grpE.k_classes_ctors.arm1] at he
  obtain ⟨s3, hs3, -, hok3, hC3, hg3, hsp3, hP3, hA3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classesCtors_refinesC hkp henv P.ccs hIlpf P.opf n hn _ a2 dn fe vis pp _ _ rd _ _ bs (cvTas.map (·.type)) rdv ms2
      hC2 hA2 (hbs.grow hg12) (by rw [decHL_grow3 hg2 hftb1]; exact hft1) (Nat.le_trans hftb1 hg2.1)
      (hrd.grow (decCR_mono _) hg12) hms2.1 (hS2.lt64 hms2.2) (hlp2 hk2) hnpk (by rw [hsz2]; exact hsz5) hP2
      hsh2 hftP2 hrdP2 hms2P hformer hMs2) (callW_of_callE h3)
  simp only at hs3 hC3 hg3 hsp3 hP3 hA3; subst hs3
  have hrun3 := AM.run_of_ok _ a2 hok3
  obtain ⟨c5, ctorsP, hctors, -⟩ := ConRon.Bridge.Inductives.classesCtors_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs pP _ _ rdv rdP ms2 Ms2P hformer hMs2 ms2 Ms2P 0 a2 _ _
    hC2.check ⟨hsh2, hftP2, hrdP2, hms2P, hms2P⟩ hrun3
  generalize AM.res (ConRon.Arena.classesCtors V fe bs (cvTas.map (·.type)) rdv ms2 0 ms2) a2 = ctors
    at hrun3 hsp3 hctors
  generalize AM.st (ConRon.Arena.classesCtors V fe bs (cvTas.map (·.type)) rdv ms2 0 ms2) a2 = a3 at hrun3 hC3 hctors c5
  have hS3 := hC3.stage
  have hg13 := hg12.trans hg3
  have hctD := spl_decB hsp3.toSPL
  refine ErrClaim.bind_right hrun3 ?_
  -- the count
  have er0 : rdW (s3.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := partsRdIW_grow hg13 (by omega)
  have er1 : rdW (s3.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [er0, er1] at he
  cases h4 : callE p n "gen_rec_check_minor_ok" [rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), r3.headD 0,
      r3.tail.headD 0] s3.mem with
  | error e4 =>
    rw [h4, grpE.k_gen_rec_check_minor_ok.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, rfl, -, hm4, hmo⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (genRecCheckMinorOk_refines P.csm P.gmo n _ _ _ _ _ rdv.slots ctors
      ((hslD.grow (OMono.decPL decCS_mono _ _) hg13).get (OMono.decPL decCS_mono _ _)) hslb
      (hctD.get (OMono.decPL decCC_lh_mono _ _)) (hS3.lt64 hsp3.2.1) hS3.2.2.2.1) (callW_of_callE h4)
  by_cases h0 : r4.headD 0 = 0
  · rw [h4, grpE.k_gen_rec_check_minor_ok.abort1 p n vis pp pO pL rd cO cL cRo cRl _ _ _ _ r4 _ h0] at he
    cases he
    have hcount : ((rdv.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum) = false := by
      rw [← hmo, h0]; rfl
    simp only [hcount, Bool.false_eq_true, ite_false]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  rw [h4, grpE.k_gen_rec_check_minor_ok.arm1 p n vis pp pO pL rd cO cL cRo cRl _ _ _ _ r4 _ h0, hm4] at he
  have hcount : ((rdv.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum) = true := by
    rw [← hmo]; simpa using h0
  simp only [hcount, ite_true]
  -- the classes' formers
  have hms3P := ConRon.Bridge.Inductives.dMajor_ext.list c5.ext _ _ hms2P
  have hcv3P := ConRon.Bridge.Inductives.dExt_denoteCV.list (c4.trans c5).ext _ _ hcvTP
  cases h5 : callE p n "gen_rec_check_former_tys_c" [vis, cO, cL, r2.headD 0, r2.tail.headD 0] s3.mem with
  | error e5 =>
    rw [h5, grpE.k_gen_rec_check_former_tys_c.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, grpE.k_gen_rec_check_former_tys_c.arm1] at he
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hftc5, hftcb5, hJ5⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (genRecCheckFormerTysC_refinesJ P.cft P.gftc n ⟨s3.mem, Locals.init []⟩ a3 dn vis fe cO cL _ _ cvTas ms2 hS3
      (hcv.grow (fun q => OMono.decCVp q) hg13) (hms2.grow (fun q => decTM_mono q) hg3)
      (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a3.store a'.store)
      (fun _ _ _ hJ hf hS' => ⟨hJ.1.of_pstep hS' (hJ.2.1.iw hf) (PStep.refl hJ.1.check.state), hJ.2.1.iw hf,
        hJ.2.2⟩)
      (fun k m0 m1 a' mp M _ hJ hS' hM' hM hdcv hol c1 => by
        obtain ⟨hCm, hAm, hxm⟩ := hJ
        obtain ⟨s1, rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
          (classFormerTy_spec p P.cft (realCall p) (realCall_spec p) k _ vis cO cL mp) c1
        obtain ⟨x, a1, hrun, hS1, hg1, hd, hAF⟩ := cftW_ok (realCall p) (IlpRd.realC hIlpf hCm) hW hS' hM hdcv hol
        obtain ⟨MP, hMP⟩ := grc_mapM_mem hms3P M hM'
        obtain ⟨c, -⟩ := ConRon.Bridge.Inductives.classFormerTy_spec fe cvTas cvTasP M MP a' a1 x hCm.check
          ⟨ConRon.Bridge.Inductives.dExt_denoteCV.list hxm _ _ hcv3P,
            ConRon.Bridge.Inductives.dMajor_ext hxm _ _ hMP⟩ hrun
        have hA1 := hAF hAm
        exact ⟨x, a1, hrun, hS1, hg1, hd, hCm.of_cstep hS1 hA1 c, hA1, hxm.trans c.ext⟩)
      ⟨hC3, hA3, ConRon.Arena.Ext.refl _⟩) (callW_of_callE h5)
  simp only at hs5 hS5 hg5 hftc5 hftcb5 hJ5; subst hs5
  have hP5 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE h5) hP3
  have hrun5 := AM.run_of_ok _ a3 hok5
  have c45 := c4.trans c5
  obtain ⟨c6, fTCP, hfTC, -⟩ := ConRon.Bridge.Inductives.GR.mapM_cspecF ConRon.Bridge.Inductives.dMajor
    ConRon.Bridge.Inductives.dMajor_ext (fun st e => denoteE st e) ConRon.Bridge.Inductives.dExt_denoteE
    (fun st => cvTas.mapM (Frontend.denoteCV st) = some cvTasP)
    (fun hx h => ConRon.Bridge.Inductives.dExt_denoteCV.list hx _ _ h) (ConRon.Arena.classFormerTy fe cvTas)
    (ConLeche.classFormerTy (m := ConLeche.FueledM) (ConLeche.mkFEnv env) cvTasP)
    (fun m mP s₀ s' r hok hpre hrun => ConRon.Bridge.Inductives.classFormerTy_spec fe cvTas cvTasP m mP s₀ s' r
      hok ⟨hpre.1, hpre.2⟩ hrun) ms2 Ms2P a3 _ _ hC3.check
    ⟨ConRon.Bridge.Inductives.dExt_denoteCV.list c45.ext _ _ hcvTP,
      ConRon.Bridge.Inductives.dMajor_ext.list c5.ext _ _ hms2P⟩ hrun5
  generalize AM.res (ms2.mapM (ConRon.Arena.classFormerTy fe cvTas)) a3 = ftc at hrun5 hftc5 hfTC
  generalize AM.st (ms2.mapM (ConRon.Arena.classFormerTy fe cvTas)) a3 = a5 at hrun5 hS5 hfTC c6 hJ5
  have hg15 := hg13.trans hg5
  have hA5 := hJ5.2.1
  have hC5 : StageC dn vis fe env s5.mem a5 := hC3.of_check hS5 hA5 c6.ok c6.ext
  have c46 := c45.trans c6
  refine ErrClaim.bind_right hrun5 ?_
  -- the elimination level
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, -, -, helimD, -, hlarge, -⟩ := decBS_some hbsD
  obtain ⟨hel5, hel5'⟩ := installIwH (i := 5) helimD hsz
  have hL := installIwB (k := 7) hlarge hsz
  have ew5 : rdW (s5.mem.arr64 IW) (pp + 5) = rdW (m.arr64 IW) (pp + UInt64.ofNat 5) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  have ew7 : rdW (s5.mem.arr64 IW) (pp + 7) = rdW (m.arr64 IW) (pp + UInt64.ofNat 7) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  rw [ew5, ew7] at he
  cases h6 : callE p n "struct_elim_level" [rdW (m.arr64 IW) (pp + UInt64.ofNat 5),
      rdW (m.arr64 IW) (pp + UInt64.ofNat 7)] s5.mem with
  | error e6 =>
    rw [h6, grpE.k_struct_elim_level.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h6)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, grpE.k_struct_elim_level.arm1] at he
  obtain ⟨s6, rfl, -, a6, hrun6, hS6, hg6, hel6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (structElimLevel_stage P.sel n _ a5 _ _ hS5 hel5) (callW_of_callE h6)
  have hP6 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE h6) hP5
  rw [hel5', hL] at hrun6
  have hg16 := hg15.trans hg6
  have hA6 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ (callW_of_callE h6) hA5
  have hsh5 := ConRon.Bridge.Inductives.dShape_ext c46.ext _ _ hsh
  obtain ⟨p7, helim⟩ := ConRon.Bridge.Inductives.structElimLevel_spec bs.elim pP.elim bs.large a5 a6 _
    hC5.check.state (ConRon.Bridge.Inductives.dShape_inv hsh5).2.2.2.1 hrun6
  have hC6 : StageC dn vis fe env s6.mem a6 := hC5.of_pstep hS6 hA6 p7
  have c18 := c46.trans (p7.toCore hC5.check)
  rw [hlargeP] at helim
  refine ErrClaim.bind_right hrun6 ?_
  -- the generator's record, denoted
  have hslP : rdv.slots.mapM (ConRon.Bridge.Inductives.dSlot a.store) = some rdP.slots := by
    simp only [ConRon.Bridge.Inductives.dClassRead, Option.map_eq_some_iff] at hrdP
    obtain ⟨q, hq, rfl⟩ := hrdP
    exact hq
  have hg0 : dClassGen a6.store (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, decI (r6.headD 0), []⟩ :
      ConRon.Arena.ClassGen) = some ⟨pP.nP, paramsP, Ms2P, fTCP, rdP.slots, ctorsP,
        ConLeche.structElimLevel pP.elim pP.large, []⟩ := by
    have e1 := ConRon.Bridge.denoteEList_ext c18.ext _ _ hparP
    have e2 := ConRon.Bridge.Inductives.dMajor_ext.list (c5.ext.trans (c6.ext.trans p7.ext)) _ _ hms2P
    have e3 := ConRon.Bridge.denoteEList_ext p7.ext _ _ (ConRon.Bridge.Inductives.mapM_denoteE hfTC)
    have e4 := ConRon.Bridge.Inductives.dSlot_ext.list c18.ext _ _ hslP
    have e5 := ConRon.Bridge.Inductives.dClassCtors_ext (c6.ext.trans p7.ext) _ _ hctors
    simp only [dClassGen, e1, e2, e3, e4, e5, helim, Frontend.denoteEList, hnPe, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  exact grpCE_claim hkp henv hApd hCrk hnv hcE hU P n hn hC6 (hbs.grow hg16)
    (hrb.grow hg16 (by omega)) (decHL_grow' hg16 hparb hpar) (Nat.le_trans hparb hg16.1)
    (hrd.grow (decCR_mono _) hg16) (hms2.grow (fun q => decTM_mono q) (hg3.trans (hg5.trans hg6)))
    (hctD.grow (OMono.decPL decCC_lh_mono _ _) (hg5.trans hg6))
    (decHL_grow' hg6 hftcb5 hftc5) (Nat.le_trans hftcb5 hg6.1) hel6 rfl
    (hcvR.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg16) hns hA6
    (ConRon.Bridge.Inductives.dShape_ext c18.ext _ _ hsh) hg0
    (ConRon.Bridge.Inductives.dExt_denoteCV.list c18.ext _ _ hcvRP) hwRis hclR hfRc hP6 e he k


include hkp henv hV hApd hCrk hIlpf hnv hcE hCcv hU in
/-- **`gen_rec_check_prep`'s model error claim** (`grpW_okC`'s hypotheses; the twin in its
continuation form). -/
theorem grpE_claim (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hlp : ClassesLp m mO mL)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR)
    (hNfs : ClassesNfsE p dn vis fe env) (hTka : TkaE p dn vis fe env) :
    ∀ e, grpE p (n + 1) m vis pp nested pO pL tO tL rd mO mL cO cL bO bL = .error e →
      ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e := by
  intro e he β k
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hT64 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hp8 := hbs.ptop
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, hrecs, -, -, -, hlarge, -⟩ := decBS_some hbsD
  have hrecsP0 := (ConRon.Bridge.Inductives.dShape_inv hsh).2.1
  -- the capacity guards
  by_cases g1 : m.len64 IW + 5 < 5
  · rw [grpE.abort1 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1] at he
    cases he
    exact absurd (by decide) hk0
  by_cases g2 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (pp + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [grpE.abort2 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1 g2] at he
    cases he
    exact absurd (by decide) hk0
  by_cases g3 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rd + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [grpE.abort3 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1 g2 g3] at he
    cases he
    exact absurd (by decide) hk0
  rw [grpE.arm1 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1 g2 g3] at he
  have hcap : (m.arr64 IW).size + 5 < 2 ^ 64 ∧ bs.nP + bs.k < 2 ^ 64 ∧ bs.nP + rdv.slots.length < 2 ^ 64 := by
    obtain ⟨e4, hnP64, -, -⟩ := partsShapeWords (IWGrow.refl m) hbs.1 (by omega)
    have hkb : bs.k < 2 ^ 64 := by
      obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some hbsD).1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
    have e1 : rdW (m.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
    obtain ⟨-, hslD, -, -, -⟩ := crWords hrd
    have hsl := decPL_length _ (show decPL (truncM m) (decCS (truncM m)) _ _ = some rdv.slots from hslD)
    refine ⟨?_, ?_, ?_⟩
    · have g1' : ¬ (m.len64 IW + 5).toNat < (5 : Word).toNat := fun e => g1 (UInt64.lt_iff_toNat_lt.mpr e)
      rw [UInt64.toNat_add] at g1'
      simp only [Mem.len64] at g1'
      rw [UInt64.toNat_ofNat_of_lt' (by omega)] at g1'
      simp at g1'
      omega
    · have := word_add_noWrap g2
      rw [e4, e1, UInt64.toNat_ofNat_of_lt' hnP64, UInt64.toNat_ofNat_of_lt' hkb] at this
      exact this
    · have := word_add_noWrap g3
      rw [e4, UInt64.toNat_ofNat_of_lt' hnP64, ← hsl] at this
      exact this
  obtain ⟨hsz5, hnpk, hns⟩ := hcap
  unfold grcTwinA
  -- `target_rec_pins`
  cases h1 : callE p n "target_rec_pins" [pp, bO, bL] m with
  | error e1 =>
    rw [h1, grpE.k_target_rec_pins.none] at he
    cases he
    exact ErrClaim.bind_left (CoreSpecE.of_callE (targetRecPins_claim P.rp hnv n ⟨m, Locals.init []⟩ a pp bO bL bs
      block hS hbs.1 hblk) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, grpE.k_target_rec_pins.arm1] at he
  obtain ⟨s1, hs1, -, hok1, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetRecPins_refines p P.rp n _ a dn vis fe pp bO bL bs block hS hbs.1 hblk)
    (callW_mono (callW_of_callE h1) (Nat.le_add_right n 3))
  simp only at hs1 hS1 hg1; subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize AM.st (ConRon.Arena.targetRecPins bs block) a = a1 at hrun1 hS1
  have hP1 := RcMR.ofClosed hclR (hfR _ (by decide)) (callW_of_callE h1) hP
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ (callW_of_callE h1) hA
  have hk1 := callW_keepW (callW_of_callE h1)
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.targetRecPins_spec bs pP block blockP a a1 _
    hC.check.state hC.check.pins ⟨hsh, hblkP⟩ hrun1
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  have c1' := p1.toCore hC.check
  refine ErrClaim.bind_right hrun1 ?_
  -- `class_stream_recs`
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m :=
    bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hw2 : rdW (s1.mem.arr64 IW) (pp + 2) = rdW (m.arr64 IW) (pp + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have hw3 : rdW (s1.mem.arr64 IW) (pp + 3) = rdW (m.arr64 IW) (pp + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [hw2, hw3] at he
  have hrecs1 := hrecsP.grow (fun q => decRS_mono q) hg1
  have hrecs1P := ConRon.Bridge.Inductives.dRec_ext.list c1'.ext _ _ hrecsP0
  cases h2 : callE p n "class_stream_recs" [vis, rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] s1.mem with
  | error e2 =>
    rw [h2, grpE.k_class_stream_recs.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classStreamRecs_claim hkp henv hV hApd hCrk hnv hCcv P.csr n (by omega)
      ⟨s1.mem, Locals.init []⟩ a1 fe vis _ _ bs.recs pP.recs hC1 hA1 (rec3RecsOK_of_decB hrecs1.1 hrecs1.2)
      hrecs1P) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hok2, hC2, hg2, hcs2, hA2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classStreamRecs_refinesC hkp henv hV hApd hCrk P.cpy P.ia P.slc P.csr n (by omega) _ a1 fe vis _ _ bs.recs
      pP.recs hC1 hA1 (rec3RecsOK_of_decB hrecs1.1 hrecs1.2) hrecs1P) (callW_of_callE h2)
  simp only at hs2 hC2 hg2 hcs2 hA2; subst hs2
  have hrun2 := AM.run_of_ok _ a1 hok2
  obtain ⟨c2', cvRisP, ⟨hcvRis, hwRis⟩, -⟩ := ConRon.Bridge.Inductives.classStreamRecs_spec fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.recs pP.recs a1 _ _ hC1.check hrecs1P hrun2
  generalize AM.res (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = cvRis at hrun2 hcs2 hcvRis
  generalize AM.st (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = a2 at hrun2 hC2 hcvRis c2'
  have hS2 := hC2.stage
  have c12 := c1'.trans c2'
  have hP2 := RcMR.ofClosed hclR (hfR _ (by decide)) (callW_of_callE h2) hP1
  have hk2 := callW_keepW (callW_of_callE h2)
  have hg12 := hg1.trans hg2
  refine ErrClaim.bind_right hrun2 ?_
  -- the family guard
  have hk : rdW (s2.mem.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact partsShapeK (hbs.dec) (by omega)
  by_cases hk0' : rdW (s2.mem.arr64 IW) (pp + 1) = 0
  · rw [h2, grpE.k_class_stream_recs.abort1 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0'] at he
    cases he
    have hkz : bs.k = 0 := by
      have h0 : UInt64.ofNat bs.k = 0 := by rw [← hk]; exact hk0'
      have := congrArg UInt64.toNat h0
      rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hnpk)] at this
      simpa using this
    have hkb : (bs.k == 0) = true := by rw [hkz]; rfl
    simp only [hkb, ite_true]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  have hkb : (bs.k == 0) = false := by
    cases e : bs.k with
    | zero => rw [e] at hk; exact absurd hk hk0'
    | succ _ => rfl
  simp only [hkb, Bool.false_eq_true, ite_false]
  -- the elimination guard
  have hL : (rdW (s2.mem.arr64 IW) (pp + 7) != 0) = bs.large := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact installIwB (k := 7) hlarge hsz
  have hcvRisD := csRes_decB hcs2
  -- the rest, from a state `a4` at the memory `m4` (the common tail)
  have key : ∀ (a4 : AState) (m4 : Mem), StageC dn vis fe env m4 a4 → IWGrow m m4 → RcMR m4 → KeepW m m4 →
      AbsOK m4 → ConRon.Bridge.CoreStep V env fe a a4 → cvRis.mapM (Frontend.denoteCV a4.store) = some cvRisP →
      CsRes m4 [r2.headD 0, r2.tail.headD 0] cvRis →
      grpE.j1 p n vis pp pO pL tO tL rd mO mL cO cL (r2.headD 0) (r2.tail.headD 0) m4 = .error e →
      ErrClaim (grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
          grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k)) a4 e := by
    intro a4 m4 hC4 hg4 hP4 hk4 hA4 c4 hcvRis4 hcs4 hj
    exact grpBE_claim hkp henv hApd hCrk hIlpf hnv hcE hU P n (by omega) hC4 (hbs.grow hg4)
      (hrb.grow hg4 (by have := hbs.ptop; omega)) (decHL_grow' hg4 hparb hpar) (Nat.le_trans hparb hg4.1)
      (htbl.grow (fun q => decNCN_mono q) hg4) (hrd.grow (decCR_mono _) hg4) (hms.grow (fun q => decTM_mono q) hg4)
      (hcv.grow (fun q => OMono.decCVp q) hg4) (hlp.grow hms hg4 hk4 hS.2.2.2.1) (csRes_decB hcs4) hns hnpk
      (by rw [hk4 IW]; exact hsz5) hP4 hA4 hkeep
      (ConRon.Bridge.Inductives.dShape_ext c4.ext _ _ hsh) (ConRon.Bridge.denoteEList_ext c4.ext _ _ hparP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list c4.ext _ _ htblP)
      (ConRon.Bridge.Inductives.dClassRead_ext c4.ext _ _ hrdP)
      (ConRon.Bridge.Inductives.dMajor_ext.list c4.ext _ _ hmsP)
      (ConRon.Bridge.Inductives.dExt_denoteCV.list c4.ext _ _ hcvTP) hT hMsT hcvRis4 hwRis hclR hfRc hNfs hTka
      e hj k
  by_cases h7 : rdW (s2.mem.arr64 IW) (pp + 7) = 0
  · rw [h2, grpE.k_class_stream_recs.arm3 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0' h7] at he
    have hl : bs.large = false := by rw [← hL, h7]; rfl
    simp only [hl, Bool.false_eq_true, ite_false]
    exact key a2 s2.mem hC2 hg12 hP2 (hk1.trans hk2) hA2 c12 hcvRis hcs2 he
  have hl : bs.large = true := by rw [← hL]; simpa using h7
  simp only [hl, ite_true]
  have hmsD : decPL s2.mem (decTM s2.mem) mO.toNat mL.toNat = some ms :=
    (hms.1.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg12).get (OMono.decPL (fun q => decTM_mono q) _ _)
  have hmsb : mO.toNat + mL.toNat < 2 ^ 64 := hS.lt64 hms.2
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh
  have hsrc2 : ShapeSrc s2.mem pp := partsHsrc_grow hg12 (partsShapeFacts hbs.1 hbs.2.1).2.1 hbs.2.1
  have large : ∀ (nb : Word), (nb != 0) = (nested != 0 || ms.any (·.member.isNone)) →
      grpE.j2 p n vis pp pO pL tO tL rd mO mL cO cL (r2.headD 0) (r2.tail.headD 0) nb s2.mem = .error e →
      ErrClaim (do
          let __do_lift ← ConRon.Arena.blockLargeElimAllowed bs (nested != 0 || ms.any fun x => x.member.isNone)
          if __do_lift = true then
              grcTwinB V fe bs tbl rdv ms cvTas fun ms2 ctors ftc elim =>
                grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k
            else do
              ConRon.Arena.fail
                  (CheckError.invalid
                    "generated recursor: large eliminator on a block whose sort may be Prop (official: elim_only_at_universe_zero)")
              grcTwinB V fe bs tbl rdv ms cvTas fun ms2 ctors ftc elim =>
                  grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k) a2 e := by
    intro nb hnb hj2
    rw [grpE.j2.arm1] at hj2
    cases h4 : callE p n "block_large_elim_allowed" [pp, nb] s2.mem with
    | error e4 =>
      rw [h4, grpE.k_block_large_elim_allowed.none] at hj2
      cases hj2
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    obtain ⟨al, a4, hr4, hC4, hm4, hd4, p4, -⟩ := blockLargeElimAllowed_simC P.ble n hC2 hA2
      (hbs.1.grow (decBS_mono _) hg12) hsrc2 hsh2 r4 m4 (callW_of_callE h4)
    subst hm4
    have c3' := p4.toCore hC2.check
    have hr4' : (nb != 0) = (nested != 0 || ms.any fun x => x.member.isNone) := hnb
    rw [hr4'] at hr4
    refine ErrClaim.bind_right hr4 ?_
    by_cases h0 : r4.headD 0 = 0
    · rw [h4, grpE.k_block_large_elim_allowed.abort1 p n vis pp pO pL tO tL rd mO mL cO cL _ _ r4 _ h0] at hj2
      cases hj2
      have hal : al = false := by rw [← hd4.1, h0]; rfl
      subst hal
      simp only [Bool.false_eq_true, ite_false]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    rw [h4, grpE.k_block_large_elim_allowed.arm1 p n vis pp pO pL tO tL rd mO mL cO cL _ _ r4 _ h0] at hj2
    have hal : al = true := by rw [← hd4.1]; simpa using h0
    subst hal
    simp only [ite_true]
    exact key a4 s2.mem hC4 hg12 hP2 (hk1.trans hk2) hA2 (c12.trans c3')
      (ConRon.Bridge.Inductives.dExt_denoteCV.list c3'.ext _ _ hcvRis) hcs2 hj2
  by_cases hn0 : nested = 0
  · rw [h2, grpE.k_class_stream_recs.arm1 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0' h7 hn0] at he
    cases h3 : callE p n "gen_rec_check_any_no_member" [mO, mL] s2.mem with
    | error e3 =>
      rw [h3, grpE.k_gen_rec_check_any_no_member.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, grpE.k_gen_rec_check_any_no_member.arm1] at he
    obtain ⟨s3, rfl, -, hm3, hany, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (genRecCheckAnyNoMember_refines p P.anm n _ mO mL ms hmsD hmsb hS2.2.2.2.1) (callW_of_callE h3)
    rw [hm3] at he
    exact large _ (by rw [hany, hn0]; rfl) he
  · rw [h2, grpE.k_class_stream_recs.arm2 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0' h7 hn0] at he
    exact large nested (by rw [show (nested != 0) = true by simpa using hn0]; rfl) he

include hkp henv hV hApd hCrk hIlpf hnv hcE hCcv hU in
/-- **`gen_rec_check_prep`'s error claim** (every fuel; `grpW_okC`'s hypotheses): a failing call of
class `1`/`2` claims that the twin's prep (in its continuation form) fails. -/
theorem genRecCheckPrep_claim (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hlp : ClassesLp m mO mL)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR)
    (hNfs : ClassesNfsE p dn vis fe env) (hTka : TkaE p dn vis fe env) :
    ∀ e, callE p n "gen_rec_check_prep" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m = .error e →
      ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e := by
  intro e hc β k
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have he := triple_of_callE_err (grpE_spec p P.prep n ⟨m, Locals.init []⟩ vis pp nested pO pL tO tL rd mO mL
    cO cL bO bL) hc (Err.code_ne_of_cls hk0)
  cases n with
  | zero =>
    rw [grpE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n =>
    exact grpE_claim hkp henv hV hApd hCrk hIlpf hnv hcE hU hCcv P hclR hfR n hn hC hbs hrb hpar hparb htbl hrd hms hcv
      hblk hlp hP hA hkeep hsh hparP htblP hrdP hmsP hcvTP hblkP hT hMsT hfRc hNfs hTka e he k

include hkp henv hV hApd hCrk hIlpf hnv hcE hCcv hU in
/-- **`gen_rec_check`'s error claim** (every fuel; `genRecCheck_refinesC`'s hypotheses), modulo the
two hypotheses `ClassesNfsE` (`classes_nfs`, whose model the generator cannot produce) and `TkaE`
(`target_k53_args`, whose model it cannot either). -/
theorem genRecCheck_claim' (P : GrcProg p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (N : Nat)
    (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word} {bs : BlockShape} {params : List EIdx}
    {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead} {ms : List TargetMajor}
    {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hC : StageC dn vis fe env s₀.mem a₀) (hbs : BSOK s₀.mem pp.toNat bs) (hrb : RecsB s₀.mem pp)
    (hpar : decHL s₀.mem pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tO tL s₀.mem) (hrd : DecB (fun m => decCR m rd.toNat) s₀.mem rdv)
    (hms : PSlR decTM ms mO mL s₀.mem) (hcv : PSlR decCVp cvTas cO cL s₀.mem)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hlp : ClassesLp s₀.mem mO mL)
    (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem)
    (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f) (hcoh : ConRon.Bridge.IFEnvCoh fe)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a₀.store bs = some pP) (hparP : Frontend.denoteEList a₀.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a₀.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a₀.store block = some blockP)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.ClassMajScoped pP.nP M)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR)
    (hNfs : ClassesNfsE p dn vis fe env) (hTka : TkaE p dn vis fe env) :
    CoreSpecE p N "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
      (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) s₀ a₀ :=
  genRecCheck_claim hkp henv hV hApd hCrk hIlpf hnv hcE hU P hclR hfR N hN s₀ a₀ hC hbs hrb hpar hparb htbl hrd hms
    hcv hblk hlp hP hA hkeep hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hMs hT hfRc
    (fun n hn e hc {β} k => genRecCheckPrep_claim hkp henv hV hApd hCrk hIlpf hnv hcE hU hCcv P hclR hfR n (by omega) hC
      hbs hrb hpar hparb htbl hrd hms hcv hblk hlp hP hA hkeep hsh hparP htblP hrdP hmsP hcvTP hblkP hT
      (fun M hM => (hMs M hM).1) hfRc hNfs hTka e hc k)

end sims


end L.Ind
