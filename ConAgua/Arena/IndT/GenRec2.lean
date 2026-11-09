module

import ConAgua.Arena.IndInstallSpec.PosFreeMfr
public import ConAgua.Arena.IndT.KeepC
import ConAgua.Arena.RecGenSpec.Classes
public import ConAgua.Verdict.IndBGrpM
public import ConAgua.Verdict.IndBRec6
import ConAgua.Arena.IndT.GenRec1
public import ConAgua.Arena.IndT.GfcE
public import ConAgua.Verdict.IndBRec3
public import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.IndT.RecGen27
import ConAgua.Arena.RecGenSpec.CftW
import ConAgua.Arena.IndInstallSpec.GfcW
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.PapW
import all ConRon.Bridge.Inductives.GenRec
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndInstallSpec.GpbWSimF
import ConAgua.Arena.IndInstallSpec.InstallIwB
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.RecCheckSpec.EraseFVarTys
import ConAgua.Arena.RecGenSpec.ClassFieldsOf
public import ConAgua.Arena.CrOKFrame
public import ConAgua.Arena.IndInstallSpec.GenRecCheckPrep
public import ConAgua.Arena.IndInstallSpec.GrcProg
public import ConAgua.Arena.IndInstallSpec.GrcTwinA
public import ConAgua.Arena.IndInstallSpec.Icvg
public import ConAgua.Arena.IndRealApdT
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.RecClassSpec.ClassNPcOf
public import ConAgua.Verdict.VCtx
public import ConRon.Bridge.Inductives.GenRec

@[expose] public section

/-!
# `gen_rec_check_prep`, parts B and C (one model, `grpE`; one refinement per part)

`grpC_ref` and `grpB_ref` refine the twin's second and third parts (`grcTwinB`, `grcTwinC`, in their
continuation forms) for both outcomes, a `RefC`: the ok half the twin's run reaching the continuation
with the post `GrpPost`, the error half the twin's failure with every continuation, under the
verdict context (`VerdictCtxU`). Twin side con-ron's `genRecCheck_spec`'s proof:
`classesNfs` (`cnfs_ref`, `classesNfs_spec`), `classesCtors` (`classesCtors_refinesC`,
`classesCtors_spec`), the formers (`GR.mapM_cspecF` of `classFormerTy_spec`), `structElimLevel`
(`structElimLevel_spec`), the generator's record (`dClassGen`), its prefix
(`ClassGen.prefixBinders_spec`: `RSim.liftPP` of `gpbW_simF`), the recursor types
(`classRecTysOk_refinesC`, `classRecTysOk_spec`; the rule-less recursors' environment well formed
from its run, `envWF_consBlockRecsBare`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor dClassGen dRec)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The callees of `gen_rec_check` (and `gen_rec_check_prep`) after the classes' walks, which write
none of the recursor stage's memos (`RcMR`, by `RcMR.ofClosed`; a program fact). -/
def grcRcCallees : List FnName :=
  ["class_gen_prefix_binders", "class_rec_tys_ok", "gen_rec_check_former_tys_c", "struct_elim_level",
    "class_fe_r", "flush_caches", "class_recs_rules_ok", "gen_rec_check_pop_all"]

private theorem grc_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | a :: l, _, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact grc_mapM_mem hys x hx

/-- `GrcProg` with the Verdict's restated callees' program facts (`class_rec_tys_ok`'s `RtsProgE`,
`class_recs_rules_ok`'s `CrrProgE`) and the lookups the new L adds (`block_shape_formers`,
`block_shape_names_of`). -/
structure GrcProgE (p : Prog) : Prop extends GrcProg p where
  rtsE : RtsProgE p
  crrE : CrrProgE p
  cft : CftProg p

/-- What `gen_rec_check_prep` (and each of its parts) gives besides the generator `G` and the
recursors' constants `cvGs` (from `m`, `a`; the result `r` the generator's record and the constants'
slice): the stage, the growth, the records, `AbsOK`, the walk memos, the core step, and the
generator's and the constants' denotations with the rule-less recursors' environment well formed. -/
structure GrpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (pP : ConLeche.BlockShape) (rdv : ConRon.Arena.ClassRead) (m : Mem) (a : AState) (r : List Word)
    (m' : Mem) (G : ConRon.Arena.ClassGen) (cvGs : List IConstantVal) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  gen : DecB (fun m => decCG m (r.headD 0).toNat) m' G
  ns : G.nP + G.slots.length < 2 ^ 64
  slots : G.slots = rdv.slots
  cvs : decCVS m' r.tail cvGs
  abs : AbsOK m'
  rc : RcMR m'
  core : ConRon.Bridge.CoreStep env fe a a'
  den : ∃ (gP : ConLeche.ClassGen) (cvGsP : List ConLeche.ConstantVal), dClassGen a'.store G = some gP ∧
    cvGs.mapM (Frontend.denoteCV a'.store) = some cvGsP ∧ (∀ c ∈ cvGsP, env.find? c.name = none) ∧
    ∀ f : Nat → Nat, ConLeche.EnvWF (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, f x.2)) env)

section parts
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hApd : ApdF p) (hCrf : CrfF p) (hIlpf : IlpfF p)

include hkp henv hApd hCrf in
/-- **`gen_rec_check_prep`'s third part refines `grcTwinC`, both outcomes** (the generator record,
its prefix, the recursor types; `class_rec_tys_ok` through its run). Besides the twin's facts the
post has the rule-less recursors' environment well formed (con-ron's `genRecCheck_spec`, from
`classRecTysOk`'s run). -/
theorem grpC_ref (P : GrcProgE p) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    (hCs : CcvSims p dn)
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
    (hwRis : ∀ cv ∈ cvRisP, ConLeche.Expr.WScoped 0 cv.type)
    (hunR : ∀ rc ∈ pP.recs, ConLeche.reservedRecName rc.cvR.name = false) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) (hP : RcMR m) :
    RefC (VerdictCtxU p) (grpE.k_iw_alloc p n vis pp pO pL rd cRo cRl m2o m2l co cl fo fl el
        (liftE (callW p n "iw_alloc" [14] m)))
      (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          (grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k).run a = (k G cvGs).run a') ∧
        GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
      (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k) a e) := by
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.iw.iwSize
  have hc : 200 < (m.arr64 CTL).size := hS.iw.ctl
  have hp8 := hbs.ptop
  have hrecsP0 := (ConRon.Bridge.Inductives.dShape_inv hsh).2.1
  obtain ⟨hrd3, hslD, hrcD, hrcb, -⟩ := crWords hrd
  -- `iw_alloc(14)`
  rcases c1 : callW p n "iw_alloc" [14] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, grpE.k_iw_alloc.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p P.ia n _ 14) c1
  simp only at hs1 hal; subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  obtain ⟨hS1, -, hqtop, -⟩ := allocW_stage hal hS
  rw [grpE.k_iw_alloc.arm1]
  generalize hgq : r1.headD 0 = g at hq hqtop hroom ⊢
  have h14 : (14 : Word).toNat = 14 := rfl
  rw [h14] at hroom
  show RefC _ (grpE.k_class_gen_prefix_binders p n vis pp rd cRo cRl g (liftE (callW p n "class_gen_prefix_binders" [g]
      (grpG3 (grpG2b (grpG2 (grpG1 s1.mem g pp pO pL m2o m2l) g fo fl rd) g rd co) g cl el)))) _ _
  rw [grpGs_eq s1.mem g pp pO pL m2o m2l fo fl rd co cl el (by omega) (by omega)]
  have e4 : rdW (s1.mem.arr64 IW) (pp + 4) = UInt64.ofNat bs.nP := by
    rw [hm1, allocMem_IW]; exact (partsShapeWords (IWGrow.refl m) hbs.1 (by omega)).1
  have er0 : rdW (s1.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := by rw [hm1, allocMem_IW]
  have er1 : rdW (s1.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) := by rw [hm1, allocMem_IW]
  rw [e4, er0, er1]
  generalize hws : [UInt64.ofNat bs.nP, pO, pL, m2o, m2l, fo, fl, rdW (m.arr64 IW) rd,
    rdW (m.arr64 IW) (rd + 1), co, cl, el, (0 : Word), 0] = ws at ⊢
  have hS1G : StageR vis fe (wrIW s1.mem g ws) a := StageR.wrIW hS1 g ws
  have hwl : ws.length = 14 := by rw [← hws]; rfl
  obtain ⟨hget, hgG, hfG, htopG⟩ := recMem_post m ws 14 (by rw [hwl]; rfl) hc (by rw [hwl, ← hq]; omega) hsz
  rw [← hm1, ← hq] at hget hgG htopG hfG
  have hAG := AFr.iw hfG hA
  have hPG := hP.fr (MFr.of_iw hfG)
  have hgt : g.toNat = iwTop m := hqtop
  have htG : iwTop (wrIW s1.mem g ws) = iwTop m + 14 := by
    simp only [iwTop]; rw [htopG, UInt64.toNat_add, h14, Nat.mod_eq_of_lt (by omega)]
    simp only [iwTop] at hgt; omega
  -- the generator record, decoded
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
    exact ⟨hparD.grow (OMono.decHL _ _) hg, hms2.dec.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg,
      hftD.grow (OMono.decHL _ _) hg, hslD.grow (OMono.decPL decCS_mono _ _) hg,
      hct.grow (OMono.decPL decCC_lh_mono _ _) hg⟩
  generalize hmG : wrIW s1.mem g ws = mG at hS1G hget hgG htopG htG hAG hPG ⊢
  obtain ⟨cP, cM, cF, cS, cC⟩ := hcomp mG hgG
  have hsl1 : rd.toNat + 1 < iwTop m := by omega
  have hG0 : DecB (fun x => decCG x g.toNat) mG
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, []⟩ : ConRon.Arena.ClassGen) := by
    subst hws
    exact cgRec_decB (fun j hj => hget j (by simpa using hj)) (by omega) (UInt64.toNat_ofNat_of_lt' hnP) cP cM cF
      cS cC hel hel' (by show decHL (truncM mG) (0 : Word).toNat (0 : Word).toNat = some []; simp [decHL, hslice?])
  have hCG : StageC dn vis fe env mG a := hC.of_pstep hS1G hAG (PStep.refl hC.check.state)
  -- the prefix
  rcases c2 : callW p n "class_gen_prefix_binders" [g] mG with _ | ⟨r2, m2⟩
  · rw [liftE_none, grpE.k_class_gen_prefix_binders.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s2, hs2, -, hgp⟩ := triple_of_callW (s₀ := ⟨mG, Locals.init []⟩) (prefixBinders_spec p P.pb n _ g) c2
  simp only at hs2 hgp; subst hs2
  obtain ⟨x2, a2, hrun2, hC2, ⟨⟨⟨hS2, hg2, hd2⟩, hA2⟩, hfr2⟩, hR2, p9⟩ :=
    RSim.liftPP hCG (gpbW_simF dn vis fe n mG a g _ hS1G hG0 hns hAG)
      (fun _ _ _ hh => ⟨hh.1.1.1, hh.1.2⟩)
      (ConRon.Bridge.Inductives.ClassGen.prefixBinders_spec _ gP0) hg0 (r2, s2.mem) hgp
  dsimp only at hS2 hg2 hd2 hfr2 hA2 hC2
  have c19 := p9.toCore hC.check
  have hk2 := callW_keepW c2
  have hP2 := RcMR.ofClosed hclR (hfRc _ (by decide)) c2 hPG
  by_cases h0 : r2.headD 0 = 0
  · rw [grpE.k_class_gen_prefix_binders.abort1 p n vis pp rd cRo cRl g r2 _ h0]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  rw [grpE.k_class_gen_prefix_binders.arm1 p n vis pp rd cRo cRl g r2 _ h0]
  rcases x2 with _ | pre
  · exact absurd hd2 h0
  obtain ⟨preP, -, hpreP⟩ := hR2
  obtain ⟨-, hpreD, hpreb⟩ := hd2
  have hfr := hfr2 pre rfl
  generalize ho : r2.tail.headD 0 = o at hpreD hpreb hfr ⊢
  generalize hl : r2.tail.tail.headD 0 = l at hpreD hpreb ⊢
  have hgs : g.toNat + 14 ≤ (s2.mem.arr64 IW).size := by
    rw [hk2 IW, ← hmG, wrIW_size, hm1, allocMem_IW]; omega
  have e12 : (g + 12).toNat = g.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have e13 : (g + 13).toNat = g.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  have hgP : IWGrow m (grpPMem s2.mem g o l) :=
    ((hgG.trans hg2).set_iw _ _ (by rw [e12]; omega)).set_iw _ _ (by rw [e13]; omega)
  have hSP : StageR vis fe (grpPMem s2.mem g o l) a2 := (hS2.set_iw _ _).set_iw _ _
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
    rw [ite_eq_right (by omega), hg2.iwGet _ (by omega), hget j (by rw [hwl]; omega), ← hws]
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
  have hpreP' : DecB (fun x => (decHL x o.toNat l.toNat : Option (List EIdx))) (grpPMem s2.mem g o l) pre := by
    refine decHL_decB ?_ (by rw [htP]; exact hpreb)
    simp only [grpPMem]
    rw [decHL_set_out (by rw [e13]; omega), decHL_set_out (by rw [e12]; omega)]
    exact hpreD
  obtain ⟨dP, dM, dF, dS, dC⟩ := hcomp _ hgP
  have hG : DecB (fun x => decCG x g.toNat) (grpPMem s2.mem g o l)
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ : ConRon.Arena.ClassGen) :=
    cgRec_decB hgetP (by rw [htP]; have := hg2.iw; rw [htG] at this; omega) (UInt64.toNat_ofNat_of_lt' hnP) dP dM dF dS dC hel hel'
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
  rw [show (s2.mem.set64 IW (g + 12) o).set64 IW (g + 13) l = grpPMem s2.mem g o l from rfl]
  rw [show (pp + 1 : Word) = pp + UInt64.ofNat 1 from rfl, show (pp + 2 : Word) = pp + UInt64.ofNat 2 from rfl,
    show (pp + 3 : Word) = pp + UInt64.ofNat 3 from rfl, show (rd + 2 : Word) = rd + UInt64.ofNat 2 from rfl,
    show (rd + 3 : Word) = rd + UInt64.ofNat 3 from rfl, rP 1 (by omega), rP 2 (by omega), rP 3 (by omega),
    rR 2 (by omega), rR 3 (by omega)]
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some (show decBS (truncM m) pp.toNat = some bs from hbs.1)).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hkw : rdW (m.arr64 IW) (pp + UInt64.ofNat 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
  rw [hkw]
  have hrcs := hrecsP.dec.grow (OMono.decPL decRS_mono _ _) hgP
  have hrecs2 := ConRon.Bridge.Inductives.dRec_ext.list c19.ext _ _ hrecsP0
  have hcv2 := ConRon.Bridge.Inductives.dExt_denoteCV.list c19.ext _ _ hcvP
  rcases c3 : callE p n "class_rec_tys_ok" [vis, g, UInt64.ofNat bs.k, rdW (m.arr64 IW) (pp + UInt64.ofNat 2),
      rdW (m.arr64 IW) (pp + UInt64.ofNat 3), cRo, cRl, rdW (m.arr64 IW) (rd + UInt64.ofNat 2),
      rdW (m.arr64 IW) (rd + UInt64.ofNat 3)] (grpPMem s2.mem g o l) with e3 | ⟨r3, m3⟩
  · rw [grpE.k_class_rec_tys_ok.none]
    refine fun hV _ k => ?_
    have := CoreSpecE.of_callE (classRecTysOk_claim hkp hApd hCrf hV.nv hV.core hV.uce hCs henv P.rtsE n hn
      ⟨grpPMem s2.mem g o l, Locals.init []⟩ a2 g (UInt64.ofNat bs.k) _ _ cRo cRl _ _ _ bs.recs cvRis rdv.recCls hCP hG
      hns hrcs (rec3RecsOK_of_decB hrcs (Nat.le_trans hrecsP.bound hgP.iw)) (hcv.grow (OMono.decPL
        (fun q => OMono.decCVp q) _ _) hgP) (hrcD.grow (OMono.decNL _ _) hgP) hAP hgPd hrecs2 hcv2 hwRis) c3
    rw [UInt64.toNat_ofNat_of_lt' hkb] at this
    unfold grcTwinC
    refine ErrClaim.bind_right hrun2 ?_
    simp only []
    exact ErrClaim.bind_left this
  rw [grpE.k_class_rec_tys_ok.arm1]
  have hP3 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE c3) hPP
  obtain ⟨s3, rfl, -, hok3, ⟨hC3, hg3, hd3⟩, hA3⟩ := triple_of_callW (s₀ := ⟨grpPMem s2.mem g o l, Locals.init []⟩)
    (classRecTysOk_refinesC hkp hApd hCrf hCs henv P.rtsE n hn _ a2 g (UInt64.ofNat bs.k) _ _ cRo cRl _ _ _ bs.recs cvRis
      rdv.recCls hCP hG hns hrcs (rec3RecsOK_of_decB hrcs (Nat.le_trans hrecsP.bound hgP.iw)) (hcv.grow (OMono.decPL
        (fun q => OMono.decCVp q) _ _) hgP) (hrcD.grow (OMono.decNL _ _) hgP) hAP hgPd hrecs2 hcv2 hwRis)
    (callW_of_callE c3)
  have hrun3 := AM.run_of_ok _ a2 hok3
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hrun3 hC3 hd3
  obtain ⟨c10, cvGsP, ⟨hcvGs, hfrG⟩, hF10⟩ := ConRon.Bridge.Inductives.classRecTysOk_spec fe
    (ConRon.Bridge.CoreSpec.of_core) henv _ _ bs.k bs.recs pP.recs cvRis cvRisP rdv.recCls hwRis a2 _ _
    hCP.check ⟨hgPd, hrecs2, hcv2⟩ hrun3
  -- the rule-less recursors' environment
  have henvR : ∀ f : Nat → Nat, ConLeche.EnvWF (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, f x.2)) env) := by
    obtain ⟨F10, hF10'⟩ := id hF10
    rw [ConLeche.classRecTysOk_datF] at hF10'
    obtain ⟨hlenG, hallG⟩ := ConLeche.classRecTysOk_run hF10'
    intro f
    have hun : ∀ cv ∈ cvGsP, ConLeche.reservedRecName cv.name = false := by
      intro cv hcv
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcv
      have hil : i < pP.recs.length := by
        rw [← hlenG]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨c, cvG, -, hcvG, ⟨R⟩⟩ := hallG i _ (List.getElem?_eq_getElem hil)
      rw [hi] at hcvG
      obtain rfl := Option.some.inj hcvG
      rw [R.hcvG]
      exact hunR _ (List.getElem_mem hil)
    refine ConLeche.Cached.envWF_consBlockRecsBare henv (fun c hc => ?_) (fun c hc => ?_)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.of_mem_zip hx).1
      have hil : i < pP.recs.length := by
        rw [← hlenG]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨c, cvG, -, hcvG, ⟨R⟩⟩ := hallG i _ (List.getElem?_eq_getElem hil)
      rw [hi] at hcvG
      obtain rfl := Option.some.inj hcvG
      exact ConLeche.classConstOk_typeWF R.hcv
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      exact ConLeche.litShapeAt_of_reservedRec (hun x.1 (List.of_mem_zip hx).1)
  refine ⟨⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩,
    AM.res (ConRon.Arena.classRecTysOk V fe ⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ bs.k bs.recs
      cvRis rdv.recCls) a2, _, fun {β} k => ?_, ⟨hC3, hgP.trans hg3, hG.grow (decCG_mono _) hg3, hns, rfl, ?_, hA3, hP3,
    c19.trans c10, _, cvGsP, ConRon.Bridge.Inductives.dClassGen_ext c10.ext _ _ hgPd, hcvGs, hfrG, henvR⟩⟩
  · simp only [grcTwinC, StateT.run_bind, hrun2, except_ok_bind, hrun3]
  · simpa [decCVS] using hd3

include hkp henv hApd hCrf hIlpf in
/-- **`gen_rec_check_prep`'s second part refines `grcTwinB`, both outcomes** (the classes' entries
and constructors, the count, the formers, the level, then the third part, `grpC_ref`). -/
theorem grpB_ref (P : GrcProgE p) (hF : FtProg p) (hWt : WhnfTopE p) (n : Nat) (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL tO tL rd mO mL cO cL cRo cRl : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvRis : List IConstantVal}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp bs.formers cO cL m)
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
    (hcvTP : bs.formers.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M)
    (hcvRP : cvRis.mapM (Frontend.denoteCV a.store) = some cvRisP)
    (hwRis : ∀ cv ∈ cvRisP, ConLeche.Expr.WScoped 0 cv.type)
    (hunR : ∀ rc ∈ pP.recs, ConLeche.reservedRecName rc.cvR.name = false) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    RefC (VerdictCtxU p) (grpE.j1 p n vis pp pO pL tO tL rd mO mL cO cL cRo cRl m)
      (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          (grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k)).run a = (k G cvGs).run a') ∧
        GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
      (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
          grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k)) a e) := by
  have hS := hC.stage
  have hT64 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.iw.iwSize
  have hp8 := hbs.ptop
  obtain ⟨hrd3, hslD, -, -, hslb⟩ := crWords hrd
  obtain ⟨-, -, hnPe, -, -, hlargeP, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh
  have hslP : rdv.slots.mapM (ConRon.Bridge.Inductives.dSlot a.store) = some rdP.slots := by
    simp only [ConRon.Bridge.Inductives.dClassRead, Option.map_eq_some_iff] at hrdP
    obtain ⟨q, hq, rfl⟩ := hrdP
    exact hq
  have hformer : ∀ t ∈ cvTasP.map (·.type), ConLeche.Expr.WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  have hftP := ConRon.Bridge.Inductives.GR.types_denote hcvTP
  rw [grpE.j1.arm1]
  -- the formers' types
  rcases c1 : callW p n "gen_rec_check_former_tys" [cO, cL] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, grpE.k_gen_rec_check_former_tys.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some, grpE.k_gen_rec_check_former_tys.arm1]
  obtain ⟨s1, hs1, -, hS1, hg1, hf1, hft1, hftb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (genRecCheckFormerTys_refines P.ia P.gft n _ a cO cL bs.formers hS hcv) c1
  simp only at hs1 hS1 hg1 hf1 hft1 hftb1; subst hs1
  have hP1 := hP.fr hf1
  have hk1 := callW_keepW c1
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c1 hA
  have hC1 : StageC dn vis fe env s1.mem a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  -- `classes_nfs`
  have hT2 := cnfs_ref hkp henv P.cns n hn (dn := dn) (vis := vis) hC1 hA1 (hbs.grow hg1) hft1 hftb1
    (htbl.grow (fun q => decNCN_mono q) hg1) (hms.grow (fun q => decTM_mono q) hg1) hP1 hsh hftP htblP hmsP
    hformer hMsT
  have hs2T := cnfsE_spec p P.cns.cns n ⟨s1.mem, Locals.init []⟩ vis pp (r1.headD 0) (r1.tail.headD 0) tO tL mO mL
  rcases c2 : callE p n "classes_nfs" [vis, pp, r1.headD 0, r1.tail.headD 0, tO, tL, mO, mL] s1.mem with
    e2 | ⟨r2, m2⟩
  · rw [grpE.k_classes_nfs.none]
    refine fun hG _ k => ?_
    unfold grcTwinB
    exact ErrClaim.bind_left (RefE.run_err hs2T hG.nv hG.toVerdictCtx hT2 c2)
  rw [grpE.k_classes_nfs.arm1]
  obtain ⟨s2, hs2, -, ms2, a2, hrun2, hR2⟩ := RefE.run_ok hs2T hT2 c2
  subst hs2
  have hms2 := hR2.slice
  have hC2 := hR2.stage
  have hg2 := hR2.grow
  have hP2 := hR2.rc
  have hA2 := hR2.abs
  dsimp only at hms2 hC2 hg2 hP2 hA2
  have hk2 := callW_keepW (callW_of_callE c2)
  obtain ⟨c4, Ms2P, ⟨hms2P, hMs2⟩, -⟩ := ConRon.Bridge.Inductives.classesNfs_spec fe
    (ConRon.Bridge.CoreSpec.of_core) henv bs pP _ _ tbl tblP hformer ms MsP hMsT a _ _ hC1.check
    ⟨hsh, hftP, htblP, hmsP⟩ hrun2
  have hS2 := hC2.stage
  have hg12 := hg1.trans hg2
  -- `classes_ctors`
  have hsz2 : (s2.mem.arr64 IW).size = (m.arr64 IW).size := by rw [hk2 IW, hk1 IW]
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext c4.ext _ _ hsh
  have hftP2 := ConRon.Bridge.denoteEList_ext c4.ext _ _ hftP
  have hrdP2 := ConRon.Bridge.Inductives.dClassRead_ext c4.ext _ _ hrdP
  rcases c3 : callE p n "classes_ctors" [vis, pp, r1.headD 0, r1.tail.headD 0, rd, r2.headD 0, r2.tail.headD 0]
      s2.mem with e3 | ⟨r3, m3⟩
  · rw [grpE.k_classes_ctors.none]
    refine fun hG _ k => ?_
    unfold grcTwinB
    refine ErrClaim.bind_right hrun2 (ErrClaim.bind_left ?_)
    exact CoreSpecE.of_callE (classesCtors_claim hkp henv P.ccs hIlpf P.opf dn fe hG.nv hG.core pp (r1.headD 0)
      (r1.tail.headD 0) rd (r2.headD 0) (r2.tail.headD 0) n hn ⟨s2.mem, Locals.init []⟩ a2 bs
      (bs.formers.map (·.type)) rdv ms2 hC2 hA2 (hbs.grow hg12) (by rw [decHL_grow3 hg2 hftb1]; exact hft1)
      (Nat.le_trans hftb1 hg2.iw) (hrd.grow (decCR_mono _) hg12) hms2.1 (hS2.lt64 hms2.2) hnpk
      (by rw [hsz2]; exact hsz5) hP2 hsh2 hftP2 hrdP2 hms2P hformer hMs2) c3
  rw [grpE.k_classes_ctors.arm1]
  obtain ⟨s3, hs3, -, hok3, hC3, hg3, hsp3, hP3, hA3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classesCtors_refinesC hkp henv P.ccs hIlpf P.opf n hn _ a2 dn fe vis pp _ _ rd _ _ bs (bs.formers.map (·.type)) rdv ms2
      hC2 hA2 (hbs.grow hg12) (by rw [decHL_grow3 hg2 hftb1]; exact hft1) (Nat.le_trans hftb1 hg2.iw)
      (hrd.grow (decCR_mono _) hg12) hms2.1 (hS2.lt64 hms2.2) hnpk (by rw [hsz2]; exact hsz5) hP2
      hsh2 hftP2 hrdP2 hms2P hformer hMs2) (callW_of_callE c3)
  simp only at hs3 hC3 hg3 hsp3 hP3 hA3; subst hs3
  have hrun3 := AM.run_of_ok _ a2 hok3
  obtain ⟨c5, ctorsP, hctors, -⟩ := ConRon.Bridge.Inductives.classesCtors_spec fe
    (ConRon.Bridge.CoreSpec.of_core) henv bs pP _ _ rdv rdP ms2 Ms2P hformer hMs2 ms2 Ms2P 0 a2 _ _
    hC2.check ⟨hsh2, hftP2, hrdP2, hms2P, hms2P⟩ hrun3
  generalize AM.res (ConRon.Arena.classesCtors V fe bs (bs.formers.map (·.type)) rdv ms2 0 ms2) a2 = ctors
    at hrun3 hsp3 hctors
  generalize AM.st (ConRon.Arena.classesCtors V fe bs (bs.formers.map (·.type)) rdv ms2 0 ms2) a2 = a3 at hrun3 hC3 hctors c5
  have hS3 := hC3.stage
  have hg13 := hg12.trans hg3
  have hctD := spl_decB hsp3.toSPL
  -- the count
  have er0 : rdW (s3.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := partsRdIW_grow hg13 (by omega)
  have er1 : rdW (s3.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [er0, er1]
  rcases c4' : callW p n "gen_rec_check_minor_ok" [rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), r3.headD 0,
      r3.tail.headD 0] s3.mem with _ | ⟨r4, m4⟩
  · rw [liftE_none, grpE.k_gen_rec_check_minor_ok.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s4, rfl, -, hm4, hmo⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (genRecCheckMinorOk_refines P.csm P.gmo n _ _ _ _ _ rdv.slots ctors
      ((hslD.grow (OMono.decPL decCS_mono _ _) hg13).get (OMono.decPL decCS_mono _ _)) hslb
      (hctD.get (OMono.decPL decCC_lh_mono _ _)) (hS3.lt64 hsp3.2.1) hS3.iw.iwSize) c4'
  by_cases h0 : r4.headD 0 = 0
  · rw [grpE.k_gen_rec_check_minor_ok.abort1 p n vis pp pO pL rd cO cL cRo cRl _ _ _ _ r4 _ h0]
    have hcount : ((rdv.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum) = false := by
      rw [← hmo, h0]; rfl
    refine fun _ _ k => ?_
    unfold grcTwinB
    refine ErrClaim.bind_right hrun2 (ErrClaim.bind_right hrun3 ?_)
    simp only [hcount, Bool.false_eq_true, ite_false]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  rw [grpE.k_gen_rec_check_minor_ok.arm1 p n vis pp pO pL rd cO cL cRo cRl _ _ _ _ r4 _ h0, hm4]
  have hcount : ((rdv.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum) = true := by
    rw [← hmo]; simpa using h0
  -- the classes' formers
  have hms3P := ConRon.Bridge.Inductives.dMajor_ext.list c5.ext _ _ hms2P
  have hcv3P := ConRon.Bridge.Inductives.dExt_denoteCV.list (c4.trans c5).ext _ _ hcvTP
  have hR5 := gfc_ref hkp P.cft hF hIlpf henv P.gftc n hn hC3 hA3 (hcv.grow (fun q => OMono.decCVp q) hg13)
    (hms2.grow (fun q => decTM_mono q) hg3) hcv3P hms3P
  have hs5T := gfcE_spec p P.cft P.gftc n ⟨s3.mem, Locals.init []⟩ vis cO cL (r2.headD 0) (r2.tail.headD 0)
  rcases c5' : callE p n "gen_rec_check_former_tys_c" [vis, cO, cL, r2.headD 0, r2.tail.headD 0] s3.mem with
    e5 | ⟨r5, m5⟩
  · rw [grpE.k_gen_rec_check_former_tys_c.none]
    refine fun hG _ k => ?_
    unfold grcTwinB
    refine ErrClaim.bind_right hrun2 (ErrClaim.bind_right hrun3 ?_)
    simp only [hcount, ite_true]
    exact ErrClaim.bind_left (RefE.run_err hs5T hG.nv ⟨hG.nv, hWt⟩ hR5 c5')
  rw [grpE.k_gen_rec_check_former_tys_c.arm1]
  obtain ⟨s5, hs5, -, ftc, a5, hrun5, hC5, hA5, hg5, hftc5, hftcb5⟩ := RefE.run_ok hs5T hR5 c5'
  subst hs5
  dsimp only at hC5 hA5 hg5 hftc5 hftcb5
  have hS5 := hC5.stage
  have hP5 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE c5') hP3
  have c45 := c4.trans c5
  obtain ⟨c6, fTCP, hfTC, -⟩ := ConRon.Bridge.Inductives.GR.mapM_cspecF ConRon.Bridge.Inductives.dMajor
    ConRon.Bridge.Inductives.dMajor_ext (fun st e => denoteE st e) ConRon.Bridge.Inductives.dExt_denoteE
    (fun st => bs.formers.mapM (Frontend.denoteCV st) = some cvTasP)
    (fun hx h => ConRon.Bridge.Inductives.dExt_denoteCV.list hx _ _ h) (ConRon.Arena.classFormerTy V fe bs.formers)
    (ConLeche.classFormerTy (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv env) cvTasP)
    (fun m mP s₀ s' r hok hpre hrun => ConRon.Bridge.Inductives.classFormerTy_spec fe
      ConRon.Bridge.CoreSpec.of_core henv bs.formers cvTasP m mP s₀ s' r
      hok ⟨hpre.1, hpre.2⟩ hrun) ms2 Ms2P a3 _ _ hC3.check
    ⟨ConRon.Bridge.Inductives.dExt_denoteCV.list c45.ext _ _ hcvTP,
      ConRon.Bridge.Inductives.dMajor_ext.list c5.ext _ _ hms2P⟩ hrun5
  have hg15 := hg13.trans hg5
  have c46 := c45.trans c6
  -- the elimination level
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, -, -, helimD, -, hlarge, -⟩ := decBS_some hbsD
  obtain ⟨hel5, hel5'⟩ := installIwH (i := 5) helimD hsz
  have hL := installIwB (k := 7) hlarge hsz
  have ew5 : rdW (s5.mem.arr64 IW) (pp + 5) = rdW (m.arr64 IW) (pp + UInt64.ofNat 5) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  have ew7 : rdW (s5.mem.arr64 IW) (pp + 7) = rdW (m.arr64 IW) (pp + UInt64.ofNat 7) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  rw [ew5, ew7]
  rcases c6' : callW p n "struct_elim_level" [rdW (m.arr64 IW) (pp + UInt64.ofNat 5),
      rdW (m.arr64 IW) (pp + UInt64.ofNat 7)] s5.mem with _ | ⟨r6, m6⟩
  · rw [liftE_none, grpE.k_struct_elim_level.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some, grpE.k_struct_elim_level.arm1]
  obtain ⟨s6, rfl, -, a6, hrun6, hS6, hg6, hel6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (structElimLevel_stage P.sel n _ a5 _ _ hS5 hel5) c6'
  have hP6 := RcMR.ofClosed hclR (hfRc _ (by decide)) c6' hP5
  rw [hel5', hL] at hrun6
  have hg16 := hg15.trans hg6
  have hA6 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c6' hA5
  have hsh5 := ConRon.Bridge.Inductives.dShape_ext c46.ext _ _ hsh
  obtain ⟨p7, helim⟩ := ConRon.Bridge.Inductives.structElimLevel_spec bs.elim pP.elim bs.large a5 a6 _
    hC5.check.state (ConRon.Bridge.Inductives.dShape_inv hsh5).2.2.2.1 hrun6
  have hC6 : StageC dn vis fe env s6.mem a6 := hC5.of_pstep hS6 hA6 p7
  have c18 := c46.trans (p7.toCore hC5.check)
  rw [hlargeP] at helim
  -- the generator's record, denoted
  have hg0 : dClassGen a6.store (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, decI (r6.headD 0), []⟩ :
      ConRon.Arena.ClassGen) = some ⟨pP.nP, paramsP, Ms2P, fTCP, rdP.slots, ctorsP,
        ConLeche.structElimLevel pP.elim pP.large, []⟩ := by
    have e1 := ConRon.Bridge.denoteEList_ext c18.ext _ _ hparP
    have e2 := ConRon.Bridge.Inductives.dMajor_ext.list (c5.ext.trans (c6.ext.trans p7.ext)) _ _ hms2P
    have e3 := ConRon.Bridge.denoteEList_ext p7.ext _ _ (ConRon.Bridge.Inductives.mapM_denoteE hfTC)
    have e4 := ConRon.Bridge.Inductives.dSlot_ext.list c18.ext _ _ hslP
    have e5 := ConRon.Bridge.Inductives.dClassCtors_ext (c6.ext.trans p7.ext) _ _ hctors
    rw [dClassGen]
    simp only [e1, e2, e3, e4, e5, helim, Frontend.denoteEList, hnPe, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  -- part C
  refine RefC.mono (grpC_ref hkp henv hApd hCrf P n hn hCs hC6 (hbs.grow hg16)
    (hrb.grow hg16 (by omega)) (decHL_grow' hg16 hparb hpar) (Nat.le_trans hparb hg16.iw)
    (hrd.grow (decCR_mono _) hg16) (hms2.grow (fun q => decTM_mono q) (hg3.trans (hg5.trans hg6)))
    (hctD.grow (OMono.decPL decCC_lh_mono _ _) (hg5.trans hg6))
    (decHL_grow' hg6 hftcb5 hftc5) (Nat.le_trans hftcb5 hg6.iw) hel6 rfl
    (hcvR.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg16) hns hA6
    (ConRon.Bridge.Inductives.dShape_ext c18.ext _ _ hsh) hg0
    (ConRon.Bridge.Inductives.dExt_denoteCV.list c18.ext _ _ hcvRP) hwRis hunR hclR hfRc hP6) ?_ ?_
  · rintro v ⟨G, cvGs, a', hrunC, hR⟩
    refine ⟨G, cvGs, a', fun {β} k => ?_, { hR with grow := hg16.trans hR.grow, core := c18.trans hR.core }⟩
    rw [← hrunC k]
    simp only [grcTwinB, StateT.run_bind, hrun2, except_ok_bind, hrun3, hcount, hrun5, hrun6, ite_true]
  · intro e _ hc _ k
    unfold grcTwinB
    refine ErrClaim.bind_right hrun2 (ErrClaim.bind_right hrun3 ?_)
    simp only [hcount, ite_true]
    exact ErrClaim.bind_right hrun5 (ErrClaim.bind_right hrun6 (hc k))

end parts

end L.Ind
