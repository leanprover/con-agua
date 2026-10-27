import ConAgua.Arena.IndT.GenRec1
import ConAgua.Arena.IndT.RecGen7
import ConAgua.Arena.IndT.RecGen27
import ConAgua.Arena.IndInstallSpec38
import ConAgua.Arena.RecGenSpec.CftW

/-!
# `genRecCheck` under `StageC`, part 2 (lane `indstaget`, helper `grc`)

`gen_rec_check_prep`'s second and third parts (`grpBW_ok`'s, `grpCW_ok`'s, `IndInstallSpec41`)
under `StageC`; twin side con-ron's `genRecCheck_spec`'s proof: `classesNfs`
(`classesNfs_refinesLpC`, `classesNfs_spec`), `classesCtors` (`classesCtors_refinesC`,
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

section parts
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)

include hkp henv hApd hCrk in
/-- **`gen_rec_check_prep`'s third part under `StageC`** (`grpCW_ok`'s): the generator record,
its prefix, the recursor types. Besides the twin's facts the post has the rule-less recursors'
environment well formed (con-ron's `genRecCheck_spec`, from `classRecTysOk`'s run). -/
theorem grpCW_okC (P : GrcProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL rd cRo cRl m2o m2l fo fl co cl el : Word}
    {bs : BlockShape} {params : List EIdx} {rdv : ConRon.Arena.ClassRead} {ms2 : List TargetMajor}
    {ctors : List (List ConRon.Arena.ClassCtor)} {ftc : List EIdx} {elim : LIdx} {cvRis : List IConstantVal}
    {r : List Word} {m' : Mem}
    (h : grpCW p n m vis pp pO pL rd cRo cRl m2o m2l fo fl co cl el = some (r, m'))
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
    ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        (grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k).run a = (k G cvGs).run a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ DecB (fun m => decCG m (r.headD 0).toNat) m' G ∧
      G.nP + G.slots.length < 2 ^ 64 ∧ G.slots = rdv.slots ∧ decCVS m' r.tail cvGs ∧ AbsOK m' ∧
      RcMR m' ∧ ConRon.Bridge.CoreStep V env fe a a' ∧
      ∃ (gP : ConLeche.ClassGen) (cvGsP : List ConLeche.ConstantVal), dClassGen a'.store G = some gP ∧
        cvGs.mapM (Frontend.denoteCV a'.store) = some cvGsP ∧ (∀ c ∈ cvGsP, env.find? c.name = none) ∧
        ∀ f : Nat → Nat, ConLeche.EnvWF (ConLeche.consBlockRecsBare pP 0
          ((cvGsP.zip rdv.recCls).map fun x => (x.1, f x.2)) env) := by
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hc : 200 < (m.arr64 CTL).size := hS.2.2.2.2.2
  have hp8 := hbs.ptop
  have hrecsP0 := (ConRon.Bridge.Inductives.dShape_inv hsh).2.1
  obtain ⟨hrd3, hslD, hrcD, hrcb, -⟩ := crWords hrd
  unfold grpCW at h
  -- `iw_alloc(14)`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [grpC1_some] at h
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p P.ia n _ 14) c1
  simp only at hs1 hal; subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  obtain ⟨hS1, -, hqtop, -⟩ := allocW_stage hal hS
  generalize hgq : r1.headD 0 = g at h hq hqtop hroom
  have h14 : (14 : Word).toNat = 14 := rfl
  rw [h14] at hroom
  unfold grpC2W grpC2bW grpC3W at h
  rw [grpGs_eq s1.mem g pp pO pL m2o m2l fo fl rd co cl el (by omega) (by omega)] at h
  have e4 : rdW (s1.mem.arr64 IW) (pp + 4) = UInt64.ofNat bs.nP := by
    rw [hm1, allocMem_IW]; exact (partsShapeWords (IWGrow.refl m) hbs.1 (by omega)).1
  have er0 : rdW (s1.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := by rw [hm1, allocMem_IW]
  have er1 : rdW (s1.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) := by rw [hm1, allocMem_IW]
  rw [e4, er0, er1] at h
  generalize hws : [UInt64.ofNat bs.nP, pO, pL, m2o, m2l, fo, fl, rdW (m.arr64 IW) rd,
    rdW (m.arr64 IW) (rd + 1), co, cl, el, (0 : Word), 0] = ws at h
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
    exact ⟨hparD.grow (OMono.decHL _ _) hg, hms2.1.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg,
      hftD.grow (OMono.decHL _ _) hg, hslD.grow (OMono.decPL decCS_mono _ _) hg,
      hct.grow (OMono.decPL decCC_lh_mono _ _) hg⟩
  generalize hmG : wrIW s1.mem g ws = mG at hS1G hget hgG htopG htG h hAG hPG
  obtain ⟨cP, cM, cF, cS, cC⟩ := hcomp mG hgG
  have hsl1 : rd.toNat + 1 < iwTop m := by omega
  have hG0 : DecB (fun x => decCG x g.toNat) mG
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, []⟩ : ConRon.Arena.ClassGen) := by
    subst hws
    exact cgRec_decB (fun j hj => hget j (by simpa using hj)) (by omega) (UInt64.toNat_ofNat_of_lt' hnP) cP cM cF
      cS cC hel hel' (by show decHL (truncM mG) (0 : Word).toNat (0 : Word).toNat = some []; simp [decHL, hslice?])
  have hCG : StageC dn vis fe env mG a := hC.of_pstep hS1G hAG (PStep.refl hC.check.state)
  -- the prefix
  unfold grpDW at h
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
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
  have h0 : ¬ (r2.headD 0 = 0) := fun h0 => by rw [grpC3_bad (h := h0)] at h; cases h
  rw [grpC3_ok (h := h0)] at h
  rcases x2 with _ | pre
  · exact absurd hd2 h0
  obtain ⟨preP, -, hpreP⟩ := hR2
  obtain ⟨-, hpreD, hpreb⟩ := hd2
  have hfr := hfr2 pre rfl
  generalize ho : r2.tail.headD 0 = o at h hpreD hpreb hfr
  generalize hl : r2.tail.tail.headD 0 = l at h hpreD hpreb
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
  rw [show (pp + 1 : Word) = pp + UInt64.ofNat 1 from rfl, show (pp + 2 : Word) = pp + UInt64.ofNat 2 from rfl,
    show (pp + 3 : Word) = pp + UInt64.ofNat 3 from rfl, show (rd + 2 : Word) = rd + UInt64.ofNat 2 from rfl,
    show (rd + 3 : Word) = rd + UInt64.ofNat 3 from rfl, rP 1 (by omega), rP 2 (by omega), rP 3 (by omega),
    rR 2 (by omega), rR 3 (by omega)] at h
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some (show decBS (truncM m) pp.toNat = some bs from hbs.1)).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hkw : rdW (m.arr64 IW) (pp + UInt64.ofNat 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
  rw [hkw] at h
  have hrcs := hrecsP.1.grow (OMono.decPL decRS_mono _ _) hgP
  have hrecs2 := ConRon.Bridge.Inductives.dRec_ext.list c19.ext _ _ hrecsP0
  have hcv2 := ConRon.Bridge.Inductives.dExt_denoteCV.list c19.ext _ _ hcvP
  obtain ⟨⟨r3, m3⟩, c3, h⟩ := of_K h rfl
  rw [grpC4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hP3 := RcMR.ofClosed hclR (hfRc _ (by decide)) c3 hPP
  obtain ⟨s3, rfl, -, hok3, ⟨hC3, hg3, hd3⟩, hA3⟩ := triple_of_callW (s₀ := ⟨grpPMem s2.mem g o l, Locals.init []⟩)
    (classRecTysOk_refinesC hkp hApd hCrk henv P.rts n hn _ a2 g (UInt64.ofNat bs.k) _ _ cRo cRl _ _ _ bs.recs cvRis
      rdv.recCls hCP hG hns hrcs (rec3RecsOK_of_decB hrcs (Nat.le_trans hrecsP.2 hgP.1)) (hcv.grow (OMono.decPL
        (fun q => OMono.decCVp q) _ _) hgP) (hrcD.grow (OMono.decNL _ _) hgP) hAP hgPd hrecs2 hcv2 hwRis) c3
  have hrun3 := AM.run_of_ok _ a2 hok3
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hrun3 hC3 hd3
  obtain ⟨c10, cvGsP, ⟨hcvGs, hfrG⟩, hF10⟩ := ConRon.Bridge.Inductives.classRecTysOk_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv _ _ bs.k bs.recs pP.recs cvRis cvRisP rdv.recCls hwRis a2 _ _
    hCP.check ⟨hgPd, hrecs2, hcv2⟩ hrun3
  -- the rule-less recursors' environment
  have henvR : ∀ f : Nat → Nat, ConLeche.EnvWF (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, f x.2)) env) := by
    obtain ⟨F10, hF10'⟩ := id hF10
    rw [ConLeche.classRecTysOk_datF] at hF10'
    obtain ⟨hlenG, hallG⟩ := ConLeche.classRecTysOk_run hF10'
    intro f
    refine ConLeche.Cached.envWF_consBlockRecsBare henv fun c hc => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.of_mem_zip hx).1
    have hil : i < pP.recs.length := by
      rw [← hlenG]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨c, cvG, -, hcvG, ⟨R⟩⟩ := hallG i _ (List.getElem?_eq_getElem hil)
    rw [hi] at hcvG
    obtain rfl := Option.some.inj hcvG
    exact ConLeche.classConstOk_typeWF R.hcv
  refine ⟨⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩,
    AM.res (ConRon.Arena.classRecTysOk V fe ⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ bs.k bs.recs
      cvRis rdv.recCls) a2, _, fun {β} k => ?_, hC3, hgP.trans hg3, hG.grow (decCG_mono _) hg3, hns, rfl, ?_, hA3, hP3,
    c19.trans c10, _, cvGsP, ConRon.Bridge.Inductives.dClassGen_ext c10.ext _ _ hgPd, hcvGs, hfrG, henvR⟩
  · simp only [grcTwinC, StateT.run_bind, hrun2, except_ok_bind, hrun3]
  · simpa [decCVS] using hd3

include hkp henv hApd hCrk hIlpf in
/-- **`gen_rec_check_prep`'s second part under `StageC`** (`grpBW_ok`'s): the classes' entries
and constructors, the count, the formers, the level, then the third part (`grpCW_okC`). -/
theorem grpBW_okC (P : GrcProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL tO tL rd mO mL cO cL cRo cRl : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {cvRis : List IConstantVal}
    {r : List Word} {m' : Mem}
    (h : grpBW p n m vis pp pO pL tO tL rd mO mL cO cL cRo cRl = some (r, m'))
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
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        (grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
          grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k)).run a = (k G cvGs).run a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ DecB (fun m => decCG m (r.headD 0).toNat) m' G ∧
      G.nP + G.slots.length < 2 ^ 64 ∧ G.slots = rdv.slots ∧ decCVS m' r.tail cvGs ∧ AbsOK m' ∧
      RcMR m' ∧ ConRon.Bridge.CoreStep V env fe a a' ∧
      ∃ (gP : ConLeche.ClassGen) (cvGsP : List ConLeche.ConstantVal), dClassGen a'.store G = some gP ∧
        cvGs.mapM (Frontend.denoteCV a'.store) = some cvGsP ∧ (∀ c ∈ cvGsP, env.find? c.name = none) ∧
        ∀ f : Nat → Nat, ConLeche.EnvWF (ConLeche.consBlockRecsBare pP 0
          ((cvGsP.zip rdv.recCls).map fun x => (x.1, f x.2)) env) := by
  have hS := hC.stage
  have hT64 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
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
  unfold grpBW at h
  -- the formers' types
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [grpB1_some] at h
  obtain ⟨s1, hs1, -, hS1, hg1, hf1, hft1, hftb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (genRecCheckFormerTys_refines P.ia P.gft n _ a cO cL cvTas hS hcv) c1
  simp only at hs1 hS1 hg1 hf1 hft1 hftb1; subst hs1
  have hP1 := hP.fr hf1
  have hk1 := callW_keepW c1
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c1 hA
  have hC1 : StageC dn vis fe env s1.mem a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  -- `classes_nfs`
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
  rw [grpB2_some] at h
  obtain ⟨s2, hs2, -, hok2, hms2, hC2, hg2, hP2, hA2, hlp2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classesNfs_refinesLpC hkp henv P.cns n hn _ a dn fe vis pp _ _ tO tL mO mL bs (cvTas.map (·.type)) tbl ms
      hC1 hA1 (hbs.grow hg1) hft1 hftb1 (htbl.grow (fun q => decNCN_mono q) hg1)
      (hms.grow (fun q => decTM_mono q) hg1) hP1 (hlp.grow hms hg1 hk1 hsz) hsh hftP htblP hmsP hformer hMsT) c2
  simp only at hs2 hms2 hC2 hg2 hP2 hA2 hlp2; subst hs2
  have hk2 := callW_keepW c2
  have hrun2 := AM.run_of_ok _ a hok2
  obtain ⟨c4, Ms2P, ⟨hms2P, hMs2⟩, -⟩ := ConRon.Bridge.Inductives.classesNfs_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs pP _ _ tbl tblP hformer ms MsP hMsT a _ _ hC1.check
    ⟨hsh, hftP, htblP, hmsP⟩ hrun2
  generalize AM.res (ConRon.Arena.classesNfs V fe bs (cvTas.map (·.type)) tbl ms) a = ms2 at hrun2 hms2 hms2P
  generalize AM.st (ConRon.Arena.classesNfs V fe bs (cvTas.map (·.type)) tbl ms) a = a2 at hrun2 hC2 hms2P c4
  have hS2 := hC2.stage
  have hg12 := hg1.trans hg2
  -- `classes_ctors`
  have hsz2 : (s2.mem.arr64 IW).size = (m.arr64 IW).size := by rw [hk2 IW, hk1 IW]
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext c4.ext _ _ hsh
  have hftP2 := ConRon.Bridge.denoteEList_ext c4.ext _ _ hftP
  have hrdP2 := ConRon.Bridge.Inductives.dClassRead_ext c4.ext _ _ hrdP
  obtain ⟨⟨r3, m3⟩, c3, h⟩ := of_K h rfl
  rw [grpB3_some] at h
  obtain ⟨s3, hs3, -, hok3, hC3, hg3, hsp3, hP3, hA3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classesCtors_refinesC hkp henv P.ccs hIlpf P.opf n hn _ a2 dn fe vis pp _ _ rd _ _ bs (cvTas.map (·.type)) rdv ms2 hC2 hA2
      (hbs.grow hg12) (by rw [decHL_grow3 hg2 hftb1]; exact hft1) (Nat.le_trans hftb1 hg2.1)
      (hrd.grow (decCR_mono _) hg12) hms2.1 (hS2.lt64 hms2.2) (hlp2 hk2) hnpk (by rw [hsz2]; exact hsz5) hP2
      hsh2 hftP2 hrdP2 hms2P hformer hMs2) c3
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
  -- the count
  have er0 : rdW (s3.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := partsRdIW_grow hg13 (by omega)
  have er1 : rdW (s3.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [er0, er1] at h
  obtain ⟨⟨r4, m4⟩, c4', h⟩ := of_K h rfl
  obtain ⟨s4, rfl, -, hm4, hmo⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (genRecCheckMinorOk_refines P.csm P.gmo n _ _ _ _ _ rdv.slots ctors
      ((hslD.grow (OMono.decPL decCS_mono _ _) hg13).get (OMono.decPL decCS_mono _ _)) hslb
      (hctD.get (OMono.decPL decCC_lh_mono _ _)) (hS3.lt64 hsp3.2.1) hS3.2.2.2.1) c4'
  have h0 : ¬ (r4.headD 0 = 0) := fun h0 => by rw [grpB4_bad (h := h0)] at h; cases h
  rw [grpB4_ok (h := h0), hm4] at h
  have hcount : ((rdv.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum) = true := by
    rw [← hmo]; simpa using h0
  -- the classes' formers
  obtain ⟨⟨r5, m5⟩, c5', h⟩ := of_K h rfl
  rw [grpB5_some] at h
  have hms3P := ConRon.Bridge.Inductives.dMajor_ext.list c5.ext _ _ hms2P
  have hcv3P := ConRon.Bridge.Inductives.dExt_denoteCV.list (c4.trans c5).ext _ _ hcvTP
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
      ⟨hC3, hA3, ConRon.Arena.Ext.refl _⟩) c5'
  simp only at hs5 hS5 hg5 hftc5 hftcb5 hJ5; subst hs5
  have hP5 := RcMR.ofClosed hclR (hfRc _ (by decide)) c5' hP3
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
  -- the elimination level
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, -, -, helimD, -, hlarge, -⟩ := decBS_some hbsD
  obtain ⟨hel5, hel5'⟩ := installIwH (i := 5) helimD hsz
  have hL := installIwB (k := 7) hlarge hsz
  have ew5 : rdW (s5.mem.arr64 IW) (pp + 5) = rdW (m.arr64 IW) (pp + UInt64.ofNat 5) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  have ew7 : rdW (s5.mem.arr64 IW) (pp + 7) = rdW (m.arr64 IW) (pp + UInt64.ofNat 7) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  rw [ew5, ew7] at h
  obtain ⟨⟨r6, m6⟩, c6', h⟩ := of_K h rfl
  rw [grpB6_some] at h
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
    simp only [dClassGen, e1, e2, e3, e4, e5, helim, Frontend.denoteEList, hnPe, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  -- part C
  obtain ⟨G, cvGs, a', hrunC, hC', hg', hG', hns', hsl', hcg', hA', hR', cC, hrest⟩ := grpCW_okC hkp henv hApd hCrk P n hn h
    hC6 (hbs.grow hg16)
    (hrb.grow hg16 (by omega)) (decHL_grow' hg16 hparb hpar) (Nat.le_trans hparb hg16.1)
    (hrd.grow (decCR_mono _) hg16) (hms2.grow (fun q => decTM_mono q) (hg3.trans (hg5.trans hg6)))
    (hctD.grow (OMono.decPL decCC_lh_mono _ _) (hg5.trans hg6))
    (decHL_grow' hg6 hftcb5 hftc5) (Nat.le_trans hftcb5 hg6.1) hel6 rfl
    (hcvR.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg16) hns hA6
    (ConRon.Bridge.Inductives.dShape_ext c18.ext _ _ hsh) hg0
    (ConRon.Bridge.Inductives.dExt_denoteCV.list c18.ext _ _ hcvRP) hwRis hclR hfRc hP6
  refine ⟨G, cvGs, a', fun {β} k => ?_, hC', hg16.trans hg', hG', hns', hsl', hcg', hA', hR', c18.trans cC, hrest⟩
  rw [← hrunC k]
  simp only [grcTwinB, StateT.run_bind, hrun2, except_ok_bind, hrun3, hcount, hrun5, hrun6, ite_true]

end parts

end L.Ind
