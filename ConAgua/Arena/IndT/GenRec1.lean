import ConAgua.Arena.IndT.KeepC
import ConAgua.Arena.IndT.StreamRecs
import ConAgua.Arena.IndT.RecGen28
import ConAgua.Arena.RecCheckSpec.TargetRecPins
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.IndInstallSpec.GpbWSimF
import ConAgua.Arena.IndInstallSpec.Icvg
import ConAgua.Arena.IndInstallSpec.PosFreeMfr

/-!
# `genRecCheck` under `StageC`, part 1 (lane `indstaget`, helper `grc`)

`gen_rec_check_prep`'s first part (`grpAW_ok`'s, `IndInstallSpec/GpbWSimF`) under `StageC`; twin side
con-ron's `genRecCheck_spec`'s proof: `targetRecPins` (`targetRecPins_spec`, a `PSpecP`),
`classStreamRecs` (`classStreamRecs_refinesC`, con-ron's `classStreamRecs_spec` on its run),
`blockLargeElimAllowed` (`blockLargeElimAllowed_simC`, `IndRealBle`). Also:
`StageC.of_checkE` (`StageC` at another view and environment, from con-ron's `CheckOK` there) and
`classesNfs_refinesLpC` (`classes_nfs` under `StageC` with the classes' constructors'
level-parameter slices, `classesNfs_refinesLp`'s).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`StageC` at another view and environment**: the stage relation there, `CheckOK` there, the
memory's half from `AbsOK` and the store's extension. -/
theorem StageC.of_checkE {dn : NIdx → Option ConLeche.Name} {vis vis' : Word} {fe fe' : IFEnv}
    {env env' : ConLeche.Env} {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis' fe' m' a') (hA : AbsOK m') (hck : ConRon.Bridge.CheckOK V env' fe' a')
    (hx : ConRon.Arena.Ext a.store a'.store) : StageC dn vis' fe' env' m' a' :=
  ⟨hS, hck,
    ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, ⟨hA.2.2.2.1, hA.1, hA.2.2.2.2.1⟩,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.2.2.2.2.2.2.2.2⟩

/-- **`classes_nfs` refines `classesNfs` under `StageC`**, with the classes' constructor records'
level-parameter slices (`ClassesLp`) carried to the result (`classesNfs_refinesLp`'s). -/
theorem classesNfs_refinesLpC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem)
    (hlp : ClassesLp s₀.mem mo ml)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor} (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP) (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀ ∧
      PSlR decTM (AM.res (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem ∧
      (KeepW s₀.mem s'.mem → ClassesLp s'.mem (r.headD 0) (r.tail.headD 0)); ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (cnfs_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  rw [cnfsW_eq] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl
  rw [cnfsK1_some] at hm
  obtain ⟨mF, c1, hm⟩ := of_K hm rfl
  rw [cnfsK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, rfl, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hC.stage
  have hA0 := allocW_afr hw0 hA
  obtain ⟨rest, a', run, hSF, hgF, htF, hPF, hAF, ws', hws', hacc'⟩ := cnsW_okC hkp henv P dn fe vis q fto ftl
    tblo tbll mo ml (r0.headD 0) bs formerTys tbl ms s₀.mem hq0 hms htbl hbs hft hftb hformer (n + 1)
    (by omega) s0.mem mF a₀ 0 [] [] MsP c1 (hC.of_pstep hS0 hA0 (PStep.refl hC.check.state)) hA0 hg0
    (by omega) (hP.fr (allocW_mfr hw0)) UInt64.zero_le (by simp [decNL]) FA2.nil hsh hftP htblP
    (by simpa using hmsP) hMs
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hacc'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, ?_, by rw [hst]; exact hSF, hgF, hPF, hAF, fun hk => ?_⟩
  · rw [hres]
    refine ⟨?_, by simpa using htF⟩
    show decPL (truncM mF) (decTM (truncM mF)) _ _ = some rest
    simp only [List.headD_cons, List.tail_cons]
    rw [decPL_eq_bind, show decNL (truncM mF) (r0.headD 0).toNat ml.toNat = some ws' from decNL_decB hws' htF]
    exact cnsRec_mapM hgF hacc'
  · simp only [List.headD_cons, List.tail_cons]
    exact classesLp_of_cnsRec hlp hgF hk hC.stage.2.2.2.1 hws' hacc'

section partA
variable {p : Prog} (hq : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hApd hCrk in
/-- **`gen_rec_check_prep`'s first part under `StageC`** (`grpAW_ok`'s): the capacity guards, the
pins, the stream's recursor types (checked), the family and elimination guards; twin side
con-ron's `genRecCheck_spec`'s first steps. -/
theorem grpAW_okC (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp nested rd mO mL bO bL : Word} {bs : BlockShape}
    {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo} {r : List Word} {m' : Mem}
    (h : grpAW p n m vis pp nested rd mO mL bO bL = some (r, m'))
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    {pP : ConLeche.BlockShape} {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP) :
    ((m.arr64 IW).size + 5 < 2 ^ 64 ∧ bs.nP + bs.k < 2 ^ 64 ∧ bs.nP + rdv.slots.length < 2 ^ 64) ∧
    ∃ cvRis a', (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ KeepW m m' ∧ CsRes m' r cvRis ∧
      AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a' ∧
      ∃ cvRisP : List ConLeche.ConstantVal, cvRis.mapM (Frontend.denoteCV a'.store) = some cvRisP ∧
        ∀ cv ∈ cvRisP, ConLeche.Expr.WScoped 0 cv.type := by
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hp8 := hbs.ptop
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, hrecs, -, -, -, hlarge, -⟩ := decBS_some hbsD
  have hrecsP0 := (ConRon.Bridge.Inductives.dShape_inv hsh).2.1
  unfold grpAW at h
  -- the capacity guards
  obtain ⟨g1, h⟩ := of_ite_none h
  obtain ⟨g2, h⟩ := of_ite_none h
  obtain ⟨g3, h⟩ := of_ite_none h
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
  refine ⟨hcap, ?_⟩
  -- `target_rec_pins`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [grpK1_some] at h
  obtain ⟨s1, hs1, -, hok1, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetRecPins_refines p P.rp n _ a dn vis fe pp bO bL bs block hS hbs.1 hblk)
    (callW_mono c1 (Nat.le_add_right n 3))
  simp only at hs1 hS1 hg1; subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize AM.st (ConRon.Arena.targetRecPins bs block) a = a1 at hrun1 hS1
  have hP1 := RcMR.ofClosed hclR (hfR _ (by decide)) c1 hP
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c1 hA
  have hk1 := callW_keepW c1
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.targetRecPins_spec bs pP block blockP a a1 _
    hC.check.state hC.check.pins ⟨hsh, hblkP⟩ hrun1
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  have c1' := p1.toCore hC.check
  -- `class_stream_recs`
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m :=
    bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hw2 : rdW (s1.mem.arr64 IW) (pp + 2) = rdW (m.arr64 IW) (pp + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have hw3 : rdW (s1.mem.arr64 IW) (pp + 3) = rdW (m.arr64 IW) (pp + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [hw2, hw3] at h
  have hrecs1 := hrecsP.grow (fun q => decRS_mono q) hg1
  have hrecs1P := ConRon.Bridge.Inductives.dRec_ext.list c1'.ext _ _ hrecsP0
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
  obtain ⟨s2, hs2, -, hok2, hC2, hg2, hcs2, hA2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classStreamRecs_refinesC hq henv hV hApd hCrk P.cpy P.ia P.slc P.csr n hn _ a1 fe vis _ _ bs.recs pP.recs hC1
      hA1 (rec3RecsOK_of_decB hrecs1.1 hrecs1.2) hrecs1P) c2
  simp only at hs2 hC2 hg2 hcs2 hA2; subst hs2
  have hrun2 := AM.run_of_ok _ a1 hok2
  obtain ⟨c2', cvRisP, ⟨hcvRis, hwRis⟩, -⟩ := ConRon.Bridge.Inductives.classStreamRecs_spec fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.recs pP.recs a1 _ _ hC1.check hrecs1P hrun2
  generalize AM.res (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = cvRis at hrun2 hcs2 hcvRis
  generalize AM.st (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = a2 at hrun2 hC2 hcvRis c2'
  have hS2 := hC2.stage
  have c12 := c1'.trans c2'
  have hP2 := RcMR.ofClosed hclR (hfR _ (by decide)) c2 hP1
  have hk2 := callW_keepW c2
  have hg12 := hg1.trans hg2
  -- the family guard
  have hk : rdW (s2.mem.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact partsShapeK (hbs.dec) (by omega)
  by_cases hk0 : rdW (s2.mem.arr64 IW) (pp + 1) = 0
  · rw [grpK2_fam (h := hk0)] at h; cases h
  have hkb : (bs.k == 0) = false := by
    cases e : bs.k with
    | zero => rw [e] at hk; exact absurd hk hk0
    | succ _ => rfl
  -- the elimination guard
  have hL : (rdW (s2.mem.arr64 IW) (pp + 7) != 0) = bs.large := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact installIwB (k := 7) hlarge hsz
  obtain ⟨a4, hC4, hrun, hc4, hcv4, h⟩ : ∃ a4, StageC dn vis fe env s2.mem a4 ∧
      (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a4) ∧
      ConRon.Bridge.CoreStep V env fe a a4 ∧ cvRis.mapM (Frontend.denoteCV a4.store) = some cvRisP ∧
      some ([r2.headD 0, r2.tail.headD 0], s2.mem) = some (r, m') := by
    by_cases h7 : rdW (s2.mem.arr64 IW) (pp + 7) = 0
    · rw [grpK2_small (h1 := hk0) (h := h7)] at h
      have hl : bs.large = false := by rw [← hL, h7]; rfl
      refine ⟨a2, hC2, fun k => ?_, c12, hcvRis, h⟩
      simp only [grcTwinA, StateT.run_bind, hrun1, except_ok_bind, hrun2, hkb, hl, Bool.false_eq_true, ite_false]
    have hl : bs.large = true := by rw [← hL]; simpa using h7
    have hmsD : decPL s2.mem (decTM s2.mem) mO.toNat mL.toNat = some ms :=
      (hms.1.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg12).get (OMono.decPL (fun q => decTM_mono q) _ _)
    have hmsb : mO.toNat + mL.toNat < 2 ^ 64 := hS.lt64 hms.2
    have hsh2 := ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh
    have hsrc2 : ShapeSrc s2.mem pp := partsHsrc_grow hg12 (partsShapeFacts hbs.1 hbs.2.1).2.1 hbs.2.1
    obtain ⟨w, hw, h⟩ : ∃ w : Word, (w != 0) = ((nested != 0) || ms.any (·.member.isNone)) ∧
        grpK4 (fun m => some ([r2.headD 0, r2.tail.headD 0], m))
          (callW p n "block_large_elim_allowed" [pp, w] s2.mem) = some (r, m') := by
      by_cases hn0 : nested = 0
      · rw [grpK2_any (h1 := hk0) (h := h7) (hn := hn0)] at h
        obtain ⟨⟨r3, m3⟩, c3, h⟩ := of_K h rfl
        obtain ⟨s3, rfl, -, hm3, hany, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
          (genRecCheckAnyNoMember_refines p P.anm n _ mO mL ms hmsD hmsb hS2.2.2.2.1) c3
        rw [grpK3_some, hm3] at h
        exact ⟨_, by rw [hany, hn0]; rfl, h⟩
      · rw [grpK2_nested (h1 := hk0) (h := h7) (hn := hn0)] at h
        exact ⟨nested, by rw [show (nested != 0) = true by simpa using hn0]; rfl, h⟩
    obtain ⟨⟨r4, m4⟩, c4, h⟩ := of_K h rfl
    obtain ⟨al, a4, hr4, hC4, hm4, hd4, p4, -⟩ := blockLargeElimAllowed_simC P.ble n hC2 hA2
      (hbs.1.grow (decBS_mono _) hg12) hsrc2 hsh2 r4 m4 c4
    subst hm4
    have c3' := p4.toCore hC2.check
    have h0 : ¬ (r4.headD 0 = 0) := fun h0 => by rw [grpK4_bad (h := h0)] at h; cases h
    rw [grpK4_ok (h := h0)] at h
    have hal : al = true := by rw [← hd4.1]; simpa using h0
    refine ⟨a4, hC4, fun k => ?_, c12.trans c3', ConRon.Bridge.Inductives.dExt_denoteCV.list c3'.ext _ _ hcvRis, h⟩
    rw [hw] at hr4; subst hal
    simp only [grcTwinA, StateT.run_bind, hrun1, except_ok_bind, hrun2, hkb, hl, hr4, Bool.false_eq_true,
      ite_false, ite_true]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨ptrs, h1, h2, h3, h4⟩ := hcs2
  exact ⟨cvRis, a4, hrun, hC4, hg12, hP2, hk1.trans hk2, ⟨ptrs, h1, h2, h3, h4⟩, hA2, hc4, cvRisP, hcv4, hwRis⟩

end partA

end L.Ind
