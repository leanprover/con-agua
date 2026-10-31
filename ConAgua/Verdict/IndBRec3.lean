module

public import ConAgua.Verdict.IndBRec2
public import ConAgua.Arena.RecGenSpec.ClassRecTysOk
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.ModelGen
public import ConRon.Bridge.Inductives.GenRec

@[expose] public section
/-!
# `class_rec_tys_ok`: one model and one refinement for both outcomes

`classRecTysOkE` (`l_model … unified`: `class_rec_ty_ok` through its unified model, `sl_cons`
lifted) and `rts_ref` under `StageC`, from the inputs' denotations con-ron's `classRecTysOk_spec`
asks: each recursor's `rto_ref`, the extension after it from con-ron's `classRecTyOk_spec`, then the
list's `cons`. Its ok half is `classRecTysOk_refinesC`, its error half `classRecTysOk_claim`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dRec dMajor dExt_denoteCV dClassGen_ext
  dClassGen_inv dRec_inv ROp RE mapM_option_cons_inv dRec_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model classRecTysOkE_spec (p : Prog) (hp : RtsProg p)
  fns [hp.rts ↦ classRecTysOkE]
  specs [classRecTyOkE_spec p hp.toRtoProg n, slCons_specW p hp.alloc hp.copy hp.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_rec_tys_ok` gives besides the twin's checked constants `xs` (from `m`): the stage
invariant under `StageC`, the growth, the result a slice of constant records, the abstraction
memo. -/
structure RtsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (m' : Mem) (xs : List IConstantVal) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  dec : decCVS m' r xs
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hApd hCrk henv in
/-- **`class_rec_tys_ok` refines `classRecTysOk`, both outcomes** under `StageC` (twin side:
con-ron's `classRecTysOk_spec`'s proof; the extension after one recursor from con-ron's
`classRecTyOk_spec` on its run). -/
theorem rts_ref (g k : Word) (G : ClassGen) (hns : G.nP + G.slots.length < 2 ^ 64)
    (gP : ConLeche.ClassGen) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (ro rl vo vl co cl : Word) (rcs : List RecShape)
      (cvs : List IConstantVal) (cs : List Nat) (rcsP : List ConLeche.RecShape)
      (cvsP : List ConLeche.ConstantVal), StageC dn vis fe env m a →
    DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m rcs →
    RecsOK m ro.toNat rl.toNat (rcs.map (·.cvR)) →
    DecB (fun m => decPL m (decCVp m) vo.toNat vl.toNat) m cvs →
    DecB (fun m => decNL m co.toNat cl.toNat) m cs → AbsOK m →
    dClassGen a.store G = some gP → rcs.mapM (dRec a.store) = some rcsP →
    cvs.mapM (Frontend.denoteCV a.store) = some cvsP →
    (∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) →
    RefE (VerdictCtxU p) (classRecTysOkE p n m vis g k ro rl vo vl co cl)
      (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a
      (fun v xs a' => RtsPost dn vis fe env m v.1 v.2 xs a') := by
  induction n with
  | zero => intros; rw [classRecTysOkE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ro rl vo vl co cl rcs cvs cs rcsP cvsP hC hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw
  have hsz := hC.stage.iw.iwSize
  have htop := hC.stage.iw.iw
  by_cases hrl : rl = 0
  · rw [classRecTysOkE.arm1 p n m vis g k ro rl vo vl co cl hrl]
    have : rcs = [] := by
      have := decPL_length _ (hrcs.get (OMono.decPL (fun q => decRS_mono q) _ _))
      rw [hrl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecTysOk
    exact RefE.ret rfl ⟨hC, IWGrow.refl m,
      by simpa [decCVS] using SPL.nil (dec := decCVX) (m := m) 0 (by omega), hA⟩
  refine RefE.ofArms (fun h => classRecTysOkE.abort1 (hc1 := hrl) (hc2 := h) ..)
    (fun h => classRecTysOkE.arm2 (hc1 := hrl) (hc2 := h) ..) (RefE.abort0 rfl fun hsh => ?_)
  have hvl : vl ≠ 0 := fun e => hsh (.inl e)
  have hcl : cl ≠ 0 := fun e => hsh (.inr e)
  have hl0 : ∀ w : Word, w ≠ 0 → ∃ j, w.toNat = j + 1 := fun w hw =>
    ⟨w.toNat - 1, by
      have : w.toNat ≠ 0 := fun e => hw (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨jr, hjr⟩ := hl0 rl hrl
  obtain ⟨jv, hjv⟩ := hl0 vl hvl
  obtain ⟨jc, hjc⟩ := hl0 cl hcl
  have hrcs' : decPL (truncM m) (decRS (truncM m)) ro.toNat (jr + 1) = some rcs := by
    rw [← hjr]; exact hrcs
  obtain ⟨pr, RS, rcs', rfl, hpp, hRS, hrcsT⟩ := decPL_cons hrcs'
  have hcvs' : decPL (truncM m) (decCVp (truncM m)) vo.toNat (jv + 1) = some cvs := by
    rw [← hjv]; exact hcvs
  obtain ⟨pv, CV, cvs', rfl, hpv, hCV, hcvsT⟩ := decPL_cons hcvs'
  have hcs' : decNL (truncM m) co.toNat (jc + 1) = some cs := by rw [← hjc]; exact hcs
  rw [decNL_succ] at hcs'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcs'
  obtain ⟨c0, hc0, cs', hcsT, rfl⟩ := hcs'
  obtain ⟨rcP, rcsP', rfl, hrcP, hrcsP'⟩ := mapM_option_cons_inv hrcsP
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := mapM_option_cons_inv hcvsP
  obtain ⟨hpt, hpm⟩ := rec2IwN_trunc hpp
  obtain ⟨hpvt, hpvm⟩ := rec2IwN_trunc hpv
  obtain ⟨hc0t, hc0m⟩ := rec2IwN_trunc hc0
  obtain ⟨ep, tp⟩ := rec2RdN (w := ro) (k := 0) (by simpa using hpm) hsz
  obtain ⟨ev, tv⟩ := rec2RdN (w := vo) (k := 0) (by simpa using hpvm) hsz
  obtain ⟨ec, tc⟩ := rec2RdN (w := co) (k := 0) (by simpa using hc0m) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ep ev ec
  rw [ep, ev, ec]
  obtain ⟨p0, q, cv, hp0, -, hq', -, hext, -⟩ := hok.2.2 0 (by omega)
  rw [Nat.add_zero, hpm] at hp0; cases hp0
  have hcvR : ∀ q', iwN m pr = some q' → CVExt m q' := fun q' h' => by
    rw [hq'] at h'; cases h'; exact hext
  unfold ConRon.Arena.classRecTysOk
  -- `class_rec_ty_ok`
  have hr := rto_ref (k := k) (c := UInt64.ofNat c0) hq hApd hCrk henv n (by omega) hC hG hns
    (by rw [tp]; exact hRS) (by rw [tp]; exact hcvR) (by rw [tv]; exact hCV) hA hgP hrcP hcvP
    (hw _ List.mem_cons_self)
  rw [tc] at hr
  refine RefE.bindE (fun _ => classRecTysOkE.k_class_rec_ty_ok.none ..) id hr
    fun ⟨r1, m1⟩ x a1 hrun1 ⟨hC1, hg1, hx, hA1⟩ => ?_
  dsimp only at hC1 hg1 hx hA1
  rw [classRecTysOkE.k_class_rec_ty_ok.arm1]
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.classRecTyOk_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv G gP k.toNat RS rcP CV cvP c0 (hw _ List.mem_cons_self) a a1 x hC.check ⟨hgP, hrcP, hcvP⟩
    hrun1
  -- the rest
  have hro1 := rec2ToNat_succ (o := ro) (i := ro.toNat) (Nat.le_refl _) (by omega)
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _) (by omega)
  have hrl1 := rec2ToNat_pred hrl
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  have hok' := RecsOK_tail (by rw [← hjr]; simpa using hok)
  have ih' := ih (by omega) m1 a1 (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1) rcs' cvs' cs' rcsP' cvsP' hC1
    (hG.grow (decCG_mono _) hg1)
    (by rw [hro1, hrl1, hjr]; exact (show DecB (fun m => decPL m (decRS m) (ro.toNat + 1) jr) m rcs' from
      hrcsT).grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1)
    (by rw [hro1, hrl1, hjr]; exact RecsOK_grow hg1 (by simpa using hok'))
    (by rw [hvo1, hvl1, hjv]; exact (show DecB (fun m => decPL m (decCVp m) (vo.toNat + 1) jv) m cvs' from
      hcvsT).grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg1)
    (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
      hcsT).grow (OMono.decNL _ _) hg1) hA1
    (dClassGen_ext c1.ext _ _ hgP) (dRec_ext.list c1.ext _ _ hrcsP')
    (dExt_denoteCV.list c1.ext _ _ hcvsP') (fun cv h => hw cv (List.mem_cons_of_mem _ h))
  refine RefE.bindE (fun _ => classRecTysOkE.k_class_rec_tys_ok.none ..) id ih'
    fun ⟨r2, m2⟩ xs a2 _ hR2 => ?_
  rw [classRecTysOkE.k_class_rec_tys_ok.arm1]
  -- `sl_cons`
  refine RefE.onlySim (fun _ => classRecTysOkE.k_sl_cons.none ..) (fun _ _ h => h) fun r3 m3 h3 => ?_
  rw [classRecTysOkE.k_sl_cons.arm1]
  have hy : StabD (fun m => decCVX m r1.toNat) m1 x := decCVX_stab hx.1 hx.2
  obtain ⟨hS3, hg3, hsp3⟩ := SPL.cons h3 hR2.stage.stage hR2.dec (hy.grow hR2.grow)
  have hA3 := consW_afr h3 hR2.abs
  exact RefE.ret rfl ⟨hR2.stage.of_pstep hS3 hA3 (PStep.refl hR2.stage.check.state),
    hg1.trans (hR2.grow.trans hg3), by simpa [decCVS] using hsp3, hA3⟩

include hq hApd hCrk henv in
/-- **`class_rec_tys_ok` refines `classRecTysOk`** under `StageC` (`rts_ref`'s ok half). -/
@[refines ConRon.Arena.classRecTysOk]
theorem classRecTysOk_refinesC (hp : RtsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (g k ro rl vo vl co cl : Word) (G : ClassGen) (rcs : List RecShape)
    (cvs : List IConstantVal) (cs : List Nat) (hC : StageC dn vis fe env s₀.mem a₀)
    (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrcs : DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) s₀.mem rcs)
    (hok : RecsOK s₀.mem ro.toNat rl.toNat (rcs.map (·.cvR)))
    (hcvs : DecB (fun m => decPL m (decCVp m) vo.toNat vl.toNat) s₀.mem cvs)
    (hcs : DecB (fun m => decNL m co.toNat cl.toNat) s₀.mem cs) (hA : AbsOK s₀.mem)
    {gP : ConLeche.ClassGen} {rcsP : List ConLeche.RecShape} {cvsP : List ConLeche.ConstantVal}
    (hgP : dClassGen a₀.store G = some gP) (hrcsP : rcs.mapM (dRec a₀.store) = some rcsP)
    (hcvsP : cvs.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hw : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀ ∧
      KPC dn vis fe env s₀.mem decCVS (r, s'.mem)
        (AM.st (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀)
        (AM.res (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (classRecTysOkE_spec p hp n s₀ vis g k ro rl vo vl co cl)
    (rts_ref hq hApd hCrk henv g k G hns gP n hn _ a₀ ro rl vo vl co cl rcs cvs cs rcsP cvsP hC hG
      hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, ⟨by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.dec⟩, hR.abs⟩

include hq hApd hCrk hnv hcE hU henv in
/-- **`class_rec_tys_ok`'s error claim** (the hypotheses of `classRecTysOk_refinesC`, and the core
stubs' error claims; `rts_ref`'s error half). -/
theorem classRecTysOk_claim (hp : RtsProg p) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (g k ro rl vo vl co cl : Word) (G : ClassGen) (rcs : List RecShape)
    (cvs : List IConstantVal) (cs : List Nat) (hC : StageC dn vis fe env s₀.mem a₀)
    (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrcs : DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) s₀.mem rcs)
    (hok : RecsOK s₀.mem ro.toNat rl.toNat (rcs.map (·.cvR)))
    (hcvs : DecB (fun m => decPL m (decCVp m) vo.toNat vl.toNat) s₀.mem cvs)
    (hcs : DecB (fun m => decNL m co.toNat cl.toNat) s₀.mem cs) (hA : AbsOK s₀.mem)
    {gP : ConLeche.ClassGen} {rcsP : List ConLeche.RecShape} {cvsP : List ConLeche.ConstantVal}
    (hgP : dClassGen a₀.store G = some gP) (hrcsP : rcs.mapM (dRec a₀.store) = some rcsP)
    (hcvsP : cvs.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hw : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) :
    CoreSpecE p n "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
      (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) s₀ a₀ :=
  RefE.coreSpecE (classRecTysOkE_spec p hp n s₀ vis g k ro rl vo vl co cl) hnv
    { nv := hnv, core := hcE, uce := hU }
    (rts_ref hq hApd hCrk henv g k G hns gP n hn _ a₀ ro rl vo vl co cl rcs cvs cs rcsP cvsP hC hG
      hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw)

end sims

end L.Ind

end
