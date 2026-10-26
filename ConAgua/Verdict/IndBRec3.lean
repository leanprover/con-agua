import ConAgua.Verdict.IndBRec2

/-!
# Error refinement of `class_rec_tys_ok` (lane `verdicts-b`, helper `ib`)
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dRec dMajor dExt_denoteCV dClassGen_ext
  dClassGen_inv dRec_inv ROp RE mapM_option_cons_inv dRec_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model classRecTysOkE_spec (p : Prog) (hf : p.lookup "class_rec_tys_ok" = some classRecTysOkL)
  fns [hf ↦ classRecTysOkE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hApd hCrk hnv hcE henv in
/-- **`class_rec_tys_ok`'s model error claim** (`rtsW_simC`'s hypotheses; the recursion is the
model's own, so the induction hypothesis is about the model). -/
theorem rtsE_claim (hp : RtsProg p) (g k : Word) (G : ClassGen) (hns : G.nP + G.slots.length < 2 ^ 64)
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
    ∀ e, classRecTysOkE p n m vis g k ro rl vo vl co cl = .error e →
      ErrClaim (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a e := by
  induction n with
  | zero =>
    intro m a ro rl vo vl co cl rcs cvs cs rcsP cvsP hC hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw e he
    rw [classRecTysOkE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ro rl vo vl co cl rcs cvs cs rcsP cvsP hC hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hsz := hC.stage.2.2.2.1
  have htop := hC.stage.2.1
  by_cases hrl : rl = 0
  · rw [classRecTysOkE.arm1 p n m vis g k ro rl vo vl co cl hrl] at he
    cases he
  by_cases hsh : vl = 0 ∨ cl = 0
  · rw [classRecTysOkE.abort1 p n m vis g k ro rl vo vl co cl hrl hsh] at he
    cases he
    exact ErrClaim.of_cls0 rfl
  rw [classRecTysOkE.arm2 p n m vis g k ro rl vo vl co cl hrl hsh] at he
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
  rw [ep, ev, ec] at he
  have hokj := hok.2.2 0 (by omega)
  obtain ⟨p0, q, cv, hp0, -, hq', -, hext, -⟩ := hokj
  rw [Nat.add_zero, hpm] at hp0; cases hp0
  have hcvR : ∀ q', iwN m pr = some q' → CVExt m q' := fun q' h' => by
    rw [hq'] at h'; cases h'; exact hext
  have hro1 := rec2ToNat_succ (o := ro) (i := ro.toNat) (Nat.le_refl _) (by omega)
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _) (by omega)
  have hrl1 := rec2ToNat_pred hrl
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  unfold ConRon.Arena.classRecTysOk
  cases h1 : callE p n "class_rec_ty_ok" [vis, g, k, UInt64.ofNat pr, UInt64.ofNat pv, UInt64.ofNat c0] m with
  | error e1 =>
    rw [h1, classRecTysOkE.k_class_rec_ty_ok.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have hcl := CoreSpecE.of_callE (classRecTyOk_claim hq hApd hCrk hnv hcE henv hp.toRtoProg n (by omega)
      ⟨m, Locals.init []⟩ a g k (UInt64.ofNat pr) (UInt64.ofNat pv)
      (UInt64.ofNat c0) G RS CV hC hG hns (by rw [tp]; exact hRS) (by rw [tp]; exact hcvR)
      (by rw [tv]; exact hCV) hA hgP hrcP hcvP (hw _ List.mem_cons_self)) h1
    rw [tc] at hcl
    exact hcl
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, classRecTysOkE.k_class_rec_ty_ok.arm1] at he
  obtain ⟨s1, hs1, -, hmodel⟩ := triple_of_callW
    (classRecTyOk_spec p hp.toRtoProg (realCall p) (realCall_spec p) n ⟨m, Locals.init []⟩ vis g k
      (UInt64.ofNat pr) (UInt64.ofNat pv) (UInt64.ofNat c0)) (callW_of_callE h1)
  subst hs1
  obtain ⟨x, a1, hrun1, ⟨⟨hC1, hg1, hx⟩, hA1⟩⟩ :=
    (rtoW_simC hq hApd hCrk henv n (by omega) m a g k (UInt64.ofNat pr) (UInt64.ofNat pv)
      (UInt64.ofNat c0) G RS CV hC hG hns (by rw [tp]; exact hRS) (by rw [tp]; exact hcvR)
      (by rw [tv]; exact hCV) hA hgP hrcP hcvP (hw _ List.mem_cons_self)) (r1, s1.mem) hmodel
  dsimp only at hC1 hg1 hx hA1
  rw [tc] at hrun1
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.classRecTyOk_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv G gP k.toNat RS rcP CV cvP c0 (hw _ List.mem_cons_self) a a1 x hC.check ⟨hgP, hrcP, hcvP⟩
    hrun1
  refine ErrClaim.bind_right hrun1 ?_
  have hok' := RecsOK_tail (by rw [← hjr]; simpa using hok)
  have hsub : ∀ e', classRecTysOkE p n s1.mem vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1)
      = .error e' → ErrClaim (ConRon.Arena.classRecTysOk V fe G k.toNat rcs' cvs' cs') a1 e' := fun e' h' =>
    ih (by omega) s1.mem a1 _ _ _ _ _ _ rcs' cvs' cs' rcsP' cvsP' hC1
      (hG.grow (decCG_mono _) hg1)
      (by rw [hro1, hrl1, hjr]; exact (show DecB (fun m => decPL m (decRS m) (ro.toNat + 1) jr) m rcs' from
        hrcsT).grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1)
      (by rw [hro1, hrl1, hjr]; exact RecsOK_grow hg1 (by simpa using hok'))
      (by rw [hvo1, hvl1, hjv]; exact (show DecB (fun m => decPL m (decCVp m) (vo.toNat + 1) jv) m cvs' from
        hcvsT).grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg1)
      (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
        hcsT).grow (OMono.decNL _ _) hg1) hA1
      (dClassGen_ext c1.ext _ _ hgP) (dRec_ext.list c1.ext _ _ hrcsP')
      (dExt_denoteCV.list c1.ext _ _ hcvsP') (fun cv h => hw cv (List.mem_cons_of_mem _ h)) e' h'
  cases h2 : classRecTysOkE p n s1.mem vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1) with
  | error e2 =>
    rw [h2, classRecTysOkE.k_class_rec_tys_ok.none] at he
    cases he
    exact ErrClaim.bind_left (hsub _ h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, classRecTysOkE.k_class_rec_tys_ok.arm1] at he
  cases h3 : callE p n "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
  | error e3 =>
    rw [h3, classRecTysOkE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, classRecTysOkE.k_sl_cons.arm1] at he
  cases he

include hq hApd hCrk hnv hcE henv in
/-- **`class_rec_tys_ok`'s error claim** (the hypotheses of `classRecTysOk_refinesC`, and the core
stubs' error claims). -/
theorem classRecTysOk_claim (hp : RtsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
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
    CoreSpecE p n "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
      (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classRecTysOkE_spec p hp.rts n ⟨s₀.mem, Locals.init []⟩ vis g k ro rl vo vl co cl)
    hc' (Err.code_ne_of_cls hk0)
  exact rtsE_claim hq hApd hCrk hnv hcE henv hp g k G hns gP n hn s₀.mem a₀ ro rl vo vl co cl rcs cvs cs _ _
    hC hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw er hW

end sims

end L.Ind
