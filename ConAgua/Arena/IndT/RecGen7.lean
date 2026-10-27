import ConAgua.Arena.IndT.RecGen3
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecGenSpec.ClassRecTysOk

/-!
# `classRecTyOk`, `classRecTysOk` under `StageC` (lane `indstaget`)

`class_rec_ty_ok`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`classRecTyOk_spec` asks (`dClassGen`, `dRec`, the stream's checked constant), its twin side
transcribed from that spec's proof: `targetMajorAt` (`targetMajorAt_spec`), `classGenRecTy`
(`classGenRecTy_spec`, a core-free grower: `RSim.liftPP` of `gtW_sim`), the record write (twin
side none), `classConstOk` (`ccoW_simT` and con-ron's `classConstOk_spec`), `isDefEqCore`
(`isDefEqC_rsim`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dRec dMajor dExt_denoteCV dClassGen_ext
  dClassGen_inv dRec_inv ROp RE mapM_option_cons_inv dRec_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The usual `RSim` post under `StageC`. -/
def KPC {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (m : Mem) (dec : Mem → List Word → α → Prop) (b : List Word × Mem)
    (a' : AState) (x : α) : Prop :=
  StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ dec b.2 b.1 x

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hApd hCrk henv in
/-- **`class_const_ok` under `StageC`**: `ccoW_simT` and con-ron's `classConstOk_spec`. -/
theorem ccoW_simC (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (q : Word)
    (cv : IConstantVal) (hC : StageC dn vis fe env m a) (hq' : decCV (erecP m) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) (hA : AbsOK m) {cP : ConLeche.ConstantVal}
    (hcP : Frontend.denoteCV a.store cv = some cP) :
    RSim (ccoW (realCall p) n m vis q) (ConRon.Arena.classConstOk V fe cv) a
      (fun b a' x => (KPC dn vis fe env m decUnit b a' x ∧ AbsOK b.2) ∧
        ConLeche.Expr.WScoped 0 cP.type ∧ ConRon.Bridge.CoreStep V env fe a a') := by
  have h := RSim.liftC hC (Q := fun b _ _ => (IWGrow m b.2 ∧ True) ∧ AbsOK b.2)
    (RSim.mono (ccoW_simT hq hApd hCrk n hn m a q cv hC.stageT hq' hqb hA (denoteCV_lps hcP))
      fun _ _ _ _ ⟨⟨hT, hg, hd⟩, hA'⟩ => ⟨hT, ⟨hg, hd⟩, hA'⟩)
    (ConRon.Bridge.Inductives.classConstOk_spec fe (ConRon.Bridge.CoreSpec.of_core rfl) henv cv cP) hcP
  refine RSim.mono h fun _ _ _ _ hh => ?_
  obtain ⟨hC', ⟨⟨hg, hd⟩, hA'⟩, ⟨_, ⟨hw, -⟩, -⟩, hs⟩ := hh
  exact ⟨⟨⟨hC', hg, hd⟩, hA'⟩, hw, hs⟩

include hq hApd hCrk henv in
/-- **`class_rec_ty_ok` under `StageC`** (twin side: con-ron's `classRecTyOk_spec`'s proof). -/
theorem rtoW_simC (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (g k rc cvRi c : Word)
    (G : ClassGen) (RS : RecShape) (CVRi : IConstantVal) (hC : StageC dn vis fe env m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decRS m rc.toNat) m RS) (hcvR : ∀ q, iwN m rc.toNat = some q → CVExt m q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) m CVRi) (hA : AbsOK m)
    {gP : ConLeche.ClassGen} {rcP : ConLeche.RecShape} {cvRiP : ConLeche.ConstantVal}
    (hgP : dClassGen a.store G = some gP) (hrcP : dRec a.store RS = some rcP)
    (hRiP : Frontend.denoteCV a.store CVRi = some cvRiP) (hRi : ConLeche.Expr.WScoped 0 cvRiP.type) :
    RSim (rtoW (realCall p) n m vis g k rc cvRi c)
      (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a
      (fun b a' x => KPC dn vis fe env m decCVR b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [rtoW_eq]
  unfold ConRon.Arena.classRecTyOk
  rcases n with _ | n
  · exact RSim.none
  obtain ⟨-, -, hcls, -, -, -, -, -⟩ := dClassGen_inv hgP
  refine rgW_sim n m a g k rc c G RS hC.stage hG hns hrc hA
    (rtoK1 (realCall p) (n + 1) vis g rc cvRi c) rfl _ _ ?_
  intro m1 a1 tm hrun1 hS1 hg1 hA1
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.targetMajorAt_spec G.cls gP.cls c.toNat a a1 tm hC.check.state
    hC.check.pins hcls hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  rw [rtoK1_some]
  refine RSim.bind (K := rtoK2 (realCall p) (n + 1) vis rc cvRi) rfl
    (RSim.liftPP hC1 (gtW_sim dn vis fe (n + 1) m1 a1 g c G hS1 (hG.grow (decCG_mono _) hg1) hns hA1)
      (fun _ _ _ h => ⟨h.1.1, h.2⟩) (ConRon.Bridge.Inductives.classGenRecTy_spec G gP c.toNat)
      (dClassGen_ext p1.ext _ _ hgP)) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hC2, ⟨⟨hS2, hg2, ho⟩, hA2⟩, hR2, p2⟩
  dsimp only at hS2 hg2 ho hA2 hC2
  rcases o with _ | gty
  · rw [rtoK2_fail (h := ho)]; exact RSim.none
  obtain ⟨gtyP, -, hgtyd⟩ := hR2
  obtain ⟨h21, hgH, hgd⟩ := ho
  rw [rtoK2_ok (h := by rw [h21]; decide)]
  subst hgd
  have hg12 := hg1.trans hg2
  obtain ⟨q0, hq0, -⟩ := rec2DecRS_parts (show decRS (truncM m) rc.toNat = some RS from hrc)
  obtain ⟨hrct, hq0m⟩ := rec2IwN_trunc hq0
  have hq2 : iwN m2 rc.toNat = some q0 := by rw [iwN_grow hg12 hrct]; exact hq0m
  obtain ⟨q0', hq0', hcv2, -⟩ := rec2DecRS_parts (hrc.stab (decRS_mono _) m2 hg12)
  rw [hq2] at hq0'; cases hq0'
  have hext2 := CVExt_grow hg12 (hcvR q0 hq0m)
  obtain ⟨erc, trc⟩ := rec2RdN (w := rc) (k := 0) (by simpa using hq2) hS2.2.2.2.1
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at erc
  rw [erc]
  refine RSim.lstep (K := rtoK3 (realCall p) (n + 1) vis cvRi (r2.tail.headD 0)) rfl
    fun ⟨q, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hqe, htop3, hsl3, hdec3⟩ := cvNew_stage (cq := UInt64.ofNat q0) h3 hS2
    (by rw [trc]; exact hcv2) (by rw [trc]; exact hext2.1) (by rw [trc]; exact hext2.2) hgH
  rw [rtoK3_some]
  have hext3 : CVExt m3 q.toNat :=
    ⟨by omega, fun o l ho hl => (hsl3 o l ho hl).imp_left fun h => Nat.le_trans h hg3.2.1⟩
  have hqb : q.toNat + 3 < 2 ^ 64 := by
    obtain ⟨-, hE1, -, hEs, -⟩ := hS3.2
    omega
  have hA3 := cvNewW_afr h3 hA2
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have p12 := p1.trans p2
  obtain ⟨hnm, hlps, -⟩ :=
    ConRon.Bridge.Core.denoteCV_inv (dExt_denoteCV p12.ext _ _ (dRec_inv hrcP).1)
  have hcvG : Frontend.denoteCV a2.store { RS.cvR with type := decI (r2.tail.headD 0) } =
      some { rcP.cvR with type := gtyP } := by
    simp only [Frontend.denoteCV, hnm, hlps, hgtyd]
  refine RSim.bind (K := rtoK4 (realCall p) (n + 1) vis cvRi (r2.tail.headD 0) q) rfl
    (ccoW_simC hq hApd hCrk henv (n + 1) (by omega) m3 a2 q _ hC3 (rec2DecCV_erecP hdec3 hext3) hqb hA3
      hcvG) ?_
  rintro ⟨r4, m4⟩ u a4 - ⟨⟨⟨hC4, hg4, -⟩, hA4⟩, hwG, c4⟩
  dsimp only at hC4 hg4 hA4
  rw [rtoK4_some]
  have hg14 := hg12.trans (hg3.trans hg4)
  have hri := hcvRi.stab (OMono.decCVp _) m4 hg14
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hri
  have hEi := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE64 := hC4.stage.2.2.2.2.1
  have et : rdW (m4.arr64 EREC) (cvRi + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hEi ⊢; omega) hwt
  rw [et]
  have hdx : denoteE a4.store (decI wt) = some cvRiP.type := by
    rw [← hwtE]
    exact (ConRon.Bridge.Core.denoteCV_inv
      (dExt_denoteCV (p12.ext.trans c4.ext) _ _ hRiP)).2.2
  have hdy : denoteE a4.store (decI (r2.tail.headD 0)) = some gtyP :=
    ConRon.Bridge.denote_ext hgtyd c4.ext
  have hi := isDefEqC_rsim hq henv (n + 1) (by omega) hC4 hA4 0 wt (r2.tail.headD 0) hwtH hgH
    hdx hdy hRi hwG
  rw [show (0 : Word).toNat = 0 from rfl, ← hwtE] at hi
  refine RSim.bind (K := rtoK5 q) rfl hi ?_
  rintro ⟨r5, m5⟩ bb a5 - ⟨hC5, hg5, hbb, hA5, -⟩
  dsimp only at hC5 hg5 hbb hA5
  by_cases h50 : r5.headD 0 = 0
  · rw [rtoK5_fail (h := h50)]; exact RSim.none
  rw [rtoK5_ok (h := h50)]
  have hbt : bb = true := by rw [← hbb]; simpa [decBool] using h50
  subst hbt
  simp only [ite_true]
  have hg35 := hg4.trans hg5
  refine RSim.pure_some ⟨⟨hC5, hg14.trans hg5, ?_, CVExt_grow hg35 hext3⟩, hA5⟩
  show decCVp m5 q.toNat = _
  rw [decCVp_grow_r hg35 hext3, hdec3]

include hq hApd hCrk henv in
/-- **`class_rec_tys_ok` under `StageC`** (twin side: con-ron's `classRecTysOk_spec`'s proof; the
extension after one recursor from con-ron's `classRecTyOk_spec` on its run). -/
theorem rtsW_simC (g k : Word) (G : ClassGen) (hns : G.nP + G.slots.length < 2 ^ 64)
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
    RSim (rtsW (realCall p) n m vis g k ro rl vo vl co cl)
      (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a
      (fun b a' x => KPC dn vis fe env m decCVS b a' x ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [rtsW] at hb
  | succ n ih =>
  intro m a ro rl vo vl co cl rcs cvs cs rcsP cvsP hC hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw
  have hsz := hC.stage.2.2.2.1
  have htop := hC.stage.2.1
  by_cases hrl : rl = 0
  · rw [rtsW_nil (h := hrl)]
    have : rcs = [] := by
      have := decPL_length _ (hrcs.get (OMono.decPL (fun q => decRS_mono q) _ _))
      rw [hrl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecTysOk
    exact RSim.pure_some ⟨⟨hC, IWGrow.refl m,
      by simpa [decCVS] using SPL.nil (dec := decCVX) (m := m) 0 (by omega)⟩, hA⟩
  by_cases hsh : vl = 0 ∨ cl = 0
  · rw [rtsW_short (h := hrl) (h2 := hsh)]; exact RSim.none
  rw [rtsW_cons (h := hrl) (h2 := hsh)]
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
  obtain ⟨pr, RS, rcs', rfl, hp, hRS, hrcsT⟩ := decPL_cons hrcs'
  have hcvs' : decPL (truncM m) (decCVp (truncM m)) vo.toNat (jv + 1) = some cvs := by
    rw [← hjv]; exact hcvs
  obtain ⟨pv, CV, cvs', rfl, hpv, hCV, hcvsT⟩ := decPL_cons hcvs'
  have hcs' : decNL (truncM m) co.toNat (jc + 1) = some cs := by rw [← hjc]; exact hcs
  rw [decNL_succ] at hcs'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcs'
  obtain ⟨c0, hc0, cs', hcsT, rfl⟩ := hcs'
  obtain ⟨rcP, rcsP', rfl, hrcP, hrcsP'⟩ := mapM_option_cons_inv hrcsP
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := mapM_option_cons_inv hcvsP
  obtain ⟨hpt, hpm⟩ := rec2IwN_trunc hp
  obtain ⟨hpvt, hpvm⟩ := rec2IwN_trunc hpv
  obtain ⟨hc0t, hc0m⟩ := rec2IwN_trunc hc0
  obtain ⟨ep, tp⟩ := rec2RdN (w := ro) (k := 0) (by simpa using hpm) hsz
  obtain ⟨ev, tv⟩ := rec2RdN (w := vo) (k := 0) (by simpa using hpvm) hsz
  obtain ⟨ec, tc⟩ := rec2RdN (w := co) (k := 0) (by simpa using hc0m) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ep ev ec
  rw [ep, ev, ec]
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
  have hr := RSim.withRun (rtoW_simC hq hApd hCrk henv n (by omega) m a g k (UInt64.ofNat pr) (UInt64.ofNat pv)
    (UInt64.ofNat c0) G RS CV hC hG hns (by rw [tp]; exact hRS) (by rw [tp]; exact hcvR)
    (by rw [tv]; exact hCV) hA hgP hrcP hcvP (hw _ List.mem_cons_self))
  rw [tc] at hr
  refine RSim.bind (K := rtsK1 (realCall p) n vis g k ro rl vo vl co cl) (by simp [rtsK1]) hr ?_
  rintro ⟨r1, m1⟩ x a1 - ⟨⟨⟨hC1, hg1, hx⟩, hA1⟩, hrun1⟩
  dsimp only at hC1 hg1 hx hA1
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.classRecTyOk_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv G gP k.toNat RS rcP CV cvP c0 (hw _ List.mem_cons_self) a a1 x hC.check ⟨hgP, hrcP, hcvP⟩
    hrun1
  rw [rtsK1_some]
  have hok' := RecsOK_tail (by rw [← hjr]; simpa using hok)
  refine RSim.bind (K := rtsK2 n (r1.headD 0)) rfl (ih (by omega) m1 a1 _ _ _ _ _ _ rcs' cvs' cs'
    rcsP' cvsP' hC1
    (hG.grow (decCG_mono _) hg1)
    (by rw [hro1, hrl1, hjr]; exact (show DecB (fun m => decPL m (decRS m) (ro.toNat + 1) jr) m rcs' from
      hrcsT).grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1)
    (by rw [hro1, hrl1, hjr]; exact RecsOK_grow hg1 (by simpa using hok'))
    (by rw [hvo1, hvl1, hjv]; exact (show DecB (fun m => decPL m (decCVp m) (vo.toNat + 1) jv) m cvs' from
      hcvsT).grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg1)
    (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
      hcsT).grow (OMono.decNL _ _) hg1) hA1
    (dClassGen_ext c1.ext _ _ hgP) (dRec_ext.list c1.ext _ _ hrcsP')
    (dExt_denoteCV.list c1.ext _ _ hcvsP') (fun cv h => hw cv (List.mem_cons_of_mem _ h))) ?_
  rintro ⟨r2, m2⟩ xs a2 - ⟨⟨hC2, hg2, hxs⟩, hA2⟩
  dsimp only at hC2 hg2 hxs
  rw [rtsK2_some]
  refine RSim.lstep (K := rtsK3) rfl fun ⟨r3, m3⟩ h3 => ?_
  have hy : StabD (fun m => decCVX m (r1.headD 0).toNat) m1 x := decCVX_stab hx.1 hx.2
  obtain ⟨hS3, hg3, hsp3⟩ := SPL.cons h3 hC2.stage hxs (hy.grow hg2)
  rw [rtsK3_some]
  have hA3 := consW_afr h3 hA2
  exact RSim.pure_some ⟨⟨hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state),
    hg1.trans (hg2.trans hg3), by simpa [decCVS] using hsp3⟩, hA3⟩

include hq hApd hCrk henv in
/-- **`class_rec_ty_ok` refines `classRecTyOk`** under `StageC` (the knot's core calls; the inputs'
denotations as con-ron's `classRecTyOk_spec` asks). -/
@[refines ConRon.Arena.classRecTyOk]
theorem classRecTyOk_refinesC (hp : RtoProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (g k rc cvRi c : Word) (G : ClassGen) (RS : RecShape) (CVRi : IConstantVal)
    (hC : StageC dn vis fe env s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) s₀.mem RS)
    (hcvR : ∀ q, iwN s₀.mem rc.toNat = some q → CVExt s₀.mem q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) s₀.mem CVRi) (hA : AbsOK s₀.mem)
    {gP : ConLeche.ClassGen} {rcP : ConLeche.RecShape} {cvRiP : ConLeche.ConstantVal}
    (hgP : dClassGen a₀.store G = some gP) (hrcP : dRec a₀.store RS = some rcP)
    (hRiP : Frontend.denoteCV a₀.store CVRi = some cvRiP)
    (hRi : ConLeche.Expr.WScoped 0 cvRiP.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀ ∧
      KPC dn vis fe env s₀.mem decCVR (r, s'.mem)
        (AM.st (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀)
        (AM.res (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀) ∧
      AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRecTyOk_spec p hp (realCall p) (realCall_spec p) n s₀ vis g k rc cvRi c)
    fun _ _ ⟨hl, hw⟩ =>
      let h := (rtoW_simC hq hApd hCrk henv n hn _ a₀ g k rc cvRi c G RS CVRi hC hG hns hrc hcvR hcvRi hA
        hgP hrcP hRiP hRi).am hw
      ⟨hl, h.1, h.2.1, h.2.2⟩

include hq hApd hCrk henv in
/-- **`class_rec_tys_ok` refines `classRecTysOk`** under `StageC`. -/
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
        (AM.res (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRecTysOk_spec p hp (realCall p) (realCall_spec p) n s₀ vis g k ro rl vo vl co cl)
    fun _ _ ⟨hl, hw'⟩ =>
      let h := (rtsW_simC hq hApd hCrk henv g k G hns gP n hn _ a₀ ro rl vo vl co cl rcs cvs cs rcsP cvsP hC
        hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw).am hw'
      ⟨hl, h.1, h.2.1, h.2.2⟩

end sims

end L.Ind
