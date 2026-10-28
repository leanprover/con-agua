import ConAgua.Verdict.IndBRec2
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecGenSpec.ClassRecTysOk
import ConRon.Bridge.Inductives.GenRec

/-!
# `classRecTysOk` under `StageC` (lane `indstaget`)

`class_rec_tys_ok`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`classRecTysOk_spec` asks: each recursor's `class_rec_ty_ok` read through its run (`rtoR`; its ok
half `rto_ref`'s, `IndBRec2.lean`), the extension after it from con-ron's `classRecTyOk_spec`, then
the list's `cons`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dRec dMajor dExt_denoteCV dClassGen_ext
  dClassGen_inv dRec_inv ROp RE mapM_option_cons_inv dRec_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hApd hCrk henv in
/-- **`class_rec_tys_ok` under `StageC`** (twin side: con-ron's `classRecTysOk_spec`'s proof; the
extension after one recursor from con-ron's `classRecTyOk_spec` on its run). -/
theorem rtsW_simC (hrp : RtoProg p) (g k : Word) (G : ClassGen) (hns : G.nP + G.slots.length < 2 ^ 64)
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
  have hr : RSim (rtoR (realCall p) n m vis g k (UInt64.ofNat pr) (UInt64.ofNat pv) (UInt64.ofNat c0))
      (ConRon.Arena.classRecTyOk V fe G k.toNat RS CV (UInt64.ofNat c0).toNat) a
      (fun b a' x => (KPC dn vis fe env m decCVR b a' x ∧ AbsOK b.2) ∧
        (ConRon.Arena.classRecTyOk V fe G k.toNat RS CV (UInt64.ofNat c0).toNat).run a = .ok (x, a')) :=
    fun ⟨r1, m1⟩ hb => by
      obtain ⟨s1, rfl, -, x, a1, run1, hR⟩ := RefE.run_okW
        (classRecTyOkE_spec p hrp n ⟨m, Locals.init []⟩ vis g k _ _ _)
        (rto_ref hq hApd hCrk henv n (by omega) hC hG hns (by rw [tp]; exact hRS) (by rw [tp]; exact hcvR)
          (by rw [tv]; exact hCV) hA hgP hrcP hcvP (hw _ List.mem_cons_self)) hb
      exact ⟨x, a1, run1, ⟨⟨hR.stage, hR.grow, hR.dec⟩, hR.abs⟩, run1⟩
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
      let h := (rtsW_simC hq hApd hCrk henv hp.toRtoProg g k G hns gP n hn _ a₀ ro rl vo vl co cl rcs cvs cs rcsP cvsP hC
        hG hrcs hok hcvs hcs hA hgP hrcsP hcvsP hw).am hw'
      ⟨hl, h.1, h.2.1, h.2.2⟩

end sims

end L.Ind
