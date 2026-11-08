module

public import ConAgua.Arena.IndSumSpec.CtorX
import ConAgua.Arena.IndSumSpec.SoaW
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndT.Sum4
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndSumSpec.SumRules
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndSum

@[expose] public section
/-!
# `check_sum_ctors`: one model and one refinement for both outcomes

`sctsE` (`l_model … unified`): `check_sum_ctor` by its unified model, the `rec2`s and the
`sl_cons` (outside the verdict closure) lifted. `scts_ref` refines `checkSumCtors` under `VerdictCtxU`
(`ctor_ref`'s: the no-verdict closure, the core stubs' claims, `unresolved_consts_error`'s program);
`checkSumCtors_refinesC` is its ok half.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model sctsE_spec (p : Prog) (hP : SumProg p) (hV : ValProg p)
  fns [hP.hcs ↦ sctsE]
  specs [ctorE_spec p hP hV n, rec2_specW p hP.ha n hP.hrec2, slCons_specW p hP.ha hP.hc hP.hsc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/-- What `check_sum_ctors` gives besides the twin's constructors and sorts `x` (from `m`): the
stage invariant, the growth, the two slices `r = [cO, cL, sO, sL]` decoded below the top,
`AbsOK`, the twin's step. -/
structure SctsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (m' : Mem)
    (x : List (IConstantVal × Nat) × List (List LIdx)) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  cns : DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' x.1
  cnsB : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
  sorts : DecB (fun m => decPL m (sortsDec m) (r.tail.tail.headD 0).toNat
    (r.tail.tail.tail.headD 0).toNat) m' x.2
  sortsB : (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hq henv hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctors` refines `checkSumCtors`, both outcomes** (twin side: con-ron's
`checkSumCtors_spec`'s proof): the head by `ctor_ref` (`check_sum_ctor` by its unified model), the
records and the conses (outside the verdict closure) claim nothing, the rest by induction. -/
theorem scts_ref (hP : SumProg p)
    (vis0 T lo ll nP nIdx rs isP lg cvTaw : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (hT : H T) (hrs : H rs) {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {rsP : ConLeche.Level} {cvTaP : ConLeche.ConstantVal} (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (cO cL : Word) (cs : List (IConstantVal × Nat))
      (csP : List (ConLeche.ConstantVal × Nat)),
    StageC dn vis fe env m a → decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    DecB (fun m => decCVp m cvTaw.toNat) m cvTa →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs → AbsOK m →
    denoteN a.store.ns (decI T) = some TP → Frontend.denoteNList a.store.ns lps = some lpsP →
    denoteL a.store.ls (decI rs) = some rsP → Frontend.denoteCV a.store cvTa = some cvTaP →
    ConRon.Bridge.Inductives.denoteCtors a.store cs = some csP →
    ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    RefE (VerdictCtxU p) (sctsE p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL)
      (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a
      (fun v x a' => SctsPost dn vis fe env m a v.1 v.2 x a') := by
  induction k with
  | zero => intros; rw [sctsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀ hfe
  have hS := hC.stage
  have hcl := decPL_length (m := truncM m) hcs
  by_cases hl : cL = 0
  · rw [sctsE.arm1 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl]
    have : cs = [] := by subst hl; cases cs with | nil => rfl | cons _ _ => simp at hcl
    subst this
    simp only [checkSumCtors]
    exact RefE.ret rfl ⟨hC, IWGrow.refl _, by simp [DecB, decPL], by simp, by simp [DecB, decPL], by simp, hA,
      ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hov1 : nP + nIdx < nP
  · rw [sctsE.abort1 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1]
    exact RefE.of_cls0 rfl
  have hni : nP.toNat + nIdx.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov1]; exact UInt64.toNat_lt _
  obtain ⟨L, hL⟩ : ∃ L, cL.toNat = L + 1 :=
    ⟨cL.toNat - 1, by have : cL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decPL (truncM m) (decCN (truncM m)) cO.toNat (L + 1) = some cs := by
    have := hcs; simp only [DecB, hL] at this; exact this
  cases cs with
  | nil => simp at hcl; omega
  | cons c cs =>
  obtain ⟨cv, nF⟩ := c
  simp only [ConRon.Bridge.Inductives.denoteCtors] at hcsP
  cases hcvP : Frontend.denoteCV a.store cv with
  | none => rw [hcvP] at hcsP; simp at hcsP
  | some cP =>
  cases hrestP : ConRon.Bridge.Inductives.denoteCtors a.store cs with
  | none => rw [hcvP, hrestP] at hcsP; simp at hcsP
  | some restP =>
  obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
  have htail := decPL_tail hcs'
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
  obtain ⟨w, hw, hwv, hcO⟩ := rdW_of_iwN_truncM hpv
  have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
  obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
  have hT0 := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hw1 : (w + 1).toNat = pv + 1 := by rw [UInt64.toNat_add, hwv]; simp; omega
  have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  by_cases hov2 : nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP
  · rw [sctsE.abort2 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1 hov2]
    exact RefE.of_cls0 rfl
  rw [sctsE.arm2 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1 hov2]
  rw [hw, hw3] at hov2
  rw [hw, hw2, hw3]
  have hcvB : DecB (fun m => decCVp m w2.toNat) m cv := by
    show decCVp (truncM m) w2.toNat = some cv; rw [hw2v]; exact hcv
  have hnf : nP.toNat + w3.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov2]; exact UInt64.toNat_lt _
  subst hw3v
  simp only [checkSumCtors]
  -- the head constructor (by its unified model)
  rcases k with _ | j
  · rw [ctorE.eq_1, sctsE.k_check_sum_ctor.none]; exact RefE.of_cls0 Err.cls_outOfFuel
  refine RefE.bindE (fun _ => sctsE.k_check_sum_ctor.none ..) id
    (ctor_ref hq henv hOpf hLC hLT hApd hCrk hP j (by omega) m a vis0 T lo ll nP nIdx rs isP lg w2 w3 cvTaw
      lps cv cvTa hC hT hlps hlb hcvB hta hrs hni hnf hA hTP hlpsP hrsP hcvP hcvTaP hws hok₀ hfe)
    fun ⟨r, m1⟩ ⟨cvCa, sorts⟩ a1 _ hR1 => ?_
  rw [sctsE.k_check_sum_ctor.arm1]
  have hC1 := hR1.stage
  have hg1 := hR1.grow
  have hr0 := hR1.cvW
  have hx1 := hR1.cv
  have hsorts := hR1.sorts
  have hsb := hR1.sortsB
  have hA1 := hR1.abs
  have c1 := hR1.core
  dsimp only at hC1 hg1 hr0 hx1 hsorts hsb hA1
  have hS1 := hC1.stage
  subst hx1
  -- the two `rec2`s (L only)
  refine RefE.onlySim (fun _ => sctsE.k_rec2.none ..) (fun _ _ h => h) fun rn m2 hn => ?_
  rw [sctsE.k_rec2.arm1]
  obtain ⟨hS2, hg2, hn0, hn1⟩ := sumRec2 hn hS1
  have hA2 : AbsOK m2 := recW_afr hn hA1
  have hC2 : StageC dn vis fe env m2 a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  refine RefE.onlySim (fun _ => sctsE.k_rec2_2.none ..) (fun _ _ h => h) fun rh m3 hh => ?_
  rw [sctsE.k_rec2_2.arm1]
  obtain ⟨hS3, hg3, hh0, hh1⟩ := sumRec2 hh hS2
  have hA3 : AbsOK m3 := recW_afr hh hA2
  have hC3 : StageC dn vis fe env m3 a1 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have x1 := c1.ext
  have hg03 := (hg1.trans hg2).trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by omega)
  have hcL1 : (cL - 1).toNat = L := by rw [sumToNat_pred hl]; omega
  -- the rest
  refine RefE.bindE (fun _ => sctsE.k_check_sum_ctors.none ..) id (ih (by omega) m3 a1 (cO + 1) (cL - 1) cs restP hC3 (by rw [decHL_grow hg03 hlb]; exact hlps)
    (by have := hg03.iw; omega) (DecB.grow (OMono.decCVp _) hg03 hta)
    (by rw [hcO1, hcL1]; exact DecB.grow (OMono.decPL decCN_mono _ _) hg03 htail) hA3
    (ConRon.Bridge.denoteN_ext hTP x1) (ConRon.Bridge.denoteNListE_ext x1 _ _ hlpsP)
    (ConRon.Bridge.denoteL_ext hrsP x1) (ConRon.Bridge.denoteCV_ext hcvTaP x1)
    (ConRon.Bridge.Inductives.denoteCtors_ext x1 _ _ hrestP) (hok₀.mono x1)
    (ConRon.Bridge.denoteFEnv_mono x1 hfe)) fun ⟨rr, m4⟩ ⟨rest, srest⟩ a4 _ hR4 => ?_
  dsimp only at hR4
  rw [sctsE.k_check_sum_ctors.arm1]
  have hS4 := hR4.stage.stage
  obtain ⟨ps1, hps1t, hps1, hmap1⟩ := sumDecNL_of_decB hR4.cns
  -- the two `sl_cons` (L only)
  refine RefE.onlySim (fun _ => sctsE.k_sl_cons.none ..) (fun _ _ h => h) fun r1 m5 hc1 => ?_
  rw [sctsE.k_sl_cons.arm1]
  obtain ⟨hS5, hg5, hd5, ht5⟩ := consW_stageN hc1 hS4 hR4.cnsB hps1
  obtain ⟨ps2, hps2t, hps2, hmap2⟩ := sumDecNL_of_decB hR4.sorts
  have hb2' : (rr.tail.tail.headD 0).toNat + (rr.tail.tail.tail.headD 0).toNat ≤ iwTop m5 := by
    have := hg5.iw; have := hR4.sortsB; omega
  refine RefE.onlySim (fun _ => sctsE.k_sl_cons_2.none ..) (fun _ _ h => h) fun r2 m6 hc2 => ?_
  rw [sctsE.k_sl_cons_2.arm1]
  obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stageN hc2 hS5 hb2'
    ((OMono.decNL _ _).mono _ _ _ (IWGrow.truncExt hg5) hps2t)
  -- the head's records, decoded at the end
  have hy1 : DecB (fun m => decCN m (rn.headD 0).toNat) m5 (cvCa, w3.toNat) := by
    have h0 : DecB (fun m => decCN m (rn.headD 0).toNat) m2 (cvCa, w3.toNat) := by
      refine sumDecCN_of hn0 hn1 ?_
      rw [hr0]; exact DecB.grow (OMono.decCVp _) (hg1.trans hg2) hcvB
    exact DecB.grow (decCN_mono _) ((hg3.trans hR4.grow).trans hg5) h0
  have hy2 : DecB (fun m => sortsDec m (rh.headD 0).toNat) m6 sorts := by
    have h0 : DecB (fun m => sortsDec m (rh.headD 0).toNat) m3 sorts :=
      sumSortsDec_of hh0 hh1 (by rw [decHL_grow (hg2.trans hg3) hsb]; exact hsorts)
        (by have := (hg2.trans hg3).iw; omega)
    exact DecB.grow (sortsDec_mono _) ((hR4.grow.trans hg5).trans hg6) h0
  have hg46 := hg5.trans hg6
  have hA6 := consW_afr hc2 (consW_afr hc1 hR4.abs)
  refine RefE.ret rfl ⟨hR4.stage.of_pstep hS6 hA6 (PStep.refl hR4.stage.check.state),
    (hg03.trans hR4.grow).trans hg46, ?_, ?_, ?_, ?_, hA6, c1.trans hR4.core⟩
  · simp only [List.headD_cons, List.tail_cons]
    exact DecB.grow (OMono.decPL decCN_mono _ _) hg6
      (sumDecB_cons decCN_mono hmap1 hd5 (by omega) hg5 hy1)
  · simp only [List.headD_cons, List.tail_cons]; have := hg6.iw; omega
  · simp only [List.headD_cons, List.tail_cons]
    exact sumDecB_cons sortsDec_mono hmap2 hd6 (by omega) hg46 hy2
  · simp only [List.headD_cons, List.tail_cons]; omega
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctors` refines `checkSumCtors .verified`** under `StageC` (the inputs'
denotations as con-ron's `checkSumCtors_spec` asks), the pre-block environment the restriction of
`fe` to `vis0`: the new constructor list and the sorts lists as fresh pointer slices decoded below
the tops. -/
@[refines ConRon.Arena.checkSumCtors]
theorem checkSumCtors_refinesC (hP : SumProg p) (k : Nat) (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (vis0 T lo ll nP nIdx rs isP lg cvTaw cO cL : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (cs : List (IConstantVal × Nat)) (hC : StageC dn vis fe env s₀.mem a₀) (hT : H T) (hrs : H rs)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) s₀.mem cvTa)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) s₀.mem cs) (hA : AbsOK s₀.mem)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvTaP : ConLeche.ConstantVal} {csP : List (ConLeche.ConstantVal × Nat)}
    (hTP : denoteN a₀.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    (hrsP : denoteL a₀.store.ls (decI rs) = some rsP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (hcsP : ConRon.Bridge.Inductives.denoteCtors a₀.store cs = some csP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a₀.store)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_ctors"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTaw, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps
        nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.tail.headD 0).toNat) s'.mem
        (AM.res (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat
          (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀).1 ∧
      DecB (fun m => decPL m (sortsDec m) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat)
        s'.mem (AM.res (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat
          nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀).2 ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (sctsE_spec p hP hV k s₀ vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL)
    (scts_ref hq henv hOpf hLC hLT hApd hCrk hP vis0 T lo ll nP nIdx rs isP lg cvTaw lps cvTa hT hrs hws k hk
      s₀.mem a₀ cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀ hfe))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ =>
      let ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      ⟨hl, hok, hst ▸ hR.stage, hR.grow, hres ▸ hR.cns, hres ▸ hR.sorts, hR.abs⟩
-/

end sims

end L.Ind
