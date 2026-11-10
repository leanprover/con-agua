module

public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndT.Sum4
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndSumSpec.SumRules
import ConAgua.Arena.RefWalk
import all ConAgua.Arena.IndSum
import ConAgua.L.WordOff

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

l_model sctsE_spec (p : Prog) (hP : SumProg p) (hV : CcvProg p)
  fns [hP.hcs ↦ sctsE]
  specs [ctorE_spec p hP hV n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_sum_ctors` gives (from `m`, `a`): the stage invariant, the growth, `AbsOK`, the
twin's core step. -/
structure SctsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctors` refines `checkSumCtors`, both outcomes** (at one environment, `vis0 = vis`,
as `check_block_ctors` calls it; twin side: con-ron's `checkSumCtors_spec`'s proof): the head by
`ctor_ref` (`check_sum_ctor` by its unified model), the rest by induction on the fuel. -/
@[refines ConRon.Arena.checkSumCtors]
theorem scts_ref (hP : SumProg p) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn)
    (T lo ll nP nIdx rs isP lg cvTaw : Word) (lps : List NIdx) (cvTa : IConstantVal)
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
    ConRon.Bridge.Inductives.IFEnvOKS env₀ fe a.store →
    RefE (VerdictCtxU p) (sctsE p k m vis vis T lo ll nP nIdx rs isP lg cvTaw cO cL)
      (checkSumCtors V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a
      (fun v _ a' => SctsPost dn vis fe env m a v.2 a') := by
  induction k with
  | zero => intros; rw [sctsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀
  have hS := hC.stage
  have hcl := decPL_length (m := truncM m) hcs
  by_cases hl : cL = 0
  · rw [sctsE.arm1 p k m vis vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl]
    have : cs = [] := by subst hl; cases cs with | nil => rfl | cons _ _ => simp at hcl
    subst this
    simp only [checkSumCtors]
    exact RefE.ret rfl ⟨hC, IWGrow.refl _, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hov1 : nP + nIdx < nP
  · rw [sctsE.abort1 p k m vis vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1]
    exact RefE.of_cls0 rfl
  have hni : nP.toNat + nIdx.toNat < 2 ^ 64 := by rw [← _root_.L.toNat_add_of_not_lt hov1]; exact UInt64.toNat_lt _
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
  · rw [sctsE.abort2 p k m vis vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1 hov2]
    exact RefE.of_cls0 rfl
  rw [sctsE.arm2 p k m vis vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1 hov2]
  rw [hw, hw3] at hov2
  rw [hw, hw2, hw3]
  have hcvB : DecB (fun m => decCVp m w2.toNat) m cv := by
    show decCVp (truncM m) w2.toNat = some cv; rw [hw2v]; exact hcv
  have hnf : nP.toNat + w3.toNat < 2 ^ 64 := by rw [← _root_.L.toNat_add_of_not_lt hov2]; exact UInt64.toNat_lt _
  subst hw3v
  simp only [checkSumCtors]
  -- the head constructor (by its unified model)
  rcases k with _ | j
  · rw [ctorE.eq_1, sctsE.k_check_sum_ctor.none]; exact RefE.of_cls0 Err.cls_outOfFuel
  refine RefE.bindE (fun _ => sctsE.k_check_sum_ctor.none ..) id
    (ctor_ref hq henv hOpf hLC hLT hApd hCrk hP hV hcr hCS j (by omega) m a T lo ll nP nIdx rs isP lg
      w2 w3 cvTaw lps cv cvTa hC hT hlps hlb hcvB hta hrs hni hnf hA hTP hlpsP hrsP hcvP hcvTaP hws)
    fun ⟨r, m1⟩ _ a1 _ hR1 => ?_
  rw [sctsE.k_check_sum_ctor.arm1]
  have hC1 := hR1.stage
  have hg1 := hR1.grow
  have hA1 := hR1.abs
  have c1 := hR1.core
  dsimp only at hC1 hg1 hA1
  have x1 := c1.ext
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by omega)
  have hcL1 : (cL - 1).toNat = L := by rw [_root_.L.toNat_sub_one_of_ne hl]; omega
  -- the rest, in tail position
  exact RefE.lastE (fun _ => sctsE.k_check_sum_ctors.none ..) (fun _ => sctsE.k_check_sum_ctors.arm1 ..) id
    (ih (by omega) m1 a1 (cO + 1) (cL - 1) cs restP hC1 (by rw [decHL_grow hg1 hlb]; exact hlps)
      (by have := hg1.iw; omega) (DecB.grow (OMono.decCVp _) hg1 hta)
      (by rw [hcO1, hcL1]; exact DecB.grow (OMono.decPL decCN_mono _ _) hg1 htail) hA1
      (ConRon.Bridge.denoteN_ext hTP x1) (ConRon.Bridge.denoteNListE_ext x1 _ _ hlpsP)
      (ConRon.Bridge.denoteL_ext hrsP x1) (ConRon.Bridge.denoteCV_ext hcvTaP x1)
      (ConRon.Bridge.Inductives.denoteCtors_ext x1 _ _ hrestP) (hok₀.mono x1))
    fun _ _ _ _ hR4 => ⟨hR4.stage, hg1.trans hR4.grow, hR4.abs, c1.trans hR4.core⟩

include hq henv hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctors` refines `checkSumCtors`, both outcomes, through the call** (`scts_ref` read
through the run; the shape of `IndT/Install7.lean`'s contract `SctsRefS`). -/
theorem scts_refC (hP : SumProg p) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn)
    (n : Nat) (hn : n ≤ 2 ^ 62) {env₀ : ConLeche.Env} (m : Mem) (a : AState)
    (T lo ll nP nIdx rs isP lg cvq cO cL : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (cs : List (IConstantVal × Nat)) (TP : ConLeche.Name) (lpsP : List ConLeche.Name)
    (rsP : ConLeche.Level) (cvTaP : ConLeche.ConstantVal) (csP : List (ConLeche.ConstantVal × Nat))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hT : H T) (hrs : H rs)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hta : DecB (fun m => decCVp m cvq.toNat) m cvTa)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs)
    (hTP : denoteN a.store.ns (decI T) = some TP) (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP) (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP)
    (hfv : cvTaP.type.hasFvar = false) (hcsP : ConRon.Bridge.Inductives.denoteCtors a.store cs = some csP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ fe a.store) :
    RefE (VerdictCtxU p) (callE p n "check_sum_ctors" [vis, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvq, cO, cL] m)
      (checkSumCtors V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a
      (fun rm _ a' => StageC dn vis fe env rm.2 a' ∧ IWGrow m rm.2 ∧ AbsOK rm.2 ∧
        ConRon.Bridge.CoreStep env fe a a') := by
  have hM := scts_ref hq henv hOpf hLC hLT hApd hCrk hP hV hcr hCS T lo ll nP nIdx rs isP lg cvq lps cvTa
    hT hrs (ConLeche.Expr.WScoped.of_not_hasFvar hfv) n hn m a cO cL cs csP hC hlps hlb hta hcs hA hTP
    hlpsP hrsP hcvTaP hcsP hok₀
  have hs := sctsE_spec p hP hV n ⟨m, Locals.init []⟩ vis vis T lo ll nP nIdx rs isP lg cvq cO cL
  rcases c : callE p n "check_sum_ctors" [vis, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvq, cO, cL] m
    with e | ⟨r, m'⟩
  · exact fun hG => RefE.run_err hs hG.nv hG hM c
  · obtain ⟨s', rfl, -, y, a', hr, hR⟩ := RefE.run_ok hs hM c
    exact ⟨y, a', hr, hR.stage, hR.grow, hR.abs, hR.core⟩

end sims

end L.Ind
