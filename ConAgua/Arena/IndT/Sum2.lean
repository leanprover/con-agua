module

import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.SumInstall
import ConAgua.L.ModelGen
import ConAgua.Arena.IndSumSpec.DecCVpGrow
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndSum
import ConAgua.Arena.IndT.Lift
public import ConAgua.Arena.TwinStep
import ConAgua.L.WordOff

@[expose] public section

/-!
# `checkSumTele` under `StageC`, both outcomes (lane `indstaget`)

The unified model of `check_sum_tele` (`ctE`) and its refinement for both outcomes (`ct_ref`), from
`StageC` and the former's denotation: `strip_pis` (`stripF_pis_ok`; the twin state unchanged),
the residual's tag and sort (`viewSort`); every other arm is the twin's reject (no slow arm: the
former is put at its telescope earlier, `reduceMembers`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_sum_tele`'s model reads. -/
structure CtProg (p : Prog) : Prop where
  st : StripProg p
  view : p.lookup "e_view" = some eView
  cst : p.lookup "check_sum_tele" = some checkSumTeleL

set_option experimental.vcgen true in
/-- **The model of `check_sum_tele`, both outcomes**: `strip_pis` and `e_view` (outside the
verdict closure) through their `Option` models. -/
l_model ctE_spec (p : Prog) (hP : CtProg p)
  fns [hP.cst ↦ ctE]
  specs [stripPis_specF p hP.st n, eView_spec p hP.view n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- What `check_sum_tele` gives besides the twin's `(cvTa, s)`: the stage, the growth, the
constant value as a record, the sort as a word, the walk memos. -/
structure CtsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (w : List Word × Mem) (res : IConstantVal × LIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env w.2 a'
  grow : IWGrow m w.2
  cv : decCVp w.2 (w.1.headD 0).toNat = some res.1
  sort32 : (w.1.tail.headD 0).toNat < 2 ^ 32
  sort : decI (w.1.tail.headD 0) = res.2
  abs : AbsOK w.2

/-- **`check_sum_tele` refines `checkSumTele`, both outcomes**, under `StageC`: `strip_pis`
(`stripF_pis_ok`, con-ron's `stripPis_pstep`: the state unchanged), the residual's tag and its
sort (`viewSort`); every other arm is the twin's reject. Its callees are outside the verdict
closure, so `G` is `True`. -/
theorem ct_ref (m : Mem) (a : AState) (n cvTa0 : Word) (cvTa : IConstantVal)
    (hC : StageC dn vis fe env m a)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hA : AbsOK m)
    {cvTaP : ConLeche.ConstantVal} (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP) :
    RefE True (ctE p m n cvTa0) (checkSumTele n.toNat cvTa) a
      (fun w res a' => CtsPost dn vis fe env m w res a') := by
  have hS := hC.stage
  rw [ctE.arm1]
  obtain ⟨w, hw, hw32, hwd⟩ := (decCV_words hta).2.2
  have h3 : (cvTa0 + 3).toNat = cvTa0.toNat + 3 := by
    have := erecP_lt64 hw; rw [UInt64.toNat_add]; simp; omega
  have hw' : rdW (m.arr64 (tierA EREC ((cvTa0 + 3) >>> 40))) (cvTa0 + 3 &&& 1099511627775) = w :=
    erRd_of_erA (by rw [h3]; exact hw)
  rw [hw']
  have hdw : denoteE a.store (decI w) = some cvTaP.type := by
    rw [← hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  unfold checkSumTele
  rw [hwd]
  -- `strip_pis` (outside the verdict closure)
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec⟩ := stripF_pis_ok vis fe n w hw32 m m1 a r1 h1 hS
  obtain ⟨ha1, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hdw hrun1
  rw [ha1] at hrun1 hS1
  refine ⟨_, _, hrun1, ?_⟩
  have hA1 := stripF_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  have hta1 : decCVp m1 cvTa0.toNat = some cvTa := hg1.erecGrow.ext.decCV hta
  by_cases h0 : r1.headD 0 = 0
  · rw [ctE.k_strip_pis.abort1 _ _ _ _ h0]
    cases x with
    | none => exact fun _ => ErrClaim.fail _ _ rfl
    | some le =>
      obtain ⟨l, e⟩ := le
      simp only [decOLE] at hdec; rw [h0] at hdec; exact absurd hdec.1 (by decide)
  cases x with
  | none => simp only [decOLE] at hdec; exact absurd hdec h0
  | some le =>
  obtain ⟨l, e⟩ := le
  simp only [decOLE, decW0E] at hdec
  obtain ⟨-, -, hb32, hbe⟩ := hdec
  rw [L.drop_three] at hb32 hbe
  by_cases ht : tagW (r1.tail.tail.tail.headD 0) = 2
  · by_cases hne : eViewW m1 (r1.tail.tail.tail.headD 0) = []
    · rw [ctE.k_strip_pis.arm1 _ _ _ _ h0 ht hne]; exact RefE.of_cls0 (by simp)
    rw [ctE.k_strip_pis.arm2 _ _ _ _ h0 ht hne]
    obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a hS1.check.arena.base _ hne
    have h2 := eViewW_head2 m1 _ ht hne
    have htag : (decE (r1.tail.tail.tail.headD 0)).tag = ETag.sort :=
      (decE_tag_sort _ (by simpa using hb32)).mpr ht
    cases vv with
    | sort u =>
      obtain ⟨-, hu32, hu⟩ := hVR
      have hvs := viewSort_of_view _ _ _ htag hview
      have hx1 : (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0 =
          (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0 := by
        cases eViewW m1 (r1.tail.tail.tail.headD 0) with
        | nil => rfl
        | cons _ t => cases t <;> rfl
      simp only []
      rw [← hbe, ← decE_eq, htag]
      simp only [beq_self_eq_true, ite_true]
      refine RefE.bind_right (viewSort_run hvs) (RefE.ret rfl ⟨hC1, hg1, by simpa using hta1,
        by simpa [hx1] using hu32, by simpa [hx1] using hu, hA1⟩)
    | _ => simp only [ViewR] at hVR <;> (rw [h2] at hVR) <;> simp at hVR
  rw [ctE.k_strip_pis.abort2 _ _ _ _ h0 ht]
  have hnt : ¬ (e.tag == ETag.sort) = true := by
    rw [← hbe, ← decE_eq]
    intro ht'
    exact ht ((decE_tag_sort _ (by simpa using hb32)).mp (by simpa using ht'))
  simp only [hnt, Bool.false_eq_true, ite_false]
  exact fun _ => ErrClaim.fail _ _ rfl

/-- **`check_sum_tele` refines `checkSumTele`** under `StageC` (`ct_ref`'s ok half): the former
unchanged, its sort as a word. -/
@[refines ConRon.Arena.checkSumTele]
theorem checkSumTele_refinesC (hP : CtProg p) (k : Nat) (s₀ : St) (a₀ : AState)
    (n cvTa0 : Word) (cvTa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hA : AbsOK s₀.mem) {cvTaP : ConLeche.ConstantVal}
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele" [n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkSumTele n.toNat cvTa) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumTele n.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decCVp s'.mem (r.headD 0).toNat = some (AM.res (checkSumTele n.toNat cvTa) a₀).1 ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = (AM.res (checkSumTele n.toNat cvTa) a₀).2 ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (ctE_spec p hP k s₀ n cvTa0)
    (ct_ref _ a₀ n cvTa0 cvTa hC hta hA hcvTaP)) fun _ _ ⟨hl, _, _, hrun, hR⟩ => ?_
  obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst']; exact hR.stage, hR.grow, by rw [hres]; exact hR.cv, hR.sort32,
    by rw [hres]; exact hR.sort, hR.abs⟩

end sims

end L.Ind

end
