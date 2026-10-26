import ConAgua.Arena.IndT.Install7
import ConAgua.Verdict.IndE
import ConAgua.Verdict.DeclValE

/-!
# Error refinements of the direct sums' field sorts (lane `verdicts-b`, helper `ib`)

`check_struct_field_sorts_i_go` (the fields from the last, per field `fvar_type_d`,
`infer_type_core`, `ensure_sort_core`, `check_field_sort_bound`) and `check_struct_field_sorts_i`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model csfGoE_spec (p : Prog) (hf : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
  fns [hf ↦ csfGoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hLC hLT hnv hcE in
/-- **`check_struct_field_sorts_i_go`'s model error claim** (`csfW_okC`'s hypotheses; the recursion is
the model's own). -/
theorem csfE_claim (hg : p.lookup "sl_get" = some slGet)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
    (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (isProp large s nP fo fl io il res j : Word) (m0 : Mem) (k : Nat)
      (acc : List LIdx) (fvs idxArgs : List EIdx) (fvsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m → iwTop m0 ≤ res.toNat →
    res.toNat + j.toNat + k ≤ iwTop m →
    decHL m (res.toNat + j.toNat) k = some acc →
    decHL m0 fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m0 →
    decHL m0 io.toNat il.toNat = some idxArgs → io.toNat + il.toNat ≤ iwTop m0 →
    H s → (∃ sP, denoteL a.store.ls (decI s) = some sP) → nP.toNat + j.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP →
    (∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) →
    ∀ e, csfGoE p n m vis isProp large s nP fo fl io il res j = .error e →
      ErrClaim (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs j.toNat) a e := by
  induction n with
  | zero =>
    intro m a isProp large s nP fo fl io il res j m0 k acc fvs idxArgs fvsP hC hA hg0 hr0 hroom hacc
      hfvs hfb hidx hib hs hsP hnj hfP hws e he
    rw [csfGoE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a isProp large s nP fo fl io il res j m0 k acc fvs idxArgs fvsP hC hA hg0 hr0 hroom hacc
    hfvs hfb hidx hib hs hsP hnj hfP hws e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  by_cases hj : j = 0
  · rw [csfGoE.arm1 p n m vis isProp large s nP fo fl io il res j hj] at he
    cases he
  rw [csfGoE.arm2 p n m vis isProp large s nP fo fl io il res j hj] at he
  obtain ⟨J, hjJ⟩ : ∃ J, j.toNat = J + 1 :=
    ⟨j.toNat - 1, by have : j.toNat ≠ 0 := fun e => hj (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hJ : (j - 1).toNat = J := by rw [sumToNat_pred hj]; omega
  rw [hjJ, checkStructFieldSortsI_succ]
  cases h1 : callE p n "sl_get" [fo, fl, j - 1] m with
  | error e1 =>
    rw [h1, csfGoE.k_sl_get.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, csfGoE.k_sl_get.arm1] at he
  obtain ⟨s1, hs1, -, hm1, hgw⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ fo fl (j - 1))
    (callW_of_callE h1)
  have hl : ¬ fl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw
  have hJl : J < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hT := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hgT := hg0.1
  have hfvs' : decHL m fo.toNat fl.toNat = some fvs := by rw [decHL_grow hg0 hfb]; exact hfvs
  obtain ⟨w, hw, hwl, hwd⟩ := decHL_get' hfvs' J hJl (by omega)
  have efo : fo + (j - 1) = UInt64.ofNat (fo.toNat + J) := by
    apply UInt64.toNat_inj.mp; rw [sum_toNat_add (by omega), hJ]; simp; omega
  have hr1 : r1.headD 0 = w := by
    simp only [getW, hl, if_false, Option.some.injEq] at hgw
    rw [← hgw, efo, hw]
  have hm1' : m = m1 := by rw [← hs1, hm1]
  subst hm1'
  rw [hr1] at he
  have hget : fvs[J]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length m hfvs']; exact hJl), hwd]
  obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP J (decI w) hget
  have hwsa := hws J (by omega) aP haP
  refine ErrClaim.bind_right (v := decI w) (a₁ := a) (by rw [hget]; rfl) ?_
  have hdep : (nP + (j - 1)).toNat = nP.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  cases h2 : callE p n "fvar_type_d" [w] m with
  | error e2 =>
    rw [h2, csfGoE.k_fvar_type_d.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨rt, m1⟩ := q2
  rw [h2, csfGoE.k_fvar_type_d.arm1] at he
  obtain ⟨s2, hs2, -, hm2⟩ := triple_of_callW (ftdF_spec0 p hftd n ⟨m, Locals.init []⟩ [w])
    (callW_of_callE h2)
  subst hs2
  obtain ⟨t, a1, hrun1, hS1, hg1, ht1, ht⟩ := (sumSim_of_relW (ftdF_ok dn vis fe w hwl) hS) rt s2.mem hm2
  have hA1 : AbsOK s2.mem := ftdF_afr hm2 hA
  obtain ⟨ha1, htd⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
  rw [ha1] at hS1 hrun1
  have hC1 : StageC dn vis fe env s2.mem a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  refine ErrClaim.bind_right hrun1 ?_
  have hdt : denoteE a.store (decI (rt.headD 0)) = some aP.fvarTypeD := by rw [ht]; exact htd
  cases h3 : callE p n "infer_type_core" [vis, nP + (j - 1), rt.headD 0] s2.mem with
  | error e3 =>
    rw [h3, csfGoE.k_infer_type_core.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := hcE.inferTypeCore n (by omega) hC1.stageT (nP + (j - 1)) (rt.headD 0) ht1 _ h3
    rwa [hdep, ht] at this
  | ok q3 =>
  obtain ⟨ry, m2⟩ := q3
  rw [h3, csfGoE.k_infer_type_core.arm1] at he
  have h2' := inferC_rsim hq henv n (by omega) hC1 hA1 (nP + (j - 1)) (rt.headD 0) ht1 hdt
    (by rw [hdep]; exact hwsa)
  rw [hdep, ht] at h2'
  obtain ⟨ty, a2, hrun2, hC2, hg2, ⟨hy1, hy⟩, hA2, c2, tyP, htyP, hwty⟩ := h2' (ry, m2) (callW_of_callE h3)
  dsimp only at hC2 hg2 hy1 hy hA2
  refine ErrClaim.bind_right hrun2 ?_
  cases h4 : callE p n "ensure_sort_core" [vis, nP + (j - 1), ry.headD 0] m2 with
  | error e4 =>
    rw [h4, csfGoE.k_ensure_sort_core.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := hcE.ensureSortCore n (by omega) hC2.stageT (nP + (j - 1)) (ry.headD 0) hy1 _ h4
    rwa [hdep, hy] at this
  | ok q4 =>
  obtain ⟨ru, m3⟩ := q4
  rw [h4, csfGoE.k_ensure_sort_core.arm1] at he
  have h3' := ensureSortC_rsim hq henv n (by omega) hC2 hA2 (nP + (j - 1)) (ry.headD 0) hy1
    (by rw [hy]; exact htyP) (by rw [hdep]; exact hwty)
  rw [hdep, hy] at h3'
  obtain ⟨u, a3, hrun3, hC3, hg3, ⟨hu1, hu⟩, hA3, c3, lu, hdu⟩ := h3' (ru, m3) (callW_of_callE h4)
  dsimp only at hC3 hg3 hu1 hu hA3
  refine ErrClaim.bind_right hrun3 ?_
  have hg03 := ((hg0.trans hg1).trans hg2).trans hg3
  have hidx3 : decHL m3 io.toNat il.toNat = some idxArgs := by rw [decHL_grow hg03 hib]; exact hidx
  obtain ⟨sP, hsP0⟩ := hsP
  rw [← hu] at hdu
  cases h5 : callE p n "check_field_sort_bound" [isProp, large, s, io, il, w, ru.headD 0] m3 with
  | error e5 =>
    rw [h5, csfGoE.k_check_field_sort_bound.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := cfbE_claim hq.closed hLC hLT hnv n m3 a3 isProp large s io il w (ru.headD 0) idxArgs hC3 hA3
      hpw het hc hu1 hs hwl hidx3 (by have := hg03.1; omega) hdu
      (ConRon.Bridge.denoteL_ext hsP0 (c2.ext.trans c3.ext)) _
      (triple_of_callE_err (cfbE_spec p hb n ⟨m3, Locals.init []⟩ isProp large s io il w (ru.headD 0)) h5
        (Err.code_ne_of_cls hk0))
    rwa [hu] at this
  | ok q5 =>
  obtain ⟨r5, m4⟩ := q5
  rw [h5, csfGoE.k_check_field_sort_bound.arm1] at he
  obtain ⟨s5, hs5, -, hmodel⟩ := triple_of_callW
    (cfbW_spec p hpw het hc hb (realCall p) (realCall_spec p) n ⟨m3, Locals.init []⟩ isProp large s io il w
      (ru.headD 0)) (callW_of_callE h5)
  subst hs5
  have h4' := cfbW_okC hq.closed hLC hLT n m3 a3 isProp large s io il w (ru.headD 0) idxArgs hC3 hA3 hu1 hs
    hwl hidx3 (by have := hg03.1; omega) hdu (ConRon.Bridge.denoteL_ext hsP0 (c2.ext.trans c3.ext))
  rw [hu] at h4'
  obtain ⟨x4, a4, hrun4, ⟨⟨hS4, hg4⟩, hA4⟩⟩ := h4' r5 s5.mem hmodel
  refine ErrClaim.bind_right hrun4 ?_
  have c4 := sfbT_cstep hC3.check hrun4
  have hC4 : StageC dn vis fe env s5.mem a4 := hC3.of_check hS4 hA4 c4.ok c4.ext
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  have hres1 : (res + (j - 1)).toNat = res.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  have hsz4 : res.toNat + J < (s5.mem.arr64 IW).size := by
    obtain ⟨h1, -, -, -, -⟩ := hS4.2; have := hg14.1; omega
  have hacc4 : decHL s5.mem (res.toNat + J + 1) k = some acc := by
    rw [decHL_grow hg14 (by omega)]; rw [show res.toNat + J + 1 = res.toNat + j.toNat by omega]; exact hacc
  have hacc' := sumDecHL_write_front s5.mem _ k _ (ru.headD 0) acc hres1 hsz4 hu1 hacc4
  rw [hu] at hacc'
  have htop' : iwTop (s5.mem.set64 IW (res + (j - 1)) (ru.headD 0)) = iwTop s5.mem := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hAw := set64IW_afr s5.mem (res + (j - 1)) (ru.headD 0) hA4
  have hCw : StageC dn vis fe env (s5.mem.set64 IW (res + (j - 1)) (ru.headD 0)) a4 :=
    hC4.of_pstep (hS4.set_iw _ _) hAw (PStep.refl hC4.check.state)
  have hx14 := c2.ext.trans (c3.ext.trans c4.ext)
  refine ErrClaim.bind_left ?_
  cases h6 : csfGoE p n (s5.mem.set64 IW (res + (j - 1)) (ru.headD 0)) vis isProp large s nP fo fl io il res (j - 1) with
  | error e6 =>
    rw [h6, csfGoE.k_check_struct_field_sorts_i_go.none] at he
    cases he
    have := ih (by omega) (s5.mem.set64 IW (res + (j - 1)) (ru.headD 0)) a4 isProp large s nP fo fl io il
      res (j - 1) m0 (k + 1) (u :: acc) fvs idxArgs fvsP hCw hAw
      ((hg03.trans hg4).set_iw _ _ (by omega)) hr0 (by rw [htop', hJ]; have := hg14.1; omega)
      (by rw [hJ]; exact hacc') hfvs hfb hidx hib hs ⟨sP, ConRon.Bridge.denoteL_ext hsP0 hx14⟩ (by omega)
      (ConRon.Bridge.denoteEList_ext hx14 _ _ hfP) (fun i hi => hws i (by omega)) _ h6
    rwa [hJ] at this
  | ok q6 =>
  obtain ⟨w6, m6⟩ := q6
  rw [h6, csfGoE.k_check_struct_field_sorts_i_go.arm1] at he
  cases he

end sims

end L.Ind
