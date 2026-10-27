import ConAgua.Verdict.IndE
import ConAgua.Verdict.DeclValE
import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinements of the direct sums' field sorts (lane `verdicts-b`, helper `ib`)

`check_struct_field_sorts_i_go` (the fields from the last, per field `fvar_type_d`,
`infer_type_core`, `ensure_sort_core`, `check_field_sort_bound`) and `check_struct_field_sorts_i`.
-/

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

l_model fsortsE_spec (p : Prog) (hf : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL)
  fns [hf ↦ fsortsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model sdomsE_spec (p : Prog) (hf : p.lookup "check_struct_doms_at" = some checkStructDomsAtL)
  fns [hf ↦ sdomsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hLC hLT hnv hcE in
/-- **`check_struct_field_sorts_i_go`'s model error claim** (`csfW_okC`'s hypotheses; the recursion is
the model's own). -/
theorem csfE_claimB (hg : p.lookup "sl_get" = some slGet)
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
    simp only [getW, hl, ite_false, Option.some.injEq] at hgw
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

include hq henv hLC hLT hnv hcE in
/-- **`check_struct_field_sorts_i`'s error claim** (the hypotheses of
`checkStructFieldSortsI_refinesC`, and the core stubs' error claims): a failing call of class
`1`/`2` claims that the twin's `checkStructFieldSortsI` fails. -/
theorem checkStructFieldSortsI_claim (hg : p.lookup "sl_get" = some slGet)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
    (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
    (hia : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL) (hftd : FtdF p)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (isProp large s nP fo fl io il nW : Word)
    (fvs idxArgs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hidx : decHL s₀.mem io.toNat il.toNat = some idxArgs) (hib : io.toNat + il.toNat ≤ iwTop s₀.mem)
    (hs : H s) {sP : ConLeche.Level} (hsP : denoteL a₀.store.ls (decI s) = some sP)
    (hnj : nP.toNat + nW.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hws : ∀ i, i < nW.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    CoreSpecE p (n + 1) "check_struct_field_sorts_i" [vis, isProp, large, s, nP, fo, fl, io, il, nW]
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs nW.toNat)
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (fsortsE_spec p hp (n + 1) ⟨s₀.mem, Locals.init []⟩ vis isProp large s nP
    fo fl io il nW) hc' (Err.code_ne_of_cls hk0)
  rw [fsortsE.arm1] at hW
  cases h1 : callE p n "iw_alloc" [nW] s₀.mem with
  | error e1 =>
    rw [h1, fsortsE.k_iw_alloc.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, fsortsE.k_iw_alloc.arm1] at hW
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (iwAlloc_specW p hia n ⟨s₀.mem, Locals.init []⟩ nW)
    (callW_of_callE h1)
  subst hs1
  obtain ⟨hS1, hg1, hrt, ht1⟩ := allocW_stage hal hC.stage
  dsimp only at hrt ht1 hal
  have hA1 := allocW_afr hal hA
  have hC1 : StageC dn vis fe env s1.mem a₀ := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  cases h2 : callE p n "check_struct_field_sorts_i_go"
      [vis, isProp, large, s, nP, fo, fl, io, il, r1.headD 0, nW] s1.mem with
  | error e2 =>
    rw [h2, fsortsE.k_check_struct_field_sorts_i_go.none] at hW
    cases hW
    exact csfE_claimB hq henv hLC hLT hnv hcE hg hpw het hc hb hftd n hn s1.mem a₀ isProp large s nP fo fl io il
      (r1.headD 0) nW s₀.mem 0 [] fvs idxArgs fvsP hC1 hA1 hg1 (by omega) (by omega)
      (by simp [decHL, hslice?]) hfvs hfb hidx hib hs ⟨sP, hsP⟩ hnj hfP hws _
      (triple_of_callE_err (csfGoE_spec p hgo n ⟨s1.mem, Locals.init []⟩ vis isProp large s nP fo fl io il
        (r1.headD 0) nW) h2 (Err.code_ne_of_cls hk0))
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, fsortsE.k_check_struct_field_sorts_i_go.arm1] at hW
  cases hW

include hq henv hnv hcE in
/-- **`check_struct_doms_at`'s model error claim** (`sdomsW_simC`'s hypotheses; the binder mismatch
is the twin's decline; the recursion is the model's own). -/
theorem sdomsE_claim (hg : p.lookup "sl_get" = some slGet) (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (fvsP domsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m fo.toNat fl.toNat = some fvs → decHL m dO.toNat dl.toNat = some doms →
    fo.toNat + fl.toNat < 2 ^ 64 → dO.toNat + dl.toNat < 2 ^ 64 → fo.toNat + fl.toNat ≤ iwTop m →
    dO.toNat + dl.toNat ≤ iwTop m → off.toNat + fl.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP → Frontend.denoteEList a.store doms = some domsP →
    (∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) →
    ∀ e, sdomsE p n m vis off fo fl dO dl j = .error e →
      ErrClaim (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a e := by
  induction n with
  | zero =>
    intro m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot hdot hoob hfP hdP
      hws e he
    rw [sdomsE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot hdot hoob hfP hdP
    hws e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hStage := hC.stage
  by_cases hj : j = 0
  · rw [sdomsE.arm2 p n m vis off fo fl dO dl j hj] at he
    cases he
  rw [sdomsE.arm1 p n m vis off fo fl dO dl j hj] at he
  have hfvl := decHL_length m hfvs
  have hdol := decHL_length m hdoms
  have hjpos : 1 ≤ j.toNat := Nat.pos_of_ne_zero fun h0 => hj (UInt64.toNat_inj.mp (by simpa using h0))
  have hj1 : (j - 1).toNat = j.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
    simp
  cases h1 : callE p n "sl_get" [fo, fl, j - 1] m with
  | error e1 =>
    rw [h1, sdomsE.k_sl_get.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, sdomsE.k_sl_get.arm1] at he
  obtain ⟨s1, hs1, -, hm1, hgw1⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ fo fl (j - 1))
    (callW_of_callE h1)
  have hl1 : ¬ fl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw1
  have hm1' : m = m1 := by rw [← hs1, hm1]
  subst hm1'
  cases h2 : callE p n "sl_get" [dO, dl, j - 1] m with
  | error e2 =>
    rw [h2, sdomsE.k_sl_get_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, sdomsE.k_sl_get_2.arm1] at he
  obtain ⟨s2, hs2, -, hm2, hgw2⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ dO dl (j - 1))
    (callW_of_callE h2)
  have hl2 : ¬ dl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw2
  have hm2' : m = m2 := by rw [← hs2, hm2]
  subst hm2'
  have hjm1f : j.toNat - 1 < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl1 (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hjm1d : j.toNat - 1 < dl.toNat := by
    have : ¬ dl.toNat ≤ (j - 1).toNat := fun e => hl2 (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hfoeq : fo + (j - 1) = UInt64.ofNat (fo.toNat + (j.toNat - 1)) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
  have hdoeq : dO + (j - 1) = UInt64.ofNat (dO.toNat + (j.toNat - 1)) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
  obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := decHL_get' hfvs (j.toNat - 1) hjm1f hfob
  obtain ⟨wb, hwb_eq, hwb_lt, hwb_dec⟩ := decHL_get' hdoms (j.toNat - 1) hjm1d hdob
  have hfvsij : fvs[j.toNat - 1]? = some (decI wa) := by
    rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < fvs.length)]
    exact congrArg some hwa_dec
  have hdomsij : doms[j.toNat - 1]? = some (decI wb) := by
    rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < doms.length)]
    exact congrArg some hwb_dec
  obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP _ _ hfvsij
  obtain ⟨bP, hbP, hdb⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? doms domsP hdP _ _ hdomsij
  obtain ⟨hwx, hwy⟩ := hws (j.toNat - 1) (by omega) aP bP haP hbP
  have hjeq : j.toNat = (j.toNat - 1) + 1 := by omega
  rw [hjeq]
  simp only [ConRon.Arena.checkStructDomsAt, unwrapOr, hfvsij, hdomsij, pure_bind]
  have hr1 : r1.headD 0 = wa := by
    simp only [getW, hl1, ite_false, Option.some.injEq] at hgw1
    rw [← hgw1, hfoeq, hwa_eq]
  rw [hr1] at he
  have hr2 : r2.headD 0 = wb := by
    simp only [getW, hl2, ite_false, Option.some.injEq] at hgw2
    rw [← hgw2, hdoeq, hwb_eq]
  rw [hr2] at he
  cases h3 : callE p n "fvar_type_d" [wa] m with
  | error e3 =>
    rw [h3, sdomsE.k_fvar_type_d.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨ra, m3⟩ := q3
  rw [h3, sdomsE.k_fvar_type_d.arm1] at he
  obtain ⟨s3, hs3, -, hm3⟩ := triple_of_callW (ftdF_spec0 p hftd n ⟨m, Locals.init []⟩ [wa])
    (callW_of_callE h3)
  subst hs3
  obtain ⟨x1, a1, hrun1, hStage1, hg1, hw1lt, hw1eq⟩ := ftdF_ok dn vis fe wa hwa_lt m s3.mem a ra
    hm3 hStage
  obtain ⟨ha1, hx1d⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
  rw [ha1] at hrun1 hStage1
  have hA1 := ftdF_afr (m := m) (m' := s3.mem) hm3 hA
  have hC1 : StageC dn vis fe env s3.mem a := hC.of_pstep hStage1 hA1 (PStep.refl hC.check.state)
  refine ErrClaim.bind_right hrun1 ?_
  have hdep : (off + (j - 1)).toNat = off.toNat + (j.toNat - 1) := by
    rw [UInt64.toNat_add, hj1]; exact Nat.mod_eq_of_lt (by omega)
  have hdx : denoteE a.store (decI (ra.headD 0)) = some aP.fvarTypeD := by rw [hw1eq]; exact hx1d
  have hdb' : denoteE a.store (decI wb) = some bP := hdb
  cases h4 : callE p n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, wb] s3.mem with
  | error e4 =>
    rw [h4, sdomsE.k_is_def_eq_core.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := hcE.isDefEqCore n (by omega) hC1.stageT (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt _ h4
    rwa [hdep, hw1eq] at this
  | ok q4 =>
  obtain ⟨rb, m4⟩ := q4
  rw [h4] at he
  have hi := isDefEqC_rsim hq henv n (by omega) hC1 hA1 (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt hdx hdb'
    (by rw [hdep]; exact hwx) (by rw [hdep]; exact hwy)
  obtain ⟨x2, a2, hrun2, hC2, hg2, hb2eq, hA2, hcs2⟩ := hi (rb, m4) (callW_of_callE h4)
  dsimp only at hC2 hg2 hb2eq hA2
  rw [hdep] at hrun2
  rw [hw1eq] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  by_cases heq0 : rb.headD 0 = 0
  · rw [sdomsE.k_is_def_eq_core.abort1 p n vis off fo fl dO dl j _ _ heq0] at he
    cases he
    have hv2 : x2 = false := by
      rw [← hb2eq]; simp [decBool]; simpa using heq0
    subst hv2
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  · rw [sdomsE.k_is_def_eq_core.arm1 p n vis off fo fl dO dl j _ _ heq0] at he
    have hv2 : x2 = true := by
      rw [← hb2eq]; simpa [decBool] using heq0
    subst hv2
    simp only [ite_true]
    cases h5 : sdomsE p n m4 vis off fo fl dO dl (j - 1) with
    | error e5 =>
      rw [h5, sdomsE.k_check_struct_doms_at.none] at he
      cases he
      have := ih (by omega) m4 a2 off fo fl dO dl (j - 1) fvs doms fvsP domsP hC2 hA2
        (by rw [decHL_grow (hg1.trans hg2) (by omega)]; exact hfvs)
        (by rw [decHL_grow (hg1.trans hg2) (by omega)]; exact hdoms) hfob hdob
        (by have := (hg1.trans hg2).1; omega) (by have := (hg1.trans hg2).1; omega) hoob
        (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hfP) (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hdP)
        (fun i hi => hws i (by omega)) _ h5
      rwa [hj1] at this
    | ok q5 =>
    obtain ⟨z5, m5⟩ := q5
    rw [h5, sdomsE.k_check_struct_doms_at.arm1] at he
    cases he

include hq henv hnv hcE in
/-- **`check_struct_doms_at`'s error claim** (the hypotheses of `checkStructDomsAt_refinesC`, and
the core stubs' error claims): a binder-domain mismatch is the twin's decline. -/
theorem checkStructDomsAt_claim (hg : p.lookup "sl_get" = some slGet)
    (hp : p.lookup "check_struct_doms_at" = some checkStructDomsAtL) (hftd : FtdF p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (off fo fl dO dl j : Word) (fvs doms : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64)
    {fvsP domsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a₀.store doms = some domsP)
    (hws : ∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) :
    CoreSpecE p n "check_struct_doms_at" [vis, off, fo, fl, dO, dl, j]
      (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (sdomsE_spec p hp n ⟨s₀.mem, Locals.init []⟩ vis off fo fl dO dl j) hc'
    (Err.code_ne_of_cls hk0)
  exact sdomsE_claim hq henv hnv hcE hg hftd n hn s₀.mem a₀ off fo fl dO dl j fvs doms _ _ hC hA hfvs hdoms
    hfob hdob hfot hdot hoob hfP hdP hws er hW

end sims

end L.Ind
