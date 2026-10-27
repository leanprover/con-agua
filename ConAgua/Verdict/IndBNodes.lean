import ConAgua.Verdict.IndBK53
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinement of `class_nodes_agree` (lane `verdicts-b`, helper `ib`)

The loop's own aborts are the twin's two `fail`s (entry too short, `target_k53` false);
`target_pi_doms_with` is `closedNV`; `target_k53`'s claim is `targetK53_claim` (it takes the
`target_k53_args` hypothesis `TkaE`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cnaE_spec (p : Prog) (hf : p.lookup "class_nodes_agree" = some classNodesAgreeL)
  fns [hf ↦ cnaE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (P : CnaProg p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) {vis : Word} (hTka : TkaE p dn vis fe env)
  (q fto ftl mc teo tel leaf fvo fvl i eo el : Word) (bs : BlockShape) (formerTys : List EIdx)
  (TM : TargetMajor) (tele fvs : List EIdx)
  {pP : ConLeche.BlockShape} {formerTysP teleP fvsP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
  {leafP : ConLeche.Expr}

include hq henv P hnv hTka in
/-- **`class_nodes_agree`' loop error claim** (`cnaW_okC`'s hypotheses). -/
theorem cnaE_claim (k : Nat) (hk : k ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState) (j : Word)
    (es : List NestCtorNf) (esP : List ConLeche.NestCtorNf),
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs →
    decHL m fto.toNat ftl.toNat = some formerTys →
    fto.toNat + ftl.toNat ≤ iwTop m → DecB (fun m => decTM m mc.toNat) m TM → HSl0 m teo tel tele →
    H leaf → decHL m fvo.toNat fvl.toNat = some fvs → fvo.toNat + fvl.toNat ≤ iwTop m →
    j ≤ el → PSlR decNCN es (eo + j) (el - j) m → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    dMajor a.store TM = some McP → Frontend.denoteEList a.store tele = some teleP →
    denoteE a.store (decE leaf) = some leafP → Frontend.denoteEList a.store fvs = some fvsP →
    es.mapM (dCtorNf a.store) = some esP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) → ConLeche.Cached.TargetMajScoped McP →
    ∀ e, cnaE.loop1 p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j = .error e →
      ErrClaim (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a e := by
  induction k with
  | zero =>
    intro m a j es esP hC hA hbs hft hftb hMc htl hl hfv hfvb hje hes hP hsh hftP hMcP htlP hlP
      hfvP hesP hformer hMs e he
    rw [cnaE.loop1.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a j es esP hC hA hbs hft hftb hMc htl hl hfv hfvb hje hes hP hsh hftP hMcP htlP hlP
    hfvP hesP hformer hMs e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  by_cases hj : j < el
  rotate_left
  · rw [cnaE.loop1.arm2 p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j hj] at he
    cases he
  rw [cnaE.loop1.arm1 p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j hj] at he
  have hsz := hS.2.2.2.1
  have hne : el - j ≠ 0 := by
    intro h0
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_sub_of_le _ _ hje] at this; simp at this; omega
  obtain ⟨nf, es', rfl, hnf0, hes'⟩ := hes.uncons hne hsz
  obtain ⟨nfP, esP', rfl, hnfP, hesP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hesP
  have hety := (ConRon.Bridge.Inductives.RC.dCtorNf_inv hnfP).2.2.2
  generalize hE : rdW (m.arr64 IW) (eo + j) = ew at he hnf0
  obtain ⟨htyH, htyD⟩ := decNCN_ty hnf0 hsz
  rw [ConRon.Arena.classNodesAgree]
  -- `target_pi_doms_with`
  cases h1 : callE p k "target_pi_doms_with" [fvo, fvl, rdW (m.arr64 IW) (ew + 4)] m with
  | error e1 =>
    rw [h1, cnaE.k_target_pi_doms_with.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetPiDomsWith_spec p P.hv P.hc P.ha P.hsc P.pd P.hi1 k _ fvo fvl (rdW (m.arr64 IW) (ew + 4)))
    (callW_of_callE h1)
  subst hs1
  obtain ⟨res, a1, run1, hS1, hg1, hpd⟩ := pdW_ok dn vis fe k _ _ a _ _ _ r1 fvs hw1 hS htyH hfv
    (hS.lt64 hfvb) hfvb
  dsimp only at hg1
  have hP1 := hP.fr (pdW_mfr _ _ _ _ _ _ _ hw1)
  have hA1 := pdW_afr _ _ _ _ _ _ _ hw1 hA
  rw [htyD] at run1
  obtain ⟨q1, ho⟩ := ConRon.Bridge.Inductives.targetPiDomsWith_spec fvs fvsP nf.ty nfP.ty a a1 res
    hC.check.state ⟨hfvP, hety⟩ run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  have hdoms := ConRon.Bridge.Inductives.ROp_REL_getD ho
  refine ErrClaim.bind_right run1 ?_
  dsimp only
  rcases res with _ | ds
  · have h0 : r1.headD 0 = 0 := hpd
    rw [h1, cnaE.k_target_pi_doms_with.arm1 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j r1 _ h0,
      cnaE.j1.abort1 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j _ 0 _ UInt64.zero_le] at he
    cases he
    simp only [Option.getD_none, List.getElem?_nil]
    exact ErrClaim.fail _ _ (by decide)
  obtain ⟨h1', hdd, hdb⟩ := hpd
  have h0 : ¬ r1.headD 0 = 0 := by rw [h1']; decide
  by_cases hsh' : r1.tail.tail.headD 0 ≤ i
  · rw [h1, cnaE.k_target_pi_doms_with.arm2 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j r1 _ h0,
      cnaE.j1.abort1 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j _ _ _ hsh'] at he
    cases he
    have hlen := decHL_length _ hdd
    have hle : ds.length ≤ i.toNat := by rw [hlen]; exact UInt64.le_iff_toNat_le.mp hsh'
    simp only [Option.getD_some, List.getElem?_eq_none hle]
    exact ErrClaim.fail _ _ (by decide)
  rw [h1, cnaE.k_target_pi_doms_with.arm2 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j r1 _ h0,
      cnaE.j1.arm1 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j _ _ _ hsh'] at he
  have hi : i.toNat < (r1.tail.tail.headD 0).toNat := by
    exact Nat.lt_of_not_le (fun hc => hsh' (UInt64.le_iff_toNat_le.mpr hc))
  have hdb64 := hS1.lt64 hdb
  obtain ⟨w, hw, hwH, hwD⟩ := decHL_get' hdd i.toNat hi (by omega)
  have hadd : r1.tail.headD 0 + i = UInt64.ofNat ((r1.tail.headD 0).toNat + i.toNat) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
  rw [hadd, hw] at he
  have hget : ds[i.toNat]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length _ hdd]; exact hi)]; rw [hwD]
  rw [← decE_eq] at hget
  obtain ⟨fP, -, hfd⟩ := (ConRon.Bridge.Inductives.denoteEList_getElem? hdoms i.toNat).2 _ hget
  simp only [Option.getD_some, hget]
  -- `target_k53`
  cases h2 : callE p k "target_k53" [vis, q, fto, ftl, mc, teo, tel, leaf, w] s1.mem with
  | error e2 =>
    rw [h2, cnaE.k_target_k53.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (targetK53_claim hnv hTka P.k53 k (by omega) ⟨s1.mem, Locals.init []⟩ a1 q fto ftl mc
      teo tel leaf w bs formerTys TM tele hC1 hA1 (hbs.grow hg1)
      (by rw [decHL_grow hg1 hftb]; exact hft) (by dsimp only; have := hg1.1; omega) (hMc.grow (decTM_mono _) hg1)
      (htl.grow hg1) hl hwH hP1
      (ConRon.Bridge.Inductives.dShape_ext q1.ext _ _ hsh) (denoteEList_ext q1.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext q1.ext _ _ hMcP) (denoteEList_ext q1.ext _ _ htlP)
      (denote_ext hlP q1.ext) hfd hformer hMs) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (tk_spec p P.k53 (realCall p) (realCall_spec p) k _ vis q fto ftl mc teo tel leaf w) (callW_of_callE h2)
  subst hs2
  dsimp only at hw2
  obtain ⟨c, a2, run2, hc, hC2, hg2, hP2, hA2⟩ := tkW_okC hq henv k (by omega) hw2 hC1 hA1 (hbs.grow hg1)
    (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.1; omega) (hMc.grow (decTM_mono _) hg1)
    (htl.grow hg1) hl hwH hP1
    (ConRon.Bridge.Inductives.dShape_ext q1.ext _ _ hsh) (denoteEList_ext q1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext q1.ext _ _ hMcP) (denoteEList_ext q1.ext _ _ htlP)
    (denote_ext hlP q1.ext) hfd hformer hMs
  have c1' := q1.toCore hC.check
  obtain ⟨c2', -⟩ := ConRon.Bridge.Inductives.targetK53_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys formerTysP TM McP tele teleP (decE leaf) (decE w) leafP fP hformer hMs
    a1 a2 c hC1.check
    ⟨ConRon.Bridge.Inductives.dShape_ext q1.ext _ _ hsh, denoteEList_ext q1.ext _ _ hftP,
      ConRon.Bridge.Inductives.dMajor_ext q1.ext _ _ hMcP, denoteEList_ext q1.ext _ _ htlP,
      denote_ext hlP q1.ext, hfd⟩ run2
  have c12 := c1'.trans c2'
  refine ErrClaim.bind_right run2 ?_
  by_cases hb : r2.headD 0 = 0
  · rw [h2, cnaE.k_target_k53.abort1 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j r2 _ hb] at he
    cases he
    have hcf : c = false := by rw [← hc, hb]; rfl
    subst hcf
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.fail _ _ (by decide)
  rw [h2, cnaE.k_target_k53.arm1 p k vis q fto ftl mc teo tel leaf fvo fvl i eo el j r2 _ hb] at he
  have hct : c = true := by rw [← hc]; simpa using hb
  subst hct
  simp only [ite_true]
  have hg12 := hg1.trans hg2
  have hj1 : j + 1 ≤ el := by
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    apply UInt64.le_iff_toNat_le.mpr; rw [UInt64.toNat_add]; simp <;> omega
  have hes2 : PSlR decNCN es' (eo + (j + 1)) (el - (j + 1)) s2.mem := by
    rw [show eo + (j + 1) = eo + j + 1 by grind, show el - (j + 1) = el - j - 1 by grind]
    exact hes'.grow (fun q => decNCN_mono q) hg12
  exact ih (by omega) s2.mem a2 (j + 1) es' esP' hC2 hA2
    (hbs.grow hg12)
    (by rw [decHL_grow hg12 hftb]; exact hft) (by have := hg12.1; omega) (hMc.grow (decTM_mono _) hg12)
    (htl.grow hg12) hl (by rw [decHL_grow hg12 hfvb]; exact hfv) (by have := hg12.1; omega) hj1 hes2 hP2
    (ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh) (denoteEList_ext c12.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext c12.ext _ _ hMcP) (denoteEList_ext c12.ext _ _ htlP)
    (denote_ext hlP c12.ext) (denoteEList_ext c12.ext _ _ hfvP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list c12.ext _ _ hesP') hformer hMs e he

include hq henv P hnv hTka in
/-- **`class_nodes_agree`' error claim** (every fuel; `classNodesAgree_refinesC`'s hypotheses). -/
theorem classNodesAgree_claim (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (es : List NestCtorNf) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hMc : DecB (fun m => decTM m mc.toNat) s₀.mem TM) (htl : HSl0 s₀.mem teo tel tele) (hl : H leaf)
    (hfv : decHL s₀.mem fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hes : PSlR decNCN es eo el s₀.mem) (hP : RcMR s₀.mem) {esP : List ConLeche.NestCtorNf}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hMcP : dMajor a₀.store TM = some McP) (htlP : Frontend.denoteEList a₀.store tele = some teleP)
    (hlP : denoteE a₀.store (decE leaf) = some leafP)
    (hfvP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a₀.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    CoreSpecE p n "class_nodes_agree" [vis, q, fto, ftl, mc, teo, tel, leaf, fvo, fvl, i, eo, el]
      (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) s₀ a₀ :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have he := triple_of_callE_err (cnaE_spec p P.cna n s₀ vis q fto ftl mc teo tel leaf fvo fvl i eo el) hc
      (Err.code_ne_of_cls hk0)
    cases n with
    | zero =>
      simp only [cnaE] at he
      cases he
      exact ErrClaim.of_cls0 Err.cls_outOfFuel
    | succ n =>
      rw [cnaE.arm1] at he
      cases hloop : cnaE.loop1 p (n + 1) s₀.mem vis q fto ftl mc teo tel leaf fvo fvl i eo el 0 with
      | error e' =>
        rw [hloop, cnaE.k_loop1.none] at he
        cases he
        exact cnaE_claim hq henv P hnv hTka q fto ftl mc teo tel leaf fvo fvl i eo el bs formerTys TM tele fvs
          (n + 1) hn s₀.mem a₀ 0 es esP hC hA hbs hft hftb hMc htl hl hfv hfvb UInt64.zero_le (by simpa using hes)
          hP hsh hftP hMcP htlP hlP hfvP hesP hformer hMs _ hloop
      | ok m' =>
        rw [hloop, cnaE.k_loop1.arm1] at he
        cases he

end sims

end L.Ind
