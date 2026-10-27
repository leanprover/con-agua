import ConAgua.Arena.IndT.RecCheckK53
import ConAgua.Arena.RecGenSpec23
import ConAgua.Arena.RecClassSpecL

/-!
# `classNodesAgree` under `StageC` (lane `indstaget`, helper `pds`)

`class_nodes_agree`'s loop (`cnaW`, the callees through the program's `callW`), from `StageC` and
the inputs' denotations con-ron's `classNodesAgree_spec` asks; its twin side transcribed from that
spec's proof: `targetPiDomsWith` (`targetPiDomsWith_spec`, a `PSpec`), the field read, then
`target_k53` (`tkW_okC`, con-ron's `targetK53_spec` on its run for the extension).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (P : CnaProg p)
  (vis q fto ftl mc teo tel leaf fvo fvl i eo el : Word) (bs : BlockShape) (formerTys : List EIdx)
  (TM : TargetMajor) (tele fvs : List EIdx)
  {pP : ConLeche.BlockShape} {formerTysP teleP fvsP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
  {leafP : ConLeche.Expr}

include hq henv P in
/-- **`class_nodes_agree`'s loop under `StageC`** (twin side: con-ron's `classNodesAgree_spec`'s
list induction). -/
theorem cnaW_okC (k : Nat) (hk : k ≤ 2 ^ 62) : ∀ (m m' : Mem) (a : AState) (j : Word)
    (es : List NestCtorNf) (esP : List ConLeche.NestCtorNf),
    cnaW p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j = some m' →
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
    ∃ a', (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es).run a =
      .ok ((), a') ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ AbsOK m' := by
  induction k with
  | zero => intro m m' a j es esP h; simp [cnaW] at h
  | succ k ih =>
  intro m m' a j es esP h hC hA hbs hft hftb hMc htl hl hfv hfvb hje hes hP hsh hftP hMcP htlP hlP
    hfvP hesP hformer hMs
  have hS := hC.stage
  by_cases hj : j < el
  rotate_left
  · rw [cnaW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have hjl : el - j = 0 := by
      apply UInt64.toNat_inj.mp
      have h1 : el.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
      have h2 : j.toNat ≤ el.toNat := UInt64.le_iff_toNat_le.mp hje
      rw [UInt64.toNat_sub_of_le _ _ hje]; simp <;> omega
    have : es = [] := by
      have := decPL_length _ (hes.1.get (OMono.decPL decNCN_mono _ _)); rw [hjl] at this; simpa using this
    subst this
    exact ⟨a, rfl, hC, IWGrow.refl _, hP, hA⟩
  rw [cnaW_step (h := hj)] at h
  have hsz := hS.2.2.2.1
  have hne : el - j ≠ 0 := by
    intro h0
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_sub_of_le _ _ hje] at this; simp at this; omega
  obtain ⟨nf, es', rfl, hnf0, hes'⟩ := hes.uncons hne hsz
  obtain ⟨nfP, esP', rfl, hnfP, hesP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hesP
  have hety := (ConRon.Bridge.Inductives.RC.dCtorNf_inv hnfP).2.2.2
  generalize hE : rdW (m.arr64 IW) (eo + j) = ew at h hnf0
  obtain ⟨htyH, htyD⟩ := decNCN_ty hnf0 hsz
  -- `target_pi_doms_with`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetPiDomsWith_spec p P.hv P.hc P.ha P.hsc P.pd P.hi1 k _ fvo fvl (rdW (m.arr64 IW) (ew + 4))) c1
  simp only at hs1 hw1
  subst hs1
  obtain ⟨res, a1, run1, hS1, hg1, hpd⟩ := pdW_ok dn vis fe k _ _ a _ _ _ r1 fvs hw1 hS htyH hfv
    (hS.lt64 hfvb) hfvb
  have hP1 := hP.fr (pdW_mfr _ _ _ _ _ _ _ hw1)
  have hA1 := pdW_afr _ _ _ _ _ _ _ hw1 hA
  rw [htyD] at run1
  obtain ⟨q1, ho⟩ := ConRon.Bridge.Inductives.targetPiDomsWith_spec fvs fvsP nf.ty nfP.ty a a1 res
    hC.check.state ⟨hfvP, hety⟩ run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  have hdoms := ConRon.Bridge.Inductives.ROp_REL_getD ho
  rcases res with _ | ds
  · have h0 : r1.headD 0 = 0 := hpd; rw [cnaK1_bad (h := h0)] at h; cases h
  obtain ⟨h1, hdd, hdb⟩ := hpd
  have h0 : ¬ r1.headD 0 = 0 := by rw [h1]; decide
  by_cases hsh' : r1.tail.tail.headD 0 ≤ i
  · rw [cnaK1_short (h0 := h0) (h := hsh')] at h; cases h
  rw [cnaK1_ok (h0 := h0) (h := hsh')] at h
  have hi : i.toNat < (r1.tail.tail.headD 0).toNat := by
    exact Nat.lt_of_not_le (fun hc => hsh' (UInt64.le_iff_toNat_le.mpr hc))
  have hdb64 := hS1.lt64 hdb
  obtain ⟨w, hw, hwH, hwD⟩ := decHL_get' hdd i.toNat hi (by omega)
  have hadd : r1.tail.headD 0 + i = UInt64.ofNat ((r1.tail.headD 0).toNat + i.toNat) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
  rw [hadd, hw] at h
  have hget : ds[i.toNat]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length _ hdd]; exact hi)]; rw [hwD]
  rw [← decE_eq] at hget
  obtain ⟨fP, -, hfd⟩ := (ConRon.Bridge.Inductives.denoteEList_getElem? hdoms i.toNat).2 _ hget
  -- `target_k53`
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (tk_spec p P.k53 (realCall p) (realCall_spec p) k _ vis q fto ftl mc teo tel leaf w) c2
  simp only at hs2 hw2
  subst hs2
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
  by_cases hb : r2.headD 0 = 0
  · rw [cnaK2_bad (h := hb)] at h; cases h
  rw [cnaK2_ok (h := hb)] at h
  have hct : c = true := by rw [← hc]; simpa using hb
  subst hct
  have hg12 := hg1.trans hg2
  have hj1 : j + 1 ≤ el := by
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    apply UInt64.le_iff_toNat_le.mpr; rw [UInt64.toNat_add]; simp <;> omega
  have hes2 : PSlR decNCN es' (eo + (j + 1)) (el - (j + 1)) s2.mem := by
    rw [show eo + (j + 1) = eo + j + 1 by grind, show el - (j + 1) = el - j - 1 by grind]
    exact hes'.grow (fun q => decNCN_mono q) hg12
  obtain ⟨a3, run3, hC3, hg3, hP3, hA3⟩ := ih (by omega) s2.mem m' a2 (j + 1) es' esP' h hC2 hA2
    (hbs.grow hg12)
    (by rw [decHL_grow hg12 hftb]; exact hft) (by have := hg12.1; omega) (hMc.grow (decTM_mono _) hg12)
    (htl.grow hg12) hl (by rw [decHL_grow hg12 hfvb]; exact hfv) (by have := hg12.1; omega) hj1 hes2 hP2
    (ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh) (denoteEList_ext c12.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext c12.ext _ _ hMcP) (denoteEList_ext c12.ext _ _ htlP)
    (denote_ext hlP c12.ext) (denoteEList_ext c12.ext _ _ hfvP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list c12.ext _ _ hesP') hformer hMs
  refine ⟨a3, ?_, hC3, hg12.trans hg3, hP3, hA3⟩
  simp only [ConRon.Arena.classNodesAgree, StateT.run_bind, run1, except_ok_bind, Option.getD_some, hget]
  simp only [run2, except_ok_bind, ite_true]
  exact run3

include hq henv P in
/-- **`class_nodes_agree` refines `classNodesAgree`** under `StageC` (the knot's core calls; the
inputs' denotations and scoping as con-ron's `classNodesAgree_spec` asks). -/
@[refines ConRon.Arena.classNodesAgree]
theorem classNodesAgree_refinesC (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
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
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_nodes_agree"
      [vis, q, fto, ftl, mc, teo, tel, leaf, fvo, fvl, i, eo, el]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (cna_spec p P.cna n s₀ vis q fto ftl mc teo tel leaf fvo fvl i eo el) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨a', run, hC', hg, hP', hA'⟩ := cnaW_okC hq henv P vis q fto ftl mc teo tel leaf fvo fvl i eo el
    bs formerTys TM tele fvs n hn _ _ a₀ 0 es esP hm hC hA hbs hft hftb hMc htl hl hfv hfvb
    UInt64.zero_le (by simpa using hes) hP hsh hftP hMcP htlP hlP hfvP hesP hformer hMs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hC', hg, hP', hA'⟩

end sims

end L.Ind
