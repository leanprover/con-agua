import ConAgua.Arena.IndT.RecGen23
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk

/-!
# `class_fields_agree`: one model, one refinement

`class_fields_agree`'s unified model (`cfaE`) and its refinement for both outcomes (`cfa_ref`, the
loop `cfaLoop_ref`), under `StageC` and
the inputs' denotations con-ron's `classFieldsAgree_spec` asks; its twin side transcribed from that
spec's proof: `exprGetD` (`exprGetD_spec`), `fvarTypeD` and `stripPis` (read-only), `targetMajorAt`
(`targetMajorAt_spec`), `classLeafAt` (`classLeafAt_spec`), then `cna_ref` (con-ron's
`classNodesAgree_spec` on its run for the extension).
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`class_fields_agree`'s unified model**: the callees outside the verdict closure lifted,
`class_nodes_agree` by its unified model. -/
l_model cfaE_spec (p : Prog) (P : CfaProg p)
  fns [P.cfa ↦ cfaE]
  specs [callW_spec p n "intern_bvar", callW_spec p n "fvar_type_d", callW_spec p n "strip_pis",
    callW_spec p n "target_major_at", callW_spec p n "class_leaf_at", cnaE_spec p P.toCnaProg n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem leafAtW_afr {m m' : Mem} {mm leaf : Word} {r : List Word} (h : leafAtW m mm leaf = some (r, m')) :
    AFr m m' := by
  simp only [leafAtW] at h
  rcases h1 : gafF m [CWF, leaf] with _ | x
  · rw [h1] at h; cases h
  obtain ⟨r1, m1⟩ := x
  simp only [h1] at h
  refine (gafF_afr h1).trans ?_
  have hm : m' = m1 := by
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  rw [hm]; exact AFr.refl _

theorem cfaFv_afr {p : Prog} (P : CfaProg p) {k : Nat} {m m0 : Mem} {fvo fvl i : Word} {r0 : List Word}
    (h : cfaFv p k m fvo fvl i = some (r0, m0)) : AFr m m0 := by
  by_cases hi : i < fvl
  · rw [cfaFv_in (h := hi)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact AFr.refl _
  · rw [cfaFv_out (h := hi)] at h
    obtain ⟨s0, rfl, -, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internBVar_spec p P.bf P.bp P.ib k _ 0) h
    exact binternW_afr hb

/-- **`target_major_at`'s step** (two call sites: `cfaLoop_ref`, `cxo_ref`): the twin's
`targetMajorAt`, the package, the major's record at the result word and its denotation. -/
theorem tma_step {p : Prog} (P : CfaProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m₀ m : Mem} {a₀ a : AState} {n : Nat} (hk : RcAt dn vis fe env m₀ a₀ m a)
    {mo ml c : Word} {t : Nat} (ht : c.toNat = t) {ms : List TargetMajor} {MsP : List ConLeche.TargetMajor}
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) :
    Sim (callW p n "target_major_at" [mo, ml, c] m) (ConRon.Arena.targetMajorAt ms t) a
      fun r tm m' a' => RcAt dn vis fe env m a m' a' ∧
        DecB (fun m => decTM m (r.headD 0).toNat) m' tm ∧ dMajor a'.store tm = some (MsP.getD t default) :=
  fun r m' hc => by
    subst ht
    obtain ⟨s1, rfl, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (targetMajorAt_spec p P.ha P.pw P.mtm P.tmd P.tma P.na n _ mo ml c) hc
    obtain ⟨tm, a1, run1, hS1, hg1, hTM⟩ := rec3TMA_sim dn vis fe n m a mo ml c ms hk.stage.stage hms hmsb _ hw1
    obtain ⟨q1, hmP⟩ := ConRon.Bridge.Inductives.targetMajorAt_spec ms MsP c.toNat a a1 tm hk.stage.check.state
      hk.stage.check.pins hmsP run1
    exact ⟨tm, a1, run1, RcAt.pstep hk.stage hS1 (tmaW_afr hw1 hk.abs) (hk.rc.fr (tmaW_mfr hw1)) hg1 q1,
      hTM, hmP⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (P : CfaProg p)
  (vis q fto ftl mo ml fvo fvl eo el ko kl : Word) (bs : BlockShape) (formerTys : List EIdx)
  (ms : List TargetMajor) (fvs : List EIdx) (es : List NestCtorNf) (ks : List ClassField)
  {pP : ConLeche.BlockShape} {formerTysP fvsP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
  {esP : List ConLeche.NestCtorNf}

include hq henv P in
/-- **`class_fields_agree`'s loop refines `classFieldsAgree`, both outcomes** (twin side: con-ron's
`classFieldsAgree_spec`'s list induction; `class_nodes_agree` by `cna_ref`). -/
theorem cfaLoop_ref (k : Nat) (hk : k ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState) (j i : Word),
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs →
    decHL m fto.toNat ftl.toNat = some formerTys →
    fto.toNat + ftl.toNat ≤ iwTop m → DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms →
    mo.toNat + ml.toNat < 2 ^ 64 →
    decHL m fvo.toNat fvl.toNat = some fvs → fvo.toNat + fvl.toNat ≤ iwTop m →
    PSlR decNCN es eo el m → SPL decCF m ko.toNat kl.toNat ks → j ≤ kl →
    i.toNat + (kl.toNat - j.toNat) < 2 ^ 64 → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    ms.mapM (dMajor a.store) = some MsP → Frontend.denoteEList a.store fvs = some fvsP →
    es.mapM (dCtorNf a.store) = some esP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) → (∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) →
    RefE (VerdictCtx p) (cfaE.loop1 p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i)
      (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i.toNat (ks.drop j.toNat)) a
      (fun m' _ a' => CnaPost dn vis fe env m m' a') := by
  induction k with
  | zero => intros; rw [cfaE.loop1.eq_def]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a j i hC hA hbs hft hftb hms hmsb hfv hfvb hes hks hje hi hP hsh hftP hmsP hfvP hesP
    hformer hMs
  have hS := hC.stage
  have hsz := hS.iw.iwSize
  have hkl := hks.length
  have hjk : j.toNat ≤ kl.toNat := UInt64.le_iff_toNat_le.mp hje
  by_cases hj : j < kl
  rotate_left
  · rw [cfaE.loop1.arm4 p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i hj]
    have h1 : kl.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have : ks.drop j.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    exact RefE.ret rfl ⟨hC, IWGrow.refl _, hP, hA⟩
  have hjl : j.toNat < kl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := kl.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have hje1 : j + 1 ≤ kl := UInt64.le_iff_toNat_le.mpr (by omega)
  have hi' : (i + 1).toNat + (kl.toNat - (j + 1).toNat) < 2 ^ 64 := by omega
  have hdrop : ks.drop j.toNat = ks[j.toNat]'(by omega) :: ks.drop (j.toNat + 1) :=
    List.drop_eq_getElem_cons (by omega)
  rw [hdrop]
  -- the field's record
  obtain ⟨kq, hkq, hstab⟩ := hks.get j.toNat hjl
  have hkb : ko.toNat + kl.toNat ≤ iwTop m := hks.1
  have hkb64 := hS.lt64 hkb
  have hkw := iwN_rdW hkq (by omega)
  have hkoj : ko + j = UInt64.ofNat (ko.toNat + j.toNat) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
  have hkf : rdW (m.arr64 IW) (ko + j) = UInt64.ofNat kq := by rw [hkoj, hkw.1]
  have hcf := hstab.get
  rcases decCF_words hcf hsz with ⟨hord, h0⟩ | ⟨t, tl, hrec, h1, ht, htb, htl, htlb⟩
  · -- an ordinary field
    rw [cfaE.loop1.arm3 p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i hj
      (by rw [hkf, h0]; decide), cfaE.j1.arm1, hord, ConRon.Arena.classFieldsAgree]
    have := ih (by omega) m a (j + 1) (i + 1) hC hA hbs hft hftb hms
      hmsb hfv hfvb hes hks hje1 hi' hP hsh hftP hmsP hfvP hesP hformer hMs
    rw [hi1, hj1] at this; exact this
  -- a recursive field
  have hrd1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j)) = 1 := by rw [hkf]; exact h1
  have htT : (UInt64.ofNat t : Word).toNat = t := UInt64.toNat_ofNat_of_lt' htb
  have htlT : (UInt64.ofNat tl : Word).toNat = tl := UInt64.toNat_ofNat_of_lt' htlb
  have hfvb64 := hS.lt64 hfvb
  have key : ∀ (r0 : List Word) (m0 : Mem), cfaFv p k m fvo fvl i = some (r0, m0) →
      RefE (VerdictCtx p) (cfaE.j2 p k vis q fto ftl mo ml fvo fvl eo el ko kl j i (UInt64.ofNat t)
        (UInt64.ofNat tl) (r0.headD 0) m0)
      (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i.toNat
        (ks[j.toNat]'(by omega) :: ks.drop (j.toNat + 1))) a
      (fun m' _ a' => CnaPost dn vis fe env m m' a') := by
    intro r0 m0 hcf0
    rw [cfaE.j2.arm1]
    obtain ⟨a0, run0, hH0, hS0, hg0, hP0⟩ := cfaFv_ok P dn fe vis fvo fvl fvs hcf0 hS hfv hfvb64 hP
    obtain ⟨q0, hfv0⟩ := ConRon.Bridge.Inductives.exprGetD_spec fvs fvsP i.toNat a a0 _ hC.check.state
      hfvP run0
    have k0 := RcAt.pstep hC hS0 (cfaFv_afr P hcf0 hA) hP0 hg0 q0
    rw [hrec, ConRon.Arena.classFieldsAgree]
    refine RefE.bind_right run0 ?_
    -- `fvar_type_d`
    refine RefE.bindLift (fun _ => cfaE.k_fvar_type_d.none ..) fun r1 m1 c1 => ?_
    obtain ⟨s1, rfl, -, hw1⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
      (ftdF_spec p P.ad k _ [r0.headD 0]) c1
    obtain ⟨fty, a1, run1, hS1, hg1, hH1, hD1⟩ := ftdF_ok dn vis fe (r0.headD 0) hH0 _ _ a0 r1 hw1 hS0
    obtain ⟨e1, hfty⟩ := ConRon.Bridge.Inductives.fvarTypeD_run k0.stage.check.state hfv0 run1
    subst a1
    have k1 := RcAt.pstep k0.stage hS1 (ftdF_afr hw1 k0.abs)
      (k0.rc.fr (MFr.of_frame (ftdF_frame hw1) (by simp) (by simp))) hg1 (PStep.refl k0.stage.check.state)
    refine ⟨_, _, run1, ?_⟩
    rw [cfaE.k_fvar_type_d.arm1]
    -- `strip_pis`
    refine RefE.bindLift (fun _ => cfaE.k_strip_pis.none ..) fun r2 m2 c2 => ?_
    obtain ⟨s2, rfl, -, hok2, hS2, hg2, hd2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (stripPis_refines p P.strip dn vis fe (UInt64.ofNat tl) (r1.headD 0) hH1 k _ a0 hS1) c2
    obtain ⟨s2', hs2', -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (stripPis_specW p P.strip k _ (UInt64.ofNat tl) (r1.headD 0)) c2
    rw [hs2'] at hw2
    have run2 := AM.run_of_ok _ a0 hok2
    rw [htlT, hD1] at run2 hS2 hd2
    generalize hx2 : AM.res (stripPis tl fty) a0 = x2 at run2 hd2
    generalize ha2 : AM.st (stripPis tl fty) a0 = a2 at run2 hS2
    obtain ⟨e2, hbp⟩ := ConRon.Bridge.Inductives.stripPis_pstep k1.stage.check.state hfty run2
    rw [e2] at hS2 run2
    have k2 := RcAt.pstep k1.stage hS2 (stripF_afr (stripF_of_TW hw2) k1.abs)
      (k1.rc.fr (MFr.ofStripF (stripF_of_TW hw2))) hg2 (PStep.refl k1.stage.check.state)
    refine ⟨_, _, run2, ?_⟩
    rcases x2 with _ | ⟨teleB, leafE⟩
    · rw [cfaE.k_strip_pis.abort1 (hc1 := hd2)]; exact RefE.of_cls0 rfl
    obtain ⟨teleP, leafP, -, hteleB, hleaf⟩ := ConRon.Bridge.Inductives.denoteBP_some hbp
    obtain ⟨h21, ⟨hdl, hbl⟩, hlwH, hlwD⟩ := hd2
    rw [cfaE.k_strip_pis.arm1 (hc1 := by rw [h21]; decide)]
    simp only [getD_one, show (1 + 1 : Nat) = 2 from rfl, getD_two] at hdl hbl
    have hl3 : (r2.drop 3).headD 0 = r2.tail.tail.tail.headD 0 := by
      rcases r2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [hl3] at hlwH hlwD
    have k02 := (k0.trans k1).trans k2
    -- `target_major_at`
    refine RefE.bindSim (fun _ => cfaE.k_target_major_at.none ..) (tma_step P k2 htT
      (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) k02.grow) hmsb
      (ConRon.Bridge.Inductives.dMajor_ext.list k02.step.ext _ _ hmsP)) fun r3 tm m3 a3 _ _ ⟨k3, hTM, hmt⟩ => ?_
    rw [cfaE.k_target_major_at.arm1]
    -- `class_leaf_at`
    refine RefE.bindLift (fun _ => cfaE.k_class_leaf_at.none ..) fun r4 m4 c4 => ?_
    rcases k with _ | k'
    · obtain ⟨_, _, hf⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩) (invoke_exec_zero p _ _ _) c4
      exact hf.elim
    obtain ⟨s4, rfl, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (classLeafAt_refines p P.cla P.hv P.ad k' _ a3 dn vis fe (r3.headD 0) (r2.tail.tail.tail.headD 0) tm
        k3.stage.stage hlwH (hTM.get (decTM_mono _)) (decTM_lt_top hTM)) c4
    obtain ⟨s4', hs4', -, hw4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (leafAt_spec p P.cla P.hv P.ad k' _ (r3.headD 0) (r2.tail.tail.tail.headD 0)) c4
    simp only at hS4 hg4 hb4 hs4' hw4
    rw [hs4'] at hw4
    have run4 := AM.run_of_ok _ a3 hok4
    rw [hlwD] at run4 hS4 hb4
    generalize hx4 : AM.res (ConRon.Arena.classLeafAt tm leafE) a3 = b4 at run4 hb4
    generalize ha4 : AM.st (ConRon.Arena.classLeafAt tm leafE) a3 = a4 at run4 hS4
    obtain ⟨q4, -⟩ := ConRon.Bridge.Inductives.classLeafAt_spec tm _ leafE leafP a3 a4 b4
      k3.stage.check.state ⟨hmt, denote_ext hleaf k3.step.ext⟩ run4
    have k4 := RcAt.pstep k3.stage hS4 (leafAtW_afr hw4 k3.abs) (k3.rc.fr (leafAtW_mfr hw4)) hg4 q4
    refine ⟨_, _, run4, ?_⟩
    refine RefE.ofArms (fun h => cfaE.k_class_leaf_at.abort1 (hc1 := h) ..)
      (fun h => cfaE.k_class_leaf_at.arm1 (hc1 := h) ..)
      (RefE.guardIf (by decide) (fun hz => by rw [← hb4, hz]; rfl) (fun hb => by simpa [hb] using hb4.symm)
        fun _ _ => ?_)
    have k04 := k02.trans (k3.trans k4)
    have k34 := k3.trans k4
    have hlP : denoteE a4.store (decE (r2.tail.tail.tail.headD 0)) = some leafP := by
      rw [decE_eq, hlwD]; exact denote_ext hleaf k34.step.ext
    -- `class_nodes_agree`
    have h5 := cna_ref hq henv P.toCnaProg vis q fto ftl (r3.headD 0) (r2.tail.headD 0)
      (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0) fvo fvl i eo el bs formerTys tm teleB fvs
      (k' + 1) (by omega) s4.mem a4 es k4.stage k4.abs
      (hbs.grow k04.grow) (by rw [decHL_grow k04.grow hftb]; exact hft) (Nat.le_trans hftb k04.grow.iw)
      (hTM.grow (decTM_mono _) k4.grow) (HSl0.of (by rw [decHL_grow k34.grow hbl]; exact hdl)
        (Nat.le_trans hbl k34.grow.iw)) hlwH
      (by rw [decHL_grow k04.grow hfvb]; exact hfv) (Nat.le_trans hfvb k04.grow.iw)
      (hes.grow (fun q => decNCN_mono q) k04.grow) k4.rc
      (ConRon.Bridge.Inductives.dShape_ext k04.step.ext _ _ hsh) (denoteEList_ext k04.step.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext k4.step.ext _ _ hmt) (denoteEList_ext k34.step.ext _ _ hteleB)
      hlP (denoteEList_ext k04.step.ext _ _ hfvP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list k04.step.ext _ _ hesP) hformer
      (ConLeche.Cached.TargetMajScoped.getD hMs t)
    rw [decE_eq, hlwD] at h5
    refine RefE.bindE (fun _ => cfaE.k_class_nodes_agree.none ..) id h5 fun ⟨r5, m5⟩ u a5 run5 hR5 => ?_
    rw [cfaE.k_class_nodes_agree.arm1, cfaE.j1.arm1]
    have run5' := run5
    rw [← hlwD, ← decE_eq] at run5'
    obtain ⟨c6, -⟩ := ConRon.Bridge.Inductives.classNodesAgree_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
      henv bs pP formerTys formerTysP tm (MsP.getD t default) teleB teleP (decE (r2.tail.tail.tail.headD 0))
      leafP fvs fvsP i.toNat default hformer (ConLeche.Cached.TargetMajScoped.getD hMs t) es esP a4 _ u
      k4.stage.check
      ⟨ConRon.Bridge.Inductives.dShape_ext k04.step.ext _ _ hsh, denoteEList_ext k04.step.ext _ _ hftP,
        ConRon.Bridge.Inductives.dMajor_ext k4.step.ext _ _ hmt, denoteEList_ext k34.step.ext _ _ hteleB,
        hlP, denoteEList_ext k04.step.ext _ _ hfvP,
        ConRon.Bridge.Inductives.dCtorNf_ext.list k04.step.ext _ _ hesP⟩ run5'
    have c06 := (k04.step.toCore hC.check).trans c6
    have hg05 : IWGrow m m5 := k04.grow.trans hR5.grow
    have := ih (by omega) m5 a5 (j + 1) (i + 1) hR5.stage hR5.abs
      (hbs.grow hg05)
      (by rw [decHL_grow hg05 hftb]; exact hft) (by have := hg05.iw; omega)
      (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg05) hmsb
      (by rw [decHL_grow hg05 hfvb]; exact hfv) (by have := hg05.iw; omega)
      (hes.grow (fun q => decNCN_mono q) hg05) (hks.grow hg05) hje1 hi' hR5.rc
      (ConRon.Bridge.Inductives.dShape_ext c06.ext _ _ hsh) (denoteEList_ext c06.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext.list c06.ext _ _ hmsP) (denoteEList_ext c06.ext _ _ hfvP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list c06.ext _ _ hesP) hformer hMs
    rw [hi1, hj1] at this
    exact RefE.mono this fun _ _ _ h => ⟨h.stage, hg05.trans h.grow, h.rc, h.abs⟩
  by_cases hif : i < fvl
  · rw [cfaE.loop1.arm1 p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i hj hrd1 hif, hkf, ht, htl]
    exact key [rdW (m.arr64 IW) (fvo + i)] m (cfaFv_in p k m fvo fvl i hif)
  · rw [cfaE.loop1.arm2 p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i hj hrd1 hif, hkf, ht, htl]
    rcases h0 : callW p k "intern_bvar" [0] m with _ | ⟨r0, m0⟩
    · rw [liftE_none, cfaE.k_intern_bvar.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, cfaE.k_intern_bvar.arm1]
    exact key r0 m0 (by rw [cfaFv_out p k m fvo fvl i hif]; exact h0)

include hq henv P in
/-- **`class_fields_agree` refines `classFieldsAgree`, both outcomes** (`cfaLoop_ref` from the
first field). -/
theorem cfa_ref (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (i0 : Word)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hfv : decHL m fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hes : PSlR decNCN es eo el m) (hks : SPL decCF m ko.toNat kl.toNat ks)
    (hi : i0.toNat + kl.toNat < 2 ^ 64) (hP : RcMR m)
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP) (hfvP : Frontend.denoteEList a.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (cfaE p n m vis q fto ftl mo ml fvo fvl eo el i0 ko kl)
      (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a
      (fun v _ a' => CnaPost dn vis fe env m v.2 a') := by
  rcases n with _ | n
  · rw [cfaE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cfaE.arm1]
  have h := cfaLoop_ref hq henv P vis q fto ftl mo ml fvo fvl eo el ko kl bs formerTys ms fvs es ks
    (n + 1) hn m a 0 i0 hC hA hbs hft hftb hms hmsb hfv hfvb hes hks UInt64.zero_le
    (by simpa using hi) hP hsh hftP hmsP hfvP hesP hformer hMs
  simp only [UInt64.toNat_zero, List.drop_zero] at h
  rcases h1 : cfaE.loop1 p (n + 1) m vis q fto ftl mo ml fvo fvl eo el ko kl 0 i0 with e1 | m1 <;>
    rw [h1] at h
  · rw [cfaE.k_loop1.none]; exact h
  · rw [cfaE.k_loop1.arm1]; exact h

include hq henv P in
/-- **`class_fields_agree` refines `classFieldsAgree`** under `StageC` (the knot's core calls; the
inputs' denotations and scoping as con-ron's `classFieldsAgree_spec` asks). -/
@[refines ConRon.Arena.classFieldsAgree]
theorem classFieldsAgree_refinesC (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (i0 : Word)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hfv : decHL s₀.mem fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hes : PSlR decNCN es eo el s₀.mem) (hks : SPL decCF s₀.mem ko.toNat kl.toNat ks)
    (hi : i0.toNat + kl.toNat < 2 ^ 64) (hP : RcMR s₀.mem)
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP) (hfvP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hesP : es.mapM (dCtorNf a₀.store) = some esP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_agree"
      [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, i0, ko, kl]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cfaE_spec p P n s₀ vis q fto ftl mo ml fvo fvl eo el i0 ko kl)
    (cfa_ref hq henv P vis q fto ftl mo ml fvo fvl eo el ko kl bs formerTys ms fvs es ks n hn s₀.mem a₀ i0
      hC hA hbs hft hftb hms hmsb hfv hfvb hes hks hi hP hsh hftP hmsP hfvP hesP hformer hMs)) ?_
  rintro r s' ⟨hl', u, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind

end
