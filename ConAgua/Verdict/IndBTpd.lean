import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndT.RecCheckTpd
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecCheckSpec.Tpd
import ConAgua.Arena.RecCheckSpec.TmFields
import ConAgua.Verdict.VCtx
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `target_params_def_eq` and its head step: one model and one refinement for both outcomes

`pdsE` (`l_model … unified`): the closedness reads (`bvar_b`, `fvar_b`), the canon forms and the
member abstractions (`target_canon_params`, `target_abs`) outside the verdict closure, through their
`Option` models; the knot's `infer_type_core` twice and `is_def_eq_core` through their runs. `pdeE`
calls `pdsE` and itself. `pds_ref` and `pde_ref` refine `tpStep` and `targetParamsDefEq` for both
outcomes; `pde_ref`'s ok half is `targetParamsDefEq_refinesC` and `target_class_match`'s refinement
(`tcm_ref`) takes both halves.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model pdsE_spec (p : Prog) (hL : TpLook p)
  fns [hL.step ↦ pdsE]
  specs [bvarBL_spec p hL.bvb n, fvbF_spec p hL.hf n, tcp_specF p hL.rc n, ta_specF p hL.ta n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model pdeE_spec (p : Prog) (hL : TpLook p)
  fns [hL.tpd ↦ pdeE]
  specs [pdsE_spec p hL n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `target_params_def_eq` gives besides the twin's result `c` (from `m`): the result word,
the stage invariant, the growth. -/
structure TpdPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : Word) (m' : Mem) (c : Bool) (a' : AState) : Prop where
  res : (r != 0) = c
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'

/-- The head step's: `TpdPost`, and the twin's core step from `a`. -/
structure PdsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : Word) (m' : Mem) (c : Bool) (a' : AState) : Prop
    extends TpdPost dn vis fe env m r m' c a' where
  core : CoreStep V env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_params_def_eq_step` refines `tpStep`, both outcomes** (twin side: con-ron's
`targetParamsDefEq_spec`, the `cons` arm): the closedness reads (`tpClosed_pstep`), the canon forms
(`targetCanonParams_spec`), the member abstractions (`targetAbs_spec`), then the knot
(`inferC_rsim`, `isDefEqC_rsim`; their errors are the core stubs' claims). -/
theorem pds_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {d no nl lvls ho hl pfo pfl x y : Word} {names : List NIdx} {holes pfvs : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hx : H x) (hy : H y) (hlv : H lvls)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hP : RcMR m)
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level} {holesP pfvsP : List ConLeche.Expr}
    {xP yP : ConLeche.Expr}
    (hTA : TAArgs names (decI lvls) holes namesP lvlsP holesP a.store)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (hxP : denoteE a.store (decE x) = some xP) (hyP : denoteE a.store (decE y) = some yP)
    (habs : ∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e))
    (hpw : ∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) :
    RefE (VerdictCtx p) (pdsE p n m vis d no nl lvls ho hl pfo pfl x y)
      (tpStep fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y)) a
      (fun v c a' => PdsPost dn vis fe env m a v.1 v.2 c a') := by
  cases n with
  | zero => rw [pdsE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [pdsE.arm1]
  have hS := hC.stage
  have hlen := ConRon.Bridge.Inductives.denoteEList_length hpfP
  have hlen' : pfvs.length = pfl.toNat := hpf.len
  unfold tpStep
  -- a `false` from the closedness reads answers `0` at once
  have early : ∀ {m' : Mem} {a' : AState},
      (tpClosed pfvs (decE x) (decE y)).run a = .ok (false, a') → StageR dn vis fe m' a' →
      IWGrow m m' → RcMR m' → AFr m m' →
      RefE (VerdictCtx p) (.ok ((0 : Word), m') : Except Err (Word × Mem))
        (do let closed ← tpClosed pfvs (decE x) (decE y)
            if !closed then pure false else tpRest fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y))
        a (fun v c a' => PdsPost dn vis fe env m a v.1 v.2 c a') := by
    intro m' a' hcl hS' hg hP' hF
    obtain ⟨q, -⟩ := tpClosed_pstep hC.check.state hxP hyP hcl
    exact RefE.bind_right hcl (RefE.ite_pos rfl
      (RefE.ret rfl ⟨⟨rfl, hC.of_pstep hS' (hF hA) q, hg, hP', hF hA⟩, q.toCore hC.check⟩))
  -- `bvar_b(a)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun b1 m1 h1 => ?_
  obtain ⟨a1, r1, hS1, hg1, hf1⟩ := bvbW_stageC dn fe vis hS n x b1 hx h1
  have hP1 := hP.fr hf1
  by_cases hb1 : b1 ≠ 0
  · rw [pdsE.k_bvar_b.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb1]
    have e1 : (b1.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hb1 (UInt64.toNat_inj.mp (by simpa using h0))
    exact early (by simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, ite_true]; rfl)
      hS1 hg1 hP1 (bvbW_afr h1)
  rw [pdsE.k_bvar_b.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using hb1)]
  have e1 : (b1.toNat != 0) = false := by simp at hb1; simp [hb1]
  -- `bvar_b(b)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun b2 m2 h2 => ?_
  obtain ⟨a2, r2, hS2, hg2, hf2⟩ := bvbW_stageC dn fe vis hS1 n y b2 hy h2
  have hP2 := hP1.fr hf2
  by_cases hb2 : b2 ≠ 0
  · rw [pdsE.k_bvar_b_2.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb2]
    have e2 : (b2.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hb2 (UInt64.toNat_inj.mp (by simpa using h0))
    exact early (by simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, ite_true,
      Bool.false_eq_true, ite_false]; rfl) hS2 (hg1.trans hg2) hP2 ((bvbW_afr h1).trans (bvbW_afr h2))
  rw [pdsE.k_bvar_b_2.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using hb2)]
  have e2 : (b2.toNat != 0) = false := by simp at hb2; simp [hb2]
  -- `fvar_b(a)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r3 m3 h3 => ?_
  obtain ⟨k3, a3, run3, hS3, hg3, hd3⟩ := fvbF_ok dn vis fe CWF x hx m2 m3 a2 r3 h3 hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofFvbF h3)
  have hF3 := ((bvbW_afr h1).trans (bvbW_afr h2)).trans (fvbF_afr h3)
  by_cases hc3 : pfl < r3.headD 0
  · rw [pdsE.k_fvar_b.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc3]
    have e3 : k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
    exact early (by simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3,
      ite_true, Bool.false_eq_true, ite_false]; rfl) hS3 ((hg1.trans hg2).trans hg3) hP3 hF3
  rw [pdsE.k_fvar_b.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc3]
  have e3 : ¬ k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
  -- `fvar_b(b)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  obtain ⟨k4, a4, run4, hS4, hg4, hd4⟩ := fvbF_ok dn vis fe CWF y hy m3 m4 a3 r4 h4 hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofFvbF h4)
  have hF4 := hF3.trans (fvbF_afr h4)
  have hg4' := ((hg1.trans hg2).trans hg3).trans hg4
  by_cases hc4 : pfl < r4.headD 0
  · rw [pdsE.k_fvar_b_2.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc4]
    have e4 : decide (k4 ≤ pfvs.length) = false := by
      rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
    exact early (by simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3,
      run4, e4, Bool.false_eq_true, ite_false]; rfl) hS4 hg4' hP4 hF4
  rw [pdsE.k_fvar_b_2.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc4]
  have e4 : decide (k4 ≤ pfvs.length) = true := by
    rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
  have hcl : (tpClosed pfvs (decE x) (decE y)).run a = .ok (true, a4) := by
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, run4, e4,
      Bool.false_eq_true, ite_false]; rfl
  obtain ⟨q, hc⟩ := tpClosed_pstep hC.check.state hxP hyP hcl
  have hA4 := hF4 hA
  have hC4 := hC.of_pstep hS4 hA4 q
  refine RefE.bind_right hcl (RefE.ite_neg (by simp) ?_)
  -- the rest (`tpRest`)
  have hc' := hc.symm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨-, -⟩, hfx⟩, hfy⟩ := hc'
  rw [hlen] at hfx hfy
  have hwx : ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP
      (ConLeche.targetCanonParams pfvsP xP)) :=
    habs _ (ConLeche.targetCanonParams_WScoped hpw xP
      (ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq xP ▸ hfx)))
  have hwy : ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP
      (ConLeche.targetCanonParams pfvsP yP)) :=
    habs _ (ConLeche.targetCanonParams_WScoped hpw yP
      (ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq yP ▸ hfy)))
  unfold tpRest
  -- the canon form of `x`
  refine RefE.bindLift (fun _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨a5, run5, hH5, hS5, hg5, hP5⟩ := tcpF_ok dn fe vis n h5 hC4.stage (hpf.grow hg4') hx hP4
  refine ⟨_, _, run5, ?_⟩
  dsimp only [pdsE.k_target_canon_params]
  have hA5 := tcpF_afr h5 hA4
  obtain ⟨q5, hR5⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE x) xP a4 a5 _
    hC4.check.state hC4.check.pins ⟨denoteEList_ext q.ext _ _ hpfP, denote_ext hxP q.ext⟩ run5
  have hC5 := hC4.of_pstep hS5 hA5 q5
  have hg45 := hg4'.trans hg5
  -- its abstraction
  refine RefE.bindLift (fun _ => rfl) fun av m6 h6 => ?_
  obtain ⟨a6, run6, hS6, hg6, hP6⟩ := taF_ok dn fe vis n h6 hS5 hH5 hlv
    (by rw [decHL_grow hg45 hnob]; exact hno) (by have := hg45.iw; omega)
    (by rw [decHL_grow hg45 hhob]; exact hho) (by have := hg45.iw; omega) hP5
  refine ⟨_, _, run6, ?_⟩
  dsimp only [pdsE.k_target_abs]
  refine RefE.abort0 rfl fun hb6 => ?_
  have hA6 := taF_afr h6 hA5
  obtain ⟨q6, hR6⟩ := ConRon.Bridge.Inductives.targetAbs_spec names (decI lvls) holes namesP lvlsP
    holesP (decE (r5.headD 0)) _ a5 a6 _ hC5.check.state ⟨(hTA.ext q.ext).ext q5.ext, hR5⟩ run6
  have hC6 := hC5.of_pstep hS6 hA6 q6
  have hav : H av := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb6; simp at hb6; omega
  have hg46 := hg45.trans hg6
  have q56 := q5.trans q6
  -- the canon form of `y`
  refine RefE.bindLift (fun _ => rfl) fun r7 m7 h7 => ?_
  obtain ⟨a7, run7, hH7, hS7, hg7, hP7⟩ := tcpF_ok dn fe vis n h7 hS6 (hpf.grow hg46) hy hP6
  refine ⟨_, _, run7, ?_⟩
  dsimp only [pdsE.k_target_canon_params_2]
  have hA7 := tcpF_afr h7 hA6
  obtain ⟨q7, hR7⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE y) yP a6 a7 _
    hC6.check.state hC6.check.pins ⟨denoteEList_ext (q.ext.trans q56.ext) _ _ hpfP,
      denote_ext hyP (q.ext.trans q56.ext)⟩ run7
  have hC7 := hC6.of_pstep hS7 hA7 q7
  have hg47 := hg46.trans hg7
  -- its abstraction
  refine RefE.bindLift (fun _ => rfl) fun bv m8 h8 => ?_
  obtain ⟨a8, run8, hS8, hg8, hP8⟩ := taF_ok dn fe vis n h8 hS7 hH7 hlv
    (by rw [decHL_grow hg47 hnob]; exact hno) (by have := hg47.iw; omega)
    (by rw [decHL_grow hg47 hhob]; exact hho) (by have := hg47.iw; omega) hP7
  refine ⟨_, _, run8, ?_⟩
  dsimp only [pdsE.k_target_abs_2]
  refine RefE.abort0 rfl fun hb8 => ?_
  have hA8 := taF_afr h8 hA7
  obtain ⟨q8, hR8⟩ := ConRon.Bridge.Inductives.targetAbs_spec names (decI lvls) holes namesP lvlsP
    holesP (decE (r7.headD 0)) _ a7 a8 _ hC7.check.state
    ⟨hTA.ext ((q.trans q56).trans q7).ext, hR7⟩ run8
  have hC8 := hC7.of_pstep hS8 hA8 q8
  have hbv : H bv := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb8; simp at hb8; omega
  have q48 := (q56.trans q7).trans q8
  have hg48 := hg47.trans hg8
  have hR6' := denote_ext hR6 (q7.trans q8).ext
  have c48 : CoreStep V env fe a a8 := (q.trans q48).toCore hC.check
  by_cases he : av = bv
  · subst he
    rw [ite_eq_left rfl]
    exact RefE.ite_pos (by simp) (RefE.ret rfl ⟨⟨rfl, hC8, hg48, hP8, hA8⟩, c48⟩)
  rw [ite_eq_right he]
  have hne : (decE av == decE bv) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he (decI_inj hav hbv e)
  refine RefE.ite_neg (by simp [hne]) ?_
  -- the knot: `infer_type_core` twice, then `is_def_eq_core`
  simp only [decE_eq]
  refine RefE.bindCall (fun _ => rfl)
    (fun hV _ h9 => hV.core.inferTypeCore n (by omega) hC8.stageT d av hav _ h9)
    (inferC_rsim hq henv n (by omega) hC8 hA8 d av hav (by rw [← decE_eq]; exact hR6') hwx)
    fun r9 m9 _ a9 h9 _ ⟨hC9, hg9, _, hA9, c9, _⟩ => ?_
  dsimp only [pdsE.k_infer_type_core]
  refine RefE.bindCall (fun _ => rfl)
    (fun hV _ h10 => hV.core.inferTypeCore n (by omega) hC9.stageT d bv hbv _ h10)
    (inferC_rsim hq henv n (by omega) hC9 hA9 d bv hbv (by rw [← decE_eq]; exact denote_ext hR8 c9.ext)
      hwy)
    fun r10 m10 _ a10 h10 _ ⟨hC10, hg10, _, hA10, c10, _⟩ => ?_
  dsimp only [pdsE.k_infer_type_core_2]
  rcases h11 : callE p n "is_def_eq_core" [vis, d, av, bv] m10 with e11 | ⟨r11, m11⟩ <;>
    dsimp only [pdsE.k_is_def_eq_core]
  · exact fun hV => hV.core.isDefEqCore n (by omega) hC10.stageT d av bv hav hbv _ h11
  obtain ⟨c, a11, run11, hC11, hg11, hd11, hA11, c11⟩ :=
    isDefEqC_rsim hq henv n (by omega) hC10 hA10 d av bv hav hbv
      (by rw [← decE_eq]; exact denote_ext hR6' (c9.trans c10).ext)
      (by rw [← decE_eq]; exact denote_ext hR8 (c9.trans c10).ext) hwx hwy _ (callW_of_callE h11)
  exact RefE.ret run11 ⟨⟨by simpa [decBool] using hd11, hC11, ((hg48.trans hg9).trans hg10).trans hg11,
    ((hP8.fr (MFr.ofCore hq.closed (by decide) (callW_of_callE h9))).fr
      (MFr.ofCore hq.closed (by decide) (callW_of_callE h10))).fr
      (MFr.ofCore hq.closed (by decide) (callW_of_callE h11)), hA11⟩,
    ((c48.trans c9).trans c10).trans c11⟩

include hq henv in
/-- **`target_params_def_eq` refines `targetParamsDefEq`, both outcomes** (twin side: con-ron's
`targetParamsDefEq_spec`'s list induction; the head step `pds_ref`). -/
theorem pde_ref (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m : Mem} {a : AState} {d no nl lvls ho hl pfo pfl ao al bo bl : Word}
    {names : List NIdx} {holes pfvs as bs : List EIdx}
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level}
    {holesP pfvsP asP bsP : List ConLeche.Expr},
    StageC dn vis fe env m a → AbsOK m → H lvls →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m ho.toNat hl.toNat = some holes → ho.toNat + hl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m ao al as → HSl0 m bo bl bs → RcMR m →
    TAArgs names (decI lvls) holes namesP lvlsP holesP a.store →
    Frontend.denoteEList a.store pfvs = some pfvsP →
    Frontend.denoteEList a.store as = some asP → Frontend.denoteEList a.store bs = some bsP →
    (∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e)) →
    (∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) →
    RefE (VerdictCtx p) (pdeE p n m vis d no nl lvls ho hl pfo pfl ao al bo bl)
      (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a
      (fun v c a' => TpdPost dn vis fe env m v.1 v.2 c a') := by
  induction n with
  | zero => intros; rw [pdeE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n ih =>
  intro m a d no nl lvls ho hl pfo pfl ao al bo bl names holes pfvs as bs namesP lvlsP holesP
    pfvsP asP bsP hC hA hlv hno hnob hho hhob hpf has hbs hP hTA hpfP hasP hbsP habs hpw
  have hS := hC.stage
  have hlt : ∀ {x : Nat}, x ≤ iwTop m → x < 2 ^ 64 := fun h => hS.lt64 h
  by_cases hal : al = 0
  · rw [pdeE.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hal]
    subst hal
    have : as = [] := by have := has.len; simpa using this
    subst this
    refine RefE.ret (by rw [tpd_nil]; rfl) ⟨?_, hC, IWGrow.refl _, hP, hA⟩
    have hbl : bs.length = bl.toNat := hbs.len
    by_cases hb0 : bl = 0
    · subst hb0; have : bs = [] := by simpa using hbl
      subst this; simp
    · have : bs ≠ [] := fun e => hb0 (UInt64.toNat_inj.mp (by rw [← hbl, e]; rfl))
      simp [hb0, this]
  by_cases hbl : bl = 0
  · rw [pdeE.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hal hbl]
    subst hbl
    have : bs = [] := by have := hbs.len; simpa using this
    subst this
    obtain ⟨w, as', rfl, -, -, -⟩ := decHL_cons has.1 hal (hlt (has.2.resolve_left hal))
    exact RefE.ret (by rw [tpd_nilr]; rfl) ⟨rfl, hC, IWGrow.refl _, hP, hA⟩
  rw [pdeE.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hal hbl]
  have hasb : ao.toNat + al.toNat ≤ iwTop m := has.2.resolve_left hal
  have hbsb : bo.toNat + bl.toNat ≤ iwTop m := hbs.2.resolve_left hbl
  obtain ⟨x, as', rfl, ex, hx, has'⟩ := decHL_cons has.1 hal (hlt hasb)
  obtain ⟨y, bs', rfl, ey, hy, hbs'⟩ := decHL_cons hbs.1 hbl (hlt hbsb)
  obtain ⟨xP, asP', hxP, hasP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hasP
  obtain ⟨yP, bsP', hyP, hbsP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hbsP
  rw [ex, ey]
  obtain ⟨ea1, el1, hal0⟩ := slice_step hal (hlt hasb)
  obtain ⟨eb1, ebl1, hbl0⟩ := slice_step hbl (hlt hbsb)
  rw [tpd_cons]
  simp only [← decE_eq]
  refine RefE.bindE (fun _ => pdeE.k_target_params_def_eq_step.none ..) id
    (pds_ref hq henv n (by omega) hC hA hx hy hlv hno hnob hho hhob hpf hP hTA hpfP hxP hyP habs hpw)
    fun ⟨r1, m1⟩ c a1 _ hR1 => ?_
  dsimp only at hR1
  by_cases hr1 : r1 = 0
  · rw [pdeE.k_target_params_def_eq_step.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr1]
    have : c = false := by rw [← hR1.res, hr1]; rfl
    subst this
    exact RefE.ite_neg (by simp) (RefE.ret rfl ⟨rfl, hR1.stage, hR1.grow, hR1.rc, hR1.abs⟩)
  rw [pdeE.k_target_params_def_eq_step.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr1]
  have : c = true := by rw [← hR1.res]; simpa using hr1
  subst this
  refine RefE.ite_pos rfl ?_
  have hg1 := hR1.grow
  have hgo := hg1.iw
  have h2 := ih (by omega) (m := m1) (ao := ao + 1) (al := al - 1) (bo := bo + 1) (bl := bl - 1)
    hR1.stage hR1.abs hlv
    (by rw [decHL_grow hg1 hnob]; exact hno) (by omega)
    (by rw [decHL_grow hg1 hhob]; exact hho) (by omega)
    (hpf.grow hg1)
    (HSl0.of (by rw [decHL_grow hg1 (by rw [ea1, el1]; omega)]; exact has') (by rw [ea1, el1]; omega))
    (HSl0.of (by rw [decHL_grow hg1 (by rw [eb1, ebl1]; omega)]; exact hbs') (by rw [eb1, ebl1]; omega))
    hR1.rc (hTA.ext hR1.core.ext) (denoteEList_ext hR1.core.ext _ _ hpfP)
    (denoteEList_ext hR1.core.ext _ _ hasP') (denoteEList_ext hR1.core.ext _ _ hbsP') habs hpw
  exact RefE.mono h2 fun _ _ _ hR2 => ⟨hR2.res, hR2.stage, hg1.trans hR2.grow, hR2.rc, hR2.abs⟩

include hq henv in
/-- **`target_params_def_eq` refines `targetParamsDefEq`** under `StageC` (`pde_ref`'s ok half; the
knot's core calls; the inputs' denotations and scoping as con-ron's `targetParamsDefEq_spec` asks). -/
@[refines ConRon.Arena.targetParamsDefEq]
theorem targetParamsDefEq_refinesC (hL : TpLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (d no nl lvls ho hl pfo pfl ao al bo bl : Word)
    (names : List NIdx) (holes pfvs as bs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hlv : H lvls)
    (hno : decHL s₀.mem no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (has : HSl0 s₀.mem ao al as) (hbs : HSl0 s₀.mem bo bl bs)
    (hP : RcMR s₀.mem)
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level}
    {holesP pfvsP asP bsP : List ConLeche.Expr}
    (hTA : TAArgs names (decI lvls) holes namesP lvlsP holesP a₀.store)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (hasP : Frontend.denoteEList a₀.store as = some asP)
    (hbsP : Frontend.denoteEList a₀.store bs = some bsP)
    (habs : ∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e))
    (hpw : ∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (pdeE_spec p hL n s₀ vis d no nl lvls ho hl pfo pfl ao al bo bl)
    (pde_ref hq henv n hn hC hA hlv hno hnob hho hhob hpf has hbs hP hTA hpfP hasP hbsP habs
      hpw)) ?_
  rintro r s' ⟨hl', c, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hR.res, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind

end
