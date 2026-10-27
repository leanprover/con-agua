import ConAgua.Arena.IndT.RecCheckTpd
import ConAgua.Checker.NoVerdictFns
import ConAgua.Verdict.DeclValE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# Error refinement of `target_params_def_eq_step` (lane `verdicts-b`, helper `ib`)

The closedness reads, the canon forms and member abstractions are core-free (class `0` on error);
the verdicts are the knot's: `infer_type_core` twice and `is_def_eq_core`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model pdsE_spec (p : Prog) (hf : p.lookup "target_params_def_eq_step" = some targetParamsDefEqStep)
  fns [hf ↦ pdsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model pdeE_spec (p : Prog) (hf : p.lookup "target_params_def_eq" = some targetParamsDefEq)
  fns [hf ↦ pdeE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`target_params_def_eq_step`'s error claim** (the hypotheses of `pdsW_okC`, and the core
stubs' error claims): a failing call of class `1`/`2` is one of the knot's. -/
theorem pdsStep_claim (L : TpLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a : AState)
    {d no nl lvls ho hl pfo pfl x y : Word} {names : List NIdx}
    {holes pfvs : List EIdx}
    (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem) (hx : H x) (hy : H y) (hlv : H lvls)
    (hno : decHL s₀.mem no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hP : RcMR s₀.mem)
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level} {holesP pfvsP : List ConLeche.Expr}
    {xP yP : ConLeche.Expr}
    (hTA : TAArgs names (decI lvls) holes namesP lvlsP holesP a.store)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (hxP : denoteE a.store (decE x) = some xP) (hyP : denoteE a.store (decE y) = some yP)
    (habs : ∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e))
    (hpw : ∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) :
    CoreSpecE p n "target_params_def_eq_step" [vis, d, no, nl, lvls, ho, hl, pfo, pfl, x, y]
      (tpStep fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y)) s₀ a := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (pdsE_spec p L.step n ⟨s₀.mem, Locals.init []⟩ vis d no nl lvls ho hl pfo pfl
    x y) hc' (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [pdsE.eq_def] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [pdsE.arm1] at hW
  have hS := hC.stage
  have hlen := ConRon.Bridge.Inductives.denoteEList_length hpfP
  have hlen' : pfvs.length = pfl.toNat := hpf.len
  unfold tpStep
  -- `bvar_b(a)`
  cases h1 : callE p n "bvar_b" [CWF, x] s₀.mem with
  | error e1 =>
    rw [h1, pdsE.k_bvar_b.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (bvarBL_spec p L.bvb n ⟨s₀.mem, Locals.init []⟩ CWF x)
    (callW_of_callE h1)
  subst hs1
  obtain ⟨a1, rr1, hS1, hg1, hf1⟩ := bvbW_stageC dn fe vis hS n x (r1.headD 0) hx h1m
  have hP1 := hP.fr hf1
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [h1, pdsE.k_bvar_b.arm1 p n vis d no nl lvls ho hl pfo pfl x y r1 s1.mem hb1] at hW
    cases hW
  have hb1' : r1.headD 0 = 0 := by simpa using hb1
  rw [h1, pdsE.k_bvar_b.arm2 p n vis d no nl lvls ho hl pfo pfl x y r1 s1.mem hb1'] at hW
  have e1 : ((r1.headD 0).toNat != 0) = false := by rw [hb1']; decide
  -- `bvar_b(b)`
  cases h2 : callE p n "bvar_b" [CWF, y] s1.mem with
  | error e2 =>
    rw [h2, pdsE.k_bvar_b_2.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (bvarBL_spec p L.bvb n ⟨s1.mem, Locals.init []⟩ CWF y)
    (callW_of_callE h2)
  subst hs2
  obtain ⟨a2, rr2, hS2, hg2, hf2⟩ := bvbW_stageC dn fe vis hS1 n y (r2.headD 0) hy h2m
  have hP2 := hP1.fr hf2
  by_cases hb2 : r2.headD 0 ≠ 0
  · rw [h2, pdsE.k_bvar_b_2.arm1 p n vis d no nl lvls ho hl pfo pfl x y r2 s2.mem hb2] at hW
    cases hW
  have hb2' : r2.headD 0 = 0 := by simpa using hb2
  rw [h2, pdsE.k_bvar_b_2.arm2 p n vis d no nl lvls ho hl pfo pfl x y r2 s2.mem hb2'] at hW
  have e2 : ((r2.headD 0).toNat != 0) = false := by rw [hb2']; decide
  -- `fvar_b(a)`
  cases h3 : callE p n "fvar_b" [CWF, x] s2.mem with
  | error e3 =>
    rw [h3, pdsE.k_fvar_b.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (fvbF_spec p L.hf n ⟨s2.mem, Locals.init []⟩ [CWF, x])
    (callW_of_callE h3)
  subst hs3
  obtain ⟨k3, a3, run3, hS3, hg3, hd3⟩ := fvbF_ok dn vis fe CWF x hx s2.mem s3.mem a2 r3 h3m hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofFvbF h3m)
  by_cases hc3 : pfl < r3.headD 0
  · rw [h3, pdsE.k_fvar_b.arm1 p n vis d no nl lvls ho hl pfo pfl x y r3 s3.mem hc3] at hW
    cases hW
  rw [h3, pdsE.k_fvar_b.arm2 p n vis d no nl lvls ho hl pfo pfl x y r3 s3.mem hc3] at hW
  have e3 : ¬ k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
  -- `fvar_b(b)`
  cases h4 : callE p n "fvar_b" [CWF, y] s3.mem with
  | error e4 =>
    rw [h4, pdsE.k_fvar_b_2.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, -, h4m⟩ := triple_of_callW (fvbF_spec p L.hf n ⟨s3.mem, Locals.init []⟩ [CWF, y])
    (callW_of_callE h4)
  subst hs4
  obtain ⟨k4, a4, run4, hS4, hg4, hd4⟩ := fvbF_ok dn vis fe CWF y hy s3.mem s4.mem a3 r4 h4m hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofFvbF h4m)
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  by_cases hc4 : pfl < r4.headD 0
  · rw [h4, pdsE.k_fvar_b_2.arm1 p n vis d no nl lvls ho hl pfo pfl x y r4 s4.mem hc4] at hW
    cases hW
  rw [h4, pdsE.k_fvar_b_2.arm2 p n vis d no nl lvls ho hl pfo pfl x y r4 s4.mem hc4] at hW
  have e4 : decide (k4 ≤ pfvs.length) = true := by
    rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
  have hclosed : (tpClosed pfvs (decE x) (decE y)).run a = .ok (true, a4) := by
    simp only [tpClosed, StateT.run_bind, rr1, except_ok_bind, e1, rr2, e2, run3, e3, run4, e4,
      Bool.false_eq_true, ite_false]; rfl
  have hA4 : AbsOK s4.mem := ((((bvbW_afr h1m).trans (bvbW_afr h2m)).trans (fvbF_afr h3m)).trans
    (fvbF_afr h4m)) hA
  obtain ⟨q, -⟩ := tpClosed_pstep hC.check.state hxP hyP hclosed
  have hC4 := hC.of_pstep hS4 hA4 q
  refine ErrClaim.bind_right hclosed (ErrClaim.ite_neg (by simp) ?_)
  have hg14' : IWGrow s₀.mem s4.mem := hg14
  -- the rest
  obtain ⟨q, hc⟩ := tpClosed_pstep hC.check.state hxP hyP hclosed
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
  cases h5 : callE p n "target_canon_params" [pfo, pfl, x] s4.mem with
  | error e5 =>
    rw [h5, pdsE.k_target_canon_params.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h5)
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, h5m⟩ := triple_of_callW (tcp_specF p L.rc n ⟨s4.mem, Locals.init []⟩ pfo pfl x)
    (callW_of_callE h5)
  subst hs5
  dsimp only at h5m
  obtain ⟨a5, run5, hH5, hS5, hg5, hP5⟩ := tcpF_ok dn fe vis n h5m hS4 (hpf.grow hg14') hx hP4
  have hA5 := tcpF_afr h5m hA4
  obtain ⟨q5, hR5⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE x) xP a4 a5 _
    hC4.check.state hC4.check.pins ⟨denoteEList_ext q.ext _ _ hpfP, denote_ext hxP q.ext⟩ run5
  have hC5 := hC4.of_pstep hS5 hA5 q5
  refine ErrClaim.bind_right run5 ?_
  -- its abstraction
  rw [h5, pdsE.k_target_canon_params.arm1] at hW
  cases h6 : callE p n "target_abs" [no, nl, lvls, ho, hl, r5.headD 0] s5.mem with
  | error e6 =>
    rw [h6, pdsE.k_target_abs.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h6)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  by_cases hb6 : 4294967296 ≤ r6.headD 0
  · rw [h6, pdsE.k_target_abs.abort1 p n vis d no nl lvls ho hl pfo pfl y r6 m6 hb6] at hW
    cases hW; exact absurd rfl hk0
  rw [h6, pdsE.k_target_abs.arm1 p n vis d no nl lvls ho hl pfo pfl y r6 m6 hb6] at hW
  obtain ⟨s6, hs6, -, h6m⟩ := triple_of_callW (ta_specF p L.ta n ⟨s5.mem, Locals.init []⟩ no nl lvls ho hl
    (r5.headD 0)) (callW_of_callE h6)
  subst hs6
  dsimp only at h6m
  obtain ⟨a6, run6, hS6, hg6, hP6⟩ := taF_ok dn fe vis n h6m hS5 hH5 hlv
    (by rw [decHL_grow (hg14'.trans hg5) hnob]; exact hno) (by have := (hg14'.trans hg5).1; omega)
    (by rw [decHL_grow (hg14'.trans hg5) hhob]; exact hho) (by have := (hg14'.trans hg5).1; omega) hP5
  have hA6 := taF_afr h6m hA5
  obtain ⟨q6', hR6⟩ := ConRon.Bridge.Inductives.targetAbs_spec names (decI lvls) holes namesP lvlsP
    holesP (decE (r5.headD 0)) _ a5 a6 _ hC5.check.state ⟨(hTA.ext q.ext).ext q5.ext, hR5⟩ run6
  have hC6 := hC5.of_pstep hS6 hA6 q6'
  have hav : H (r6.headD 0) := by
    have h' : ¬ (4294967296 : Word).toNat ≤ (r6.headD 0).toNat := fun e => hb6 (UInt64.le_iff_toNat_le.mpr e)
    have : (r6.headD 0).toNat < 4294967296 := Nat.lt_of_not_le h'
    simpa [H] using this
  refine ErrClaim.bind_right run6 ?_
  have hg56 := hg5.trans hg6
  have q56 := q5.trans q6'
  have hg46 : IWGrow s₀.mem s6.mem := hg14'.trans hg56
  -- the canon form of `y`
  cases h7 : callE p n "target_canon_params" [pfo, pfl, y] s6.mem with
  | error e7 =>
    rw [h7, pdsE.k_target_canon_params_2.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h7)
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  obtain ⟨s7, hs7, -, h7m⟩ := triple_of_callW (tcp_specF p L.rc n ⟨s6.mem, Locals.init []⟩ pfo pfl y)
    (callW_of_callE h7)
  subst hs7
  dsimp only at h7m
  obtain ⟨a7, run7, hH7, hS7, hg7, hP7⟩ := tcpF_ok dn fe vis n h7m hS6 (hpf.grow hg46) hy hP6
  have hA7 := tcpF_afr h7m hA6
  obtain ⟨q7', hR7⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE y) yP a6 a7 _
    hC6.check.state hC6.check.pins ⟨denoteEList_ext (q.ext.trans q56.ext) _ _ hpfP,
      denote_ext hyP (q.ext.trans q56.ext)⟩ run7
  have hC7 := hC6.of_pstep hS7 hA7 q7'
  refine ErrClaim.bind_right run7 ?_
  -- its abstraction
  rw [h7, pdsE.k_target_canon_params_2.arm1] at hW
  cases h8 : callE p n "target_abs" [no, nl, lvls, ho, hl, r7.headD 0] s7.mem with
  | error e8 =>
    rw [h8, pdsE.k_target_abs_2.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h8)
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  by_cases hb8 : 4294967296 ≤ r8.headD 0
  · rw [h8, pdsE.k_target_abs_2.abort1 p n vis d (r6.headD 0) r8 m8 hb8] at hW
    cases hW; exact absurd rfl hk0
  obtain ⟨s8, hs8, -, h8m⟩ := triple_of_callW (ta_specF p L.ta n ⟨s7.mem, Locals.init []⟩ no nl lvls ho hl
    (r7.headD 0)) (callW_of_callE h8)
  subst hs8
  dsimp only at h8m
  have hg47 : IWGrow s₀.mem s7.mem := hg46.trans hg7
  obtain ⟨a8, run8, hS8, hg8, hP8⟩ := taF_ok dn fe vis n h8m hS7 hH7 hlv
    (by rw [decHL_grow hg47 hnob]; exact hno) (by have := hg47.1; omega)
    (by rw [decHL_grow hg47 hhob]; exact hho) (by have := hg47.1; omega) hP7
  have hA8 := taF_afr h8m hA7
  obtain ⟨q8', hR8⟩ := ConRon.Bridge.Inductives.targetAbs_spec names (decI lvls) holes namesP lvlsP
    holesP (decE (r7.headD 0)) _ a7 a8 _ hC7.check.state ⟨(hTA.ext (q.ext.trans q56.ext)).ext q7'.ext, hR7⟩ run8
  have hC8 := hC7.of_pstep hS8 hA8 q8'
  have hbv : H (r8.headD 0) := by
    have h' : ¬ (4294967296 : Word).toNat ≤ (r8.headD 0).toNat := fun e => hb8 (UInt64.le_iff_toNat_le.mpr e)
    have : (r8.headD 0).toNat < 4294967296 := Nat.lt_of_not_le h'
    simpa [H] using this
  refine ErrClaim.bind_right run8 ?_
  have q58 := (q56.trans q7').trans q8'
  have hR6' := denote_ext hR6 (q7'.trans q8').ext
  by_cases he : r6.headD 0 = r8.headD 0
  · rw [h8, pdsE.k_target_abs_2.arm1 p n vis d (r6.headD 0) r8 s8.mem hb8 he] at hW
    cases hW
  rw [h8, pdsE.k_target_abs_2.arm2 p n vis d (r6.headD 0) r8 s8.mem hb8 he] at hW
  have hne : (decE (r6.headD 0) == decE (r8.headD 0)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he (decE_inj _ _ hav hbv e)
  simp only [hne, Bool.false_eq_true, ite_false]
  -- the knot: `infer_type_core` twice, then `is_def_eq_core`
  have hg58 : IWGrow s₀.mem s8.mem := hg47.trans hg8
  cases h9 : callE p n "infer_type_core" [vis, d, r6.headD 0] s8.mem with
  | error e9 =>
    rw [h9, pdsE.k_infer_type_core.none] at hW
    cases hW
    refine ErrClaim.bind_left ?_
    have := hcE.inferTypeCore n (by omega) hC8.stageT d (r6.headD 0) hav _ h9
    simpa [decE_eq] using this
  | ok q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9, pdsE.k_infer_type_core.arm1] at hW
  have hR6' := denote_ext hR6 (q7'.trans q8').ext
  obtain ⟨t9, a9, run9, hC9, hg9, -, hA9, c9, -⟩ :=
    inferC_rsim hq henv n (by omega) hC8 hA8 d (r6.headD 0) hav (by rw [← decE_eq]; exact hR6') hwx (r9, m9) (callW_of_callE h9)
  simp only [← decE_eq] at run9
  refine ErrClaim.bind_right run9 ?_
  cases h10 : callE p n "infer_type_core" [vis, d, r8.headD 0] m9 with
  | error e10 =>
    rw [h10, pdsE.k_infer_type_core_2.none] at hW
    cases hW
    refine ErrClaim.bind_left ?_
    have := hcE.inferTypeCore n (by omega) hC9.stageT d (r8.headD 0) hbv _ h10
    simpa [decE_eq] using this
  | ok q10 =>
  obtain ⟨r10, m10⟩ := q10
  rw [h10, pdsE.k_infer_type_core_2.arm1] at hW
  obtain ⟨t10, a10, run10, hC10, hg10, -, hA10, c10, -⟩ :=
    inferC_rsim hq henv n (by omega) hC9 hA9 d (r8.headD 0) hbv (by rw [← decE_eq]; exact denote_ext hR8 c9.ext) hwy
      (r10, m10) (callW_of_callE h10)
  simp only [← decE_eq] at run10
  refine ErrClaim.bind_right run10 ?_
  cases h11 : callE p n "is_def_eq_core" [vis, d, r6.headD 0, r8.headD 0] m10 with
  | error e11 =>
    rw [h11, pdsE.k_is_def_eq_core.none] at hW
    cases hW
    have := hcE.isDefEqCore n (by omega) hC10.stageT d (r6.headD 0) (r8.headD 0) hav hbv _ h11
    simpa [decE_eq] using this
  | ok q11 =>
  rw [h11, pdsE.k_is_def_eq_core.arm1] at hW
  cases hW

include hq henv hnv hcE in
/-- **`target_params_def_eq`'s model error claim** (`pdeW_okC`'s hypotheses; the recursion is the
model's own). -/
theorem pdeE_claim (L : TpLook p) (n : Nat) (hn : n ≤ 2 ^ 62) :
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
    ∀ e, pdeE p n m vis d no nl lvls ho hl pfo pfl ao al bo bl = .error e →
      ErrClaim (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a e := by
  induction n with
  | zero =>
    intro m a d no nl lvls ho hl pfo pfl ao al bo bl names holes pfvs as bs namesP lvlsP holesP pfvsP asP bsP
      hC hA hlv hno hnob hho hhob hpf has hbs hP hTA hpfP hasP hbsP habs hpw e he
    rw [pdeE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a d no nl lvls ho hl pfo pfl ao al bo bl names holes pfvs as bs namesP lvlsP holesP
    pfvsP asP bsP hC hA hlv hno hnob hho hhob hpf has hbs hP hTA hpfP hasP hbsP habs hpw e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hlt : ∀ {x : Nat}, x ≤ iwTop m → x < 2 ^ 64 := fun h => hS.lt64 h
  by_cases hal : al = 0
  · rw [pdeE.arm1 p n m vis d no nl lvls ho hl pfo pfl ao al bo bl hal] at he
    cases he
  by_cases hbl : bl = 0
  · rw [pdeE.arm2 p n m vis d no nl lvls ho hl pfo pfl ao al bo bl hal hbl] at he
    cases he
  rw [pdeE.arm3 p n m vis d no nl lvls ho hl pfo pfl ao al bo bl hal hbl] at he
  have hasb : ao.toNat + al.toNat ≤ iwTop m := has.2.resolve_left hal
  have hbsb : bo.toNat + bl.toNat ≤ iwTop m := hbs.2.resolve_left hbl
  obtain ⟨x, as', rfl, ex, hx, has'⟩ := decHL_cons has.1 hal (hlt hasb)
  obtain ⟨y, bs', rfl, ey, hy, hbs'⟩ := decHL_cons hbs.1 hbl (hlt hbsb)
  obtain ⟨xP, asP', hxP, hasP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hasP
  obtain ⟨yP, bsP', hyP, hbsP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hbsP
  rw [ex, ey] at he
  obtain ⟨ea1, el1, hal0⟩ := slice_step hal (hlt hasb)
  obtain ⟨eb1, ebl1, hbl0⟩ := slice_step hbl (hlt hbsb)
  rw [tpd_cons]
  cases h1 : callE p n "target_params_def_eq_step" [vis, d, no, nl, lvls, ho, hl, pfo, pfl, x, y] m with
  | error e1 =>
    rw [h1, pdeE.k_target_params_def_eq_step.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      obtain ⟨e', he', h0⟩ := callE_zero p "target_params_def_eq_step"
        [vis, d, no, nl, lvls, ho, hl, pfo, pfl, x, y] m
      rw [h1] at he'
      cases he'
      exact ErrClaim.of_cls0 h0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact CoreSpecE.of_callE (pdsStep_claim hq henv hnv hcE L (k + 1) (by omega) ⟨m, Locals.init []⟩ a hC hA hx hy hlv
        hno hnob hho hhob hpf hP hTA hpfP hxP hyP habs hpw) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "target_params_def_eq_step"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, x, y] m
    rw [h1] at he'; cases he'
  | succ k =>
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (tpdStep_spec p L (realCall p) (realCall_spec p) k
    ⟨m, Locals.init []⟩ vis d no nl lvls ho hl pfo pfl x y) (callW_of_callE h1)
  subst hs1
  dsimp only at h1m
  obtain ⟨c, a1, run1, hc, hC1, hg1, hP1, hA1, cs1⟩ :=
    pdsW_okC hq henv k (by omega) h1m hC hA hx hy hlv hno hnob hho hhob hpf hP hTA hpfP hxP hyP habs hpw
  refine ErrClaim.bind_right (by simp only [← decE_eq] at run1 ⊢; exact run1) ?_
  by_cases hr1 : r1.headD 0 = 0
  · rw [h1, pdeE.k_target_params_def_eq_step.arm1 p (k + 1) vis d no nl lvls ho hl pfo pfl ao al bo bl r1 s1.mem hr1] at he
    cases he
  rw [h1, pdeE.k_target_params_def_eq_step.arm2 p (k + 1) vis d no nl lvls ho hl pfo pfl ao al bo bl r1 s1.mem hr1] at he
  have : c = true := by rw [← hc]; simpa using hr1
  subst this
  simp only [ite_true]
  have hgo := hg1.1
  exact ih (by omega) (m := s1.mem) hC1 hA1 hlv
    (by rw [decHL_grow hg1 hnob]; exact hno) (by omega)
    (by rw [decHL_grow hg1 hhob]; exact hho) (by omega)
    (hpf.grow hg1)
    (HSl0.of (by rw [decHL_grow hg1 (by rw [ea1, el1]; omega)]; exact has') (by rw [ea1, el1]; omega))
    (HSl0.of (by rw [decHL_grow hg1 (by rw [eb1, ebl1]; omega)]; exact hbs') (by rw [eb1, ebl1]; omega)) hP1
    (hTA.ext cs1.ext) (denoteEList_ext cs1.ext _ _ hpfP) (denoteEList_ext cs1.ext _ _ hasP')
    (denoteEList_ext cs1.ext _ _ hbsP') habs hpw e he

include hq henv hnv hcE in
/-- **`target_params_def_eq`'s error claim** (the hypotheses of `targetParamsDefEq_refinesC`): a
failing call of class `1`/`2` claims that the twin's `targetParamsDefEq` fails. -/
theorem targetParamsDefEq_claim (L : TpLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
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
    CoreSpecE p n "target_params_def_eq" [vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl]
      (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (pdeE_spec p L.tpd n ⟨s₀.mem, Locals.init []⟩ vis d no nl lvls ho hl pfo pfl
    ao al bo bl) hc' (Err.code_ne_of_cls hk0)
  exact pdeE_claim hq henv hnv hcE L n hn hC hA hlv hno hnob hho hhob hpf has hbs hP hTA hpfP hasP hbsP habs
    hpw er hW

end sims

end L.Ind
