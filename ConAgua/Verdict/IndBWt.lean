import ConAgua.Verdict.IndBSum2
import ConAgua.Verdict.PosKnotE
import ConAgua.Verdict.KnotAllE

/-!
# `whnf_telescope`'s error claim (lane `verdicts-b`, helper `fin`, fork `wt`)

The generated `errors` model `wtE` (its recursion is the model's own) and the claim by induction
on its fuel, mirroring `wtW_simC` (`IndT/Sum1.lean`): `whnf_top`'s error by `WhnfTopE` (from the
error knot, `whnfTop_stageE`), its ok run by `whnfC_rsim`; the view; the `fail` site (every arm of
`wtArm` the guards leave is the twin's `.invalid`); `intern_fvar`, `instantiate1_fast`,
`sl_cons` outside the verdict closure; the recursion by the induction hypothesis.

`whnfC_rsim` (the ok run of `whnf`) needs the environment well formed, so the claim is `WtE'`:
`WtE` with `ConLeche.EnvWF env`.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model wtE_spec (p : Prog) (hf : p.lookup "whnf_telescope" = some whnfTelescopeL)
  fns [hf ↦ wtE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

/-- **`whnf_telescope`'s error claim** (`WtE` with the environment well formed, as
`whnfTelescope_refinesC` takes it). -/
def WtE' (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env},
    ConLeche.EnvWF env → ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (i n e : Word),
    StageC dn vis fe env s₀.mem a₀ → AbsOK s₀.mem → H e → i.toNat + n.toNat < 2 ^ 64 →
    ∀ {eP : ConLeche.Expr}, denoteE a₀.store (decI e) = some eP → ConLeche.Expr.WScoped i.toNat eP →
    CoreSpecE p k "whnf_telescope" [vis, i, n, e] (whnfTelescope V fe i.toNat n.toNat (decI e)) s₀ a₀

/-- The arms of `wtArm` the L guards leave (not a sort at `0`, not a `∀` at `n + 1`) are the
twin's `.invalid` failures. -/
theorem wtArm_fail (fe : IFEnv) (i : Nat) {vv : ENodeView} {v : List Word} {n : Word}
    (hVR : ViewR v vv) (h1 : ¬ (v.headD 0 = 2 ∧ n = 0)) (h2 : ¬ (v.headD 0 = 6 ∧ n ≠ 0)) :
    ∃ msg, wtArm V fe i vv n.toNat = ConRon.Arena.fail (.invalid msg) := by
  by_cases hn : n = 0
  · subst hn
    cases vv with
    | sort u => exact absurd ⟨hVR.1, rfl⟩ h1
    | _ => exact ⟨_, rfl⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h0 => hn (UInt64.toNat_inj.mp (by simpa using h0)))
    rw [hk]
    cases vv with
    | forallE ty b => exact absurd ⟨hVR.1, hn⟩ h2
    | _ => exact ⟨_, rfl⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (hW : WhnfTopE p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hv : p.lookup "e_view" = some eView)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar) (hi1 : I1Prog p)

include hq hnv hW henv hv hff hfp hif hi1 in
/-- **The model's error claim** (by induction on its fuel; `wtW_simC`'s case structure). -/
theorem wtE_claim (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (i n e : Word) {eP : ConLeche.Expr},
    StageC dn vis fe env m a → AbsOK m → H e → i.toNat + n.toNat < 2 ^ 64 →
    denoteE a.store (decI e) = some eP → ConLeche.Expr.WScoped i.toNat eP →
    ∀ er, wtE p k m vis i n e = .error er →
      ErrClaim (whnfTelescope V fe i.toNat n.toNat (decI e)) a er := by
  induction k with
  | zero =>
    intro m a i n e eP _ _ _ _ _ _ er h
    rw [wtE.eq_def] at h; cases h; exact ErrClaim.of_cls0 rfl
  | succ k ih =>
  intro m a i n e eP hC hA he hin hdP hwsP er h
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  rw [wtE.arm1] at h
  rw [whnfTelescope_eq]
  cases h1 : callE p k "whnf_top" [vis, i, e] m with
  | error e1 =>
    rw [h1, wtE.k_whnf_top.none] at h; cases h
    exact ErrClaim.bind_left (hW k (by omega) hC.stageT i e he _ h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, wtE.k_whnf_top.arm1] at h
  obtain ⟨e', a1, hrun1, hC1, hg1, ⟨he'32, he'eq⟩, hA1, hcs1, wP, hwP, hwsw⟩ :=
    whnfC_rsim hq henv k (by omega) hC hA i e he hdP hwsP _ (callW_of_callE h1)
  dsimp only at hC1 hg1 he'32 he'eq hA1
  have hS1 := hC1.stage
  refine ErrClaim.bind_right hrun1 ?_
  rw [← he'eq] at hwP ⊢
  generalize hw : r1.headD 0 = w at h he'32 hwP
  -- the view
  cases h2 : callE p k "e_view" [w] m1 with
  | error e2 =>
    rw [h2, wtE.k_e_view.none] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, hl2, hne2, hr2⟩ := triple_of_callE (eView_spec p hv k ⟨m1, Locals.init []⟩ w) h2
  have hm2 : m2 = m1 := by rw [← hs2, hl2]
  subst hm2
  rw [h2] at h
  generalize hvv : eViewW m2 w = v at hr2
  subst hr2
  obtain ⟨vv, hview, hVR⟩ := eViewW_ok m2 a1 hS1.1.arena.1 w (hvv ▸ hne2)
  rw [hvv] at hVR
  have hrv : (view (decI w)).run a1 = .ok (vv, a1) := by
    rw [← decE_eq]; exact view_run _ _ _ hview
  refine ErrClaim.bind_right hrv ?_
  by_cases hs : r2.headD 0 = 2 ∧ n = 0
  · rw [wtE.k_e_view.arm1 _ _ _ _ _ _ _ hs] at h; cases h
  by_cases hp' : ¬ (r2.headD 0 = 6 ∧ n ≠ 0)
  · rw [wtE.k_e_view.abort1 _ _ _ _ _ _ _ hs hp'] at h; cases h
    obtain ⟨msg, hm⟩ := wtArm_fail fe i.toNat hVR hs hp'
    rw [hm]
    exact ErrClaim.fail _ _ rfl
  have hp : r2.headD 0 = 6 ∧ n ≠ 0 := Decidable.not_not.mp hp'
  rw [wtE.k_e_view.arm2 _ _ _ _ _ _ _ hs hp] at h
  cases vv with
  | forallE ty body =>
    obtain ⟨domP, bodyP, rfl, hd, hbd⟩ :=
      ConRon.Bridge.denote_forallE_inv hC1.check.state.wf hview hwP
    have hwsdb : ConLeche.Expr.WScoped i.toNat domP ∧ ConLeche.Expr.WScoped i.toNat bodyP := by
      simp only [ConLeche.Expr.WScoped] at hwsw; exact hwsw
    obtain ⟨hwsd, hwsb⟩ := hwsdb
    obtain ⟨-, hx32, hxe, hy32, hye⟩ := hVR
    have hx1 : r2.getD 1 0 = r2.tail.headD 0 := by
      cases r2 with | nil => rfl | cons _ t => cases t <;> rfl
    have hy1 : r2.getD 2 0 = r2.tail.tail.headD 0 := by
      cases r2 with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ u => cases u <;> rfl
    rw [hx1] at hx32 hxe
    rw [hy1] at hy32 hye
    generalize r2.tail.headD 0 = x at h hx32 hxe
    generalize r2.tail.tail.headD 0 = y at h hy32 hye
    have hn1 : 1 ≤ n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hp.2
      · omega
    have hnm : (n - 1).toNat = n.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hn1))]; simp
    have hiS : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hns : n.toNat = (n.toNat - 1) + 1 := by omega
    rw [hns]
    simp only [wtArm]
    -- `intern_fvar`
    cases h3 : callE p k "intern_fvar" [i, x] m2 with
    | error e3 =>
      rw [h3, wtE.k_intern_fvar.none] at h; cases h
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    obtain ⟨s3, hs3, -, h3'⟩ := triple_of_callE
      (internFVar_spec p hff hfp hif k ⟨m2, Locals.init []⟩ i x) h3
    rw [hs3] at h3'
    generalize hfvw : r3.headD 0 = fv at h3'
    by_cases hfv : 4294967296 ≤ fv
    · rw [h3, wtE.k_intern_fvar.abort1 _ _ _ _ _ _ _ _ _ (by rw [hfvw]; exact hfv)] at h; cases h
      exact absurd rfl hk0
    rw [h3, wtE.k_intern_fvar.arm1 _ _ _ _ _ _ _ _ _ (by rw [hfvw]; exact hfv)] at h
    rw [hfvw] at h
    have hfv32 : fv.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ fv.toNat := hfv; omega
    obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 i x hx32 h3'
    have hrun2' : (internE (.fvar i.toNat ty)).run a1 = .ok (decE fv, a2) := by
      rw [← hxe]; exact hrun2
    obtain ⟨p2, hfvd⟩ := ConRon.Bridge.Inductives.internE_run hC1.check.state
      (ConRon.Bridge.viewOK_fvar (by rw [hd]; rfl)) hrun2'
    have hfv' : denoteE a2.store (decE fv) = some (.fvar i.toNat domP) := by
      rw [hfvd]; simp [denoteEView, ConRon.Bridge.denote_ext hd p2.ext]
    have hA2 := fvinternW_afr h3' hA1
    have hC2 : StageC dn vis fe env m3 a2 := hC1.of_pstep hS2 hA2 p2
    refine ErrClaim.bind_right hrun2' ?_
    -- `instantiate1_fast`
    cases h4 : callE p k "instantiate1_fast" [CWF, y, fv, 0] m3 with
    | error e4 =>
      rw [h4, wtE.k_instantiate1_fast.none] at h; cases h
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨rb, m4⟩ := q4
    obtain ⟨s4, hs4, -, h4'⟩ := triple_of_callE (i1F_spec p hi1 k ⟨m3, Locals.init []⟩ _) h4
    rw [hs4] at h4'
    rw [h4, wtE.k_instantiate1_fast.arm1] at h
    obtain ⟨b', a3, hrun3, hS3, hg3, hb32, hbeq⟩ :=
      i1F_ok dn vis fe y fv 0 hy32 m3 m4 a2 rb h4' hS2
    rw [CWF_eq, show (0 : Word).toNat = 0 from rfl, ← decE_eq y, hye, ← decE_eq fv] at hrun3
    have hb2 : denoteE a2.store body = some bodyP := ConRon.Bridge.denote_ext hbd p2.ext
    obtain ⟨i1, i2, i4, i5, -, i7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run hC2.check.state hfv'
      (by rw [hb2]; rfl) hrun3
    have p3 : PStep a2 a3 := PStep.of_caches i1 i2 i4 i5
    have hop : denoteE a3.store b' = some (bodyP.instantiate1 (.fvar i.toNat domP) 0) := i7 _ hb2
    have hA3 := i1F_afr h4' hA2
    have hC3 : StageC dn vis fe env m4 a3 := hC2.of_pstep hS3 hA3 p3
    refine ErrClaim.bind_right hrun3 ?_
    -- the recursion
    cases h5 : wtE p k m4 vis (i + 1) (n - 1) (rb.headD 0) with
    | error e5 =>
      rw [h5, wtE.k_whnf_telescope.none] at h; cases h
      refine ErrClaim.bind_left ?_
      have := ih (by omega) m4 a3 (i + 1) (n - 1) (rb.headD 0) hC3 hA3 hb32 (by omega)
        (by rw [hbeq]; exact hop) (by rw [hiS]; exact ConLeche.Expr.WScoped.instantiate1 hwsd 0 hwsb)
        _ h5
      rw [hiS, hnm, hbeq] at this
      exact this
    | ok q5 =>
    obtain ⟨rr, m5⟩ := q5
    rw [h5, wtE.k_whnf_telescope.arm1] at h
    cases h6 : callE p k "sl_cons" [x, rr.headD 0, rr.tail.headD 0] m5 with
    | error e6 =>
      rw [h6, wtE.k_sl_cons.none] at h; cases h
      exact absurd (callE_nv hnv (by decide +kernel) _ _ _ h6) hk0
    | ok q6 =>
    obtain ⟨ro, m6⟩ := q6
    rw [h6, wtE.k_sl_cons.arm1] at h; cases h
  | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hp.1; simp_all)

end sims

/-- **`whnf_telescope`'s error claim** (`WtE'`) from the program's facts: the knot (`whnf_top`'s
claim from the error knot), the lookups of the callees `wtW_spec` reads. -/
theorem wtE_of {p : Prog} (hq : KnotStageProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hp : p.lookup "whnf_telescope" = some whnfTelescopeL) (hv : p.lookup "e_view" = some eView)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar) (hi1 : I1Prog p) : WtE' p := by
  intro dn vis fe env henv k hk s₀ a₀ i n e hC hA he hin eP hdP hwsP
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hM := triple_of_callE_err (wtE_spec p hp k ⟨s₀.mem, Locals.init []⟩ vis i n e) hc
    (Err.code_ne_of_cls hk0)
  exact wtE_claim hq hnv (whnfTop_stageE hq.whnfTop (fun n => L.Arena.KnotAllProg.knotE_all hq.knot hnv n)) henv hv hff
    hfp hif hi1 k hk s₀.mem a₀ i n e hC hA he hin hdP hwsP er hM

end L.Ind
