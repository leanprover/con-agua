import ConAgua.Verdict.DeclValE
import ConAgua.Arena.DeclStep
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.DeclValT
import ConAgua.Checker.NoVerdictClosed

/-!
# The verdict claims of `install_value_guards` and `install_header` (lane `verdicts-b`, helper `d`)

The error models and error refinements of the two guard functions, under the hypotheses of their
ok refinements (`ivgW_okT`, `ihW_okT`): a failing call of class `1`/`2` claims the twin's
`installValueGuards`/`installHeader` fails with an error of that class. The callees are all
outside the verdict closure (`nvFns`), so their failures claim nothing; the abort sites are the
twin's `fail`s (the consts-resolve site aborts with the class-0 code).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

l_model installValueGuards_specE (p : Prog)
  (hf : p.lookup "install_value_guards" = some installValueGuardsL)
  fns [hf ↦ installValueGuardsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installHeader_specE (p : Prog) (hf : p.lookup "install_header" = some installHeaderL)
  fns [hf ↦ installHeaderE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

/-- The callees of the declaration family outside the verdict closure. -/
theorem declHdrE_nv : ∀ f ∈ ["cv_lps", "loose_bvars_bounded_fast", "has_fvar_fast",
    "all_level_params_defined", "consts_resolve_ffast", "sl_nodup", "reserved_contains",
    "env_find", "env_push"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- A failing callee of the list claims nothing. -/
theorem nvl {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {α : Type} {T : AM α} {a : AState}
    {f : FnName} (hf : f ∈ ["cv_lps", "loose_bvars_bounded_fast", "has_fvar_fast",
    "all_level_params_defined", "consts_resolve_ffast", "sl_nodup", "reserved_contains",
    "env_find", "env_push"]) {n : Nat} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hnv (declHdrE_nv f hf) h

/-- **`install_value_guards`' error claim under `StageT`** (the error half of `ivgW_okT`). -/
theorem ivgE_okT {p : Prog} (hP : CvgProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) : IvgE p := by
  intro dn vis fe a n m q v cv e hc hS hq hqb hv hlps hCr
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installValueGuards_specE p hP.ivg n ⟨m, Locals.init []⟩ vis q v)
    hc (Err.code_ne_of_cls hk0)
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => rw [installValueGuardsE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [installValueGuardsE.eq_2] at hW
  simp only [installValueGuards, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]
  cases h1 : callE p n "cv_lps" [q] m with
  | error e1 =>
    rw [h1, installValueGuardsE.k_cv_lps.none] at hW; cases hW
    exact nvl hnv (by simp) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, installValueGuardsE.k_cv_lps.eq_2] at hW
  obtain ⟨s1, hs1, -, hW1, -⟩ := triple_of_callE
    (cvLps_specW p hP.alloc hP.copy hP.eti hP.lps n ⟨m, Locals.init []⟩ q) h1
  subst hs1
  cases n with
  | zero => simp [cvLpsW] at hW1
  | succ n =>
  rw [cvLpsW_step, e1, e2] at hW1
  obtain ⟨-, hr1t, hdec1, hS1R, hg1, htop1⟩ := erToIwW_stage hW1 hS.stage hsrc
  have hS1 := StageT.of_iw hS hS1R (erToIwW_frame hW1 hS.stage hsrc)
  have hCr1 := CrOK.frame hCr (erToIwW_frame hW1 hS.stage hsrc) (by decide) (by decide)
  -- `loose_bvars_bounded_fast(4000000000, 0, v)`
  cases h2 : callE p (n + 1) "loose_bvars_bounded_fast" [4000000000, 0, v] s1.mem with
  | error e2 =>
    rw [h2, installValueGuardsE.k_loose_bvars_bounded_fast.none] at hW; cases hW
    exact nvl hnv (by simp) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callE
    (lbbF_spec p hP.bvb (n + 1) ⟨s1.mem, Locals.init []⟩ [4000000000, 0, v]) h2
  subst hs2
  have hCr2 := CrOK.frame hCr1 (lbbF_frame hW2) (by decide) (by decide)
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 v hv s1.mem s2.mem a r2 hW2 hS1
  rw [fuelW] at hrun2
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  by_cases hb2 : r2.headD 0 = 0
  · rw [installValueGuardsE.k_loose_bvars_bounded_fast.abort1 p _ _ _ _ _ _ _ hb2] at hW
    cases hW
    have ex2 : x2 = false := by rw [← hx2]; simpa using hb2
    rw [ex2]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [installValueGuardsE.k_loose_bvars_bounded_fast.arm1 p _ _ _ _ _ _ _ hb2] at hW
  have ex2 : x2 = true := by rw [← hx2]; simpa using hb2
  rw [ex2]
  refine ErrClaim.ite_pos rfl ?_
  -- `has_fvar_fast(4000000000, v)`
  cases h3 : callE p (n + 1) "has_fvar_fast" [4000000000, v] s2.mem with
  | error e3 =>
    rw [h3, installValueGuardsE.k_has_fvar_fast.eq_1] at hW; cases hW
    exact nvl hnv (by simp) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at hW
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callE
    (hffF_spec p hP.hf (n + 1) ⟨s2.mem, Locals.init []⟩ [4000000000, v]) h3
  subst hs3
  have hCr3 := CrOK.frame hCr2 (hffF_frame hW3) (by decide) (by decide)
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    hffF_okT dn vis fe 4000000000 v hv s2.mem s3.mem a2 r3 hW3 hS2
  rw [fuelW] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [installValueGuardsE.k_has_fvar_fast.abort1 p _ _ _ _ _ _ _ hb3] at hW
    cases hW
    have ex3 : x3 = true := by rw [← hx3]; simpa using hb3
    rw [ex3]
    exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ rfl)
  have hb3' : r3.headD 0 = 0 := by simpa using hb3
  rw [installValueGuardsE.k_has_fvar_fast.arm1 p _ _ _ _ _ _ _ hb3'] at hW
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  rw [ex3]
  refine ErrClaim.ite_neg (by decide) ?_
  -- `all_level_params_defined(o, l, v)`
  have hdec3 : decHL s3.mem (r1.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg2.trans hg3) (by omega), hdec1]; exact hsl
  have hst3 : a3.store = a.store := (hffF_store hrun3).trans (lbbF_store hrun2)
  rw [hr1t] at hW
  cases h4 : callE p (n + 1) "all_level_params_defined" [r1.headD 0, w2, v] s3.mem with
  | error e4 =>
    rw [h4, installValueGuardsE.k_all_level_params_defined.eq_1] at hW; cases hW
    exact nvl hnv (by simp) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4] at hW
  have h4' := apdF_of_callW hap (callW_of_callE h4)
  have hCr4 := CrOK.frame hCr3 (apdF_frame h4') (by decide) (by decide)
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    apdF_okT dn vis fe (r1.headD 0) w2 v hv cv.levelParams s3.mem m4 a3 r4 h4'
      ⟨hS3, hdec3, by rw [hst3]; exact hlps⟩
  refine ErrClaim.bind_right hrun4 ?_
  by_cases hb4 : r4.headD 0 = 0
  · rw [installValueGuardsE.k_all_level_params_defined.abort1 p _ _ _ _ _ hb4] at hW
    cases hW
    have ex4 : x4 = false := by rw [← hx4]; simpa using hb4
    rw [ex4]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [installValueGuardsE.k_all_level_params_defined.arm1 p _ _ _ _ _ hb4] at hW
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  rw [ex4]
  refine ErrClaim.ite_pos rfl ?_
  -- `consts_resolve_ffast(vis, v)`
  cases h5 : callE p (n + 1) "consts_resolve_ffast" [vis, v] m4 with
  | error e5 =>
    rw [h5, installValueGuardsE.k_consts_resolve_ffast.none] at hW; cases hW
    exact nvl hnv (by simp) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  obtain ⟨x5, a5, hrun5, ⟨hS5, hg5, hx5, -⟩, hCr5⟩ :=
    crfF_okT dn vis fe v hv m4 m5 a4 r5 (crfF_of_callW hkp.crf (callW_of_callE h5)) ⟨hS4, hCr4.crMemo⟩
  refine ErrClaim.bind_right hrun5 ?_
  by_cases hb5 : r5.headD 0 = 0
  · rw [installValueGuardsE.k_consts_resolve_ffast.abort1 p _ _ hb5] at hW
    cases hW
    exact ErrClaim.of_cls0 rfl
  rw [installValueGuardsE.k_consts_resolve_ffast.arm1 p _ _ hb5] at hW
  cases hW

end L.Arena
