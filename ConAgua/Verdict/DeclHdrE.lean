import ConAgua.Verdict.DeclValE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# The verdict claims of `install_value_guards` and `install_header` (lane `verdicts-b`, helper `d`)

The error models and error refinements of the two guard functions, under the hypotheses of their
ok refinements (`ivgW_okT`, `ihW_okT`): a failing call of class `1`/`2` claims the twin's
`installValueGuards`/`installHeader` fails with an error of that class. The callees are all
outside the verdict closure (`nvFns`), so their failures claim nothing; the abort sites are the
twin's `fail`s. The consts-resolve site is a call of `unresolved_consts_error` (it always fails):
its error's class is the twin's `unresolvedConstsErrorL (← strLitSupported fe) …`
(`uce_errClaim_lo`, `UnresolvedE.lean`).
-/

noncomputable section

set_option experimental.vcgen true

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

/-- `cv_lps`' spec without the result's length (as a `simp` hypothesis `r = [r.headD 0, …]` loops). -/
theorem cvLps_specW1 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "cv_lps" = some cvLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ cvLpsW n s₀.mem q = some (r, s'.mem); ⊤⦄ :=
  triple_post (cvLps_specW p ha hc he hp n s₀ q) fun _ _ h => ⟨h.1, h.2.1⟩

/-- **The model of `install_header`, both outcomes**: the callees outside the verdict closure with
`Option` models lifted; `all_level_params_defined`, `consts_resolve_ffast` and
`unresolved_consts_error` through their runs. -/
l_model installHeader_specE (p : Prog) (hP : IhProg p)
  fns [hP.ih ↦ installHeaderE]
  specs [envFind_specW p hP.ix hP.rowGet hP.find n, resCont_spec p hP.resF hP.resC n,
    cvLps_specW1 p hP.alloc hP.copy hP.eti hP.lps n, slNodup_spec p hP.cont hP.nodup n,
    lbbF_spec p hP.bvb n, hffF_spec p hP.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] locals unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The callees of the declaration family outside the verdict closure. -/
def declNvList : List FnName :=
  ["cv_lps", "loose_bvars_bounded_fast", "has_fvar_fast", "all_level_params_defined",
   "consts_resolve_ffast", "sl_nodup", "reserved_contains", "env_find", "env_push", "erec_ci",
   "reduce_stored_ok", "reduce_elem_ok", "reduce_pin_guard", "reduce_decl_pin", "reduce_cert_var",
   "mk_app", "pin_at", "is_none", "is_some", "tbl_cnt", "flush_caches", "scratch_enter",
   "scratch_drop", "and_pin_ok", "pin_in", "erec_vg", "rom_ci", "rom_basis_decls", "find_is",
   "ci_to_cv", "ci_canon_eq", "cv_canon_eq", "std_axiom_ok", "trust_compiler_ok",
   "of_reduce_ax_ok", "sl_contains", "nat_op_names", "nat_op_guard", "nat_op_deps",
   "nat_op_stored_ok_all", "nat_div_mod_names", "rom_pin_sets", "ind_block_to_erec",
   "rom_basis_decls_a", "quot_pin_hit", "pin_word", "iw_reset", "promote_new", "promote_vg",
   "pend_push"]

theorem declNv_mem : ∀ f ∈ declNvList, f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- A failing callee of the list claims nothing. -/
theorem nvl {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {α : Type} {T : AM α} {a : AState}
    {f : FnName} (hf : f ∈ declNvList) {n : Nat} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hnv (declNv_mem f hf) h

/-- A hit of `reserved_from`: one of the reserved words is `x`. -/
theorem resFromW_hit (n : Nat) : ∀ (m : Mem) (x j c : Word), j.toNat ≤ 16 → c ≠ 0 →
    resFromW n m x j = some c → ∃ i, i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j c _ _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j c hj hc h
    rw [resFromW_step] at h
    have hn16 : ¬ 16 ≤ j := by
      by_cases h16 : 16 ≤ j
      · rw [ite_eq_left h16] at h; simp at h; exact absurd h.symm hc
      · exact h16
    rw [ite_eq_right hn16] at h
    have hj16 : j.toNat < 16 := by
      refine Classical.byContradiction fun hh => hn16 ?_
      rw [UInt64.le_iff_toNat_le]; simp; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    exact ih m x (j + 1) c (by omega) hc h

/-- **A hit of `reserved_contains` is a hit of `reservedBasisNames`.** -/
theorem resContW_hit {m : Mem} {a : AState} {n : Nat} {x : Word}
    {c : Word} (hc : c ≠ 0) (h : resContW n m x = some c) (hP : PinsR m a.pins) :
    ∃ l, reservedBasisNames.run a = .ok (l, a) ∧ l.contains (decI x) = true := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  obtain ⟨i, hi, e⟩ := resFromW_hit n m x 0 c (by simp) hc h
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
  exact ⟨i, hi, by rw [e]⟩

/-- **`install_value_guards`' error claim under `StageT`** (the error half of `ivgW_okT`). -/
theorem ivgE_okT {p : Prog} (hP : CvgProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hU : UceProg p) : IvgE p := by
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
  simp only [installValueGuards, fail_bindAM]
  cases h1 : callE p n "cv_lps" [q] m with
  | error e1 =>
    rw [h1, installValueGuardsE.k_cv_lps.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
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
    exact nvl hnv (by decide +kernel) h2
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
    exact nvl hnv (by decide +kernel) h3
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
    exact nvl hnv (by decide +kernel) h4
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
    exact nvl hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  obtain ⟨x5, a5, hrun5, ⟨hS5, hg5, hx5, -⟩, hCr5⟩ :=
    crfF_okT dn vis fe v hv m4 m5 a4 r5 (crfF_of_callW hkp.crf (callW_of_callE h5)) ⟨hS4, hCr4.crMemo⟩
  refine ErrClaim.bind_right hrun5 ?_
  by_cases hb5 : r5.headD 0 = 0
  · rw [installValueGuardsE.k_consts_resolve_ffast.arm1 p _ _ _ _ _ hb5] at hW
    have ex5 : x5 = false := by rw [← hx5]; simpa using hb5
    rw [ex5]
    refine ErrClaim.ite_neg (by decide) ?_
    cases h6 : callE p (n + 1) "unresolved_consts_error" [vis, v, 1] m5 with
    | error e6 =>
      rw [h6, installValueGuardsE.k_unresolved_consts_error.none] at hW; cases hW
      obtain ⟨M5, hC5⟩ := hS5.core
      exact uce_errClaim_lo hU hnv hC5 hv (by decide) h6 "value"
    | ok q6 =>
      obtain ⟨r6, m6⟩ := q6
      rw [h6, installValueGuardsE.k_unresolved_consts_error.abort1] at hW; cases hW
      exact ErrClaim.of_cls0 rfl
  rw [installValueGuardsE.k_consts_resolve_ffast.arm2 p _ _ _ _ _ hb5] at hW
  cases hW

/-- What `install_header`'s error arms assume: the no-verdict closure (`all_level_params_defined`,
`consts_resolve_ffast`) and `unresolved_consts_error`'s program. -/
structure IhCtx (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  uce : UceProg p

/-- What `install_header` gives besides the twin's run: the stage, the growth, the memos. -/
structure IhPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  crOK : L.Stubs.CrOK m'
  afr : AFr m m'

/-- **`install_header` refines `installHeader`, both outcomes**, under `StageT`: the duplicate,
reserved-name and universe-parameter guards, the closedness walks (`lbbF_okT`, `hffF_okT`,
`apdF_okT`, `crfF_okT`), the consts-resolve site by `uce_errClaim_lo`. -/
theorem ih_ref {p : Prog} (hap : ApdF p) (hCrf : CrfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (IhCtx p) (installHeaderE p n m vis q) (installHeader fe cv) a
      (fun v _ a' => IhPost dn vis fe m v.2 a') := by
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => rw [installHeaderE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [installHeaderE.arm1, ex, et]
  simp only [installHeader, fail_bindAM]
  -- `env_find(x, vis)`
  rcases h1 : envFindW m wx vis with _ | ⟨r1, m1⟩
  · rw [liftE_none, installHeaderE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [installHeaderE.k_env_find.abort1 p _ _ _ _ _ _ _ hb1]
    have : (fe.find? cv.name).isSome = true := by
      rw [hname]; exact envFindW_hitSome h1 hS.stage.1.env hwxl hb1
    exact fun _ => ErrClaim.ite_pos this (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_env_find.arm1 p _ _ _ _ _ _ _ (by simpa using hb1)]
  obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.stage.1.env hwxl (by simpa using hb1)
  have hfind' : (fe.find? cv.name).isSome = false := by rw [hname, hfind]; rfl
  refine RefE.ite_neg (by simp [hfind']) ?_
  -- `reserved_contains(x)`
  rcases h2 : resContW n m1 wx with _ | c
  · rw [liftE_none, installHeaderE.k_reserved_contains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb2 : c ≠ 0
  · rw [installHeaderE.k_reserved_contains.abort1 p _ _ _ _ _ _ hb2]
    obtain ⟨l, hrunR, hcl⟩ := resContW_hit hb2 h2 hS.stage.1.pins
    refine RefE.bind_right hrunR (RefE.ite_pos ?_ (fun _ => ErrClaim.fail_abort _ _ rfl))
    rw [hname]; exact hcl
  have hc0 : c = 0 := by simpa using hb2
  subst hc0
  rw [installHeaderE.k_reserved_contains.arm1 p _ _ _ _ _ _ rfl]
  obtain ⟨l, hrunR, hcl⟩ := resContW_miss hwxl h2 hS.stage.1.pins
  refine RefE.bind_right hrunR (RefE.ite_neg ?_ ?_)
  · rw [hname, hcl]; decide
  -- `cv_lps(q)`
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq0
  have e1 : rdW (m1.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m1.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m1.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  rcases h4 : cvLpsW n m1 q with _ | ⟨r4, m4⟩
  · rw [liftE_none, installHeaderE.k_cv_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, installHeaderE.k_cv_lps.arm1]
  cases n with
  | zero => simp [cvLpsW] at h4
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h4
  obtain ⟨-, hr4t, hdec4, hS4R, hg4, htop4⟩ := erToIwW_stage h4 hS.stage hsrc
  have hS4 := StageT.of_iw hS hS4R (erToIwW_frame h4 hS.stage hsrc)
  have hCr4 := CrOK.frame hCr (erToIwW_frame h4 hS.stage hsrc) (by decide) (by decide)
  have hA4 : AFr m1 m4 := erToIwW_afr h4
  rw [hr4t]
  have hdecL : decHL m4 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [hdec4]; exact hsl
  -- `sl_nodup(o, l)`
  rcases h5 : nodupW (n + 1) m4 (r4.headD 0) w2 with _ | d
  · rw [liftE_none, installHeaderE.k_sl_nodup.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have htopb : iwTop m4 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m4 _ _ _ hdecL (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h5
  by_cases hb5 : d = 0
  · rw [installHeaderE.k_sl_nodup.abort1 p _ _ _ _ _ _ _ hb5]
    have hnd : nameNodup cv.levelParams = false := by
      rw [hlps, nameNodup_map ws hwsl]
      by_cases hn : ws.Nodup
      · rw [ite_eq_left hn, hb5] at hd; exact absurd hd (by decide)
      · simp [hn]
    exact fun _ => ErrClaim.ite_neg (by simp [hnd]) (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_sl_nodup.arm1 p _ _ _ _ _ _ _ hb5]
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · rw [ite_eq_right hn] at hd; exact absurd hd hb5
  refine RefE.ite_pos hnd ?_
  -- `loose_bvars_bounded_fast(4000000000, 0, t)`
  rcases h6 : lbbF m4 [4000000000, 0, wt] with _ | ⟨r6, m6⟩
  · rw [liftE_none, installHeaderE.k_loose_bvars_bounded_fast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x6, a6, hrun6, hS6, hg6, hx6, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 wt hwtl m4 m6 a r6 h6 hS4
  have hCr6 := CrOK.frame hCr4 (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m1 m6 := hA4.trans (AFr.of_frame (lbbF_frame h6))
  rw [fuelW] at hrun6
  rw [show ((0 : Word).toNat) = 0 from rfl, ← hty] at hrun6
  refine RefE.bind_right hrun6 ?_
  by_cases hb6 : r6.headD 0 = 0
  · rw [installHeaderE.k_loose_bvars_bounded_fast.abort1 p _ _ _ _ _ _ _ hb6]
    have ex6 : x6 = false := by rw [← hx6]; simpa using hb6
    rw [ex6]
    exact fun _ => ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_loose_bvars_bounded_fast.arm1 p _ _ _ _ _ _ _ hb6]
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  rw [ex6]
  refine RefE.ite_pos rfl ?_
  -- `has_fvar_fast(4000000000, t)`
  rcases h7 : hffF m6 [4000000000, wt] with _ | ⟨r7, m7⟩
  · rw [liftE_none, installHeaderE.k_has_fvar_fast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7, -⟩ :=
    hffF_okT dn vis fe 4000000000 wt hwtl m6 m7 a6 r7 h7 hS6
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m1 m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  rw [fuelW] at hrun7
  rw [← hty] at hrun7
  refine RefE.bind_right hrun7 ?_
  by_cases hb7 : r7.headD 0 ≠ 0
  · rw [installHeaderE.k_has_fvar_fast.abort1 p _ _ _ _ _ _ _ hb7]
    have ex7 : x7 = true := by rw [← hx7]; simpa using hb7
    rw [ex7]
    exact fun _ => ErrClaim.ite_pos rfl (ErrClaim.fail_abort _ _ rfl)
  have hb7' : r7.headD 0 = 0 := by simpa using hb7
  rw [installHeaderE.k_has_fvar_fast.arm1 p _ _ _ _ _ _ _ hb7']
  have ex7 : x7 = false := by rw [← hx7]; simpa using hb7
  rw [ex7]
  refine RefE.ite_neg (by decide) ?_
  -- `all_level_params_defined(o, l, t)`
  have hdec7 : decHL m7 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  have hst7 : a7.store = a.store := by
    rw [hffF_store hrun7, lbbF_store hrun6]
  rcases h8 : callE p (n + 1) "all_level_params_defined" [r4.headD 0, w2, wt] m7 with e8 | ⟨r8, m8⟩
  · rw [installHeaderE.k_all_level_params_defined.none]
    exact fun hG => nvl hG.nv (by decide +kernel) h8
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    apdF_okT dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams m7 m8 a7 r8 h8'
      ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩
  have hA8 : AFr m1 m8 := fun hA => absOK_apdF h8' (hA7 hA) hS8
  rw [← hty] at hrun8
  refine RefE.bind_right hrun8 ?_
  by_cases hb8 : r8.headD 0 = 0
  · rw [installHeaderE.k_all_level_params_defined.abort1 p _ _ _ _ _ hb8]
    have ex8 : x8 = false := by rw [← hx8]; simpa using hb8
    rw [ex8]
    exact fun _ => ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_all_level_params_defined.arm1 p _ _ _ _ _ hb8]
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  rw [ex8]
  refine RefE.ite_pos rfl ?_
  -- `consts_resolve_ffast(vis, t)`
  rcases h9 : callE p (n + 1) "consts_resolve_ffast" [vis, wt] m8 with e9 | ⟨r9, m9⟩
  · rw [installHeaderE.k_consts_resolve_ffast.none]
    exact fun hG => nvl hG.nv (by decide +kernel) h9
  have h9' := crfF_of_callW hCrf (callW_of_callE h9)
  obtain ⟨x9, a9, hrun9, ⟨hS9, hg9, hx9, -⟩, hCr9⟩ :=
    crfF_okT dn vis fe wt hwtl m8 m9 a8 r9 h9' ⟨hS8, hCr8.crMemo⟩
  have hA9 : AFr m1 m9 := fun hA => absOK_crfF h9' (hA8 hA) hCr9 hS9
  rw [← hty] at hrun9
  refine RefE.bind_right hrun9 ?_
  by_cases hb9 : r9.headD 0 = 0
  · rw [installHeaderE.k_consts_resolve_ffast.arm1 p _ _ _ _ _ hb9]
    have ex9 : x9 = false := by rw [← hx9]; simpa using hb9
    rw [ex9]
    refine RefE.ite_neg (by decide) ?_
    rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 0] m9 with e10 | ⟨r10, m10⟩
    · rw [installHeaderE.k_unresolved_consts_error.none]
      intro hG
      obtain ⟨M9, hC9⟩ := hS9.core
      rw [hty]
      exact uce_errClaim_lo hG.uce hG.nv hC9 hwtl (by decide) h10 "type"
    · rw [installHeaderE.k_unresolved_consts_error.abort1]; exact RefE.of_cls0 rfl
  rw [installHeaderE.k_consts_resolve_ffast.arm2 p _ _ _ _ _ hb9]
  have ex9 : x9 = true := by rw [← hx9]; simpa using hb9
  rw [ex9]
  exact RefE.ite_pos rfl (RefE.ret rfl
    ⟨hS9, hg4.trans (hg6.trans (hg7.trans (hg8.trans hg9))), hCr9.crOK, hA9⟩)

end L.Arena
