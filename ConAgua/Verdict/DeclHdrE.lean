import ConAgua.Verdict.DeclValE
import ConAgua.Verdict.UnresolvedE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

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

l_model installHeader_specE (p : Prog) (hf : p.lookup "install_header" = some installHeaderL)
  fns [hf ↦ installHeaderE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

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

/-- **A hit of `env_find` is a hit of `find?`**. -/
theorem envFindW_hitSome {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 ≠ 0) : (fe.find? (decI w)).isSome = true := by
  unfold envFindW at h
  by_cases ht : 2 < tagW w
  · simp [ht] at h
  rw [ite_eq_right ht] at h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  by_cases hc : rowCW m w = 0
  · rw [ite_eq_left hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [ite_eq_right hc] at h
  have hv : rowCW m w - 1 < vis := by
    refine Classical.byContradiction fun hv => ?_
    rw [ite_eq_right hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [ite_eq_left hv] at h
  rw [rowCW_eq m w hw ht2] at hc hv
  have hk := hE.keys (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk
  simp only [rowW, hc, ite_false, Option.map_some] at hk
  have hv' : (rowC m w).toNat - 1 < vis.toNat := by
    have hc' : (rowC m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at hv
    simpa using hv
  simp only [IFEnv.find?, hE.vis]
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e] at hk
  | some r =>
    obtain ⟨c, ci⟩ := r
    simp only [e, Option.map_some, Option.some.injEq] at hk
    simp; omega

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

/-- **`install_header`'s error claim under `StageT`** (the error half of `ihW_okT`). -/
theorem ihE_okT {p : Prog} (hP : IhProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hU : UceProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m : Mem} {q : Word} {cv : IConstantVal} {e : Err}
    (hc : callE p n "install_header" [vis, q] m = .error e) (hS : StageT dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ErrClaim (installHeader fe cv) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installHeader_specE p hP.ih n ⟨m, Locals.init []⟩ vis q) hc
    (Err.code_ne_of_cls hk0)
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => rw [installHeaderE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [installHeaderE.arm1, ex, et] at hW
  simp only [installHeader, fail_bindAM]
  -- `env_find(x, vis)`
  cases h1 : callE p n "env_find" [wx, vis] m with
  | error e1 =>
    rw [h1, installHeaderE.k_env_find.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE
    (envFind_specW p hP.ix hP.rowGet hP.find n ⟨m, Locals.init []⟩ wx vis) h1
  subst hs1
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [installHeaderE.k_env_find.eq_2, ite_eq_left hb1] at hW; cases hW
    have : (fe.find? cv.name).isSome = true := by
      rw [hname]; exact envFindW_hitSome hW1 hS.stage.1.env hwxl hb1
    exact ErrClaim.ite_pos this (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_env_find.eq_2, ite_eq_right hb1] at hW
  obtain ⟨rfl, hfind⟩ := envFindW_miss hW1 hS.stage.1.env hwxl (by simpa using hb1)
  have hfind' : (fe.find? cv.name).isSome = false := by rw [hname, hfind]; rfl
  refine ErrClaim.ite_neg (by simp [hfind']) ?_
  -- `reserved_contains(x)`
  cases h2 : callE p n "reserved_contains" [wx] s1.mem with
  | error e2 =>
    rw [h2, installHeaderE.k_reserved_contains.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨s2, hs2, -, hm2, hW2⟩ := triple_of_callE
    (resCont_spec p hP.resF hP.resC n ⟨s1.mem, Locals.init []⟩ wx) h2
  have hm2' : m2 = s1.mem := hs2.symm.trans hm2
  subst hm2'
  have hW2' : resContW n s1.mem wx = some (r2.headD 0) := hW2
  by_cases hb2 : r2.headD 0 ≠ 0
  · rw [installHeaderE.k_reserved_contains.eq_2, ite_eq_left hb2] at hW; cases hW
    obtain ⟨l, hrunR, hcl⟩ := resContW_hit hb2 hW2' hS.stage.1.pins
    refine ErrClaim.bind_right hrunR (ErrClaim.ite_pos ?_ (ErrClaim.fail_abort _ _ rfl))
    rw [hname]; exact hcl
  rw [installHeaderE.k_reserved_contains.eq_2, ite_eq_right hb2] at hW
  have hb2' : r2.headD 0 = 0 := by simpa using hb2
  rw [hb2'] at hW2'
  obtain ⟨l, hrunR, hcl⟩ := resContW_miss hwxl hW2' hS.stage.1.pins
  refine ErrClaim.bind_right hrunR (ErrClaim.ite_neg ?_ ?_)
  · rw [hname, hcl]; decide
  -- `cv_lps(q)`
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq0
  have e1 : rdW (s1.mem.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (s1.mem.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (s1.mem.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases h4 : callE p n "cv_lps" [q] s1.mem with
  | error e4 =>
    rw [h4, installHeaderE.k_cv_lps.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, installHeaderE.k_cv_lps.eq_2] at hW
  obtain ⟨s4, hs4, -, hW4, -⟩ := triple_of_callE
    (cvLps_specW p hP.alloc hP.copy hP.eti hP.lps n ⟨s1.mem, Locals.init []⟩ q) h4
  subst hs4
  cases n with
  | zero => simp [cvLpsW] at hW4
  | succ n =>
  rw [cvLpsW_step, e1, e2] at hW4
  obtain ⟨-, hr4t, hdec4, hS4R, hg4, htop4⟩ := erToIwW_stage hW4 hS.stage hsrc
  have hS4 := StageT.of_iw hS hS4R (erToIwW_frame hW4 hS.stage hsrc)
  have hCr4 := CrOK.frame hCr (erToIwW_frame hW4 hS.stage hsrc) (by decide) (by decide)
  have hdecL : decHL s4.mem (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [hdec4]; exact hsl
  rw [hr4t] at hW
  -- `sl_nodup(o, l)`
  cases h5 : callE p (n + 1) "sl_nodup" [r4.headD 0, w2] s4.mem with
  | error e5 =>
    rw [h5, installHeaderE.k_sl_nodup.eq_1] at hW; cases hW
    exact nvl hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  obtain ⟨s5, hs5, -, hm5, hW5⟩ := triple_of_callE
    (slNodup_spec p hP.cont hP.nodup (n + 1) ⟨s4.mem, Locals.init []⟩ (r4.headD 0) w2) h5
  have hW5' : nodupW (n + 1) s4.mem (r4.headD 0) w2 = some (r5.headD 0) := hW5
  have htopb : iwTop s4.mem < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL s4.mem _ _ _ hdecL (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws hW5'
  have hm5' : m5 = s4.mem := hs5.symm.trans hm5
  subst hm5'
  by_cases hb5 : r5.headD 0 = 0
  · rw [installHeaderE.k_sl_nodup.eq_2, ite_eq_left hb5] at hW; cases hW
    have hnd : nameNodup cv.levelParams = false := by
      rw [hlps, nameNodup_map ws hwsl]
      by_cases hn : ws.Nodup
      · rw [ite_eq_left hn, hb5] at hd; exact absurd hd (by decide)
      · simp [hn]
    exact ErrClaim.ite_neg (by simp [hnd]) (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_sl_nodup.eq_2, ite_eq_right hb5] at hW
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · rw [ite_eq_right hn] at hd; exact absurd hd hb5
  refine ErrClaim.ite_pos hnd ?_
  -- `loose_bvars_bounded_fast(4000000000, 0, t)`
  cases h6 : callE p (n + 1) "loose_bvars_bounded_fast" [4000000000, 0, wt] s4.mem with
  | error e6 =>
    rw [h6, installHeaderE.k_loose_bvars_bounded_fast.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6] at hW
  obtain ⟨s6, hs6, -, hW6⟩ := triple_of_callE
    (lbbF_spec p hP.bvb (n + 1) ⟨s4.mem, Locals.init []⟩ [4000000000, 0, wt]) h6
  subst hs6
  have hCr6 := CrOK.frame hCr4 (lbbF_frame hW6) (by decide) (by decide)
  obtain ⟨x6, a6, hrun6, hS6, hg6, hx6, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 wt hwtl s4.mem s6.mem a r6 hW6 hS4
  rw [fuelW] at hrun6
  rw [show ((0 : Word).toNat) = 0 from rfl, ← hty] at hrun6
  refine ErrClaim.bind_right hrun6 ?_
  by_cases hb6 : r6.headD 0 = 0
  · rw [installHeaderE.k_loose_bvars_bounded_fast.abort1 p _ _ _ _ _ _ _ hb6] at hW
    cases hW
    have ex6 : x6 = false := by rw [← hx6]; simpa using hb6
    rw [ex6]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_loose_bvars_bounded_fast.arm1 p _ _ _ _ _ _ _ hb6] at hW
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  rw [ex6]
  refine ErrClaim.ite_pos rfl ?_
  -- `has_fvar_fast(4000000000, t)`
  cases h7 : callE p (n + 1) "has_fvar_fast" [4000000000, wt] s6.mem with
  | error e7 =>
    rw [h7, installHeaderE.k_has_fvar_fast.eq_1] at hW; cases hW
    exact nvl hnv (by decide +kernel) h7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7] at hW
  obtain ⟨s7, hs7, -, hW7⟩ := triple_of_callE
    (hffF_spec p hP.hf (n + 1) ⟨s6.mem, Locals.init []⟩ [4000000000, wt]) h7
  subst hs7
  have hCr7 := CrOK.frame hCr6 (hffF_frame hW7) (by decide) (by decide)
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7, -⟩ :=
    hffF_okT dn vis fe 4000000000 wt hwtl s6.mem s7.mem a6 r7 hW7 hS6
  rw [fuelW] at hrun7
  rw [← hty] at hrun7
  refine ErrClaim.bind_right hrun7 ?_
  by_cases hb7 : r7.headD 0 ≠ 0
  · rw [installHeaderE.k_has_fvar_fast.abort1 p _ _ _ _ _ _ _ hb7] at hW
    cases hW
    have ex7 : x7 = true := by rw [← hx7]; simpa using hb7
    rw [ex7]
    exact ErrClaim.ite_pos rfl (ErrClaim.fail_abort _ _ rfl)
  have hb7' : r7.headD 0 = 0 := by simpa using hb7
  rw [installHeaderE.k_has_fvar_fast.arm1 p _ _ _ _ _ _ _ hb7'] at hW
  have ex7 : x7 = false := by rw [← hx7]; simpa using hb7
  rw [ex7]
  refine ErrClaim.ite_neg (by decide) ?_
  -- `all_level_params_defined(o, l, t)`
  have hdec7 : decHL s7.mem (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  have hst7 : a7.store = a.store := by
    rw [hffF_store hrun7, lbbF_store hrun6]
  cases h8 : callE p (n + 1) "all_level_params_defined" [r4.headD 0, w2, wt] s7.mem with
  | error e8 =>
    rw [h8, installHeaderE.k_all_level_params_defined.eq_1] at hW; cases hW
    exact nvl hnv (by decide +kernel) h8
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [h8] at hW
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    apdF_okT dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams s7.mem m8 a7 r8 h8'
      ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩
  rw [← hty] at hrun8
  refine ErrClaim.bind_right hrun8 ?_
  by_cases hb8 : r8.headD 0 = 0
  · rw [installHeaderE.k_all_level_params_defined.abort1 p _ _ _ _ _ hb8] at hW
    cases hW
    have ex8 : x8 = false := by rw [← hx8]; simpa using hb8
    rw [ex8]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [installHeaderE.k_all_level_params_defined.arm1 p _ _ _ _ _ hb8] at hW
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  rw [ex8]
  refine ErrClaim.ite_pos rfl ?_
  -- `consts_resolve_ffast(vis, t)`
  cases h9 : callE p (n + 1) "consts_resolve_ffast" [vis, wt] m8 with
  | error e9 =>
    rw [h9, installHeaderE.k_consts_resolve_ffast.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h9
  | ok q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9] at hW
  obtain ⟨x9, a9, hrun9, ⟨hS9, hg9, hx9, -⟩, hCr9⟩ :=
    crfF_okT dn vis fe wt hwtl m8 m9 a8 r9 (crfF_of_callW hkp.crf (callW_of_callE h9))
      ⟨hS8, hCr8.crMemo⟩
  rw [← hty] at hrun9
  refine ErrClaim.bind_right hrun9 ?_
  by_cases hb9 : r9.headD 0 = 0
  · rw [installHeaderE.k_consts_resolve_ffast.arm1 p _ _ _ _ _ hb9] at hW
    have ex9 : x9 = false := by rw [← hx9]; simpa using hb9
    rw [ex9]
    refine ErrClaim.ite_neg (by decide) ?_
    cases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 0] m9 with
    | error e10 =>
      rw [h10, installHeaderE.k_unresolved_consts_error.none] at hW; cases hW
      obtain ⟨M9, hC9⟩ := hS9.core
      rw [hty]
      exact uce_errClaim_lo hU hnv hC9 hwtl (by decide) h10 "type"
    | ok q10 =>
      obtain ⟨r10, m10⟩ := q10
      rw [h10, installHeaderE.k_unresolved_consts_error.abort1] at hW; cases hW
      exact ErrClaim.of_cls0 rfl
  rw [installHeaderE.k_consts_resolve_ffast.arm2 p _ _ _ _ _ hb9] at hW
  cases hW

end L.Arena
