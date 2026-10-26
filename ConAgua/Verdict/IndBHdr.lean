import ConAgua.Arena.IndT.RecGen3
import ConAgua.Verdict.DeclValE
import ConAgua.Arena.DeclStep
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.DeclValT
import ConAgua.Checker.NoVerdictClosed

/-!
# `class_const_ok_header`'s error claim (lane `verdicts-b`, helper `ib`)

The same body as `install_header` (`DeclHdrE.lean` of helper `d`, whose lemmas are copied here under
`ib` names): a failing call of class `1`/`2` claims that the twin's `classConstOk` fails.
The consts-resolve abort of the current code is class `0`.
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

l_model classConstOkHeader_specE (p : Prog) (hf : p.lookup "class_const_ok_header" = some classConstOkHeader)
  fns [hf ↦ classConstOkHeaderE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

def ibNvList : List FnName :=
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

theorem ibNv_mem : ∀ f ∈ ibNvList, f ∈ L.Checker.nvFns := by
  decide +kernel

/-- A failing callee of the list claims nothing. -/
theorem ibNvl {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {α : Type} {T : AM α} {a : AState}
    {f : FnName} (hf : f ∈ ibNvList) {n : Nat} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hnv (ibNv_mem f hf) h

/-- **A hit of `env_find` is a hit of `find?`**. -/
theorem ibEnvFindW_hitSome {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 ≠ 0) : (fe.find? (decI w)).isSome = true := by
  unfold envFindW at h
  by_cases ht : 2 < tagW w
  · simp [ht] at h
  rw [if_neg ht] at h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  by_cases hc : rowCW m w = 0
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [if_neg hc] at h
  have hv : rowCW m w - 1 < vis := by
    refine Classical.byContradiction fun hv => ?_
    rw [if_neg hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [if_pos hv] at h
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
    simp [e]; omega

/-- A hit of `reserved_from`: one of the reserved words is `x`. -/
theorem ibResFromW_hit (n : Nat) : ∀ (m : Mem) (x j c : Word), j.toNat ≤ 16 → c ≠ 0 →
    resFromW n m x j = some c → ∃ i, i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j c _ _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j c hj hc h
    rw [resFromW_step] at h
    have hn16 : ¬ 16 ≤ j := by
      by_cases h16 : 16 ≤ j
      · rw [if_pos h16] at h; simp at h; exact absurd h.symm hc
      · exact h16
    rw [if_neg hn16] at h
    have hj16 : j.toNat < 16 := by
      refine Classical.byContradiction fun hh => hn16 ?_
      rw [UInt64.le_iff_toNat_le]; simp; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [if_neg he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    exact ih m x (j + 1) c (by omega) hc h

/-- **A hit of `reserved_contains` is a hit of `reservedBasisNames`.** -/
theorem ibResContW_hit {m : Mem} {a : AState} {n : Nat} {x : Word}
    {c : Word} (hc : c ≠ 0) (h : resContW n m x = some c) (hP : PinsR m a.pins) :
    ∃ l, reservedBasisNames.run a = .ok (l, a) ∧ l.contains (decI x) = true := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [if_pos h0] at h; simp at h
  rw [if_neg h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  obtain ⟨i, hi, e⟩ := ibResFromW_hit n m x 0 c (by simp) hc h
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
  exact ⟨i, hi, by rw [e]⟩


theorem classConstOkHeader_claim {p : Prog} (hP : IhProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m : Mem} {q : Word} {cv : IConstantVal} {e : Err}
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : callE p n "class_const_ok_header" [vis, q] m = .error e) (hS : StageT dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ErrClaim (ConRon.Arena.classConstOk V fe cv) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classConstOkHeader_specE p hh n ⟨m, Locals.init []⟩ vis q) hc
    (Err.code_ne_of_cls hk0)
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => rw [classConstOkHeaderE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [classConstOkHeaderE.arm1, ex, et] at hW
  simp only [ConRon.Arena.classConstOk, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]
  -- `env_find(x, vis)`
  cases h1 : callE p n "env_find" [wx, vis] m with
  | error e1 =>
    rw [h1, classConstOkHeaderE.k_env_find.none] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE
    (envFind_specW p hP.ix hP.rowGet hP.find n ⟨m, Locals.init []⟩ wx vis) h1
  subst hs1
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [classConstOkHeaderE.k_env_find.eq_2, if_pos hb1] at hW; cases hW
    have : (fe.find? cv.name).isSome = true := by
      rw [hname]; exact ibEnvFindW_hitSome hW1 hS.stage.1.env hwxl hb1
    exact ErrClaim.ite_pos this (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_env_find.eq_2, if_neg hb1] at hW
  obtain ⟨rfl, hfind⟩ := envFindW_miss hW1 hS.stage.1.env hwxl (by simpa using hb1)
  have hfind' : (fe.find? cv.name).isSome = false := by rw [hname, hfind]; rfl
  refine ErrClaim.ite_neg (by simp [hfind']) ?_
  -- `reserved_contains(x)`
  cases h2 : callE p n "reserved_contains" [wx] s1.mem with
  | error e2 =>
    rw [h2, classConstOkHeaderE.k_reserved_contains.none] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨s2, hs2, -, hm2, hW2⟩ := triple_of_callE
    (resCont_spec p hP.resF hP.resC n ⟨s1.mem, Locals.init []⟩ wx) h2
  have hm2' : m2 = s1.mem := hs2.symm.trans hm2
  subst hm2'
  have hW2' : resContW n s1.mem wx = some (r2.headD 0) := hW2
  by_cases hb2 : r2.headD 0 ≠ 0
  · rw [classConstOkHeaderE.k_reserved_contains.eq_2, if_pos hb2] at hW; cases hW
    obtain ⟨l, hrunR, hcl⟩ := ibResContW_hit hb2 hW2' hS.stage.1.pins
    refine ErrClaim.bind_right hrunR (ErrClaim.ite_pos ?_ (ErrClaim.fail_abort _ _ rfl))
    rw [hname]; exact hcl
  rw [classConstOkHeaderE.k_reserved_contains.eq_2, if_neg hb2] at hW
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
    rw [h4, classConstOkHeaderE.k_cv_lps.none] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, classConstOkHeaderE.k_cv_lps.eq_2] at hW
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
    rw [h5, classConstOkHeaderE.k_sl_nodup.eq_1] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h5
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
  · rw [classConstOkHeaderE.k_sl_nodup.eq_2, if_pos hb5] at hW; cases hW
    have hnd : nameNodup cv.levelParams = false := by
      rw [hlps, nameNodup_map ws hwsl]
      by_cases hn : ws.Nodup
      · rw [if_pos hn, hb5] at hd; exact absurd hd (by decide)
      · simp [hn]
    exact ErrClaim.ite_neg (by simp [hnd]) (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_sl_nodup.eq_2, if_neg hb5] at hW
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · rw [if_neg hn] at hd; exact absurd hd hb5
  refine ErrClaim.ite_pos hnd ?_
  -- `loose_bvars_bounded_fast(4000000000, 0, t)`
  cases h6 : callE p (n + 1) "loose_bvars_bounded_fast" [4000000000, 0, wt] s4.mem with
  | error e6 =>
    rw [h6, classConstOkHeaderE.k_loose_bvars_bounded_fast.none] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h6
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
  · rw [classConstOkHeaderE.k_loose_bvars_bounded_fast.abort1 p _ _ _ _ _ _ _ hb6] at hW
    cases hW
    have ex6 : x6 = false := by rw [← hx6]; simpa using hb6
    rw [ex6]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_loose_bvars_bounded_fast.arm1 p _ _ _ _ _ _ _ hb6] at hW
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  rw [ex6]
  refine ErrClaim.ite_pos rfl ?_
  -- `has_fvar_fast(4000000000, t)`
  cases h7 : callE p (n + 1) "has_fvar_fast" [4000000000, wt] s6.mem with
  | error e7 =>
    rw [h7, classConstOkHeaderE.k_has_fvar_fast.eq_1] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h7
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
  · rw [classConstOkHeaderE.k_has_fvar_fast.abort1 p _ _ _ _ _ _ _ hb7] at hW
    cases hW
    have ex7 : x7 = true := by rw [← hx7]; simpa using hb7
    rw [ex7]
    exact ErrClaim.ite_pos rfl (ErrClaim.fail_abort _ _ rfl)
  have hb7' : r7.headD 0 = 0 := by simpa using hb7
  rw [classConstOkHeaderE.k_has_fvar_fast.arm1 p _ _ _ _ _ _ _ hb7'] at hW
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
    rw [h8, classConstOkHeaderE.k_all_level_params_defined.eq_1] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h8
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
  · rw [classConstOkHeaderE.k_all_level_params_defined.abort1 p _ _ _ _ _ hb8] at hW
    cases hW
    have ex8 : x8 = false := by rw [← hx8]; simpa using hb8
    rw [ex8]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_all_level_params_defined.arm1 p _ _ _ _ _ hb8] at hW
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  rw [ex8]
  refine ErrClaim.ite_pos rfl ?_
  -- `consts_resolve_ffast(vis, t)`
  cases h9 : callE p (n + 1) "consts_resolve_ffast" [vis, wt] m8 with
  | error e9 =>
    rw [h9, classConstOkHeaderE.k_consts_resolve_ffast.none] at hW; cases hW
    exact ibNvl hnv (by decide +kernel) h9
  | ok q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9] at hW
  obtain ⟨x9, a9, hrun9, ⟨hS9, hg9, hx9, -⟩, hCr9⟩ :=
    crfF_okT dn vis fe wt hwtl m8 m9 a8 r9 (crfF_of_callW hkp.crf (callW_of_callE h9))
      ⟨hS8, hCr8.crMemo⟩
  rw [← hty] at hrun9
  refine ErrClaim.bind_right hrun9 ?_
  by_cases hb9 : r9.headD 0 = 0
  · rw [classConstOkHeaderE.k_consts_resolve_ffast.abort1 p _ _ hb9] at hW
    cases hW
    exact ErrClaim.of_cls0 rfl
  rw [classConstOkHeaderE.k_consts_resolve_ffast.arm1 p _ _ hb9] at hW
  cases hW

end L.Arena
