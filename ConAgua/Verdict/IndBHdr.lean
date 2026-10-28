import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC
import ConAgua.Verdict.VCtx
import ConAgua.Arena.IndT.Base
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# `class_const_ok_header`, `class_const_ok`: one model and one refinement for both outcomes

`class_const_ok_header` is `classConstOk`'s guards (the twin prefix `cchT`, `cchT_bind`): its
`l_model … unified` model lifts the callees outside the verdict closure, and `cch_ref` refines
`cchT` under `StageT` (`reserved_contains`' hit as in `DeclHdrE.lean`, copied under `ib` names);
the consts-resolve site calls `unresolved_consts_error` (`uce_errClaim_hi`, so `G` is
`VerdictCtxU`). `class_const_ok` (`cco_ref`) is the guards through `cch_ref`, then the knot's
`infer_type_core` and `ensure_sort_core`; its ok half is `classConstOk_refinesT` and
`class_rec_ty_ok`'s refinement, its error half the callers' error claims.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

l_model classConstOkHeaderE_spec (p : Prog) (hP : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
  fns [hh ↦ classConstOkHeaderE]
  specs [envFind_specW p hP.ix hP.rowGet hP.find n, resCont_spec p hP.resF hP.resC n,
    cvLps_specW p hP.alloc hP.copy hP.eti hP.lps n, slNodup_spec p hP.cont hP.nodup n,
    lbbF_spec p hP.bvb n, hffF_spec p hP.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] gen 20 heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The twin's guards of `classConstOk`** (the prefix `class_const_ok_header` stands for): the
syntactic checks of the constant, in `classConstOk`'s order and with its messages. -/
def cchT (fe : IFEnv) (cv : IConstantVal) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid "reserved basis name")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters in")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.internal "generated recursor: loose bound variable in type of")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.internal "generated recursor: free variable in type of")
  unless ← allLevelParamsDefined cv.levelParams cv.type do
    fail (.invalid "undeclared universe parameter in type of")
  unless ← constsResolveFFast fe cv.type do
    fail (← unresolvedConstsError "type of" cv.type)

/-- `classConstOk` is its guards, then the inference. -/
theorem cchT_bind (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    ConRon.Arena.classConstOk mode fe cv = cchT fe cv >>= fun _ => (do
      let stype ← inferTypeCore mode fe checkFuel 0 cv.type
      let _u ← ensureSortCore mode fe checkFuel 0 stype) := by
  unfold ConRon.Arena.classConstOk cchT
  by_cases h1 : (fe.find? cv.name).isSome = true <;> simp only [h1, ite_true, ite_false, Bool.false_eq_true, fail_bindAM, bind_assoc]
  congr 1; funext b2
  by_cases h2 : b2.contains cv.name = true <;> simp only [h2, ite_true, ite_false, Bool.false_eq_true, fail_bindAM]
  by_cases h3 : nameNodup cv.levelParams = true <;> simp only [h3, ite_true, ite_false, Bool.false_eq_true, fail_bindAM, bind_assoc]
  congr 1; funext b4
  by_cases h4 : b4 = true <;> simp only [h4, ite_true, ite_false, Bool.false_eq_true, fail_bindAM, bind_assoc]
  congr 1; funext b5
  by_cases h5 : b5 = true <;> simp only [h5, ite_true, ite_false, Bool.false_eq_true, fail_bindAM, bind_assoc]
  congr 1; funext b6
  by_cases h6 : b6 = true <;> simp only [h6, ite_true, ite_false, Bool.false_eq_true, fail_bindAM, bind_assoc]
  congr 1; funext b7
  by_cases h7 : b7 = true <;> simp only [h7, ite_true, ite_false, Bool.false_eq_true, fail_bindAM, bind_assoc, pure_bind]

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
theorem ibResContW_hit {m : Mem} {a : AState} {n : Nat} {x : Word}
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
  obtain ⟨i, hi, e⟩ := ibResFromW_hit n m x 0 c (by simp) hc h
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
  exact ⟨i, hi, by rw [e]⟩


/-- What `class_const_ok_header` gives besides the twin's run of `classConstOk`'s guards (from `m`):
the stage invariant, the growth, the abstraction memo carried. -/
structure CchPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  afr : AFr m m'

/-- **`class_const_ok_header` refines `classConstOk`'s guards (`cchT`), both outcomes**: the
name's guards (`env_find`, `reserved_contains`), the level parameters' copy and their
duplicates (`cv_lps`, `sl_nodup`), the four walks under `StageT` (`lbbF_okT`, `hffF_okT`,
`apdF_okT`, `crfF_okT`), each a reject site of the twin's; the consts-resolve site calls
`unresolved_consts_error` (`uce_errClaim_hi`). -/
theorem cch_ref {p : Prog} (hApd : ApdF p) (hCrf : CrfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (classConstOkHeaderE p n m vis q) (cchT fe cv) a
      (fun v _ a' => CchPost dn vis fe m v.2 a') := by
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => rw [classConstOkHeaderE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [classConstOkHeaderE.arm1, ex, et]
  simp only [cchT, fail_bindAM]
  -- `env_find(x, vis)`
  rcases h1 : envFindW m wx vis with _ | ⟨r1, m1⟩
  · rw [liftE_none, classConstOkHeaderE.k_env_find.eq_1]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [classConstOkHeaderE.k_env_find.abort1 _ _ _ _ _ _ _ _ hb1]
    have : (fe.find? cv.name).isSome = true := by
      rw [hname]; exact envFindW_hitSome h1 hS.stage.1.env hwxl hb1
    exact fun _ => ErrClaim.ite_pos this (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_env_find.arm1 _ _ _ _ _ _ _ _ (by simpa using hb1)]
  obtain ⟨hm1, hfind⟩ := envFindW_miss h1 hS.stage.1.env hwxl (by simpa using hb1)
  rw [hm1]
  have hfind' : (fe.find? cv.name).isSome = false := by rw [hname, hfind]; rfl
  refine RefE.ite_neg (by simp [hfind']) ?_
  -- `reserved_contains(x)`
  rcases h2 : resContW n m wx with _ | c
  · rw [liftE_none, classConstOkHeaderE.k_reserved_contains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb2 : c ≠ 0
  · rw [classConstOkHeaderE.k_reserved_contains.abort1 _ _ _ _ _ _ _ hb2]
    obtain ⟨l, hrunR, hcl⟩ := ibResContW_hit hb2 h2 hS.stage.1.pins
    refine fun _ => ErrClaim.bind_right hrunR (ErrClaim.ite_pos ?_ (ErrClaim.fail_abort _ _ rfl))
    rw [hname]; exact hcl
  have hc0 : c = 0 := by simpa using hb2
  subst hc0
  rw [classConstOkHeaderE.k_reserved_contains.arm1 _ _ _ _ _ _ _ rfl]
  obtain ⟨l, hrunR, hcl⟩ := resContW_miss hwxl h2 hS.stage.1.pins
  refine RefE.bind_right hrunR (RefE.ite_neg ?_ ?_)
  · rw [hname, hcl]; decide
  -- `cv_lps(q)`
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq0
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero =>
    rw [show cvLpsW 0 m q = none by simp [cvLpsW], liftE_none, classConstOkHeaderE.k_cv_lps.none]
    exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [cvLpsW_step, e1, e2]
  rcases h4 : erToIwW n m w1 w2 with _ | ⟨r4, m4⟩
  · rw [liftE_none, classConstOkHeaderE.k_cv_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, classConstOkHeaderE.k_cv_lps.eq_2]
  obtain ⟨-, hr4t, hdec4, hS4R, hg4, htop4⟩ := erToIwW_stage h4 hS.stage hsrc
  have hS4 := StageT.of_iw hS hS4R (erToIwW_frame h4 hS.stage hsrc)
  have hCr4 := CrOK.frame hCr (erToIwW_frame h4 hS.stage hsrc) (by decide) (by decide)
  have hA4 : AFr m m4 := erToIwW_afr h4
  rw [hr4t]
  have hdecL : decHL m4 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [hdec4]; exact hsl
  -- `sl_nodup(o, l)`
  rcases h5 : nodupW (n + 1) m4 (r4.headD 0) w2 with _ | d
  · rw [liftE_none, classConstOkHeaderE.k_sl_nodup.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have htopb : iwTop m4 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m4 _ _ _ hdecL (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h5
  by_cases hb5 : d = 0
  · rw [classConstOkHeaderE.k_sl_nodup.abort1 _ _ _ _ _ _ _ _ hb5]
    have hnd : nameNodup cv.levelParams = false := by
      rw [hlps, nameNodup_map ws hwsl]
      by_cases hn : ws.Nodup
      · rw [ite_eq_left hn, hb5] at hd; exact absurd hd (by decide)
      · simp [hn]
    exact fun _ => ErrClaim.ite_neg (by simp [hnd]) (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_sl_nodup.arm1 _ _ _ _ _ _ _ _ hb5]
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · rw [ite_eq_right hn] at hd; exact absurd hd hb5
  refine RefE.ite_pos hnd ?_
  -- `loose_bvars_bounded_fast(4000000000, 0, t)`
  rcases h6 : lbbF m4 [4000000000, 0, wt] with _ | ⟨r6, m6⟩
  · rw [liftE_none, classConstOkHeaderE.k_loose_bvars_bounded_fast.eq_1]
    exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x6, a6, hrun6, hS6, hg6, hx6, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 wt hwtl m4 m6 a r6 h6 hS4
  have hCr6 := CrOK.frame hCr4 (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m m6 := hA4.trans (AFr.of_frame (lbbF_frame h6))
  rw [fuelW, show ((0 : Word).toNat) = 0 from rfl, ← hty] at hrun6
  refine RefE.bind_right hrun6 ?_
  by_cases hb6 : r6.headD 0 = 0
  · rw [classConstOkHeaderE.k_loose_bvars_bounded_fast.abort1 _ _ _ _ _ _ _ _ hb6]
    exact RefE.of_cls0 rfl
  rw [classConstOkHeaderE.k_loose_bvars_bounded_fast.arm1 _ _ _ _ _ _ _ _ hb6]
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  rw [ex6]
  refine RefE.ite_pos rfl ?_
  -- `has_fvar_fast(4000000000, t)`
  rcases h7 : hffF m6 [4000000000, wt] with _ | ⟨r7, m7⟩
  · rw [liftE_none, classConstOkHeaderE.k_has_fvar_fast.eq_1]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7, -⟩ :=
    hffF_okT dn vis fe 4000000000 wt hwtl m6 m7 a6 r7 h7 hS6
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  rw [fuelW, ← hty] at hrun7
  refine RefE.bind_right hrun7 ?_
  by_cases hb7 : r7.headD 0 ≠ 0
  · rw [classConstOkHeaderE.k_has_fvar_fast.abort1 _ _ _ _ _ _ _ _ hb7]
    exact RefE.of_cls0 rfl
  have hb7' : r7.headD 0 = 0 := by simpa using hb7
  rw [classConstOkHeaderE.k_has_fvar_fast.arm1 _ _ _ _ _ _ _ _ hb7']
  have ex7 : x7 = false := by rw [← hx7]; simpa using hb7
  rw [ex7]
  refine RefE.ite_neg (by decide) ?_
  -- `all_level_params_defined(o, l, t)`
  have hdec7 : decHL m7 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  have hst7 : a7.store = a.store := by
    rw [hffF_store hrun7, lbbF_store hrun6]
  rcases h8 : callE p (n + 1) "all_level_params_defined" [r4.headD 0, w2, wt] m7 with e8 | ⟨r8, m8⟩
  · rw [classConstOkHeaderE.k_all_level_params_defined.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h8
  have h8' := apdF_of_callW hApd (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    apdF_okT dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams m7 m8 a7 r8 h8'
      ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩
  have hA8 : AFr m m8 := fun hA => absOK_apdF h8' (hA7 hA) hS8
  rw [← hty] at hrun8
  refine RefE.bind_right hrun8 ?_
  by_cases hb8 : r8.headD 0 = 0
  · rw [classConstOkHeaderE.k_all_level_params_defined.abort1 _ _ _ _ _ _ hb8]
    have ex8 : x8 = false := by rw [← hx8]; simpa using hb8
    rw [ex8]
    exact fun _ => ErrClaim.ite_neg (by decide) (ErrClaim.fail_abort _ _ rfl)
  rw [classConstOkHeaderE.k_all_level_params_defined.arm1 _ _ _ _ _ _ hb8]
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  rw [ex8]
  refine RefE.ite_pos rfl ?_
  -- `consts_resolve_ffast(vis, t)`
  rcases h9 : callE p (n + 1) "consts_resolve_ffast" [vis, wt] m8 with e9 | ⟨r9, m9⟩
  · rw [classConstOkHeaderE.k_consts_resolve_ffast.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h9
  have h9' := crfF_of_callW hCrf (callW_of_callE h9)
  obtain ⟨x9, a9, hrun9, ⟨hS9, hg9, hx9, -⟩, hCr9⟩ :=
    crfF_okT dn vis fe wt hwtl m8 m9 a8 r9 h9' ⟨hS8, hCr8.crMemo⟩
  rw [← hty] at hrun9
  refine RefE.bind_right hrun9 ?_
  by_cases hb9 : r9.headD 0 = 0
  · rw [classConstOkHeaderE.k_consts_resolve_ffast.arm1 _ _ _ _ _ _ hb9]
    have ex9 : x9 = false := by rw [← hx9]; simpa using hb9
    rw [ex9]
    refine RefE.ite_neg (by decide) ?_
    rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 2] m9 with e10 | ⟨r10, m10⟩
    · rw [classConstOkHeaderE.k_unresolved_consts_error.eq_1]
      obtain ⟨M9, hC9⟩ := hS9.core
      rw [hty]
      exact fun hG => uce_errClaim_hi hG.uce hG.nv hC9.arena.1 hC9.pins hwtl (by decide) h10 "type of"
    · rw [classConstOkHeaderE.k_unresolved_consts_error.abort1]
      exact RefE.of_cls0 rfl
  rw [classConstOkHeaderE.k_consts_resolve_ffast.arm2 _ _ _ _ _ _ hb9]
  have ex9 : x9 = true := by rw [← hx9]; simpa using hb9
  rw [ex9]
  exact RefE.ite_pos rfl (RefE.ret rfl ⟨hS9, hg4.trans (hg6.trans (hg7.trans (hg8.trans hg9))),
    fun hA => absOK_crfF h9' (hA8 hA) hCr9 hS9⟩)

end L.Arena

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model classConstOkE_spec (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hf : p.lookup "class_const_ok" = some classConstOkL)
  fns [hf ↦ classConstOkE] specs [classConstOkHeaderE_spec p h hh n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_const_ok` gives besides the twin's run (from `m`): the stage invariant, the
growth, the abstraction memo. -/
structure CcoPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

section cco
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hq hApd hCrk in
/-- **`class_const_ok` refines `classConstOk`, both outcomes**: its guards (`cch_ref`, against
`cchT`: `cchT_bind`), then the knot's `infer_type_core` and `ensure_sort_core` (their ok halves
`Base.lean`'s, their errors the core stubs' claims). -/
theorem cco_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hq' : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hA : AbsOK m) (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) :
    RefE (VerdictCtxU p) (classConstOkE p n m vis q) (ConRon.Arena.classConstOk V fe cv) a
      (fun v _ a' => CcoPost dn vis fe m v.2 a') := by
  cases n with
  | zero => rw [classConstOkE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [classConstOkE.arm1, cchT_bind]
  have hh := cch_ref hApd hCrk.crf n hS hq' hqb hlps hA.crMemo.crOK
  rcases h1 : classConstOkHeaderE p n m vis q with e1 | ⟨r1, m1⟩
  · rw [h1] at hh
    rw [classConstOkE.k_class_const_ok_header.eq_1]
    exact RefE.bind_left hh
  rw [h1] at hh
  obtain ⟨_, a1, hrun, hS1, hg1, hA1⟩ := hh
  rw [classConstOkE.k_class_const_ok_header.eq_2]
  refine RefE.bind_right hrun ?_
  have hq1 : decCV (erA m1) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg1) hq'
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq1
  have et : rdW (m1.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  have hA1 : AbsOK m1 := hA1 hA
  rw [et, hty]
  rcases h2 : callE p n "infer_type_core" [vis, 0, wt] m1 with e2 | ⟨r2, m2⟩
  · rw [classConstOkE.k_infer_type_core.eq_1]
    exact RefE.bind_left fun hG => hG.core.inferTypeCore n (by omega) hS1 0 wt hwtl _ h2
  rw [classConstOkE.k_infer_type_core.arm1]
  have hi := RSim.coreAbs hq.closed (by decide) hA1 (inferT_rsim hq n (by omega) hS1 0 wt hwtl)
  rw [show (0 : Word).toNat = 0 from rfl] at hi
  obtain ⟨st, a2, hrun2, ⟨⟨hS2, hg2, hb2, rfl⟩, hA2⟩⟩ := hi (r2, m2) (callW_of_callE h2)
  refine RefE.bind_right hrun2 ?_
  rcases h3 : callE p n "ensure_sort_core" [vis, 0, r2.headD 0] m2 with e3 | ⟨r3, m3⟩
  · rw [classConstOkE.k_ensure_sort_core.eq_1]
    exact RefE.bind_left fun hG => hG.core.ensureSortCore n (by omega) hS2 0 (r2.headD 0) hb2 _ h3
  rw [classConstOkE.k_ensure_sort_core.arm1]
  have he := RSim.coreAbs hq.closed (by decide) hA2
    (ensureSortT_rsim hq n (by omega) hS2 0 (r2.headD 0) hb2)
  rw [show (0 : Word).toNat = 0 from rfl] at he
  obtain ⟨u, a3, hrun3, ⟨⟨hS3, hg3, -⟩, hA3⟩⟩ := he (r3, m3) (callW_of_callE h3)
  exact RefE.bind_right hrun3 (RefE.ret rfl ⟨hS3, (hg1.trans hg2).trans hg3, hA3⟩)

include hq hApd hCrk in
/-- **`class_const_ok` refines `classConstOk`** under `StageT` (`cco_ref`'s ok half). -/
@[refines ConRon.Arena.classConstOk]
theorem classConstOk_refinesT (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : p.lookup "class_const_ok" = some classConstOkL) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q : Word) (cv : IConstantVal) (hS : StageT dn vis fe s₀.mem a₀)
    (hq' : decCV (erecP s₀.mem) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hA : AbsOK s₀.mem) (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classConstOk V fe cv) a₀ ∧
      KPT dn vis fe s₀.mem decUnit (r, s'.mem) (AM.st (ConRon.Arena.classConstOk V fe cv) a₀)
        (AM.res (ConRon.Arena.classConstOk V fe cv) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (classConstOkE_spec p h hh hc n s₀ vis q)
    (cco_ref hq hApd hCrk n hn hS hq' hqb hA hlps)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, ⟨by rw [hst]; exact hR.stage, hR.grow, trivial⟩, hR.abs⟩

end cco

end L.Ind

end
