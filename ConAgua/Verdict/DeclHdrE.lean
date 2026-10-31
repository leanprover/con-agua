import ConAgua.Arena.IndT.WalkC
import ConAgua.Verdict.DeclValE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# `install_header`'s refinement

`install_header`: one unified model and one refinement for both outcomes (`ih_ref`, under
`StageT`; `install_value_guards`', on the same pattern, is `ivg_ref` in `DeclValE.lean`). The
callees are all outside the verdict closure (`nvFns`), so their failures claim nothing; the abort sites are the twin's `fail`s. The
consts-resolve site is a call of `unresolved_consts_error` (it always fails): its error's class is
the twin's `unresolvedConstsErrorL (← strLitSupported fe) …` (`uce_errClaim_lo`,
`UnresolvedE.lean`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **The model of `install_header`, both outcomes**: the callees outside the verdict closure with
`Option` models lifted; `all_level_params_defined`, `consts_resolve_ffast` and
`unresolved_consts_error` through their runs. -/
l_model installHeader_specE (p : Prog) (hP : IhProg p)
  fns [hP.ih ↦ installHeaderE]
  specs [envFind_specW p hP.ix hP.rowGet hP.find n, resCont_spec p hP.resF hP.resC n,
    cvLps_specW p hP.alloc hP.copy hP.eti hP.lps n, slNodup_spec p hP.cont hP.nodup n,
    lbbF_spec p hP.bvb n, hffF_spec p hP.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
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
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  dsimp only [installHeaderE.k_env_find]
  refine RefE.guardThen (by rfl)
    (fun hb1 => by rw [hname]; exact envFindW_hitSome h1 hS.stage.check.env hwxl hb1)
    (fun hb => Classical.byContradiction fun hb1 => by
      rw [hname, (envFindW_miss h1 hS.stage.check.env hwxl (by simpa using hb1)).2] at hb; cases hb)
    fun hb1 _ => ?_
  obtain ⟨rfl, -⟩ := envFindW_miss h1 hS.stage.check.env hwxl (by simpa using hb1)
  -- `reserved_contains(x)`
  rcases h2 : resContW n m1 wx with _ | c
  · rw [liftE_none, installHeaderE.k_reserved_contains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb2 : c ≠ 0
  · rw [installHeaderE.k_reserved_contains.abort1 p _ _ _ _ _ _ hb2]
    obtain ⟨l, hrunR, hcl⟩ := resContW_hit hb2 h2 hS.stage.check.pins
    refine RefE.bind_right hrunR (RefE.ite_pos ?_ (fun _ => ErrClaim.fail_abort _ _ rfl))
    rw [hname]; exact hcl
  have hc0 : c = 0 := by simpa using hb2
  subst hc0
  rw [installHeaderE.k_reserved_contains.arm1 p _ _ _ _ _ _ rfl]
  obtain ⟨l, hrunR, hcl⟩ := resContW_miss hwxl h2 hS.stage.check.pins
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
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  dsimp only [installHeaderE.k_cv_lps]
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
  dsimp only [installHeaderE.k_sl_nodup]
  refine RefE.guardIf (by rfl)
    (fun hb5 => by
      rw [hlps, nameNodup_map ws hwsl]
      by_cases hn : ws.Nodup
      · rw [ite_eq_left hn, hb5] at hd; exact absurd hd (by decide)
      · simp [hn])
    (fun hnd => Classical.byContradiction fun hb5 => by
      rw [hlps, nameNodup_map ws hwsl] at hnd
      by_cases hn : ws.Nodup
      · simp [hn] at hnd
      · rw [ite_eq_right hn] at hd; exact hb5 hd) fun _ _ => ?_
  -- `loose_bvars_bounded_fast(4000000000, 0, t)`
  rw [hty]
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_okT dn vis fe 4000000000 0 wt hwtl m4 m' a r h hS4)
    fun r6 x6 m6 a6 h6 hrun6 ⟨hS6, hg6, hx6, _⟩ => ?_
  have hCr6 := CrOK.frame hCr4 (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m1 m6 := hA4.trans (AFr.of_frame (lbbF_frame h6))
  dsimp only [installHeaderE.k_loose_bvars_bounded_fast]
  refine RefE.guardIf rfl (fun hb6 => by rw [← hx6]; simpa using hb6)
    (fun hb6 => by rw [← hx6] at hb6; simpa using hb6) fun _ _ => ?_
  -- `has_fvar_fast(4000000000, t)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => hffF_okT dn vis fe 4000000000 wt hwtl m6 m' a6 r h hS6)
    fun r7 x7 m7 a7 h7 hrun7 ⟨hS7, hg7, hx7, _⟩ => ?_
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m1 m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  dsimp only [installHeaderE.k_has_fvar_fast]
  refine RefE.guardThen rfl (fun hb7 => by rw [← hx7]; simpa using hb7)
    (fun hb7 => by rw [← hx7] at hb7; simpa using hb7) fun _ _ => ?_
  -- `all_level_params_defined(o, l, t)`
  have hdec7 : decHL m7 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  have hst7 : a7.store = a.store := (hffF_store hrun7).trans (lbbF_store hrun6)
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h8 => nvl hG.nv (by decide +kernel) h8)
    (fun b h8 => apdF_okT dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams m7 b.2 a7 b.1
      (apdF_of_callW hap h8) ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩)
    fun r8 m8 x8 a8 h8 _ ⟨hS8, hg8, hx8, _⟩ => ?_
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  have hA8 : AFr m1 m8 := fun hA => absOK_apdF h8' (hA7 hA) hS8
  dsimp only [installHeaderE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb8 => by rw [← hx8]; simpa using hb8)
    (fun hb8 => by rw [← hx8] at hb8; simpa using hb8) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, t)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT dn vis fe wt hwtl m8 b.2 a8 b.1 (crfF_of_callW hCrf h9) ⟨hS8, hCr8.crMemo⟩)
    fun r9 m9 x9 a9 h9 _ ⟨⟨hS9, hg9, hx9, _⟩, hCr9⟩ => ?_
  have hA9 : AFr m1 m9 := fun hA => absOK_crfF (crfF_of_callW hCrf (callW_of_callE h9)) (hA8 hA) hCr9 hS9
  dsimp only [installHeaderE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun hb9 => by rw [← hx9]; simpa using hb9)
    (fun hb9 => by rw [← hx9] at hb9; simpa using hb9) (fun _ _ => ?_) fun _ _ => RefE.ret rfl
      ⟨hS9, hg4.trans (hg6.trans (hg7.trans (hg8.trans hg9))), hCr9.crOK, hA9⟩
  rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 0] m9 with e10 | ⟨r10, m10⟩ <;>
    dsimp only [installHeaderE.k_unresolved_consts_error]
  · obtain ⟨M9, hC9⟩ := hS9.core
    exact fun hG => uce_errClaim_lo hG.uce hG.nv hC9 hwtl (by decide) h10 "type"
  · exact RefE.of_cls0 rfl

end L.Arena
