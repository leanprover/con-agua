module

public import ConAgua.Arena.IndT.BlockRM
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndPosSpec.SnocWMfr
import ConAgua.Arena.IndInstallSpec.TabSimSpg
import all ConAgua.Arena.IndPos2
import ConAgua.Arena.QuotCiT
public import ConAgua.Arena.IndPosSpec.BvbWMfr

@[expose] public section

/-!
# `family_telescope`: one model and one refinement for both outcomes

`family_telescope(vis, cv, caps)` (`IndPos2.lean`) refines con-ron's `familyTelescope .verified`
(`ft_ref`): `former_def_headed` by `fdhW_ok`, `reduced_former` (through its call) by `rf_ref`;
the twin's `CoreStep` is `rf_ref`'s (or the identity). The positivity memos stand across it
(`ftE_pos`, from `wtE_pos` and `rfE_pos`: only the core's `hb` memo moves, by its own claim).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `family_telescope`'s model and refinement read. -/
structure FtProg (p : Prog) : Prop extends RfProg p where
  pir : p.lookup "pi_result" = some piResultL
  frs : p.lookup "former_res_sort" = some formerResSortL
  fdh : p.lookup "former_def_headed" = some formerDefHeadedL
  ft : p.lookup "family_telescope" = some familyTelescopeL
  /-- `env_find`'s row reader (`envFind_spec`, for `nest_inst_type_ty`'s lookup). -/
  brg : p.lookup "base_row_get" = some baseRowGetL

set_option experimental.vcgen true in
/-- **`family_telescope`'s unified model**: `reduced_former` through its call, `former_def_headed`
(outside the verdict closure) lifted. -/
l_model ftE_spec (p : Prog) (hP : FtProg p)
  fns [hP.ft ↦ ftE]
  specs [callW_spec p n "former_def_headed"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `family_telescope` gives besides the twin's type `x` (from `m`, `a`): the stage after the
twin's `CoreStep`, the pools grown, the type's word. -/
structure FtPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (v : Word × Mem) (x : EIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env v.2 a'
  grow : IWGrow m v.2
  abs : AbsOK v.2
  core : ConRon.Bridge.CoreStep env fe a a'
  hw : H v.1
  dec : decI v.1 = x


/-! ## The positivity memos across `family_telescope` -/

theorem liftE_ok {α : Type} {o : Option α} {x : α} (h : liftE o = .ok x) : o = some x := by
  cases o <;> simp_all

theorem cvNewW_mfr {m m' : Mem} {nm lo ll ty q : Word} (h : cvNewW m nm lo ll ty = some (q, m')) :
    MFr [] [] m m' := by
  obtain ⟨m1, h1, rfl⟩ := cvNewW_some h
  exact (erAllocW_mfr h1).trans (wrER_mfr _ _ _)

/-- **`whnf_telescope` keeps the positivity memos** (`whnf_top` by the core's claim, the rest by
their frames). -/
theorem wtE_pos {p : Prog} (hcl : CoreStageClosed p) (hW : WtProg p) :
    ∀ (k : Nat) (m m' : Mem) (vis i n e oo ol : Word) (r : List Word),
    PosMR m → wtE p k m vis i n e oo ol = .ok (r, m') → PosMR m' := by
  intro k
  induction k with
  | zero => intro m m' vis i n e oo ol r _ h; rw [wtE.eq_1] at h; cases h
  | succ k ih =>
  intro m m' vis i n e oo ol r hP h
  rw [wtE.arm1] at h
  rcases h1 : callE p k "whnf_top" [vis, i, e] m with e1 | ⟨r1, m1⟩
  · rw [h1, wtE.k_whnf_top.none] at h; cases h
  rw [h1, wtE.k_whnf_top.arm1] at h
  have hP1 := hP.ofCore hcl (by decide) (callW_of_callE h1)
  rcases h2 : callE p k "e_view" [r1.headD 0] m1 with e2 | ⟨r2, m2⟩
  · rw [h2, wtE.k_e_view.none] at h; cases h
  rw [h2] at h
  obtain ⟨s2, hs2, hl2, -, -⟩ := triple_of_callE (eView_spec p hW.view k ⟨m1, Locals.init []⟩ _) h2
  have hm2 : m2 = m1 := by rw [← hs2, hl2]
  subst hm2
  by_cases g2 : r2.headD 0 = 2
  · by_cases hn : n = 0
    · rw [wtE.k_e_view.arm1 _ _ _ _ _ _ _ _ _ g2 hn] at h; cases h; exact hP1
    · rw [wtE.k_e_view.abort1 _ _ _ _ _ _ _ _ _ g2 hn] at h; cases h
  by_cases g6' : ¬ r2.headD 0 = 6
  · have g6 := g6'
    by_cases hn : n = 0
    · rw [wtE.k_e_view.abort3 _ _ _ _ _ _ _ _ _ g2 g6 hn] at h; cases h
    · rw [wtE.k_e_view.abort4 _ _ _ _ _ _ _ _ _ g2 g6 hn] at h; cases h
  have g6 : r2.headD 0 = 6 := Decidable.not_not.mp g6'
  by_cases hn : n = 0
  · rw [wtE.k_e_view.abort2 _ _ _ _ _ _ _ _ _ g2 g6 hn] at h; cases h
  rw [wtE.k_e_view.arm2 _ _ _ _ _ _ _ _ _ g2 g6 hn] at h
  rcases h3 : fvinternW m2 i (r2.tail.headD 0) with _ | ⟨fv, m3⟩
  · rw [h3, liftE_none, wtE.k_intern_fvar.none] at h; cases h
  rw [h3, liftE_some] at h
  have hP3 := hP1.fr (fvinternW_mfr h3)
  by_cases hfv : 4294967296 ≤ fv
  · rw [wtE.k_intern_fvar.abort1 _ _ _ _ _ _ _ _ _ _ _ hfv] at h; cases h
  rw [wtE.k_intern_fvar.arm1 _ _ _ _ _ _ _ _ _ _ _ hfv] at h
  rcases h4 : i1F m3 [CWF, r2.tail.tail.headD 0, fv, 0] with _ | ⟨rb, m4⟩
  · rw [h4, liftE_none, wtE.k_instantiate1_fast.none] at h; cases h
  rw [h4, liftE_some, wtE.k_instantiate1_fast.arm1] at h
  have hP4 := hP3.fr (MFr.ofI1F h4)
  rcases h5 : snocW k m4 oo ol (r2.tail.headD 0) with _ | ⟨ro, m5⟩
  · rw [h5, liftE_none, wtE.k_sl_snoc.none] at h; cases h
  rw [h5, liftE_some, wtE.k_sl_snoc.arm1] at h
  have hP5 := hP4.fr (snocW_mfr h5)
  rcases h6 : wtE p k m5 vis (i + 1) (n - 1) (rb.headD 0) (ro.headD 0) (ro.tail.headD 0) with _ | ⟨r6, m6⟩
  · rw [h6, wtE.k_whnf_telescope.none] at h; cases h
  rw [h6, wtE.k_whnf_telescope.arm1] at h
  cases h
  exact ih _ _ _ _ _ _ _ _ _ hP5 h6

/-- **`reduced_former` keeps the positivity memos.** -/
theorem rfE_pos {p : Prog} (hcl : CoreStageClosed p) (hP : RfProg p) {k : Nat} {m m' : Mem}
    {vis cv n : Word} {r : Word} (hPm : PosMR m) (h : rfE p k m vis cv n = .ok (r, m')) : PosMR m' := by
  rcases k with _ | k
  · rw [rfE.eq_1] at h; cases h
  rw [rfE.arm1] at h
  simp only [rfE.k_whnf_telescope] at h
  split at h
  · cases h
  rename_i r1 m1 h1
  obtain ⟨s1, hs1, -, hfx⟩ := triple_of_callE (wtE_spec p hP.wtp k ⟨m, Locals.init []⟩ vis 0 n _ 0 0) h1
  have hP1 : PosMR m1 := by
    rw [← hs1]; exact wtE_pos hcl hP.wtp _ _ _ _ _ _ _ _ _ _ hPm hfx
  simp only [rfE.k_intern_sort] at h
  split at h
  · cases h
  rename_i r2 m2 h2
  have hP2 := hP1.ofCore hcl (by decide) (liftE_ok h2)
  split at h
  · cases h
  simp only [rfE.k_close_telescope] at h
  split at h
  · cases h
  rename_i r3 m3 h3
  obtain ⟨s3, hs3, -, hc3⟩ := triple_of_callW (closeTelescope_spec p hP.derB hP.forallFind hP.forallPush
    hP.internForall hP.mkForall hP.closeTele hP.ab k ⟨m2, Locals.init []⟩ _ _ _ _) (liftE_ok h3)
  simp only at hc3
  rw [hs3] at hc3
  have hP3 := hP2.fr (closeW_mfr _ _ _ _ _ _ _ _ hc3)
  obtain ⟨q, m4⟩ := (r, m')
  exact hP3.fr (cvNewW_mfr (liftE_ok h))

/-- The caps' parameter and index counts, as the words that hold them. -/
theorem decCaps_counts {m : Mem} {q : Word} {caps : IIndCaps} (h : decCaps (erecP m) q.toNat = some caps) :
    (erRd m (q + 12)).toNat = caps.nparams ∧ (erRd m (q + 6)).toNat = caps.nIdx := by
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ni, hni, _, _, np, hnp, _, _, rfl⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hni hnp
  obtain ⟨w1, hw1, rfl⟩ := hnp
  obtain ⟨w2, hw2, rfl⟩ := hni
  have h1 := erecP_lt64 hw1
  have h2 := erecP_lt64 hw2
  have e1 : (q + 12).toNat = q.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (q + 6).toNat = q.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  rw [← e1] at hw1; rw [← e2] at hw2
  rw [(erRd_of_erecP hw1).1, (erRd_of_erecP hw2).1]
  exact ⟨rfl, rfl⟩

section ft
variable {p : Prog} (hq : KnotStageProg p) (hP : FtProg p) {dn : NIdx → Option ConLeche.Name}
  {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hP henv in
/-- **`family_telescope` refines `familyTelescope .verified`, both outcomes**, under `StageC`:
`former_def_headed` (`fdhW_ok`), the parameter-and-index count (its overflow aborts: the caps'
counts are below `2 ^ 32`), `reduced_former` (`rf_ref`). -/
theorem ft_ref (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {cvq capsq : Word}
    {cv : IConstantVal} {caps : IIndCaps} {cvP : ConLeche.ConstantVal}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hcv : DecB (fun m => decCVp m cvq.toNat) m cv) (hcaps : decCaps (erecP m) capsq.toNat = some caps)
    (hcvP : Frontend.denoteCV a.store cv = some cvP) (hws : ConLeche.Expr.WScoped 0 cvP.type) :
    RefE (WtG p) (ftE p k m vis cvq capsq) (familyTelescope V fe cv caps) a
      (fun v x a' => FtPost dn vis fe env m a v x a') := by
  rcases k with _ | k
  · rw [ftE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hS := hC.stage
  obtain ⟨hty32, htye⟩ := partsCVType hcv (w := cvq) rfl
  rw [ftE.arm1]
  unfold familyTelescope
  -- `former_def_headed`
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (fdhW_spec p hP.fdh k _ _) h1
  simp only at hs1 hW1
  subst hs1
  obtain ⟨hm1, hrun1⟩ := fdhW_ok hP.pir hP.frs hS.check.arena.base hty32 hW1 (cv := cv) htye.symm
  rw [hm1]
  refine ⟨_, _, hrun1, ?_⟩
  dsimp only [ftE.k_former_def_headed]
  by_cases hz : r1.headD 0 = 0
  · rw [ite_eq_left hz]
    simp only [hz, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check, hty32, htye⟩
  rw [ite_eq_right hz]
  simp only [show (r1.headD 0 != 0) = true by simpa using hz, ite_true]
  obtain ⟨hnp, hni⟩ := decCaps_counts hcaps
  change RefE _ (if erRd m (capsq + 12) + erRd m (capsq + 6) < erRd m (capsq + 12) then _ else _) _ _ _
  refine RefE.abort0 rfl fun hov => ?_
  have hsum : (erRd m (capsq + 12) + erRd m (capsq + 6)).toNat = caps.nparams + caps.nIdx := by
    rw [partsAddNoOv hov, hnp, hni]
  -- `reduced_former`
  have hRF := rf_ref hq hP.toRfProg henv k (by omega) (n := erRd m (capsq + 12) + erRd m (capsq + 6))
    hC hA hcv hcvP hws
  rw [hsum] at hRF
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl)
    (rfE_spec p hP.toRfProg k _ vis _ _) (fun hG => hG.nv) id hRF fun r5 s5 cvR a5 _ _ hr5 hR5 => ?_
  dsimp only [ftE.k_reduced_former]
  have hcvR5 := installCvDecB hR5.cv (CVExt.of_dec hR5.cv)
  obtain ⟨hy32, hye⟩ := partsCVType hcvR5 (w := r5.headD 0) rfl
  exact RefE.ret rfl ⟨hR5.stage, hR5.grow, hR5.abs, hR5.core, hy32, hye⟩

/-- **`family_telescope` keeps the positivity memos.** -/
theorem ftE_pos {p : Prog} (hcl : CoreStageClosed p) (hP : FtProg p) {k : Nat} {m m' : Mem} {a : AState}
    {vis cvq capsq r : Word} {cv : IConstantVal} (hR : ArenaR m a)
    (hcv : DecB (fun m => decCVp m cvq.toNat) m cv) (hPm : PosMR m)
    (h : ftE p k m vis cvq capsq = .ok (r, m')) : PosMR m' := by
  rcases k with _ | k
  · rw [ftE.eq_1] at h; cases h
  obtain ⟨hty32, htye⟩ := partsCVType hcv (w := cvq) rfl
  rw [ftE.arm1] at h
  simp only [ftE.k_former_def_headed] at h
  split at h
  · cases h
  rename_i r1 m1 h1
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (fdhW_spec p hP.fdh k _ _) (liftE_ok h1)
  simp only at hs1 hW1
  subst hs1
  obtain ⟨hm1, -⟩ := fdhW_ok hP.pir hP.frs hR hty32 hW1 (cv := cv) htye.symm
  rw [hm1] at h
  split at h
  · cases h; exact hPm
  split at h
  · cases h
  simp only [ftE.k_reduced_former] at h
  split at h
  · cases h
  rename_i r2 m2 h2
  cases h
  obtain ⟨s2, hs2, -, hfx⟩ := triple_of_callE (rfE_spec p hP.toRfProg k ⟨m, Locals.init []⟩ vis _ _) h2
  rw [← hs2]
  exact rfE_pos hcl hP.toRfProg hPm hfx

end ft

end L.Ind

end
