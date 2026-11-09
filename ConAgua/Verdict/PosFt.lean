module

public import ConAgua.Arena.IndT.BlockRM
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.RecClassSpec.Classes
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# `family_telescope`: one model and one refinement for both outcomes

`family_telescope(vis, cv, caps)` (`IndPos2.lean`) refines con-ron's `familyTelescope .verified`
(`ft_ref`): `former_def_headed` by `fdhW_ok`, `reduced_former` (through its call) by `rf_ref`;
the twin's `CoreStep` is `rf_ref`'s (or the identity).
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

end ft

end L.Ind

end
