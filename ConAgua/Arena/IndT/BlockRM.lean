module

public import ConAgua.Arena.IndT.BlockC
public import ConAgua.Arena.WhnfSpineRefine
public import ConAgua.Arena.IndT.Sum1
public import ConAgua.Arena.IndInstallSpec.InstallCvDecB
import all ConAgua.Arena.IndPos2
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IlpRd
import ConAgua.Arena.IndPosSpec.CloseTelescope
import ConAgua.Arena.IndInstallSpec.InstallSimCall
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.IndSumSpec.DecCVpGrow
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# `reduce_members`' callees (lane `ronsync2`, stage 3)

`former_res_sort` and `former_def_headed` (`WhnfIota.lean`) as `Option` models refining con-ron's
`formerResSort`/`formerDefHeaded` (`frsW_ok`, `fdhW_ok`: only the flag, the twin's state kept);
`reduced_former` (`IndPos2.lean`) refining `reducedFormer .verified`, both outcomes (`rf_ref`:
`whnf_telescope` by `wt_ref`, `intern_sort`, `close_telescope`, `cv_new`; the twin's `CoreStep`
by con-ron's `reducedFormer_specF`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`former_res_sort`'s model**: `pi_result` lifted. -/
l_model frsW_spec (p : Prog) (hf : p.lookup "former_res_sort" = some formerResSortL)
  fns [hf ↦ frsW] specs [callW_spec p n "pi_result"] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

set_option experimental.vcgen true in
/-- **`former_def_headed`'s model**: `former_res_sort` lifted. -/
l_model fdhW_spec (p : Prog) (hf : p.lookup "former_def_headed" = some formerDefHeadedL)
  fns [hf ↦ fdhW] specs [callW_spec p n "former_res_sort"] grind [arena_grind]

/-- **`former_res_sort` refines `formerResSort`** (only whether it found a sort: the flag word). -/
theorem frsW_ok {p : Prog} (hpr : p.lookup "pi_result" = some piResultL) {n : Nat} {m m' : Mem}
    {a : AState} {ty : Word} {r : List Word} (hR : ArenaR m a) (hty : HW ty)
    (h : frsW p n m ty = some (r, m')) :
    m' = m ∧ ∃ x, (formerResSort (decE ty)).run a = .ok (x, a) ∧ (r.headD 0 = 0 ↔ x = none) := by
  rcases n with _ | n
  · simp [frsW] at h
  rw [frsW.arm1] at h
  rcases hc : callW p n "pi_result" [ty] m with _ | ⟨r1, m1⟩
  · rw [hc] at h; simp [frsW.k_pi_result] at h
  rw [hc] at h
  obtain ⟨s', hs', hm, -, hw, hrun⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (piResult_refines' p hpr n _ a hR ty hty) hc
  simp only at hm
  subst hs'
  rw [hm] at h
  have hrun' : (formerResSort (decE ty)).run a =
      (if ((decE (r1.headD 0)).tag == ETag.sort) = true then
        (do match ← viewSort (decE (r1.headD 0)) with
          | none => failDanglingE
          | some s => pure (some s) : AM (Option LIdx)).run a
      else .ok (none, a)) := by
    simp only [formerResSort, StateT.run_bind, hrun, except_ok_bind]
    split <;> rfl
  rw [decE_tag_sort_beq (hh := hw)] at hrun'
  simp only [frsW.k_pi_result] at h
  by_cases ht : tagW (r1.headD 0) = 2
  · rw [ite_eq_right (by simpa using ht)] at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, some (decI (tfld m SORT (tierW (r1.headD 0)) (idxW (r1.headD 0)) 0)), ?_, by simp⟩
    rw [hrun', ite_eq_left (by simpa using ht)]
    have hv := pr_viewSort_ok m a hR (r1.headD 0) hw ⟨h1, by have := UInt64.not_le.mp h2; exact this⟩ ht
    simp only [StateT.run_bind]
    rw [L.Ind.viewSort_run hv]
    rfl
  · rw [ite_eq_left (by simpa using ht)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, none, ?_, by simp⟩
    rw [hrun', ite_eq_right (by simpa using ht)]


/-- **`former_def_headed` refines `formerDefHeaded`** (the twin's state kept). -/
theorem fdhW_ok {p : Prog} (hpr : p.lookup "pi_result" = some piResultL)
    (hfrs : p.lookup "former_res_sort" = some formerResSortL) {n : Nat} {m m' : Mem}
    {a : AState} {ty : Word} {r : Word} (hR : ArenaR m a) (hty : HW ty)
    (h : fdhW p n m ty = some (r, m')) {cv : IConstantVal} (hcv : cv.type = decE ty) :
    m' = m ∧ (formerDefHeaded cv).run a = .ok (r != 0, a) := by
  rcases n with _ | n
  · simp [fdhW] at h
  rw [fdhW.arm1] at h
  rcases hc : callW p n "former_res_sort" [ty] m with _ | ⟨r1, m1⟩
  · rw [hc] at h; simp [fdhW.k_former_res_sort] at h
  rw [hc] at h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (frsW_spec p hfrs n _ ty) hc
  simp only at hs' hW
  subst hs'
  obtain ⟨rfl, x, hx, hxr⟩ := frsW_ok hpr hR hty hW
  simp only [fdhW.k_former_res_sort, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  simp only [formerDefHeaded, StateT.run_bind, hcv, hx, except_ok_bind]
  cases x with
  | none => simp only [hxr.2 rfl, ite_true]; rfl
  | some u =>
    have : r1.headD 0 ≠ 0 := fun h0 => by simpa using hxr.1 h0
    simp only [this, ite_false]; rfl
/-- The lookups `reduced_former`'s model and refinement read. -/
structure RfProg (p : Prog) : Prop extends CstProg p where
  put : p.lookup "erec_put" = some erecPut
  wtp : WtProg p
  rf : p.lookup "reduced_former" = some reducedFormerL

set_option experimental.vcgen true in
/-- **`reduced_former`'s unified model**: `whnf_telescope` through its call, `intern_sort`,
`close_telescope` and `cv_new` (outside the verdict closure) lifted. -/
l_model rfE_spec (p : Prog) (hP : RfProg p)
  fns [hP.rf ↦ rfE]
  specs [callW_spec p n "intern_sort", callW_spec p n "close_telescope", cvNew_specW p hP.erAlloc hP.put hP.cvNew n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `reduced_former` gives (from `m`, `a`): the stage after the twin's `CoreStep`, the pools
grown, the reduct's record below the tops. -/
structure RfPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (v : Word × Mem) (cvR : IConstantVal) (a' : AState) : Prop where
  stage : StageC dn vis fe env v.2 a'
  grow : IWGrow m v.2
  abs : AbsOK v.2
  core : ConRon.Bridge.CoreStep env fe a a'
  cv : decCVp v.2 v.1.toNat = some cvR

section rf
variable {p : Prog} (hq : KnotStageProg p) (hP : RfProg p) {dn : NIdx → Option ConLeche.Name}
  {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hP henv in
/-- **`reduced_former` refines `reducedFormer .verified`, both outcomes**, under `StageC`:
`whnf_telescope` (`wt_ref`), `intern_sort` (`installSortSim`), `close_telescope`
(`closeTelescope_refines`), `cv_new` (`cvNew_stage`; no twin step); the twin's `CoreStep` by
con-ron's `reducedFormer_specF`. -/
theorem rf_ref (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {cvq n : Word} {cv : IConstantVal}
    {cvP : ConLeche.ConstantVal} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hcv : DecB (fun m => decCVp m cvq.toNat) m cv) (hcvP : Frontend.denoteCV a.store cv = some cvP)
    (hws : ConLeche.Expr.WScoped 0 cvP.type) :
    RefE (WtG p) (rfE p (k + 1) m vis cvq n) (reducedFormer V fe cv n.toNat) a
      (fun v cvR a' => RfPost dn vis fe env m a v cvR a') := by
  have hS := hC.stage
  obtain ⟨hty32, htye⟩ := partsCVType hcv (w := cvq) rfl
  have hcvm : decCVp m cvq.toNat = some cv := DecB.get (OMono.decCVp _) hcv
  rw [rfE.arm1]
  unfold reducedFormer
  -- `whnf_telescope`
  have hW := wt_ref hq hP.wtp henv k hk m a 0 n (erRd m (cvq + 3)) 0 0 [] hC hA hty32
    (by simpa using n.toNat_lt) (decHL_zero_zero m) (by simp)
    (by rw [htye]; exact ConRon.Bridge.denoteCV_type hcvP) hws
  rw [htye, show UInt64.toNat (0 : Word) = 0 from rfl] at hW
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl)
    (wtE_spec p hP.wtp k _ vis 0 n (erRd m (cvq + 3)) 0 0) (fun hG => hG.nv) id hW
    fun r1 s1 x1 a1 _ _ hr1 hW1 => ?_
  obtain ⟨bs1, s1L⟩ := x1
  dsimp only [rfE.k_whnf_telescope]
  have hS1 := hW1.stage.stage
  -- `intern_sort`
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨srt, a4, hr4, hS4, hg4, hsrt, hf4⟩ := installSortSim hP.toCstProg k hS1 hW1.sort32 r4 m4 h4
  rw [hW1.sort] at hr4
  refine ⟨_, _, hr4, ?_⟩
  dsimp only [rfE.k_intern_sort]
  split
  · exact RefE.of_cls0 rfl
  rename_i h40
  have hH4 : H (r4.headD 0) := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h40); simpa using this
  have hA4 : AbsOK m4 := hf4 hW1.abs
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  have htop1 := hW1.top
  have hdoms1 := hW1.doms
  have hgr1 := hW1.grow
  simp only at htop1 hdoms1 hgr1 hS1 hg4 hf4
  rw [decE_eq] at hsrt
  subst hsrt
  -- `close_telescope`
  refine RefE.bindLift (fun _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hd5, hA5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (closeTelescope_refines p hP.derB hP.forallFind hP.forallPush hP.internForall hP.mkForall
      hP.closeTele hP.ab k _ a4 dn fe vis (r1.headD 0) (r1.tail.headD 0) 0 (r4.headD 0) bs1 hH4 hS4
      (decHL_grow' hg4 htop1 hdoms1) (by omega) (Nat.le_trans htop1 hg4.iw)
      (by rw [show UInt64.toNat (0 : Word) = 0 from rfl, Nat.zero_add]; exact UInt64.toNat_lt _) hA4) h5
  simp only [show UInt64.toNat (0 : Word) = 0 from rfl] at hs5 hok5 hS5 hg5 hd5 hA5
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  refine ⟨_, _, hrun5, ?_⟩
  dsimp only [rfE.k_close_telescope]
  -- `cv_new` (no twin step)
  have hg15 := (hgr1.trans hg4).trans hg5
  refine RefE.onlySim (K := id) (fun _ => rfl) (fun _ _ h => h) fun q m6 h6 => ?_
  obtain ⟨hS6, hg6, -, -, -, -, hdec6⟩ := cvNew_stage (cq := cvq) h6 hS5
    (DecB.stab (OMono.decCVp _) hcv _ hg15) hd5.1
  have hA6 := cvNewW_afr h6 hA5
  have hrunAll : (reducedFormer V fe cv n.toNat).run a =
      .ok ({ cv with type := AM.res (ConRon.Arena.closeTelescope bs1 0 (decI (r4.headD 0))) a4 },
        AM.st (ConRon.Arena.closeTelescope bs1 0 (decI (r4.headD 0))) a4) := by
    unfold reducedFormer
    simp only [StateT.run_bind, hr1, hr4, hrun5, except_ok_bind]
    rfl
  obtain ⟨c, -, -, -⟩ := ConRon.Bridge.Inductives.reducedFormer_specF ConRon.Bridge.CoreSpec.of_core
    henv cv cvP n.toNat hws a _ _ hC.check hcvP hrunAll
  refine RefE.ret (by simp only [StateT.run_pure]; rfl)
    ⟨StageC.of_check hC hS6 hA6 c.ok c.ext, hg15.trans hg6, hA6, c, ?_⟩
  rw [hdec6, hd5.2]

end rf

end L.Ind

end
