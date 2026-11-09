module

public import ConAgua.Verdict.PosNty
public import ConAgua.Arena.IndT.Install1
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.IndView
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.StageInst1
import ConAgua.Arena.IndPosSpec.NoGoStep
import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.IndRealAbs
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.ExprOps.Inst1
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# `family_key_check` and `check_spine_at` (lane `ronsync2`, stage 3)

`check_spine_at(vis, d, t, ao, al)` (`IndPos2.lean`): an application's arguments against a
telescope, each typed (`infer_type_core`) and compared (`is_def_eq_core`); `family_key_check(vis,
d, c, us, ao, al)`: a stored family at a key, its level count, its telescope (`family_telescope`) at
the key's levels, the arguments by `check_spine_at`. Their unified models `csaE`, `fkcE` and their
refinements `csa_ref`, `fkc_ref` against con-ron's `checkSpineAt`, `familyKeyCheck` (both
outcomes; twin side: `checkSpineAt_specF`, `familyKeyCheck_specF`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `family_key_check` and `check_spine_at`. -/
structure FkcProg (p : Prog) : Prop where
  nty : NtyLook p
  ft : FtProg p
  csa : p.lookup "check_spine_at" = some checkSpineAtL
  fkc : p.lookup "family_key_check" = some familyKeyCheckL

set_option experimental.vcgen true in
/-- **`check_spine_at`'s unified model**: `e_view`, `instantiate1_fast` lifted, the core's
`infer_type_core`, `is_def_eq_core` and the recursion through their calls. -/
l_model csaE_spec (p : Prog) (hP : FkcProg p)
  fns [hP.csa ↦ csaE]
  specs [callW_spec p n "e_view", callW_spec p n "instantiate1_fast"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`family_key_check`'s unified model**: `env_find`, `view_ls_len`, `cv_lps`, `inst_lp_fast`
lifted, `family_telescope` and `check_spine_at` through their calls. -/
l_model fkcE_spec (p : Prog) (hP : FkcProg p)
  fns [hP.fkc ↦ fkcE]
  specs [callW_spec p n "env_find", callW_spec p n "view_ls_len",
    cvLps_spec p hP.nty.ha hP.nty.hc hP.nty.he hP.nty.hcv n, callW_spec p n "inst_lp_fast"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

local notation "V" => ConLeche.CheckMode.verified

/-- A call's refinement, its post with the call's ok result at hand (`PassCS`'s `RefE.callOk`, local). -/
theorem RefE.withCall {β : Type} {G : Prop} {x : Except Err (List Word × Mem)} {T : AM β} {a : AState}
    {R : List Word × Mem → β → AState → Prop} (h : RefE G x T a R) :
    RefE G x T a (fun rm y a' => R rm y a' ∧ x = .ok rm) := by
  cases x with
  | error e => exact h
  | ok v => obtain ⟨y, a', h1, h2⟩ := h; exact ⟨y, a', h1, h2, rfl⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) {G : Prop}

include hq henv in
/-- **`check_spine_at` refines `checkSpineAt .verified`, both outcomes** (twin side: con-ron's
`checkSpineAt_specF`'s proof): the binder viewed (`e_view`), the argument typed
(`inferC_rsim`, the core stubs' claim) and compared (`idc_ref`), the body instantiated
(`i1F_ok`); induction on the fuel. -/
theorem csa_ref (hP : FkcProg p) (hGc : G → CoreStubsE p) (d : Word) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (t ao al : Word) (ds : List EIdx) (dsP : List ConLeche.Expr)
      (tP : ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m → H t → decHL m ao.toNat al.toNat = some ds →
    ao.toNat + al.toNat ≤ iwTop m → denoteE a.store (decI t) = some tP →
    Frontend.denoteEList a.store ds = some dsP → ConLeche.Expr.WScoped d.toNat tP →
    (∀ x ∈ dsP, ConLeche.Expr.WScoped d.toNat x) →
    RefE G (csaE p n m vis d t ao al) (ConRon.Arena.checkSpineAt V fe d.toNat (decI t) ds) a
      (fun v _ a' => InsAt dn vis fe env m a v.2 a' ∧ (PosMR m → PosMR v.2)) := by
  induction n with
  | zero => intros; rw [csaE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a t ao al ds dsP tP hC hA ht hds hdb htP hdsP hwt hwds
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  by_cases hl0 : al = 0
  · rw [csaE.arm1 p n m vis d t ao al hl0]
    have : ds = [] := by subst hl0; simpa [decHL, hslice?] using hds.symm
    subst this
    exact RefE.ret rfl ⟨InsAt.refl hC hA, id⟩
  obtain ⟨w, xs, rfl, hw0, hwl, hxs⟩ := decHL_cons hds hl0 (by omega)
  have hwH : H w := hwl
  have hal1 : 1 ≤ al.toNat := Nat.pos_of_ne_zero fun h0 => hl0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hb1 : (ao + 1).toNat + (al - 1).toNat ≤ iwTop m := by
    have e1 : (ao + 1).toNat = ao.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have e2 : (al - 1).toNat = al.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hal1))]; simp
    rw [e1, e2]; omega
  rcases hda : denoteE a.store (decI w) with _ | aP
  · simp [Frontend.denoteEList, hda] at hdsP
  rcases hdas : Frontend.denoteEList a.store xs with _ | asP
  · simp [Frontend.denoteEList, hda, hdas] at hdsP
  simp only [Frontend.denoteEList, hda, hdas, Option.some.injEq] at hdsP
  subst hdsP
  have hwa : ConLeche.Expr.WScoped d.toNat aP := hwds aP List.mem_cons_self
  simp only [ConRon.Arena.checkSpineAt]
  by_cases h6 : ¬ tagW t = 6
  · rw [csaE.abort1 p n m vis d t ao al hl0 h6]
    have htg : ¬ ((decI t : EIdx).tag == ETag.forallE) = true := by
      have h' := fun e' => h6 ((decE_tag_forallE _ ht).mp e')
      simp only [decE_eq] at h'
      simpa using h'
    rw [ite_eq_right htg]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  rw [Classical.not_not] at h6
  rw [csaE.arm2 p n m vis d t ao al hl0 h6]
  -- `e_view`
  refine RefE.onlySim (fun _ => csaE.k_e_view.none ..) (fun _ _ h => h) fun rv m1 h1 => ?_
  obtain ⟨s1, hs1, hm1, hev, hrv⟩ := triple_of_callW (eView_spec p hP.nty.hv n ⟨m, Locals.init []⟩ t) h1
  have hm1' : m1 = m := by rw [← hs1, hm1]
  rw [hm1']
  dsimp only at hrv
  rw [csaE.k_e_view.arm1, hrv]
  rw [hrv] at hev
  obtain ⟨dw, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS ht h6 hev
  simp only [hv, List.tail_cons, List.headD_cons]
  rw [ite_eq_left (by simp [htag])]
  obtain ⟨-, hvbS⟩ := ConRon.Bridge.Inductives.viewBind_run hvb
  obtain ⟨dP, bP, rfl, hdP, hbP⟩ := ConRon.Bridge.denote_forallE_inv hC.check.state.wf
    (ConRon.Bridge.view_forallE_of_viewBind (by simp [htag]) hvbS.symm) htP
  simp only [ConLeche.Expr.WScoped] at hwt
  refine RefE.bind_right hvb ?_
  dsimp only
  rw [hw0]
  -- `infer_type_core`
  refine RefE.bindCall (fun _ => csaE.k_infer_type_core.none ..)
    (fun hV e h3 => (hGc hV).inferTypeCore n (by omega) hC.stageT _ _ hwH e h3)
    (inferC_rsim hq henv n (by omega) hC hA _ _ hwH hda hwa)
    fun ry m2 ty a2 h2 hrun2 ⟨hC2, hg2, ⟨hy1, hy⟩, hA2, c2, tyP, htyP, hwty⟩ => ?_
  dsimp only at hC2 hg2 hy1 hy hA2
  rw [csaE.k_infer_type_core.arm1]
  subst hy
  have hP2 : PosMR m → PosMR m2 := fun hPm => hPm.ofCore hq.closed (by decide) (callW_of_callE h2)
  -- `is_def_eq_core`
  have k2 : InsAt dn vis fe env m a m2 a2 := ⟨hC2, hA2, hg2, c2⟩
  refine RefE.bindE (fun _ => csaE.k_is_def_eq_core.none ..) hGc
    (RefE.withCall (idc_ref hq henv (by omega) k2 rfl rfl hy1 hd htyP (ConRon.Bridge.denote_ext hdP c2.ext)
      hwty hwt.1))
    fun ⟨rb, m3⟩ q a3 _ ⟨⟨k3, hc⟩, h3⟩ => ?_
  dsimp only at k3 hc
  have hP3 : PosMR m → PosMR m3 := fun hPm => (hP2 hPm).ofCore hq.closed (by decide) (callW_of_callE h3)
  refine RefE.ofArms (fun h => csaE.k_is_def_eq_core.abort1 (hc1 := h) ..)
    (fun h => csaE.k_is_def_eq_core.arm1 (hc1 := h) ..)
    (RefE.guard (by decide) hc.1 hc.2 fun _ _ => ?_)
  have k23 := k2.trans k3
  -- `instantiate1_fast`
  refine RefE.bindLift (fun _ => csaE.k_instantiate1_fast.none ..) fun ri m4 h4 => ?_
  obtain ⟨s4, hs4, -, hin⟩ := triple_of_callW (i1F_spec p hP.nty.hi1 n ⟨m3, Locals.init []⟩ _) h4
  dsimp only at hin
  rw [hs4] at hin
  obtain ⟨b2, a4, hrun4, hS4, hg4, hb2H, hb2d⟩ := i1F_ok dn vis fe b w 0 hb m3 m4 a3 ri hin k23.stage.stage
  rw [CWF_eq] at hrun4
  have e4 : (instantiate1Fast coreWalkFuel (decI b) (decI w) 0).run a3 = .ok (b2, a4) := by
    simpa using hrun4
  refine ⟨b2, a4, e4, ?_⟩
  rw [csaE.k_instantiate1_fast.arm1]
  have hb3 := ConRon.Bridge.denote_ext hbP k23.core.ext
  obtain ⟨h41, h42, h44, h45, -, h47⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run k23.stage.check.state
    (ConRon.Bridge.denote_ext hda k23.core.ext) (by rw [hb3]; rfl) e4
  have p4 := ConRon.Bridge.Inductives.PStep.of_caches h41 h42 h44 h45
  have hA4 : AbsOK m4 := i1F_afr hin k23.abs
  have k4 : InsAt dn vis fe env m3 a3 m4 a4 := InsAt.pstep k3.stage hS4 hA4 hg4 p4
  have k24 := k23.trans k4
  -- the rest of the spine
  have hR := ih (by omega) m4 a4 (ri.headD 0) (ao + 1) (al - 1) xs asP (bP.instantiate1 aP 0) k24.stage
    k24.abs hb2H (k24.decHL hxs hb1) (k24.top hb1)
    (by rw [hb2d]; exact h47 _ hb3) (ConRon.Bridge.denoteEList_ext k24.core.ext _ _ hdas)
    (ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hwt.2) (fun x hx => hwds x (List.mem_cons_of_mem _ hx))
  rw [hb2d] at hR
  exact RefE.lastE (K := csaE.k_check_spine_at p) (f := fun v => (0, v.2)) (fun _ => rfl) (fun _ => rfl) id hR
    fun v _ a5 _ ⟨k5, hP5⟩ => ⟨k24.trans k5, fun hPm => hP5 ((hP3 hPm).fr (MFr.ofI1F hin))⟩

end sims

end L.Ind

end
