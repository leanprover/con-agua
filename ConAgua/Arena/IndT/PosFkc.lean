module

import ConAgua.Arena.RecLayout.CapsDec
public import ConAgua.Verdict.PosNty
public import ConAgua.Arena.IndT.Install1
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.ExprOps.Inst1
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndPosSpec.FgW
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.PosWalks
import ConAgua.Arena.WhnfCoreProj
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.InferLemmas
import all ConAgua.Arena.IndPos2
import ConAgua.Arena.BasisBlockC
import ConAgua.Arena.RecLayout.CIDec

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
  fkcs : p.lookup "family_key_checks" = some familyKeyChecksL

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

set_option experimental.vcgen true in
/-- **`family_key_checks`'s unified model**: the group mate's name read off its record,
`family_key_check` through its call, the recursion. -/
l_model fkcsE_spec (p : Prog) (hP : FkcProg p)
  fns [hP.fkcs ↦ fkcsE]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
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
    (al = 0 ∨ ao.toNat + al.toNat ≤ iwTop m) → denoteE a.store (decI t) = some tP →
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
  replace hdb : ao.toNat + al.toNat ≤ iwTop m := hdb.resolve_left hl0
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
    k24.abs hb2H (k24.decHL hxs hb1) (.inr (k24.top hb1))
    (by rw [hb2d]; exact h47 _ hb3) (ConRon.Bridge.denoteEList_ext k24.core.ext _ _ hdas)
    (ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hwt.2) (fun x hx => hwds x (List.mem_cons_of_mem _ hx))
  rw [hb2d] at hR
  exact RefE.lastE (K := csaE.k_check_spine_at p) (f := fun v => (0, v.2)) (fun _ => rfl) (fun _ => rfl) id hR
    fun v _ a5 _ ⟨k5, hP5⟩ => ⟨k24.trans k5, fun hPm => hP5 ((hP3 hPm).fr (MFr.ofI1F hin))⟩

include hq henv in
/-- **`family_key_check` refines `familyKeyCheck .verified`, both outcomes** (twin side: con-ron's
`familyKeyCheck_specF`'s proof; `nty_ref`'s first half): the family (`env_find`, a miss or another
kind the twin's failure), its level count (`view_ls_len`), `family_telescope` (`ft_ref`), `cv_lps`,
`inst_lp_fast` (its real reading), the arguments (`csa_ref`). -/
theorem fkc_ref (hP : FkcProg p) (hIlpf : IlpfF p) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true)
    (hGc : G → CoreStubsE p) (hGw : G → WhnfTopE p) (d : Word) (k : Nat) (hk62 : k ≤ 2 ^ 62) {m : Mem}
    {a : AState} {c us dO dL : Word} {ds : List EIdx} {cP : ConLeche.Name} {usP : List ConLeche.Level}
    {dsP : List ConLeche.Expr} (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hcH : H c) (hlH : H us)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : dL = 0 ∨ dO.toNat + dL.toNat ≤ iwTop m)
    (hcP : denoteN a.store.ns (decI c) = some cP) (husP : denoteLs a.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a.store ds = some dsP) (hwds : ∀ x ∈ dsP, ConLeche.Expr.WScoped d.toNat x) :
    RefE G (fkcE p k m vis d c us dO dL) (ConRon.Arena.familyKeyCheck V fe d.toNat (decI c) (decI us) ds) a
      (fun v _ a' => InsAt dn vis fe env m a v.2 a' ∧ (PosMR m → PosMR v.2)) := by
  cases k with
  | zero => rw [fkcE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hS := hC.stage
  have hE := hS.check.env
  have hR := hS.check.arena.base
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  rw [fkcE.arm1]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 hef => ?_
  obtain ⟨hm1, rfl⟩ := envFind_callB' hP.nty hP.ft hcH hE hef
  subst m1
  dsimp only [fkcE.k_env_find]
  unfold ConRon.Arena.familyKeyCheck
  by_cases hf0 : (findRes m vis c).headD 0 = 0
  · refine RefE.abortAt hf0 fun _ => ?_
    rw [findRes_miss hE hcH hf0]
    exact ErrClaim.fail _ _ (by decide)
  refine RefE.pass hf0 ?_
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hcH hf0
  rw [hci] at hfind
  generalize (findRes m vis c).tail.headD 0 = q at hfind hci ⊢
  change RefE _ (if erRd m q ≠ 3 then _ else _) _ _ _
  by_cases h3 : erRd m q ≠ 3
  · refine RefE.abortAt h3 fun _ => ?_
    rw [hfind]
    cases ci with
    | indInfo cv caps =>
      exfalso; apply h3
      have hk := decCI_indInfo_kind hci
      obtain ⟨w, hw⟩ := decCI_rd hci
      simp only [nat?, hw, Option.map_some, Option.some.injEq] at hk
      rw [(erRd_of_erecP hw).1]
      exact UInt64.toNat_inj.mp (by simpa using hk)
    | _ => exact ErrClaim.fail _ _ (by decide)
  refine RefE.pass h3 ?_
  have hk3 : nat? (erecP m) q.toNat = some 3 := by
    obtain ⟨w, hw⟩ := decCI_rd hci
    have h3' : erRd m q = 3 := Decidable.not_not.mp h3
    rw [(erRd_of_erecP hw).1] at h3'
    simp [nat?, hw, h3']
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
  have hcv : decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨kd, hkd, hci⟩ := hci
    rw [hk3] at hkd; cases hkd
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
    obtain ⟨cv', h1, _, _, h2⟩ := hci
    cases h2; exact h1
  obtain ⟨v16, hv16⟩ := decCI_indInfo_word hci
  have hq64 := L.Arena.erecP_lt64 hv16
  have := CI.indCaps_ge
  obtain ⟨wn, hwn, -⟩ := decCV_name hcv
  have e1 : (q + CI.cv).toNat = q.toNat + CI.cv.toNat := off_add_toNat rfl (erecP_lt64 hwn)
  have e5 : (q + CI.indCaps).toNat = q.toNat + CI.indCaps.toNat := off_add_toNat rfl hq64
  have hlen : (erRd m (q + (CI.cv + CV.lpsLen))).toNat = cv.levelParams.length :=
    (decCV_rd_ci (erRdOK m) hcv).2.2.2.1.symm
  -- the twin's family and its denotation
  obtain ⟨cc, hcc, he⟩ := ConRon.Bridge.Inductives.find_some_rel hC.check.ienv hcP hfind
  obtain ⟨cvP, capsP, hcvP, hcapsP, rfl⟩ := ConRon.Bridge.Inductives.denoteCI_indInfo_inv hcc
  obtain ⟨-, hlpsC, -⟩ := ConRon.Bridge.denoteCV_inv hcvP
  have hws : ConLeche.Expr.WScoped 0 cvP.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (henv.consts _ (ConLeche.Env.find?_mem he)).1
  rw [hfind]
  dsimp only
  -- `view_ls_len`
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨s2, hs2, -, hm2, hln0, hr2⟩ :=
    triple_of_callW (viewLsLen_specE p hP.nty.hls hP.nty.hvl k ⟨m, Locals.init []⟩ _) h2
  simp only at hm2
  rw [hs2] at hm2
  subst hr2
  rw [hm2]
  rcases lsNodeW_cases m us with hln | ⟨o', l', hln⟩
  · exact absurd hln hln0
  have hvl := lsNodeW_viewLen hR hlH hln
  refine ⟨some l'.toNat, a, by simp [ConRon.Arena.viewLsLen, hvl]; rfl, ?_⟩
  dsimp only [fkcE.k_view_ls_len]
  simp only [hln, List.tail_cons, List.headD_cons]
  change RefE _ (if l' ≠ erRd m (q + (CI.cv + CV.lpsLen)) then _ else _) _ _ _
  refine RefE.guardThen (by decide) (fun h => by rw [← hlen]; simpa [UInt64.toNat_inj] using h)
    (fun h => by rw [← hlen] at h; simpa [UInt64.toNat_inj] using h) fun hneq _ => ?_
  -- `family_telescope`
  have hcvB : DecB (fun m => decCVp m (q + CI.cv).toNat) m cv := by
    show decCV (erA (truncM m)) _ = _
    rw [truncM_erA, e1]; exact hcv
  have hFT := ft_ref hq hP.ft henv k (by omega) (cvq := q + CI.cv) (capsq := q + CI.indCaps) hC hA hcvB
    (by rw [e5]; exact hcaps) hcvP hws
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) (ftE_spec p hP.ft k _ vis _ _) hGnv
    (fun hG => ⟨hGnv hG, hGw hG⟩) hFT fun r3 s3 tyC a2 hc3 _ hr3 hP3 => ?_
  dsimp only [fkcE.k_family_telescope]
  obtain ⟨s3', hs3', -, hfx3⟩ := triple_of_callE (ftE_spec p hP.ft k ⟨m, Locals.init []⟩ vis (q + CI.cv) (q + CI.indCaps)) hc3
  obtain ⟨c2, tyCP, htyCP, hF1⟩ := ConRon.Bridge.Inductives.familyTelescope_specF ConRon.Bridge.CoreSpec.of_core
    henv cv cvP caps capsP hws a a2 tyC hC.check ⟨hcvP, hcapsP⟩ hr3
  have hS3 := hP3.stage.stage
  have hg3 := hP3.grow
  generalize s3.mem = m3 at hS3 hg3 hP3 hs3' ⊢
  -- `cv_lps`
  have hcv4 : decCVp m3 (q + CI.cv).toNat = some cv := by
    rw [e1]; exact hg3.ext.decCV hcv
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r5 m5 hlp => ?_
  dsimp only [fkcE.k_cv_lps]
  obtain ⟨hS5, hg5, -, hdec5, -⟩ := L.Ind.cvLpsW_stage hlp hS3 hcv4
  have hg35 := hg3.trans hg5
  -- `inst_lp_fast`
  refine RefE.bindLift (fun _ => rfl) fun r6 m6 hil => ?_
  obtain ⟨tl, a4, hrun5, ⟨hS6, hg6, htlH, htld⟩, ⟨_, _, hfA, hfC, hf6⟩, hA6⟩ :=
    IlpRd.realC hIlpf hP3.stage k CWF _ _ _ _ cv.levelParams m5 m6 a2 r6 hlH hP3.hw
      ⟨rfl, erToIwW_iwFr hlp⟩ hS5 hdec5 hil
  rw [CWF_eq, hP3.dec] at hrun5
  refine ⟨_, _, hrun5, ?_⟩
  dsimp only [fkcE.k_inst_lp_fast]
  have hg36 := hg35.trans hg6
  obtain ⟨c4, htl⟩ := ConRon.Bridge.Inductives.instLPFast_cstep c2.ok
    (ConRon.Bridge.denoteNListE_ext c2.ext _ _ hlpsC) (ConRon.Bridge.denoteLs_ext husP c2.ext) htyCP hrun5
  have c24 := c2.trans c4
  have hA6' : AbsOK m6 := ((AFr.iw (erToIwW_iwFr hlp)).trans hA6) hP3.abs
  have hC6 : StageC dn vis fe env m6 a4 := StageC.of_check hC hS6 hA6' c24.ok c24.ext
  have hcl : tyCP.hasFvar = false := by
    obtain ⟨F, hFt⟩ := hF1
    rw [ConLeche.familyTelescope_datF] at hFt
    exact ConLeche.familyTelescope_hasFvar
      (fun _ _ _ hw he => ConLeche.whnf_WScoped henv F hw he) hFt
      (henv.consts _ (ConLeche.Env.find?_mem he)).1
  have hP6 : PosMR m → PosMR m6 := fun hPm => by
    have hP3m : PosMR m3 := by
      rw [← hs3']; exact ftE_pos hq.closed hP.ft hR hcvB hPm hfx3
    exact hP3m.fr ((posmemo_cvLpsW_mfr hlp).trans (MFr.of_frame hf6 hfA hfC))
  -- `check_spine_at`
  have hcsa := csa_ref hq henv hP hGc d k (by omega) m6 a4 (r6.headD 0) dO dL ds dsP _ hC6 hA6' htlH
    (by
      rw [decHL_agree (RdS.of_grow hg36) (fun j hj => by
        rcases hdsb with h0 | hb
        · subst h0; simp at hj
        · omega)]
      exact hds)
    (hdsb.imp_right fun hb => by have := hg36.iw; omega) (by rw [htld]; exact htl)
    (ConRon.Bridge.denoteEList_ext c24.ext _ _ hdsP)
    (ConLeche.Expr.WScoped.of_not_hasFvar (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl))
    hwds
  rw [htld] at hcsa
  exact RefE.lastE (K := fkcE.k_check_spine_at p) (f := fun v => (0, v.2)) (fun _ => rfl) (fun _ => rfl) id
    (RefE.ofCallE (s₀ := ⟨m6, Locals.init []⟩) (csaE_spec p hP k _ vis d _ dO dL) hGnv hcsa)
    fun v _ a5 _ ⟨s', hs', _, k7, hP7⟩ => by
      rw [← hs']
      exact ⟨(InsAt.cstep hC hS6 hA6' hg36 c24).trans k7, fun hPm => hP7 (hP6 hPm)⟩

end sims

end L.Ind

end
