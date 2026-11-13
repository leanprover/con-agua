module

import ConAgua.Arena.RecLayout.CapsDec
public import ConAgua.Verdict.PosE1M
public import ConAgua.Verdict.PosFt
public import ConAgua.Arena.IndRealIlpL
import ConAgua.Arena.IlpRdReal
import ConRon.Bridge.Inductives.FieldTele
import ConAgua.Arena.IndPosSpec.FgW
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.PosWalks
import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.L.WordOff
public import ConAgua.Arena.IndPosSpec.NkFields
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `nest_inst_type_ty`: one model and one refinement for both outcomes

`ntyE` (`l_model … unified`, `PosE1M.lean`): its callees outside the verdict closure through their
`Option` models (`view_ls_len` and `inst_lp_fast` through their runs), `family_telescope` through
its call (`ft_ref`, `PosFt.lean`). `nty_ref` refines `ntyTV`, the twin's `nestInstType .verified`
up to the instantiated type, for both outcomes, under `StageC` (the twin's `CoreStep` from
con-ron's `familyTelescope_specF`, `instLPFast_cstep`, `instPisWith_spec`); `nest_inst_type`'s
refinement (`nit_ref`, `PosE1N.lean`) applies it to its unified callee.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
open L.Arena

/-- `env_find` through its call: the memory unchanged, the result `findRes`. -/
theorem envFind_callB' {p : Prog} (hl : NtyLook p) (hF : FtProg p) {vis : Word} {fe : IFEnv} {w : Word}
    (_hw : w.toNat < 2 ^ 32) {n : Nat} {m m' : Mem} {r : List Word}
    (_hE : EnvR m vis fe) (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ r = findRes m vis w := by
  obtain ⟨s', rfl, h1, -, h3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_spec p hl.hg hF.brg hl.hf n _ vis w) h
  exact ⟨h1, h3⟩

local notation "V" => ConLeche.CheckMode.verified

/-- `nestInstType .verified` up to the instantiated container type `ty`, then `K ty` (the twin's
text). -/
def ntyTV {β : Type} (fe : IFEnv) (key : NestKey) (K : EIdx → AM β) : AM β := do
  let (cvC, capsC) ← unwrapOr
    (match fe.find? key.cname with
     | some (.indInfo cv caps) => some (cv, caps)
     | _ => none)
    (.internal "nested positivity: container vanished")
  match ← viewLsLen key.lvls with
  | none => failDanglingLs
  | some nl =>
    if nl != cvC.levelParams.length then
      fail (.invalid "nested positivity: incorrect number of universe levels for a nested inductive datatype (official: incorrect number of universe levels)")
    else do
      let tyC ← familyTelescope V fe cvC capsC
      match ← stripPis key.ds.length tyC with
      | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
      | some _ => do
        let tl ← instLPFast coreWalkFuel cvC.levelParams key.lvls tyC
        match ← ConRon.Arena.instPisWith key.ds tl with
        | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
        | some ty => K ty

/-- `ntyTV` with its continuation split off. -/
theorem ntyTV_eq {β : Type} (fe : IFEnv) (key : NestKey) (K : EIdx → AM β) :
    ntyTV fe key K = ntyTV fe key pure >>= K := by
  unfold ntyTV
  simp only [bind_assoc]
  congr 1; funext cv
  congr 1; funext o
  split
  · funext s; rfl
  · split
    · funext s; rfl
    · simp only [bind_assoc]
      congr 1; funext tyC
      congr 1; funext q
      split
      · funext s; rfl
      · simp only [bind_assoc]
        congr 1; funext tl
        congr 1; funext t
        split
        · funext s; rfl
        · simp

/-- What `nest_inst_type_ty` gives besides the twin's type `ty` (from `m`, `a`): the twin's steps,
the stage after its `CoreStep`, the growth, the result word and its denotation, the positivity
memos. -/
structure NtyPostV (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (kk : NestKey) (m : Mem) (a : AState) (w : Word) (m' : Mem) (ty : EIdx) (a' : AState) : Prop where
  steps : ∃ cv caps a2 tyC q a4 tl, fe.find? kk.cname = some (.indInfo cv caps) ∧
    a.store.lss.viewLen kk.lvls = some cv.levelParams.length ∧
    (familyTelescope V fe cv caps).run a = .ok (tyC, a2) ∧
    (stripPis kk.ds.length tyC).run a2 = .ok (some q, a2) ∧
    (instLPFast coreWalkFuel cv.levelParams kk.lvls tyC).run a2 = .ok (tl, a4) ∧
    (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a')
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  hw : H w
  dec : decI w = ty
  den : ∃ tyP, denoteE a'.store ty = some tyP
  abs : AbsOK m'
  pos : PosMR m → PosMR m'
  core : ConRon.Bridge.CoreStep env fe a a'

/-- **`nest_inst_type_ty` refines `ntyTV`, both outcomes**, under `StageC`: the container
(`env_find`), the level count (`view_ls_len`), `family_telescope` (`ft_ref`), `strip_pis`,
`cv_lps`, `inst_lp_fast` (its real reading), `inst_pis_with`; the errors under `WtG` (the
no-verdict callees closed, `whnf_top`'s claim). -/
theorem nty_ref {p : Prog} (hl : NtyLook p) (hq : KnotStageProg p) (hF : FtProg p) (hIlpf : IlpfF p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (k : Nat) (hk62 : k ≤ 2 ^ 62) {m : Mem}
    {a : AState} {key : Word} {kk : NestKey} {keyP : ConLeche.NestKey}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m)) (hksl : NKSl m key)
    (hkey : ConRon.Bridge.Inductives.dKey a.store kk = some keyP) :
    RefE (WtG p) (ntyE p k m vis key) (ntyTV fe kk pure) a
      (fun v ty a' => NtyPostV dn vis fe env kk m a v.1 v.2 ty a') := by
  cases k with
  | zero => rw [ntyE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hS := hC.stage
  have hE := hS.check.env
  have hR := hS.check.arena.base
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨hcH, hcd, hlH, hld, hds, hdsb, hk4⟩ := nk_fields hk hkin htop
  rw [ntyE.arm1]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 hef => ?_
  obtain ⟨hm1, rfl⟩ := envFind_callB' hl hF hcH hE hef
  subst m1
  dsimp only [ntyE.k_env_find]
  refine RefE.abort0 rfl fun hf0 => ?_
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hcH hf0
  rw [hci] at hfind
  refine RefE.abort0 rfl fun h3 => ?_
  generalize (findRes m vis (rdW (m.arr64 IW) key)).tail.headD 0 = q at hfind hci h3 ⊢
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
  have hlen : (erRd m (q + CI.cv + CV.lpsLen)).toNat = cv.levelParams.length :=
    (decCV_rd (erRdOK m) (q := q + CI.cv) (by rw [e1]; exact hcv)).2.2.2.1.symm
  -- the twin's container and its denotation
  obtain ⟨hcn, hlv, hdsP⟩ := ConRon.Bridge.Inductives.dKey_inv hkey
  have hfind' : fe.find? kk.cname = some (.indInfo cv caps) := by rw [← hcd]; exact hfind
  obtain ⟨cc, hcc, he⟩ := ConRon.Bridge.Inductives.find_some_rel hC.check.ienv hcn hfind'
  obtain ⟨cvP, capsP, hcvP, hcapsP, rfl⟩ := ConRon.Bridge.Inductives.denoteCI_indInfo_inv hcc
  obtain ⟨-, hlpsC, -⟩ := ConRon.Bridge.denoteCV_inv hcvP
  have hws : ConLeche.Expr.WScoped 0 cvP.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (henv.consts _ (ConLeche.Env.find?_mem he)).1
  unfold ntyTV
  refine RefE.bind_right (v := (cv, caps)) (a₁ := a) (by rw [hfind']; rfl) ?_
  -- `view_ls_len`
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨s2, hs2, -, hm2, hln0, hr2⟩ := triple_of_callW (viewLsLen_specE p hl.hls hl.hvl k ⟨m, Locals.init []⟩ _) h2
  simp only at hm2
  rw [hs2] at hm2
  subst hr2
  rw [hm2]
  rcases lsNodeW_cases m (rdW (m.arr64 IW) (key + 1)) with hln | ⟨o', l', hln⟩
  · exact absurd hln hln0
  have hvl := lsNodeW_viewLen hR hlH hln
  rw [hld] at hvl
  refine ⟨some l'.toNat, a, by simp [ConRon.Arena.viewLsLen, hvl]; rfl, ?_⟩
  dsimp only [ntyE.k_view_ls_len]
  simp only [hln, List.tail_cons, List.headD_cons]
  change RefE _ (if l' ≠ erRd m (q + CI.cv + CV.lpsLen) then _ else _) _ _ _
  refine RefE.guardThen (by decide) (fun h => by rw [← hlen]; simpa [UInt64.toNat_inj] using h)
    (fun h => by rw [← hlen] at h; simpa [UInt64.toNat_inj] using h) fun hneq _ => ?_
  have hl'eq : l'.toNat = cv.levelParams.length := by rw [← hlen, Classical.not_not.mp hneq]
  -- `family_telescope`
  have hcvB : DecB (fun m => decCVp m (q + CI.cv).toNat) m cv := by
    show decCV (erA (truncM m)) _ = _
    rw [truncM_erA, e1]; exact hcv
  have hFT := ft_ref hq hF henv k (by omega) (cvq := q + CI.cv) (capsq := q + CI.indCaps) hC hA hcvB
    (by rw [e5]; exact hcaps) hcvP hws
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) (ftE_spec p hF k _ vis _ _) (fun hG => hG.nv)
    id hFT fun r3 s3 tyC a2 hc3 _ hr3 hP3 => ?_
  dsimp only [ntyE.k_family_telescope]
  obtain ⟨s3', hs3', -, hfx3⟩ := triple_of_callE (ftE_spec p hF k ⟨m, Locals.init []⟩ vis (q + CI.cv) (q + CI.indCaps)) hc3
  obtain ⟨c2, tyCP, htyCP, -⟩ := ConRon.Bridge.Inductives.familyTelescope_specF ConRon.Bridge.CoreSpec.of_core
    henv cv cvP caps capsP hws a a2 tyC hC.check ⟨hcvP, hcapsP⟩ hr3
  have hS3 := hP3.stage.stage
  have hg3 := hP3.grow
  generalize s3.mem = m3 at hS3 hg3 hP3 hs3' ⊢
  have hrd3' : rdW (m3.arr64 IW) (key + 3) = rdW (m.arr64 IW) (key + 3) := by
    simp (disch := omega) only [rdW, off_toNat]; rw [hg3.iwGet _ (by omega)]
  rw [hrd3']
  -- `strip_pis`
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 hst => ?_
  obtain ⟨x4, a3, hrun4, hS4, hg4, hx4⟩ := stripF_pis_ok vis fe _ (r3.headD 0) hP3.hw m3 m4 a2 r4 hst hS3
  have ha3 : a3 = a2 := stripPis_st _ _ _ _ _ hrun4
  subst a3
  have hdsl := decHL_length m hds
  rw [← hdsl, hP3.dec] at hrun4
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only [ntyE.k_strip_pis]
  cases x4 with
  | none => exact RefE.abortAt hx4 fun _ => ErrClaim.fail _ _ (by decide)
  | some q4 =>
  refine RefE.pass (by rw [hx4.1]; decide) ?_
  -- `cv_lps`
  have hg34 := hg3.trans hg4
  have hcv4 : decCVp m4 (q + CI.cv).toNat = some cv := by
    rw [e1]; exact hg34.ext.decCV hcv
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r5 m5 hlp => ?_
  dsimp only [ntyE.k_cv_lps]
  obtain ⟨hS5, hg5, -, hdec5, -⟩ := L.Ind.cvLpsW_stage hlp hS4 hcv4
  have hg35 := hg34.trans hg5
  have hlv5 : rdW (m5.arr64 IW) (key + 1) = rdW (m.arr64 IW) (key + 1) := by
    simp (disch := omega) only [rdW, off_toNat]; rw [hg35.iwGet _ (by omega)]
  rw [hlv5]
  -- `inst_lp_fast`
  refine RefE.bindLift (fun _ => rfl) fun r6 m6 hil => ?_
  obtain ⟨tl, a4, hrun5, ⟨hS6, hg6, htlH, htld⟩, ⟨_, _, hfA, hfC, hf6⟩, hA6⟩ :=
    IlpRd.realC hIlpf hP3.stage k CWF _ _ _ _ cv.levelParams m5 m6 a2 r6 hlH hP3.hw
      ⟨rfl, (stripF_frame hst).trans (erToIwW_iwFr hlp)⟩ hS5 hdec5 hil
  rw [CWF_eq, hld, hP3.dec] at hrun5
  refine ⟨_, _, hrun5, ?_⟩
  dsimp only [ntyE.k_inst_lp_fast]
  have hg36 := hg35.trans hg6
  have hrd2 : rdW (m6.arr64 IW) (key + 2) = rdW (m.arr64 IW) (key + 2) := by
    simp (disch := omega) only [rdW, off_toNat]; rw [hg36.iwGet _ (by omega)]
  have hrd3 : rdW (m6.arr64 IW) (key + 3) = rdW (m.arr64 IW) (key + 3) := by
    simp (disch := omega) only [rdW, off_toNat]; rw [hg36.iwGet _ (by omega)]
  rw [hrd2, hrd3]
  -- `inst_pis_with`
  refine RefE.bindLift (fun _ => rfl) fun r7 m7 hiw => ?_
  have hg16 := hg36
  obtain ⟨x7, a5, hrun6, hS7, hg7, hx7⟩ := instW_ok k dn fe vis m6 m7 a4 _ _ _ kk.ds r7 hiw hS6 htlH
    (by rw [decHL_agree (RdS.of_grow hg16) (fun j hj => hdsb j hj)]; exact hds) (by unfold NKSl at hksl; omega)
    (by have := hg16.iw; exact Nat.le_trans hksl this)
  rw [htld] at hrun6
  refine ⟨_, _, hrun6, ?_⟩
  dsimp only [ntyE.k_inst_pis_with]
  cases x7 with
  | none => exact RefE.abortAt hx7 fun _ => ErrClaim.fail _ _ (by decide)
  | some ty =>
  obtain ⟨hx71, hx7H, hx7d⟩ := hx7
  refine RefE.pass (by rw [hx71]; decide) ?_
  -- the twin's steps
  obtain ⟨c4, htl⟩ := ConRon.Bridge.Inductives.instLPFast_cstep c2.ok
    (ConRon.Bridge.denoteNListE_ext c2.ext _ _ hlpsC) (ConRon.Bridge.denoteLs_ext hlv c2.ext) htyCP hrun5
  have c24 := c2.trans c4
  obtain ⟨p5, ho2⟩ := ConRon.Bridge.Inductives.instPisWith_spec kk.ds keyP.ds tl _ a4 a5 (some ty)
    c4.ok.state ⟨ConRon.Bridge.denoteEList_ext c24.ext _ _ hdsP, htl⟩ hrun6
  have c5 := c24.trans (p5.toCore c4.ok)
  obtain ⟨tyP, -, htyP⟩ := ho2
  have hA7 : AbsOK m7 :=
    ((AFr.iw (stripF_frame hst)).trans ((AFr.iw (erToIwW_iwFr hlp)).trans (hA6.trans
      (instW_afr _ _ _ _ _ _ _ hiw)))) hP3.abs
  exact RefE.ret rfl ⟨⟨cv, caps, a2, tyC, q4, a4, tl, hfind', by rw [hvl, hl'eq], hr3, hrun4, hrun5, hrun6⟩,
    StageC.of_check hC hS7 hA7 c5.ok c5.ext, hg16.trans hg7, hx7H, hx7d, ⟨tyP, htyP⟩, hA7,
    fun hPm => by
      have hP3m : PosMR m3 := by
        rw [← hs3']; exact ftE_pos hq.closed hF hR hcvB hPm hfx3
      exact hP3m.fr ((((MFr.of_iw (stripF_frame hst)).trans (posmemo_cvLpsW_mfr hlp)).trans
        (MFr.of_frame hf6 hfA hfC)).trans (instW_mfr _ _ _ _ _ _ _ hiw)),
    c5⟩

end L.Ind

end
