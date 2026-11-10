module

public import ConAgua.Verdict.PosE1M
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.NestCrest
import all Init.Data.List.Control
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NtyW
import ConAgua.Arena.RefWalk
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.IndPosSpec.UCtx

@[expose] public section

/-!
# `nest_pos_fvar`, `nest_cont_checks`: one refinement for both outcomes

`pfv_ref` refines the twin's `pfK` (the `.fvar` arm of `nestPos`, its continuation split off by
`pfK_eq`) by `pfvE` (unified), `ncc_ref` the checks of `nestCont` (`nccT`, the rest split off by
`nccT_eq`) by `nccE` (unified). The callees are outside the verdict closure (lifted), so the
errors' claims need only `closedNV`. Both halves serve `appRef_step` and `contRef_step` through the run
(`RefE.run_ok`, `RefE.run_err`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
open L.Arena

/-- `pfK` with its continuation split off. -/
theorem pfK_eq {β : Type} (fe : IFEnv) (c : NestCtx) (prog : List NestHole) (kb hi i : Nat)
    (args : List EIdx) (K : NestFieldKind → AM β) :
    pfK fe c prog kb hi i args K = pfK fe c prog kb hi i args pure >>= K := by
  unfold pfK
  split
  · funext s; rfl
  · simp only [bind_assoc]
    congr 1; funext b
    split
    · funext s; rfl
    · split
      · simp
      · funext s; rfl

/-- `pfK`'s run through its continuation, from its run alone. -/
theorem pfK_run {β : Type} {fe : IFEnv} {c : NestCtx} {prog : List NestHole} {kb hi i : Nat}
    {args : List EIdx} {x : NestFieldKind} {a a' : AState}
    (h : (pfK fe c prog kb hi i args pure).run a = .ok (x, a')) (K : NestFieldKind → AM β) :
    (pfK fe c prog kb hi i args K).run a = (K x).run a' := by
  rw [pfK_eq]; simp only [StateT.run_bind, h]; rfl

/-- A decoded hole's index count is the word L reads at `+ 2`. -/
theorem nh_nidx {m : Mem} {p : Word} {hl : NestHole} (hd : decNH m p.toNat = some hl)
    (hin : NHIn m p.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64) :
    (rdW (m.arr64 IW) (p + 2)).toNat = hl.nIdx := by
  simp only [decNH, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hd
  obtain ⟨k, hk, key, hkey, b, hb, x, hx, h'⟩ := hd
  obtain rfl := Option.some.inj h'
  exact rd_iwN (i := 2) (by simpa using hx) (by have := hin.w2; simp; omega)

/-- What `nest_pos_fvar` gives besides the twin's field kind `x`: the stage, the growth, the
result word, the frames. -/
structure PfvPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (w : Word)
    (m' : Mem) (x : NestFieldKind) (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  kind : decNFK w = some x
  pos : PosMR m'
  abs : AFr m m'

/-- **`nest_pos_fvar` refines `pfK`, both outcomes.** -/
theorem pfv_ref {p : Prog} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m : Mem} {a : AState} {ctx po pl kb hi i aO aL : Word} {c : NestCtx}
    {prog : List NestHole} {args : List EIdx} (hS : StageR vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hpr : HSl m po.toNat pl.toNat prog) (hhi : c.hiAt 0 < 2 ^ 64)
    (hargs : decHL m aO.toNat aL.toNat = some args) (hab : aO.toNat + aL.toNat ≤ iwTop m) (hP : PosMR m) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (pfvE p k m vis ctx po pl kb hi i aO aL)
      (pfK fe c prog kb.toNat hi.toNat i.toNat args pure) a
      (fun v x a' => PfvPost dn vis fe m v.1 v.2 x a') := by
  cases k with
  | zero => rw [pfvE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  rw [pfvE.arm1]
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  refine RefE.onlySim (fun _ => pfvE.k_nest_hole_at.none ..) (fun _ _ h => h) fun r1 m1 hha => ?_
  cases k with
  | zero => simp [haWf.eq_1] at hha
  | succ k =>
  obtain ⟨hS1, hg1, hon⟩ := haW_ok k dn fe vis a m m1 ctx po pl i r1 c prog hha hS hU.dec hU.inn hpr
  unfold pfK
  cases hnh : ConRon.Arena.nestHoleAt c prog i.toNat with
  | none =>
    rw [hnh] at hon; simp only [decONH] at hon
    rw [pfvE.k_nest_hole_at.abort1 (hc1 := hon)]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  | some hl =>
  rw [hnh] at hon
  obtain ⟨hon1, hdec, hnin⟩ := hon
  rw [pfvE.k_nest_hole_at.arm1 (hc1 := by rw [hon1]; decide)]
  dsimp only
  have hU1 := hU.grow hg1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hU1.dec hU1.inn htop1
  have hne1 := ctx_names_end hU1.dec hU1.inn hU1.sl htop1
  rcases hoa : noaW (k + 1) m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1))
      (rdW (m1.arr64 IW) (ctx + 4)) hi aO aL with _ | ⟨r2, m2⟩
  · rw [liftE_none, pfvE.k_nest_occ_any.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨b, hrunoa, hS2, hg2, hr2, hP2⟩ := noaW_ok dn fe vis _ _ _ _ c.names (k + 1) m1 m2 a aO aL args _ hoa hS1
    hn1 hne1 (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs)
    (fun j hj => by have := hg1.iw; omega) (hP.fr (haW_mfr hha))
  rw [hnP1] at hrunoa
  refine RefE.bind_right hrunoa ?_
  rw [pfvE.k_nest_occ_any.eq_2]
  refine RefE.guardThen (by decide) (fun h => by rw [hr2] at h; cases b <;> simp at h ⊢) (fun h => by rw [hr2, h]; decide)
    fun _ hb => ?_
  subst hb
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
  obtain ⟨hd2, hnin2⟩ := hnin.grow hg2
  rw [← hd2] at hdec
  have hni := nh_nidx hdec hnin2 htop2
  have hal := decHL_length m hargs
  refine RefE.splitNot (fun hne hq => hne (UInt64.toNat_inj.mp (by rw [hni, ← hal]; simpa using hq)))
    (fun hq he => hq (by rw [hal, ← hni, he, beq_self_eq_true])) (fun _ _ _ => ErrClaim.fail _ _ (by decide))
    fun _ _ => ?_
  rcases hk : hkW m2 ctx kb i with _ | w
  · rw [liftE_none, pfvE.k_nest_pos_hole_kind.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, pfvE.k_nest_pos_hole_kind.arm1]
  have hU2 := hU1.grow hg2
  have hw := hkW_ok hk hU2.dec hU2.inn htop2 hhi (nestHoleAt_nP hnh)
  exact RefE.ret rfl ⟨hS2, hg1.trans hg2, by simpa using hw,
    hP2, (haW_afr hha).trans (noaW_afr _ _ _ _ _ _ _ _ _ _ hoa)⟩

/-- `nestCont`'s checks between the container and the instantiation's former (`nest_cont_checks`),
the rest of the twin `REST`. -/
def nccT {β : Type} (c : NestCtx) (hp : Nat) (n : NIdx) (ds idx : List EIdx) (REST : AM β) : AM β := do
  if ← idx.anyM (fun x => ConRon.Arena.nestOcc c.names c.nP hp x) then fail nestNonValid
  else do
    let q ← pinQuot
    if n == q then fail nestNonValid
    else do
      let pc ← ds.allM (pcF hp)
      if !pc then
        fail (.invalid "nested positivity: nested inductive datatypes parameters cannot contain local variables")
      else REST

/-- `cpW_ok` with no exec-fuel bound (its walks run at `CWF`: `bvbW_stageW`'s first case). -/
theorem cpW_okW (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis hp : Word) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (dO dL : Word) (ds : List EIdx) (r : List Word),
    cpW n m hp dO dL = some (r, m') → StageR vis fe m a →
    decHL m dO.toNat dL.toNat = some ds → (∀ j < dL.toNat, dO.toNat + j < iwTop m) →
    ∃ b a', (ds.allM (pcF hp.toNat)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      r.headD 0 = (if b then 1 else 0) := by
  induction n with
  | zero => intro m m' a dO dL ds r h; simp [cpW.eq_1] at h
  | succ n ih =>
    intro m m' a dO dL ds r h hS hds hin
    by_cases hl0 : dL = 0
    · rw [cpW.arm1 (hc1 := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : ds = [] := by simpa [decHL, hslice?] using hds.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl⟩
    rw [cpW.arm2 (hc1 := hl0)] at h
    have hl : dL.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', dL.toNat = l' + 1 := ⟨dL.toNat - 1, by omega⟩
    have hds' := hds
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hds'
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hds'
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := dO) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hdO1 : (dO + 1).toNat = dO.toNat + 1 :=
      word_add_toNat (show dO.toNat + 1 < 2 ^ 64 by have := hin 0 (by omega); have := hS.iw.iw; have := hS.iw.iwSize; omega)
    have hl1 : (dL - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rw [List.allM_cons]
    rcases hb : bvbW n m (rdW (m.arr64 IW) dO) CWF with _ | ⟨bb, m1⟩ <;> rw [hb] at h; · rw [cpW.k_bvar_b.none] at h; cases h
    obtain ⟨a1, hrun1, hS1, hg1, -⟩ := bvbW_stageW vis fe hS n coreWalkFuel CWF (.inl (Nat.le_of_eq CWF_eq)) _ bb hxH hb
    rw [decE_eq, hxd] at hrun1
    by_cases hbb : bb ≠ 0
    · rw [cpW.k_bvar_b.arm1 (hc1 := hbb)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a1, ?_, hS1, hg1, rfl⟩
      have : (bb.toNat != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro h0; exact hbb (UInt64.toNat_inj.mp (by simpa using h0))
      simp only [pcF, StateT.run_bind, hrun1, except_ok_bind, this, ite_true]
      rfl
    rw [cpW.k_bvar_b.arm2 (hc1 := by simpa using hbb)] at h
    have hbb0 : (bb.toNat != 0) = false := by simp at hbb; simp [hbb]
    have hrd1 : rdW (m1.arr64 IW) dO = rdW (m.arr64 IW) dO := by
      simp only [rdW]; rw [hg1.iwGet _ (by simpa using hin 0 (by omega))]
    rw [hrd1] at h
    rcases hst : fvbF m1 [CWF, rdW (m.arr64 IW) dO] with _ | ⟨r2, m2⟩ <;> rw [hst] at h; · rw [cpW.k_fvar_b.none] at h; cases h
    obtain ⟨k, a2, hrun2, hS2, hg2, hk⟩ := fvbF_ok dn vis fe CWF _ hxH _ _ a1 r2 hst hS1
    rw [CWF_eq, hxd] at hrun2
    simp only [decW0Nat] at hk
    by_cases hc : hp < r2.headD 0
    · rw [cpW.k_fvar_b.arm1 (hc1 := hc)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hgt : ¬ k ≤ hp.toNat := by have := UInt64.lt_iff_toNat_lt.mp hc; omega
      refine ⟨false, a2, ?_, hS2, hg1.trans hg2, rfl⟩
      simp only [pcF, StateT.run_bind, hrun1, except_ok_bind, hbb0, Bool.false_eq_true, ite_false,
        hrun2, hgt, decide_false]
      rfl
    rw [cpW.k_fvar_b.arm2 (hc1 := hc)] at h
    rcases hgo : cpW n m2 hp (dO + 1) (dL - 1) with _ | ⟨r', m''⟩ <;> rw [hgo] at h
    · rw [cpW.k_nest_cont_params_closed.none] at h; cases h
    rw [cpW.k_nest_cont_params_closed.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hle : k ≤ hp.toNat := by
      have : ¬ hp.toNat < (r2.headD 0).toNat := fun e => hc (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    have hg12 := hg1.trans hg2
    obtain ⟨b, a', hrun, hS', hg', hr⟩ := ih m2 m'' a2 (dO + 1) (dL - 1) xs r' hgo hS2
      (by rw [hdO1, hl1, ← hxs, decHL]; exact decHL_agree (RdS.of_grow hg12) (fun j hj => by
            have := hin (j + 1) (by omega); simp only [decHL] at *; omega))
      (fun j hj => by rw [hdO1, hl1] at *; have := hin (j + 1) (by omega); have := hg12.iw; omega)
    refine ⟨b, a', ?_, hS', hg12.trans hg', hr⟩
    simp only [pcF, StateT.run_bind, hrun1, except_ok_bind, hbb0, Bool.false_eq_true, ite_false,
      hrun2, hle, decide_true]
    exact hrun

/-- `nccT` with its rest split off. -/
theorem nccT_eq {β : Type} (c : NestCtx) (hp : Nat) (n : NIdx) (ds idx : List EIdx) (REST : AM β) :
    nccT c hp n ds idx REST = nccT c hp n ds idx (pure ()) >>= fun _ => REST := by
  unfold nccT
  simp only [bind_assoc]
  congr 1; funext b
  split
  · funext s; rfl
  · simp only [bind_assoc]
    congr 1; funext q
    split
    · funext s; rfl
    · simp only [bind_assoc]
      congr 1; funext pc
      split
      · funext s; rfl
      · simp

/-- What `nest_cont_checks` gives (from `m`, the twin from `a`): the three checks' runs, the stage,
the growth, the frames. -/
structure NccPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (c : NestCtx) (a : AState)
    (m : Mem) (hp nn : Word) (ds idx : List EIdx) (m' : Mem) (a' : AState) : Prop where
  occ : (idx.anyM (fun x => ConRon.Arena.nestOcc c.names c.nP hp.toNat x)).run a = .ok (false, a)
  quot : ∃ q, pinQuot.run a = .ok (q, a) ∧ (decI nn == q) = false
  params : (ds.allM (pcF hp.toNat)).run a = .ok (true, a')
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  pos : PosMR m'
  abs : AFr m m'

/-- **`nest_cont_checks` refines `nccT`, both outcomes.** -/
theorem ncc_ref {p : Prog} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m : Mem} {a : AState} {ctx hp nn dO dL iO iL : Word}
    {c : NestCtx} {ds idx : List EIdx} (hS : StageR vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hds : decHL m dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m) (hidx : decHL m iO.toNat iL.toNat = some idx)
    (hidxb : ∀ j < iL.toNat, iO.toNat + j < iwTop m) (hnH : H nn) (hP : PosMR m) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (nccE p k m ctx hp nn dO dL iO iL)
      (nccT c hp.toNat (decI nn) ds idx (pure ())) a
      (fun v _ a' => NccPost dn vis fe c a m hp nn ds idx v.2 a') := by
  cases k with
  | zero => rw [nccE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  rw [nccE.arm1]
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨hn, -, -, -, hnP, -⟩ := ctx_fields hU.dec hU.inn htop
  have hne := ctx_names_end hU.dec hU.inn hU.sl htop
  rcases hoa : noaW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4)) hp
      iO iL with _ | ⟨r1, m1⟩
  · rw [liftE_none, nccE.k_nest_occ_any.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨b, hrunoa, hS1, hg1, hr1, hP1⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m m1 a iO iL idx _ hoa hS
    hn hne hidx hidxb hP
  rw [hnP] at hrunoa
  unfold nccT
  refine RefE.bind_right hrunoa ?_
  rw [nccE.k_nest_occ_any.eq_2]
  refine RefE.guardThen (by decide) (fun h => by rw [hr1] at h; cases b <;> simp at h ⊢) (fun h => by rw [hr1, h]; decide)
    fun _ hb => ?_
  subst hb
  refine RefE.onlySim (fun _ => nccE.k_pin_at.none ..) (fun _ _ h => h) fun rq m2 hq => ?_
  obtain ⟨hm2, hqH, hqrun⟩ := pos2PinW_ok hq hS1.check.pins
  subst hm2
  have hpq : pinQuot = pinAt 47 := rfl
  have hqrun' : pinQuot.run a = .ok ((decI (rq.headD 0) : NIdx), a) := by rw [hpq]; simpa using hqrun
  refine RefE.bind_right hqrun' ?_
  rw [nccE.k_pin_at.eq_2]
  refine RefE.guardThen (by decide) (fun h => by rw [decI_beq _ _ hnH hqH]; simpa using h)
    (fun h => by rw [decI_beq _ _ hnH hqH] at h; simpa using h) fun _ hbeq => ?_
  refine RefE.onlySim (fun _ => nccE.k_nest_cont_params_closed.none ..) (fun _ _ h => h) fun r3 m3 hcp => ?_
  obtain ⟨b3, a3, hrun3, hS3, hg3, hr3⟩ := cpW_okW dn fe vis hp k m2 m3 a dO dL ds r3 hcp hS1
    (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => hdsb j hj)]; exact hds)
    (fun j hj => by have := hdsb j hj; have := hg1.iw; omega)
  refine RefE.bind_right hrun3 ?_
  rw [nccE.k_nest_cont_params_closed.eq_2]
  refine RefE.guardThen (by decide) (fun h => by rw [hr3] at h; cases b3 <;> simp at h ⊢) (fun h => by rw [hr3]; cases b3 <;> simp at h ⊢)
    fun _ hb => ?_
  obtain rfl : b3 = true := by simpa using hb
  exact RefE.ret rfl ⟨hrunoa, ⟨_, hqrun', hbeq⟩, hrun3, hS3, hg1.trans hg3, hP1.fr (cpW_mfr _ _ _ _ _ _ _ hcp),
    ((noaW_afr _ _ _ _ _ _ _ _ _ _ hoa).trans (pos2PinW_afr hq)).trans (cpW_afr _ _ _ _ _ _ _ hcp)⟩

end L.Ind
