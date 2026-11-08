module

public import ConAgua.Verdict.PosE1M
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.NestCrest
import all Init.Data.List.Control
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
import ConAgua.Arena.IndPosSpec.NtyW
import ConAgua.Arena.RefWalk
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPosSpec.FgW

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
    · simp only [bind_assoc]
      congr 1; funext ar
      split
      · simp
      · funext s; rfl
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `pfK`'s run through its continuation, from its run alone. -/
theorem pfK_run {β : Type} {fe : IFEnv} {c : NestCtx} {prog : List NestHole} {kb hi i : Nat}
    {args : List EIdx} {x : NestFieldKind} {a a' : AState}
    (h : (pfK fe c prog kb hi i args pure).run a = .ok (x, a')) (K : NestFieldKind → AM β) :
    (pfK fe c prog kb hi i args K).run a = (K x).run a' := by
  rw [pfK_eq]; simp only [StateT.run_bind, h]; rfl
-/

/-- What `nest_pos_fvar` gives besides the twin's field kind `x`: the stage, the growth, the
result word, the frames. -/
structure PfvPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (w : Word)
    (m' : Mem) (x : NestFieldKind) (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  kind : decNFK w = some x
  pos : PosMR m'
  abs : AFr m m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
  | zero => simp [haWf] at hha
  | succ k =>
  have hha' : haW k m ctx po pl i = some (r1, m1) := by simpa [haWf] using hha
  obtain ⟨hS1, hg1, hon⟩ := haW_ok k dn fe vis a m m1 ctx po pl i r1 c prog hha' hS hU.dec hU.inn hpr
  unfold pfK
  cases hnh : ConRon.Arena.nestHoleAt c prog i.toNat with
  | none =>
    rw [hnh] at hon; simp only [decONH] at hon
    rw [pfvE.k_nest_hole_at.abort1 _ _ _ _ _ _ _ _ _ _ _ hon]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  | some hl =>
  rw [hnh] at hon
  obtain ⟨hon1, hdec, hnin⟩ := hon
  rw [pfvE.k_nest_hole_at.arm1 _ _ _ _ _ _ _ _ _ _ _ (by rw [hon1]; decide)]
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
    (fun j hj => by have := hg1.iw; omega) (hP.fr (haW_mfr hha'))
  rw [hnP1] at hrunoa
  refine RefE.bind_right hrunoa ?_
  rw [pfvE.k_nest_occ_any.eq_2]
  refine RefE.guardThen (by decide) (fun h => by rw [hr2] at h; cases b <;> simp at h ⊢) (fun h => by rw [hr2, h]; decide)
    fun _ hb => ?_
  subst hb
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
  obtain ⟨hd2, hnin2⟩ := hnin.grow hg2
  rw [← hd2] at hdec
  obtain ⟨hcH, hcd, hdl⟩ := nh_key_words hdec hnin2 htop2
  refine RefE.onlySim (fun _ => pfvE.k_nest_arity.none ..) (fun _ _ h => h) fun r3 m3 hna => ?_
  have hna' : naW k m2 vis (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0))) = some (r3, m3) := by
    simpa [naWf] using hna
  obtain ⟨ar, a3, hrun3, hS3, hg3, hr3⟩ := naW_ok dn fe vis _ hcH k m2 m3 a r3 hna' hS2
  rw [hcd] at hrun3
  refine RefE.bind_right hrun3 ?_
  have hal := decHL_length m hargs
  rw [pfvE.k_nest_arity.eq_2]
  refine RefE.abort0 rfl fun hov => ?_
  have hsum : (aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat =
      aL.toNat + hl.key.ds.length := by
    rw [← hdl]
    rcases Nat.lt_or_ge (aL.toNat + (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat) (2 ^ 64)
      with hl' | hl'
    · exact word_add_toNat hl'
    · exfalso; apply hov; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
      have := aL.toNat_lt; have := (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat_lt; omega
  refine RefE.splitNot (fun hne hq => hne (UInt64.toNat_inj.mp (by rw [hsum, hr3, ← hal]; simpa using hq)))
    (fun hq he => hq (by rw [hal, ← hsum, ← hr3, he, beq_self_eq_true])) (fun _ _ _ => ErrClaim.fail _ _ (by decide)) fun _ _ => ?_
  rcases hk : hkWf (k + 1) m3 ctx kb i with _ | w
  · rw [liftE_none, pfvE.k_nest_pos_hole_kind.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, pfvE.k_nest_pos_hole_kind.arm1]
  have hU3 := (hU1.grow hg2).grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.iw.iw hS3.iw.iwSize
  have hw := hkW_ok (by simpa [hkWf] using hk) hU3.dec hU3.inn htop3 hhi (nestHoleAt_nP hnh)
  exact RefE.ret rfl ⟨hS3, (hg1.trans hg2).trans hg3, by simpa using hw,
    hP2.fr (naW_mfr hna'), ((haW_afr hha').trans (noaW_afr _ _ _ _ _ _ _ _ _ _ hoa)).trans (naW_afr hna')⟩
-/

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
  sorry

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
