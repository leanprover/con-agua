import ConAgua.Arena.DeclNatSub

/-!
# `nat_op_equations` refines `natOpEquations` (lane `decls3`, helper `decls3-nat`)

`nat_eq_ctx` (the terms built before the dispatch) and the dispatch over the seven operations.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section keepsp
open L.Arena
theorem keepsP_internE (v : ENodeView) : Keeps (fun a : AState => a.pins) (internE v) :=
  (keeps_internE v).map Prod.snd

theorem keepsP_constE (n : NIdx) : Keeps (fun a : AState => a.pins) (constE n) := by
  unfold constE emptyLevels
  refine Keeps.bind ?_ fun us => keepsP_internE _
  unfold Keeps; intro a r a' h
  simp only [pinEmptyLevels, StateT.run_bind, StateT.run_get, StateT.run_pure] at h
  by_cases hr : pinsReady a = true
  · simp [hr] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · simp [hr, fail, throwThe, MonadExceptOf.throw] at h
    cases h

theorem keepsP_natAp1 (n : NIdx) (x : EIdx) : Keeps (fun a : AState => a.pins) (natAp1 n x) := by
  unfold natAp1
  exact Keeps.bind (keepsP_constE n) fun f => keepsP_internE _

end keepsp

structure NatSubProg' (p : Prog) : Prop extends NatSubProg p where
  lNatEqCtx : p.lookup "nat_eq_ctx" = some natEqCtx

section opeq
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- The pin record at `pi` in `m`: the 21 words `nat_op_pins` writes, below the pool's top. -/
def PinRecAt (m : Mem) (pi : Word) : Prop :=
  pinW m 0 ≠ 0 ∧ pi.toNat + 21 ≤ iwTop m ∧
    ∀ j (hj : j < 21), (iwA m)[pi.toNat + j]? = some ((pinRecW m)[j]'(by simp [pinRecW]; omega))

/-- The twin's prefix of `natOpEquations`: the terms the dispatch is over. -/
def natEqCtxT (d : Nat) : AM (EIdx × EIdx × EIdx × NIdx × EIdx × EIdx × EIdx × EIdx) := do
  let nN ← pinNat
  let natTy ← constE nN
  let x ← internE (.fvar d natTy)
  let y ← internE (.fvar (d + 1) natTy)
  let zN ← pinNatZero
  let z ← constE zN
  let sN ← pinNatSucc
  let sx ← natAp1 sN x
  let sy ← natAp1 sN y
  let bT ← constE (← boolTrueName)
  let bF ← constE (← boolFalseName)
  pure (x, y, z, sN, sx, sy, bT, bF)

def natEqCtxW (p : Prog) (n : Nat) (m : Mem) (pi d : Word) : Option (List Word × Mem) :=
  bW (callW p n "const_e" [pw m pi 15] m) fun r1 m1 =>
  bW (callW p n "intern_fvar" [d, r1.headD 0] m1) fun r2 m2 =>
  bW (callW p n "intern_fvar" [d + 1, r1.headD 0] m2) fun r3 m3 =>
  bW (callW p n "const_e" [pw m3 pi 16] m3) fun r4 m4 =>
  bW (callW p n "nat_ap1" [pw m4 pi 17, r2.headD 0] m4) fun r5 m5 =>
  bW (callW p n "nat_ap1" [pw m4 pi 17, r3.headD 0] m5) fun r6 m6 =>
  bW (callW p n "const_e" [pw m6 pi 18] m6) fun r7 m7 =>
  bW (callW p n "const_e" [pw m7 pi 19] m7) fun r8 m8 =>
  bW (callW p n "iw_alloc" [8] m8) fun rq mq =>
  some ([rq.headD 0], ((((((((mq.set64 IW (rq.headD 0) (r2.headD 0)).set64 IW (rq.headD 0 + 1)
    (r3.headD 0)).set64 IW (rq.headD 0 + 2) (r4.headD 0)).set64 IW (rq.headD 0 + 3) (pw m4 pi 17)).set64 IW
    (rq.headD 0 + 4) (r5.headD 0)).set64 IW (rq.headD 0 + 5) (r6.headD 0)).set64 IW (rq.headD 0 + 6)
    (r7.headD 0)).set64 IW (rq.headD 0 + 7) (r8.headD 0)))

set_option maxHeartbeats 3200000 in
theorem natEqCtx_specW (p : Prog) (hp : p.lookup "nat_eq_ctx" = some natEqCtx) (n : Nat) (s₀ : St)
    (pi d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_ctx" [pi, d]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqCtxW p n s₀.mem pi d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqCtx]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "const_e", callW_spec p n "intern_fvar", callW_spec p n "nat_ap1",
      callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) (instances := 10000) [natEqCtxW, bW, pw]

/-- The context record of the dispatch: eight handle words at `cx`, below the pool's top. -/
def CtxR (m : Mem) (r : List Word) (c : EIdx × EIdx × EIdx × NIdx × EIdx × EIdx × EIdx × EIdx) :
    Prop :=
  ∃ wx wy wz wn wsx wsy wt wf : Word, c = (decE wx, decE wy, decE wz, decI wn, decE wsx, decE wsy,
      decE wt, decE wf) ∧ H wx ∧ H wy ∧ H wz ∧ H wn ∧ H wsx ∧ H wsy ∧ H wt ∧ H wf ∧
    (r.headD 0).toNat + 8 ≤ iwTop m ∧ ∀ (j : Nat) (hj : j < 8),
      (iwA m)[(r.headD 0).toNat + j]? = some ([wx, wy, wz, wn, wsx, wsy, wt, wf][j])

theorem pw_of_rec {m m' : Mem} {pi : Word} (hP : PinRecAt m pi) (hI : IWOK m) (hg : IWGrow m m')
    (j : Nat) (hj : j < 21) : pw m' pi (UInt64.ofNat j) = (pinRecW m)[j]'(by simp [pinRecW]; omega) := by
  obtain ⟨-, hroom, hget⟩ := hP
  have hsz := hI.2.2.1
  have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < UInt64.size by unfold UInt64.size; omega)
  have hadd : (pi + UInt64.ofNat j).toNat = pi.toNat + j := by
    rw [UInt64.toNat_add, hj64]; have := hI.1; omega
  have h1 := hget j hj
  simp only [pw, rdW, hadd]
  simp only [iwA] at h1
  rw [hg.2.2.1 _ (by omega), h1]
  simp

theorem natEqCtx_ref (hN : NatSubProg' p) (pi d : Word) :
    CallRef p "nat_eq_ctx" [pi, d]
      (fun m a => StageR dn vis fe m a ∧ PinRecAt m pi ∧ H d)
      (natEqCtxT d.toNat) (KeepPost dn vis fe CtxR) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hP, hd⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqCtxW p k mm pi d) (natEqCtx_specW p hN.lNatEqCtx k · pi d) hc
  unfold natEqCtxW at hw
  have hF := hS.1.pins.full hP.1
  have hI := hS.2
  -- pin words at any later memory
  have pwr : ∀ m2, IWGrow m m2 → ∀ j (hj : j < 21), pw m2 pi (UInt64.ofNat j) = (pinRecW m)[j]'(by simp [pinRecW]; omega) :=
    fun m2 hg j hj => pw_of_rec hP hI hg j hj
  have hnames : ∀ j (hj : j < 51), H (pinW m (1 + j)) := fun j hj => hF.names_lt j hj
  have e15 : ∀ m2, IWGrow m m2 → pw m2 pi 15 = pinW m 2 := fun m2 hg => pwr m2 hg 15 (by decide)
  have e16 : ∀ m2, IWGrow m m2 → pw m2 pi 16 = pinW m 3 := fun m2 hg => pwr m2 hg 16 (by decide)
  have e17 : ∀ m2, IWGrow m m2 → pw m2 pi 17 = pinW m 4 := fun m2 hg => pwr m2 hg 17 (by decide)
  have e18 : ∀ m2, IWGrow m m2 → pw m2 pi 18 = pinW m 31 := fun m2 hg => pwr m2 hg 18 (by decide)
  have e19 : ∀ m2, IWGrow m m2 → pw m2 pi 19 = pinW m 32 := fun m2 hg => pwr m2 hg 19 (by decide)
  rw [e15 m (IWGrow.refl m)] at hw
  cases h1 : callW p k "const_e" [pinW m 2] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 2) k m a r1 m1 ⟨hS, hnames 1 (by decide)⟩ h1
  have hp1 : a1.pins = a.pins := (keepsP_constE _).run hrun1
  cases h2 : callW p k "intern_fvar" [d, r1.headD 0] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := internFVar_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg d (r1.headD 0) hl1 k m1 a1 r2 m2 hS1 h2
  have hp2 : a2.pins = a1.pins := (keepsP_internE _).run hrun2
  cases h3 : callW p k "intern_fvar" [d + 1, r1.headD 0] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := internFVar_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (d + 1) (r1.headD 0) hl1 k m2 a2 r3 m3 hS2 h3
  have hp3 : a3.pins = a2.pins := (keepsP_internE _).run hrun3
  have g1 : IWGrow m m1 := hg1
  have g2 : IWGrow m m2 := g1.trans hg2
  have g3 : IWGrow m m3 := g2.trans hg3
  rw [e16 m3 g3] at hw
  cases h4 : callW p k "const_e" [pinW m 3] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 3) k m3 a3 r4 m4 ⟨hS3, hnames 2 (by decide)⟩ h4
  have hp4 : a4.pins = a3.pins := (keepsP_constE _).run hrun4
  have g4 : IWGrow m m4 := g3.trans hg4
  rw [e17 m4 g4] at hw
  cases h5 : callW p k "nat_ap1" [pinW m 4, r2.headD 0] m4 with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hl5, hx5⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe)
    (hN.toNatSubProg.toNatEqProg) (pinW m 4) (r2.headD 0) k m4 a4 r5 m5 ⟨hS4, hnames 3 (by decide), hl2⟩ h5
  have hp5 : a5.pins = a4.pins := (keepsP_natAp1 _ _).run hrun5
  have g5 : IWGrow m m5 := g4.trans hg5
  cases h6 : callW p k "nat_ap1" [pinW m 4, r3.headD 0] m5 with
  | none => rw [h6] at hw; simp at hw
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, bW_some] at hw
  obtain ⟨x6, a6, hrun6, hS6, hg6, hl6, hx6⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe)
    (hN.toNatSubProg.toNatEqProg) (pinW m 4) (r3.headD 0) k m5 a5 r6 m6 ⟨hS5, hnames 3 (by decide), hl3⟩ h6
  have hp6 : a6.pins = a5.pins := (keepsP_natAp1 _ _).run hrun6
  have g6 : IWGrow m m6 := g5.trans hg6
  rw [e18 m6 g6] at hw
  cases h7 : callW p k "const_e" [pinW m 31] m6 with
  | none => rw [h7] at hw; simp at hw
  | some q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7, bW_some] at hw
  obtain ⟨x7, a7, hrun7, hS7, hg7, hl7, hx7⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 31) k m6 a6 r7 m7 ⟨hS6, hnames 30 (by decide)⟩ h7
  have hp7 : a7.pins = a6.pins := (keepsP_constE _).run hrun7
  have g7 : IWGrow m m7 := g6.trans hg7
  rw [e19 m7 g7] at hw
  cases h8 : callW p k "const_e" [pinW m 32] m7 with
  | none => rw [h8] at hw; simp at hw
  | some q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [h8, bW_some] at hw
  obtain ⟨x8, a8, hrun8, hS8, hg8, hl8, hx8⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 32) k m7 a7 r8 m8 ⟨hS7, hnames 31 (by decide)⟩ h8
  have hp8 : a8.pins = a7.pins := (keepsP_constE _).run hrun8
  have g8 : IWGrow m m8 := g7.trans hg8
  -- the allocation and the record
  cases hq : callW p k "iw_alloc" [8] m8 with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨hq0, hmq, hKeep, hroom, htop⟩ := iwAlloc_fref p hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.lIwAlloc 8 k m8 rq mq hS8.2 hq
  have hlt : ∀ w ∈ [r2.headD 0, r3.headD 0, r4.headD 0, pinW m 4, r5.headD 0, r6.headD 0, r7.headD 0, r8.headD 0],
      w.toNat < 2 ^ 32 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl2
    · exact hl3
    · exact hl4
    · exact hnames 3 (by decide)
    · exact hl5
    · exact hl6
    · exact hl7
    · exact hl8
  have hrec := recPost_wr m8 [r2.headD 0, r3.headD 0, r4.headD 0, pinW m 4, r5.headD 0, r6.headD 0, r7.headD 0, r8.headD 0] 8 rfl hS8.2 (by simpa [iwTop] using hroom)
  have echain : (((((((((allocMem m8 8).set64 IW (rdW (m8.arr64 CTL) 200) (r2.headD 0)).set64 IW (rdW (m8.arr64 CTL) 200 + 1) (r3.headD 0)).set64 IW (rdW (m8.arr64 CTL) 200 + 2) (r4.headD 0)).set64 IW (rdW (m8.arr64 CTL) 200 + 3) (pinW m 4)).set64 IW (rdW (m8.arr64 CTL) 200 + 4) (r5.headD 0)).set64 IW (rdW (m8.arr64 CTL) 200 + 5) (r6.headD 0)).set64 IW (rdW (m8.arr64 CTL) 200 + 6) (r7.headD 0)).set64 IW (rdW (m8.arr64 CTL) 200 + 7) (r8.headD 0)) =
      wrIW (allocMem m8 8) (rdW (m8.arr64 CTL) 200) [r2.headD 0, r3.headD 0, r4.headD 0, pinW m 4, r5.headD 0, r6.headD 0, r7.headD 0, r8.headD 0] := by
    simp [wrIW, UInt64.add_assoc]
  have hq' : (rdW (m8.arr64 CTL) 200).toNat = iwTop m8 := rfl
  subst hmq
  rw [hq0] at hm
  rw [echain] at hm
  subst hm
  have hr' : r = [rdW (m8.arr64 CTL) 200] := by rw [← hr, hq0]
  subst hr'
  obtain ⟨hqq, hKp, hroom', htop', hget⟩ := hrec
  -- the twin run
  have hF0 : PinsFull m a.pins := hF
  have F : ∀ b : AState, b.pins = a.pins → PinsFull m b.pins := fun b hb => hb ▸ hF0
  have rN : pinNat.run a = .ok (decI (pinW m 2), a) := pinAt_run hF0 1 (by decide)
  have hp3' : a3.pins = a.pins := by rw [hp3, hp2, hp1]
  have hp4' : a4.pins = a.pins := by rw [hp4, hp3']
  have hp6' : a6.pins = a.pins := by rw [hp6, hp5, hp4']
  have hp7' : a7.pins = a.pins := by rw [hp7, hp6']
  have rZ : pinNatZero.run a3 = .ok (decI (pinW m 3), a3) := pinAt_run (F a3 hp3') 2 (by decide)
  have rS : pinNatSucc.run a4 = .ok (decI (pinW m 4), a4) := pinAt_run (F a4 hp4') 3 (by decide)
  have rT : boolTrueName.run a6 = .ok (decI (pinW m 31), a6) := pinAt_run (F a6 hp6') 30 (by decide)
  have rF : boolFalseName.run a7 = .ok (decI (pinW m 32), a7) := pinAt_run (F a7 hp7') 31 (by decide)
  have hd1 : (d + 1).toNat = d.toNat + 1 := by
    have : (1 : Word).toNat = 1 := rfl
    rw [UInt64.toNat_add, this]; have : d.toNat < 2 ^ 32 := hd
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hd1] at hrun3
  refine ⟨(x2, x3, x4, decI (pinW m 4), x5, x6, x7, x8), a8, ?_, ?_⟩
  · have hxe : decE (r1.headD 0) = x1 := hx1
    rw [hxe] at hrun2 hrun3
    subst hx2 hx3 hx4 hx5 hx6 hx7 hx8
    have hrun5' : (natAp1 (decI (pinW m 4)) (decI (r2.headD 0))).run a4 = .ok (decI (r5.headD 0), a5) := hrun5
    have hrun6' : (natAp1 (decI (pinW m 4)) (decI (r3.headD 0))).run a5 = .ok (decI (r6.headD 0), a6) := hrun6
    simp only [natEqCtxT, StateT.run_bind, rN, hrun1, hrun2, hrun3, rZ, hrun4, rS, hrun5, hrun6,
      rT, hrun7, rF, hrun8, StateT.run_pure]
    simp only [bind, Except.bind, pure, Except.pure]
    simp only [hrun1, hrun2, hrun3, rZ, hrun4, rS, hrun5', hrun6', rT, hrun7, rF, hrun8]
  · refine ⟨hKp.stage hS8, g8.trans hKp.1, ?_⟩
    refine ⟨r2.headD 0, r3.headD 0, r4.headD 0, pinW m 4, r5.headD 0, r6.headD 0, r7.headD 0,
      r8.headD 0, ?_, hl2, hl3, hl4, hnames 3 (by decide), hl5, hl6, hl7, hl8, ?_, ?_⟩
    · subst hx2 hx3 hx4 hx5 hx6 hx7 hx8; rfl
    · simp only [List.headD_cons]; rw [hq', htop']; simp
    · intro j hj
      simp only [List.headD_cons, hq', iwA]
      have := hget j (by simpa using hj)
      rw [this]
      have hj8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      rcases hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end opeq

end L.Ind
