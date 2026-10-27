import ConAgua.Arena.DeclNatSub
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `nat_op_equations` refines `natOpEquations` (lane `decls3`, helper `decls3-nat`)

`nat_eq_ctx` (the terms built before the dispatch) and the dispatch over the seven operations.
-/

set_option experimental.vcgen true

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
  simp only [pinEmptyLevels, StateT.run_bind, StateT.run_get] at h
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
  lNatEqDisp : p.lookup "nat_eq_disp" = some natEqDisp

section opeq
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- The pin record at `pi` in `m`: the 21 words `nat_op_pins` writes, below the pool's top. -/
theorem pw_fold (m : Mem) (pi j : Word) : rdW (m.arr64 IW) (pi + j) = pw m pi j := rfl

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

/-- **`nat_eq_ctx` is its model `natEqCtxW`** (generated). -/
l_model natEqCtx_specW (p : Prog) (hp : p.lookup "nat_eq_ctx" = some natEqCtx)
  fns [hp ↦ natEqCtxW list]
  specs [callW_spec p n "const_e", callW_spec p n "intern_fvar", callW_spec p n "nat_ap1", callW_spec p n "iw_alloc"]
  grind [arena_grind] finish [ntBW, pw] gen 20 heartbeats 3200000 bind ntBW instances 10000

/-- The context record of the dispatch: eight handle words at `cx`, below the pool's top. -/
def NatCtxR (m : Mem) (r : List Word) (c : EIdx × EIdx × EIdx × NIdx × EIdx × EIdx × EIdx × EIdx) :
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
      (natEqCtxT d.toNat) (KeepPost dn vis fe NatCtxR) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hP, hd⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqCtxW p (k + 1) mm pi d) (natEqCtx_specW p hN.lNatEqCtx (k + 1) · pi d) hc
  rw [natEqCtxW.arm1] at hw; simp only [pw_fold] at hw
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
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 2) k m a r1 m1 ⟨hS, hnames 1 (by decide)⟩ h1
  have hp1 : a1.pins = a.pins := (keepsP_constE _).run hrun1
  replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := internFVar_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg d (r1.headD 0) hl1 k m1 a1 r2 m2 hS1 h2
  have hp2 : a2.pins = a1.pins := (keepsP_internE _).run hrun2
  replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := internFVar_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (d + 1) (r1.headD 0) hl1 k m2 a2 r3 m3 hS2 h3
  have hp3 : a3.pins = a2.pins := (keepsP_internE _).run hrun3
  have g1 : IWGrow m m1 := hg1
  have g2 : IWGrow m m2 := g1.trans hg2
  have g3 : IWGrow m m3 := g2.trans hg3
  rw [e16 m3 g3] at hw
  replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 3) k m3 a3 r4 m4 ⟨hS3, hnames 2 (by decide)⟩ h4
  have hp4 : a4.pins = a3.pins := (keepsP_constE _).run hrun4
  have g4 : IWGrow m m4 := g3.trans hg4
  rw [e17 m4 g4] at hw
  replace hw := ntBW_some hw; obtain ⟨r5, m5, h5, hw⟩ := hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hl5, hx5⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe)
    (hN.toNatSubProg.toNatEqProg) (pinW m 4) (r2.headD 0) k m4 a4 r5 m5 ⟨hS4, hnames 3 (by decide), hl2⟩ h5
  have hp5 : a5.pins = a4.pins := (keepsP_natAp1 _ _).run hrun5
  have g5 : IWGrow m m5 := g4.trans hg5
  replace hw := ntBW_some hw; obtain ⟨r6, m6, h6, hw⟩ := hw
  obtain ⟨x6, a6, hrun6, hS6, hg6, hl6, hx6⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe)
    (hN.toNatSubProg.toNatEqProg) (pinW m 4) (r3.headD 0) k m5 a5 r6 m6 ⟨hS5, hnames 3 (by decide), hl3⟩ h6
  have hp6 : a6.pins = a5.pins := (keepsP_natAp1 _ _).run hrun6
  have g6 : IWGrow m m6 := g5.trans hg6
  rw [e18 m6 g6] at hw
  replace hw := ntBW_some hw; obtain ⟨r7, m7, h7, hw⟩ := hw
  obtain ⟨x7, a7, hrun7, hS7, hg7, hl7, hx7⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 31) k m6 a6 r7 m7 ⟨hS6, hnames 30 (by decide)⟩ h7
  have hp7 : a7.pins = a6.pins := (keepsP_constE _).run hrun7
  have g7 : IWGrow m m7 := g6.trans hg7
  rw [e19 m7 g7] at hw
  replace hw := ntBW_some hw; obtain ⟨r8, m8, h8, hw⟩ := hw
  obtain ⟨x8, a8, hrun8, hS8, hg8, hl8, hx8⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg (pinW m 32) k m7 a7 r8 m8 ⟨hS7, hnames 31 (by decide)⟩ h8
  have hp8 : a8.pins = a7.pins := (keepsP_constE _).run hrun8
  have g8 : IWGrow m m8 := g7.trans hg8
  -- the allocation and the record
  replace hw := ntBW_some hw; obtain ⟨rq, mq, hq, hw⟩ := hw
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
    simp only [natEqCtxT, StateT.run_bind, rN, StateT.run_pure]
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

/-! ### The dispatch -/

def natEqDispW (p : Prog) (n : Nat) (m : Mem) (c pi cx : Word) : Option (List Word × Mem) :=
  let fin := fun (r : List Word) (m' : Mem) => some ([r.headD 0, r.tail.headD 0], m')
  if c = pw m pi 0 then ntBW (callW p n "nat_eq_pr" [c, pw m cx 2, pw m cx 0, pw m cx 4] m) fin else
  if c = pw m pi 1 then ntBW (callW p n "nat_eq_un" [c, pw m cx 0, pw m cx 1, pw m cx 2, pw m cx 5, pw m cx 3] m) fin else
  if c = pw m pi 2 then ntBW (callW p n "nat_eq_un" [c, pw m cx 0, pw m cx 1, pw m cx 2, pw m cx 5, pw m pi 0] m) fin else
  if c = pw m pi 3 then ntBW (callW p n "nat_eq_mu" [c, pw m cx 0, pw m cx 1, pw m cx 2, pw m cx 5, pw m pi 1] m) fin else
  if c = pw m pi 4 then ntBW (callW p n "nat_eq_po" [c, pw m cx 0, pw m cx 1, pw m cx 2, pw m cx 5, pw m cx 3, pw m pi 3] m) fin else
  if c = pw m pi 5 then ntBW (callW p n "nat_eq_be" [c, pw m cx 0, pw m cx 1, pw m cx 2, pw m cx 4, pw m cx 5, pw m cx 6, pw m cx 7] m) fin else
  if c = pw m pi 6 then ntBW (callW p n "nat_eq_bl" [c, pw m cx 0, pw m cx 1, pw m cx 2, pw m cx 4, pw m cx 5, pw m cx 6, pw m cx 7] m) fin else
  some ([0, 0], m)

set_option maxHeartbeats 6400000 in
theorem natEqDisp_specW (p : Prog) (hp : p.lookup "nat_eq_disp" = some natEqDisp) (n : Nat) (s₀ : St)
    (c pi cx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_disp" [c, pi, cx]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqDispW p n s₀.mem c pi cx = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqDisp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "nat_eq_pr", callW_spec p n "nat_eq_un", callW_spec p n "nat_eq_mu",
      callW_spec p n "nat_eq_po", callW_spec p n "nat_eq_be", callW_spec p n "nat_eq_bl"] <;>
    finish (gen := 20) (instances := 10000) [natEqDispW, ntBW, pw]

def natEqDispT (c pr ad su mu po be bl : NIdx) (x y z : EIdx) (sN : NIdx) (sx sy bT bF : EIdx) :
    AM (List (EIdx × EIdx)) :=
  if c == pr then natEqPrT c z x sx
  else if c == ad then natEqUnT c x y z sy sN
  else if c == su then natEqUnT c x y z sy pr
  else if c == mu then natEqMuT c x y z sy ad
  else if c == po then natEqPoT c x y z sy sN mu
  else if c == be then natEqBeT c x y z sx sy bT bF
  else if c == bl then natEqBlT c x y z sx sy bT bF
  else pure []

theorem decEqRL_norm {m : Mem} {r : List Word} {ps : List (EIdx × EIdx)} (h : decEqRL m r ps) :
    decEqRL m [r.headD 0, r.tail.headD 0] ps := by
  cases r with
  | nil => simpa [decEqRL] using h
  | cons a t => cases t <;> simpa [decEqRL] using h

/-- The model's `if c = q` against the twin's `if decI c == decI q`. -/
theorem Sim.iteH {β α : Type} {c q : Word} {e1 e2 : Option (β × Mem)} {o1 o2 : AM α} {a : AState}
    {R : β → α → Mem → AState → Prop} (hc : H c) (hq : H q)
    (h1 : c = q → Sim e1 o1 a R) (h2 : c ≠ q → Sim e2 o2 a R) :
    Sim (if c = q then e1 else e2) (if (decI c : NIdx) == decI q then o1 else o2) a R := by
  by_cases hd : c = q
  · rw [ite_eq_left hd, decI_beq_word hc hq, decide_eq_true hd, ite_eq_left rfl]; exact h1 hd
  · rw [ite_eq_right hd, decI_beq_word hc hq, decide_eq_false hd]; exact h2 hd

/-- A last callee returning an equation list, as the pair `(o, l)`. -/
theorem CallRef.simPairE {f : FnName} {args : List Word} {pre : Mem → AState → Prop}
    {op : AM (List (EIdx × EIdx))} (h : CallRef p f args pre op (KeepPost dn vis fe decEqRL)) {n : Nat}
    {m : Mem} {a : AState} (hp : pre m a) :
    Sim (ntBW (callW p n f args m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')) op a
      (fun r x m' a' => KeepPost dn vis fe decEqRL m m' a' r x) :=
  Sim.ntRet (h.sim hp) fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decEqRL_norm h3⟩

theorem natEqDisp_ref (hN : NatSubProg' p) (c pi cx p0 p1 p2 p3 p4 p5 p6 x y z sN sx sy bT bF : Word) :
    CallRef p "nat_eq_disp" [c, pi, cx]
      (fun m a => StageR dn vis fe m a ∧ H c ∧ H p0 ∧ H p1 ∧ H p2 ∧ H p3 ∧ H p4 ∧ H p5 ∧ H p6 ∧
        H x ∧ H y ∧ H z ∧ H sN ∧ H sx ∧ H sy ∧ H bT ∧ H bF ∧
        pw m pi 0 = p0 ∧ pw m pi 1 = p1 ∧ pw m pi 2 = p2 ∧ pw m pi 3 = p3 ∧ pw m pi 4 = p4 ∧
        pw m pi 5 = p5 ∧ pw m pi 6 = p6 ∧ pw m cx 0 = x ∧ pw m cx 1 = y ∧ pw m cx 2 = z ∧
        pw m cx 3 = sN ∧ pw m cx 4 = sx ∧ pw m cx 5 = sy ∧ pw m cx 6 = bT ∧ pw m cx 7 = bF)
      (natEqDispT (decI c) (decI p0) (decI p1) (decI p2) (decI p3) (decI p4) (decI p5) (decI p6)
        (decE x) (decE y) (decE z) (decI sN) (decE sx) (decE sy) (decE bT) (decE bF))
      (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqDispW p k mm c pi cx)
    (fun k s₀ => natEqDisp_specW p hN.lNatEqDisp k s₀ c pi cx) fun k m a ⟨hS, hc, h0, h1, h2, h3, h4, h5, h6,
      hx, hy, hz, hsN, hsx, hsy, hbT, hbF, e0, e1, e2, e3, e4, e5, e6, f0, f1, f2, f3, f4, f5, f6, f7⟩ => ?_
  have hE := hN.toNatSubProg.toNatEqProg
  unfold natEqDispW natEqDispT
  simp only [e0, e1, e2, e3, e4, e5, e6, f0, f1, f2, f3, f4, f5, f6, f7]
  refine Sim.iteH hc h0 (fun _ => (natEqPr_ref hE c z x sx).simPairE ⟨hS, hc, hz, hx, hsx⟩) fun _ => ?_
  refine Sim.iteH hc h1 (fun _ => (natEqUn_ref hE c x y z sy sN).simPairE ⟨hS, hc, hx, hy, hz, hsy, hsN⟩) fun _ => ?_
  refine Sim.iteH hc h2 (fun _ => (natEqUn_ref hE c x y z sy p0).simPairE ⟨hS, hc, hx, hy, hz, hsy, h0⟩) fun _ => ?_
  refine Sim.iteH hc h3 (fun _ => (natEqMu_ref hE c x y z sy p1).simPairE ⟨hS, hc, hx, hy, hz, hsy, h1⟩) fun _ => ?_
  refine Sim.iteH hc h4 (fun _ => (natEqPo_ref hE c x y z sy sN p3).simPairE ⟨hS, hc, hx, hy, hz, hsy, hsN, h3⟩)
    fun _ => ?_
  refine Sim.iteH hc h5 (fun _ => (natEqBe_ref hE c x y z sx sy bT bF).simPairE
    ⟨hS, hc, hx, hy, hz, hsx, hsy, hbT, hbF⟩) fun _ => ?_
  refine Sim.iteH hc h6 (fun _ => (natEqBl_ref hE c x y z sx sy bT bF).simPairE
    ⟨hS, hc, hx, hy, hz, hsx, hsy, hbT, hbF⟩) fun _ => ?_
  exact Sim.ret ⟨hS, IWGrow.refl m, by simp [decEqRL, EqL]⟩

/-! ### `nat_op_equations` -/

/-- **`nat_op_equations` is its model `natOpEquationsW`** (generated). -/
l_model natOpEquations_specW (p : Prog) (hp : p.lookup "nat_op_equations" = some natOpEquationsL)
  fns [hp ↦ natOpEquationsW list]
  specs [callW_spec p n "nat_op_pins", callW_spec p n "nat_eq_ctx", callW_spec p n "nat_eq_disp"]
  grind [arena_grind] bind ntBW simp [ntBW]

def natEqTailT (c : NIdx) (ctx : EIdx × EIdx × EIdx × NIdx × EIdx × EIdx × EIdx × EIdx) :
    AM (List (EIdx × EIdx)) := do
  let (x, y, z, sN, sx, sy, bT, bF) := ctx
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName
  let _di ← natDivName; let _mo ← natModName; let _gc ← natGcdName
  let _la ← natLandName; let _lo ← natLorName; let _xo ← natXorName
  let _sl ← natShiftLeftName; let _sr ← natShiftRightName
  natEqDispT c pr ad su mu po be bl x y z sN sx sy bT bF

theorem natOpEquations_split (d : Nat) (c : NIdx) :
    natOpEquations d c = (natEqCtxT d >>= natEqTailT c) := by
  simp only [natOpEquations, natEqCtxT, natEqTailT, natEqDispT, bind_assoc, pure_bind]
  rfl

theorem keepsP_pinAt (i : Nat) : Keeps (fun a : AState => a.pins) (pinAt i) := by
  unfold Keeps; intro a r a' h
  simp only [pinAt, StateT.run_bind, StateT.run_get] at h
  by_cases hi : i < a.pins.names.size
  · simp [hi] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · simp [hi, fail, throwThe, MonadExceptOf.throw] at h
    cases h

theorem keepsP_natEqCtxT (d : Nat) : Keeps (fun a : AState => a.pins) (natEqCtxT d) := by
  unfold natEqCtxT
  refine Keeps.bind (keepsP_pinAt _) fun _ => Keeps.bind (keepsP_constE _) fun _ =>
    Keeps.bind (keepsP_internE _) fun _ => Keeps.bind (keepsP_internE _) fun _ =>
    Keeps.bind (keepsP_pinAt _) fun _ => Keeps.bind (keepsP_constE _) fun _ =>
    Keeps.bind (keepsP_pinAt _) fun _ => Keeps.bind (keepsP_natAp1 _ _) fun _ =>
    Keeps.bind (keepsP_natAp1 _ _) fun _ => Keeps.bind (keepsP_pinAt _) fun _ =>
    Keeps.bind (keepsP_constE _) fun _ => Keeps.bind (keepsP_pinAt _) fun _ =>
    Keeps.bind (keepsP_constE _) fun _ => Keeps.pure _

theorem pinRecW_pins {m m1 : Mem} (h : m1.arr64 PINS = m.arr64 PINS) : pinRecW m1 = pinRecW m := by
  simp only [pinRecW, pinW, h]

theorem pw_of_get {m : Mem} {cx w : Word} {j : Nat} (hI : IWOK m) (hcx : cx.toNat + 8 ≤ iwTop m)
    (hj : j < 8) (h : (iwA m)[cx.toNat + j]? = some w) : pw m cx (UInt64.ofNat j) = w := by
  have hsz := hI.2.2.1
  have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < UInt64.size by unfold UInt64.size; omega)
  have hadd : (cx + UInt64.ofNat j).toNat = cx.toNat + j := by
    rw [UInt64.toNat_add, hj64]; have := hI.1; omega
  simp only [pw, rdW, hadd]
  simp only [iwA] at h
  rw [h]; rfl

theorem natOpEquations_ref (hN : NatSubProg' p) (d c : Word) :
    CallRef p "nat_op_equations" [d, c]
      (fun m a => StageR dn vis fe m a ∧ H d ∧ H c)
      (natOpEquations d.toNat (decI c)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hd, hc⟩ hw => ?_
  have hw := callW_model (M := fun mm => natOpEquationsW p (k + 1) mm d c) (natOpEquations_specW p hN.toNatSubProg.toNatEqProg.lNatOpEquations (k + 1) · d c) hw
  rw [natOpEquationsW.arm1] at hw
  have hF := hS.1.pins.full
  have hGate := hN.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  replace hw := ntBW_some hw; obtain ⟨rp, m1, h1, hw⟩ := hw
  obtain ⟨h0, hrec, hpins, hrp⟩ := natOpPins_fref hGate k m rp m1 hS.2 h1
  have hK1 := hrec.2.1
  have hS1 := hK1.stage hS
  have hpi : (rp.headD 0).toNat = iwTop m := by rw [hrec.1]; rfl
  have hP : PinRecAt m1 (rp.headD 0) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [pinW, hpins] using h0
    · have := hrec.2.2.2.1; rw [hpi]; simp [pinRecW] at this ⊢; omega
    · intro j hj
      have := hrec.2.2.2.2 j (by simp [pinRecW]; omega)
      simp only [iwA, hpi]
      rw [this]
      have hv := pinRecW_pins hpins
      simp [hv, List.getElem?_eq_getElem (show j < (pinRecW m).length by simp [pinRecW]; omega)]
  have hF0 : PinsFull m a.pins := hF h0
  replace hw := ntBW_some hw; obtain ⟨rc, m2, h2, hw⟩ := hw
  obtain ⟨cx0, a2, hrun2, hS2, hg2, wx, wy, wz, wn, wsx, wsy, wt, wf, hcx, hx, hy, hz, hn, hsx, hsy, ht, hf,
    hroom, hget⟩ := natEqCtx_ref hN (rp.headD 0) d k m1 a rc m2 ⟨hS1, hP, hd⟩ h2
  have hp2 : a2.pins = a.pins := by
    have := (keepsP_natEqCtxT d.toNat).run hrun2
    exact this
  have hF2 : PinsFull m a2.pins := by rw [hp2]; exact hF0
  have hnm : ∀ j (hj : j < 51), H (pinW m (1 + j)) := fun j hj => hF0.names_lt j hj
  have pwr : ∀ j (hj : j < 21), pw m2 (rp.headD 0) (UInt64.ofNat j) = (pinRecW m)[j]'(by simp [pinRecW]; omega) := by
    intro j hj
    have := pw_of_rec hP hS1.2 hg2 j hj
    rw [this]; simp only [pinRecW_pins hpins]
  have cxr : ∀ j (hj : j < 8), pw m2 (rc.headD 0) (UInt64.ofNat j) = [wx, wy, wz, wn, wsx, wsy, wt, wf][j] :=
    fun j hj => pw_of_get hS2.2 hroom hj (hget j hj)
  have hnr : ∀ j (hj : j < 15), H (pinW m (15 + j)) := fun j hj => by
    have := hnm (14 + j) (by omega); rwa [show 1 + (14 + j) = 15 + j by omega] at this
  replace hw := ntBW_some hw; obtain ⟨rr, m3, h3, hw⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  subst hr hm
  obtain ⟨xx, a3, hrun3, hS3, hg3, hdec⟩ := natEqDisp_ref hN c (rp.headD 0) (rc.headD 0)
    (pinW m (15+0)) (pinW m (15+1)) (pinW m (15+2)) (pinW m (15+3)) (pinW m (15+4)) (pinW m (15+5)) (pinW m (15+6))
    wx wy wz wn wsx wsy wt wf k m2 a2 rr m3
    ⟨hS2, hc, hnr 0 (by decide), hnr 1 (by decide), hnr 2 (by decide), hnr 3 (by decide), hnr 4 (by decide),
      hnr 5 (by decide), hnr 6 (by decide), hx, hy, hz, hn, hsx, hsy, ht, hf,
      pwr 0 (by decide), pwr 1 (by decide), pwr 2 (by decide), pwr 3 (by decide), pwr 4 (by decide),
      pwr 5 (by decide), pwr 6 (by decide), cxr 0 (by decide), cxr 1 (by decide), cxr 2 (by decide),
      cxr 3 (by decide), cxr 4 (by decide), cxr 5 (by decide), cxr 6 (by decide), cxr 7 (by decide)⟩ h3
  refine ⟨xx, a3, ?_, hS3, (hK1.1.trans hg2).trans hg3, decEqRL_norm hdec⟩
  rw [natOpEquations_split, StateT.run_bind, hrun2, hcx]
  have rr0 := fun i hi => pinAt_run (m := m) (a := a2) hF2 i hi
  simp (disch := decide) only [natEqTailT, StateT.run_bind, natPredName, natAddName, natSubName, natMulName, natPowName, natBeqName,
    natBleName, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
    natShiftRightName, pinNatPred, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq, pinNatBle, pinNatDiv,
    pinNatMod, pinNatGcd, pinNatLand, pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight,
    PIN_NAT_PRED, PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE, PIN_NAT_DIV,
    PIN_NAT_MOD, PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT]
  simp (disch := decide) only [rr0, bind, Except.bind]
  exact hrun3

@[refines ConRon.Arena.natOpEquations]
theorem natOpEquations_refines (hN : NatSubProg' p) (d c : Word) :
    RefAM p "nat_op_equations" [d, c] (fun m a => StageR dn vis fe m a ∧ H d ∧ H c)
      (natOpEquations d.toNat (decI c)) (KeepPost dn vis fe decEqRL) :=
  (natOpEquations_ref hN d c).refAM

end opeq

end L.Ind
