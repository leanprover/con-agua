module

public import ConAgua.Arena.DeclNatSub
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.DeclNatDeps
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

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
    ∀ j (hj : j < 21), iwA m (pi.toNat + j) = some ((pinRecW m)[j]'(by simp [pinRecW]; omega))

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
      iwA m ((r.headD 0).toNat + j) = some ([wx, wy, wz, wn, wsx, wsy, wt, wf][j])

theorem pw_of_rec {m m' : Mem} {pi : Word} (hP : PinRecAt m pi) (hI : IWOK m) (hg : IWGrow m m')
    (j : Nat) (hj : j < 21) : pw m' pi (UInt64.ofNat j) = (pinRecW m)[j]'(by simp [pinRecW]; omega) := by
  sorry

theorem natEqCtx_ref (hN : NatSubProg' p) (pi d : Word) :
    CallRef p "nat_eq_ctx" [pi, d]
      (fun m a => StageR vis fe m a ∧ PinRecAt m pi ∧ H d)
      (natEqCtxT d.toNat) (KeepPost vis fe NatCtxR) := by
  sorry

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
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
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
  · rw [ite_eq_left hd, decI_beq _ _ hc hq, decide_eq_true hd, ite_eq_left rfl]; exact h1 hd
  · rw [ite_eq_right hd, decI_beq _ _ hc hq, decide_eq_false hd]; exact h2 hd

/-- A last callee returning an equation list, as the pair `(o, l)`. -/
theorem CallRef.simPairE {f : FnName} {args : List Word} {pre : Mem → AState → Prop}
    {op : AM (List (EIdx × EIdx))} (h : CallRef p f args pre op (KeepPost vis fe decEqRL)) {n : Nat}
    {m : Mem} {a : AState} (hp : pre m a) :
    Sim (ntBW (callW p n f args m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')) op a
      (fun r x m' a' => KeepPost vis fe decEqRL m m' a' r x) :=
  Sim.ntRet (h.sim hp) fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decEqRL_norm h3⟩

theorem natEqDisp_ref (hN : NatSubProg' p) (c pi cx p0 p1 p2 p3 p4 p5 p6 x y z sN sx sy bT bF : Word) :
    CallRef p "nat_eq_disp" [c, pi, cx]
      (fun m a => StageR vis fe m a ∧ H c ∧ H p0 ∧ H p1 ∧ H p2 ∧ H p3 ∧ H p4 ∧ H p5 ∧ H p6 ∧
        H x ∧ H y ∧ H z ∧ H sN ∧ H sx ∧ H sy ∧ H bT ∧ H bF ∧
        pw m pi 0 = p0 ∧ pw m pi 1 = p1 ∧ pw m pi 2 = p2 ∧ pw m pi 3 = p3 ∧ pw m pi 4 = p4 ∧
        pw m pi 5 = p5 ∧ pw m pi 6 = p6 ∧ pw m cx 0 = x ∧ pw m cx 1 = y ∧ pw m cx 2 = z ∧
        pw m cx 3 = sN ∧ pw m cx 4 = sx ∧ pw m cx 5 = sy ∧ pw m cx 6 = bT ∧ pw m cx 7 = bF)
      (natEqDispT (decI c) (decI p0) (decI p1) (decI p2) (decI p3) (decI p4) (decI p5) (decI p6)
        (decE x) (decE y) (decE z) (decI sN) (decE sx) (decE sy) (decE bT) (decE bF))
      (KeepPost vis fe decEqRL) := by
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
  grind [arena_grind] bind ntBW

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
    (hj : j < 8) (h : iwA m (cx.toNat + j) = some w) : pw m cx (UInt64.ofNat j) = w := by
  sorry

theorem natOpEquations_ref (hN : NatSubProg' p) (d c : Word) :
    CallRef p "nat_op_equations" [d, c]
      (fun m a => StageR vis fe m a ∧ H d ∧ H c)
      (natOpEquations d.toNat (decI c)) (KeepPost vis fe decEqRL) := by
  sorry

@[refines ConRon.Arena.natOpEquations]
theorem natOpEquations_refines (hN : NatSubProg' p) (d c : Word) :
    RefAM p "nat_op_equations" [d, c] (fun m a => StageR vis fe m a ∧ H d ∧ H c)
      (natOpEquations d.toNat (decI c)) (KeepPost vis fe decEqRL) :=
  (natOpEquations_ref hN d c).refAM

end opeq

end L.Ind
