import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WhnfDeltaRefine2

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 3 (`nat_succ_lit`, `reduce_nat`'s arms)

Split from `WhnfDeltaRefine.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `nat_succ_lit` -/

/-- **An interned `lit` handle word is below `2^32`.** -/
theorem internW_hw (m : Mem) (a : AState) (hR : LitR m a) (o l : Word) (w : Word) (m' : Mem)
    (hI : internW m o l = some (w, m')) : w.toNat < 2 ^ 32 := by
  obtain ⟨hpool, hS⟩ := hR
  exact consInternM_lt litCS_wf hS hI

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `ArenaD`, with the handle word below
`2^32`. -/
theorem internLit_refinesD_hw (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hA : ArenaD s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (hn : Norm (vpool s₀.mem) o.toNat l.toNat)
    (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0) ∧ HW (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hA.1.lit.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨h1, h2, h3⟩ := internLit_D s.mem a₀ hA o l _ hq hn hq0 _ hI
  exact ⟨hloc, h1, h2, h3, internW_hw s.mem a₀ hA.1.lit o l _ _ hI⟩

section addhw
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd) (hpn : p.lookup "nat_add_lit" = some natAddLit)
  (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m)
  (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄)

include hpl hpc hpt hpa hpn hpool hgrow hI in
/-- `natAddLit_refines` with the result a handle word (`hI` carries `HW`). -/
theorem natAddLit_refines_hw (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)) ∧
      HW (r.headD 0); ⊤⦄ := by
  have hok := hpool _ _ hR
  have hm0 : s₀.mem.flag = 0 → s₀.mem.top.toNat < 2 ^ 40 := fun hf => by
    rcases hmode with h | h
    · exact absurd hf h
    · exact h
  rw [invoke_eq _ hpn]
  simp only [callFn, natAddLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, natAdd_spec p hpl hpc hpt hpa n,
        hI a₀ n] <;>
      finish [natAddArm]

end addhw

section succ
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd) (hpn : p.lookup "nat_add_lit" = some natAddLit)
  (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m)
  (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄)
  (hg : p.lookup "nat_succ_lit" = some natSuccLitL)

include hpl hpc hpt hpa hpn hpool hgrow hI hg in
/-- **`nat_succ_lit` refines the `Nat.add` arm at the literal `1`**, with a handle word result. -/
theorem natSuccLit_refines_hw (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (oa la : Word) (ha : SliceOK s₀.mem oa la) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_succ_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat) 1) a₀ ∧
      R s'.mem (AM.st (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat) 1) a₀) ∧
      AM.res (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat) 1) a₀ =
        some (decE (r.headD 0)) ∧ HW (r.headD 0); ⊤⦄ := by
  have hok := hpool _ _ hR
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  rw [invoke_eq _ hg]
  simp only [callFn, natSuccLitL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        fun s => natAddLit_refines_hw p hpl hpc hpt hpa hpn R hpool hgrow hI n s a₀] <;>
      finish (gen := 20) [natAddArm]

end succ

theorem keeps_cpl_natAddArm (a b : Nat) : Keeps cpl (natAddArm a b) := by
  unfold natAddArm
  exact Keeps.bind (keeps_cpl_internLit _) (fun _ => Keeps.pure _)

section refs17
variable (p : Prog)

theorem natSuccLit_inst (hp : WhnfDeltaProg' p) :
    ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), ArenaD s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄ :=
  fun a₀ n s₀ o l hA hq hn hq0 => internLit_refinesD_hw p hp.litHash' hp.limbsEq' hp.litMatch' hp.litFind'
    hp.litPush' hp.internLit a₀ n s₀ o l hA hq hn hq0

/-- `natSuccLit_inst` with "the pool only grew since `m₀`" carried along. -/
theorem natSuccLit_instP (hp : WhnfDeltaProg' p) (m₀ : Mem) :
    ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), (ArenaD s₀.mem a₀ ∧ PoolGrew m₀ s₀.mem) →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      (ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
        PoolGrew m₀ s'.mem) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄ := by
  intro a₀ n s₀ o l ⟨hA, hP⟩ hq hn hq0
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hD, hres, hhw⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (natSuccLit_inst p hp a₀ n s₀ o l hA hq hn hq0)
  obtain ⟨hfr, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hp.litClosed n (f := "intern_lit") (by decide) [o, l] s₀)
  subst hs
  exact ⟨hloc, hok, ⟨hD, hP.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩, hres, hhw⟩

/-- **`nat_succ_lit` as a run.** -/
theorem callW_natSuccLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt) (r : List Word) (m' : Mem)
    (h : callW p n "nat_succ_lit" [o, cnt] s₀.mem = some (r, m')) :
    AM.ok (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1) a₀ ∧
    CoreS dn m' (AM.st (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1) a₀) vis fe MM eb ∧
    AM.res (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1) a₀ = some (decE (r.headD 0)) ∧
    MemFrame natA natC s₀.mem m' ∧ HW (r.headD 0) ∧ PoolGrew s₀.mem m' := by
  obtain ⟨s', rfl, -, hok, ⟨hD, hP⟩, hres, hhw⟩ := triple_of_callW
    (natSuccLit_refines_hw p hp.natLimb' hp.addCarry' hp.natTrim' hp.natAdd' hp.natAddLit
      (fun m a => ArenaD m a ∧ PoolGrew s₀.mem m)
      (fun _ _ h => h.1.1.lit.1)
      (fun m m' a hA hg => ⟨ArenaD.grow m m' hg a hA.1, hA.2.trans (PoolGrew.of_grows hg)⟩)
      (natSuccLit_instP p hp s₀.mem) hp.natSuccLit n s₀ a₀ ⟨hC.arena, PoolGrew.refl _⟩ o cnt hs hC.mode) h
  have hfr := callW_natFrame p hp.natClosed "nat_succ_lit" (by decide +kernel) n _ _ _ _ h
  exact ⟨hok, hC.of_nat hD (Keeps.run (keeps_cpl_natAddArm _ _) (AM.run_of_ok _ _ hok)) hfr
    (internE_pure_views (by rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h) rfl _ (AM.run_of_ok _ _ hok)) hP, hres,
    hfr, hhw, hP⟩

end refs17

/-! ## `reduce_nat`: the twin's arms -/

/-- The `Nat.succ` arm of `reduceNat`, past the level test. -/
def redSuccT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let ns ← pinNatSucc
  if c == ns && (← natLitSupported fe) then do
    match ← rawNatLit? (← r.whnf depth b) with
    | some n => do
      let x ← internE (.lit (.natVal (n + 1)))
      pure (some x)
    | none => pure none
  else pure none

/-- The certified binary operation arm of `reduceNat`. -/
def redOpT (r : CoreFnsA) (depth : Nat) (c : NIdx) (a b : EIdx) : AM (Option EIdx) := do
  match ← rawNatLit? (← r.whnf depth a) with
  | some n₁ => do
    match ← rawNatLit? (← r.whnf depth b) with
    | some n₂ => natOpResult c n₁ n₂
    | none => pure none
  | none => pure none

/-- The safety-net arm of `reduceNat`. -/
def redWfT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (a b : EIdx) :
    AM (Option EIdx) := do
  let wf ← natOpWfNames
  if wf.contains c && (← natLitSupported fe) then do
    match ← rawNatLit? (← r.whnf depth a) with
    | some _ => do
      match ← rawNatLit? (← r.whnf depth b) with
      | some _ =>
        fail (.notImplemented "native Nat computation on literals")
      | none => pure none
    | none => pure none
  else pure none

/-- The binary arm of `reduceNat`, past the level test. -/
def redBinT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (a b : EIdx) :
    AM (Option EIdx) := do
  if (← natBinOpName c) && (← natOpStored fe c) then
    redOpT r depth c a b
  else
    redWfT r fe depth c a b

theorem reduceNat_notapp (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) (a : AState)
    (h : (e.tag == ETag.app) = false) : (reduceNat r fe depth e).run a = .ok (none, a) := by
  simp only [reduceNat, h]; rfl

theorem redBin_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (a b : EIdx) (s : AState)
    (b1 b2 : Bool) (h1 : (natBinOpName c).run s = .ok (b1, s))
    (h2 : (natOpStored fe c).run s = .ok (b2, s)) :
    (redBinT r fe depth c a b).run s =
      if (b1 && b2) = true then (redOpT r depth c a b).run s else (redWfT r fe depth c a b).run s := by
  simp only [redBinT, StateT.run_bind, h1, h2, except_ok_bind]
  cases b1 <;> cases b2 <;> rfl

section redruns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

theorem redSucc_run_skip (c : NIdx) (b : EIdx) (s s₁ : AState) (m : Mem) (hP : PinsFull m s.pins)
    (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = false) : (redSuccT r fe depth c b).run s = .ok (none, s₁) := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc]; rfl

theorem redSucc_run_none (c : NIdx) (b : EIdx) (s s₁ s₂ s₃ : AState) (m : Mem)
    (hP : PinsFull m s.pins) (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = true) (wb : EIdx)
    (hw : (r.whnf depth b).run s₁ = .ok (wb, s₂))
    (hr : (rawNatLit? wb).run s₂ = .ok (none, s₃)) :
    (redSuccT r fe depth c b).run s = .ok (none, s₃) := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc, ite_true, hw, hr]; rfl

theorem redSucc_run_some (c : NIdx) (b : EIdx) (s s₁ s₂ s₃ s₄ : AState) (m : Mem)
    (hP : PinsFull m s.pins) (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = true) (wb : EIdx)
    (hw : (r.whnf depth b).run s₁ = .ok (wb, s₂)) (N : Nat)
    (hr : (rawNatLit? wb).run s₂ = .ok (some N, s₃)) (x : EIdx)
    (hi : (internE (.lit (.natVal (N + 1)))).run s₃ = .ok (x, s₄)) :
    (redSuccT r fe depth c b).run s = .ok (some x, s₄) := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc, ite_true, hw, hr, hi]; rfl

theorem redOp_run_none1 (c : NIdx) (a b : EIdx) (s s₁ s₂ : AState) (wa : EIdx)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (none, s₂)) :
    (redOpT r depth c a b).run s = .ok (none, s₂) := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr]; rfl

theorem redOp_run_none2 (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ : AState) (wa wb : EIdx) (N : Nat)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (some N, s₂))
    (hw2 : (r.whnf depth b).run s₂ = .ok (wb, s₃)) (hr2 : (rawNatLit? wb).run s₃ = .ok (none, s₄)) :
    (redOpT r depth c a b).run s = .ok (none, s₄) := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr, hw2, hr2]; rfl

theorem redOp_run_some (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ s₅ : AState) (wa wb : EIdx)
    (N₁ N₂ : Nat) (o : Option EIdx)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (some N₁, s₂))
    (hw2 : (r.whnf depth b).run s₂ = .ok (wb, s₃))
    (hr2 : (rawNatLit? wb).run s₃ = .ok (some N₂, s₄))
    (hres : (natOpResult c N₁ N₂).run s₄ = .ok (o, s₅)) :
    (redOpT r depth c a b).run s = .ok (o, s₅) := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr, hw2, hr2, hres]

theorem redWf_run_skip (c : NIdx) (a b : EIdx) (s s₁ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = false) :
    (redWfT r fe depth c a b).run s = .ok (none, s₁) := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc]; rfl

theorem redWf_run_none1 (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (wa : EIdx) (hw : (r.whnf depth a).run s₁ = .ok (wa, s₂))
    (hr : (rawNatLit? wa).run s₂ = .ok (none, s₃)) :
    (redWfT r fe depth c a b).run s = .ok (none, s₃) := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw, hr]; rfl

theorem redWf_run_none2 (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ s₅ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (wa wb : EIdx) (N : Nat) (hw : (r.whnf depth a).run s₁ = .ok (wa, s₂))
    (hr : (rawNatLit? wa).run s₂ = .ok (some N, s₃))
    (hw2 : (r.whnf depth b).run s₃ = .ok (wb, s₄))
    (hr2 : (rawNatLit? wb).run s₄ = .ok (none, s₅)) :
    (redWfT r fe depth c a b).run s = .ok (none, s₅) := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw, hr, hw2, hr2]; rfl

end redruns

/-! ## `reduce_nat_succ`, `reduce_nat_op`, `reduce_nat_wf` -/

/-- The model of `reduce_nat_succ`: `(flag, result, memory)`. -/
def reduceNatSuccW (p : Prog) (n : Nat) (m : Mem) (mode vis d c b : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "nat_lit_supported" [vis] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "pin_at" [3] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if c ≠ r₂.headD 0 then some (0, 0, m₂)
  else if r₁.headD 0 = 0 then some (0, 0, m₂)
  else
  match callW p n "whnf" [mode, vis, d, b] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  if r₄.headD 0 = 0 then some (0, 0, m₄)
  else
  match callW p n "nat_succ_lit" [r₄.tail.headD 0, r₄.tail.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (1, r₅.headD 0, m₅)

theorem reduceNatSucc_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d c b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_succ" [mode, vis, d, c, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatSuccW p n s₀.mem mode vis d c b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatSucc]
  simp only [callFn, reduceNatSuccL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_lit_supported", callW_spec p n "pin_at", callW_spec p n "whnf",
      callW_spec p n "raw_nat_lit", callW_spec p n "nat_succ_lit"] <;>
    finish (gen := 30) [reduceNatSuccW]

/-- The model of `reduce_nat_op`: `(flag, result, memory)`. -/
def reduceNatOpW (p : Prog) (n : Nat) (m : Mem) (mode vis d c a b : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "whnf" [mode, vis, d, a] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "raw_nat_lit" [r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 = 0 then some (0, 0, m₂)
  else
  match callW p n "whnf" [mode, vis, d, b] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  if r₄.headD 0 = 0 then some (0, 0, m₄)
  else
  match callW p n "nat_op_result" [c, r₂.tail.headD 0, r₂.tail.tail.headD 0, r₄.tail.headD 0,
      r₄.tail.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (Cmp.evalW .ne (r₅.headD 0) 0, BinOp.eval .and (r₅.tail.headD 0) 4294967295, m₅)

section ropw
variable (p : Prog) (n : Nat) (mode vis d c a b : Word) (m m₁ m₂ m₃ m₄ m₅ : Mem)
  (r₁ r₂ r₃ r₄ r₅ : List Word)

end ropw

theorem reduceNatOp_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d c a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_op" [mode, vis, d, c, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatOpW p n s₀.mem mode vis d c a b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatOp]
  simp only [callFn, reduceNatOpL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "whnf", callW_spec p n "raw_nat_lit", callW_spec p n "nat_op_result"] <;>
  simp_all [reduceNatOpW, Cmp.evalW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- `natOpWfNames` with its pins read: pin word `k` is `w k`. -/
def natOpWfSel (w : Nat → Word) (c : Word) : Bool :=
  decide (c = w 22) || decide (c = w 23) || decide (c = w 24) || decide (c = w 25) ||
  decide (c = w 26) || decide (c = w 27) || decide (c = w 28) || decide (c = w 29)

theorem natOpIsWfL_spec (p : Prog) (hp : p.lookup "nat_op_is_wf" = some natOpIsWfL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_op_is_wf" [c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧
      (r.headD 0 != 0) = natOpWfSel (pinW s₀.mem) c ∧ HW (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpIsWfL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [natOpWfSel, pinW_eq, HW]

theorem natOpWfNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    natOpWfNames.run a = .ok ([decI (pinW m 22), decI (pinW m 23), decI (pinW m 24),
      decI (pinW m 25), decI (pinW m 26), decI (pinW m 27), decI (pinW m 28), decI (pinW m 29)], a) := by
  simp only [natOpWfNames, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor,
    pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD, PIN_NAT_LAND,
    PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT, StateT.run_bind,
    pinAt_run h _ (by decide : 21 < 51), pinAt_run h _ (by decide : 22 < 51),
    pinAt_run h _ (by decide : 23 < 51), pinAt_run h _ (by decide : 24 < 51),
    pinAt_run h _ (by decide : 25 < 51), pinAt_run h _ (by decide : 26 < 51),
    pinAt_run h _ (by decide : 27 < 51), pinAt_run h _ (by decide : 28 < 51), except_ok_bind]
  rfl

theorem wfContains {m : Mem} {a : AState} (h : PinsFull m a.pins) (c : Word) (hc : HW c) :
    ([decI (pinW m 22), decI (pinW m 23), decI (pinW m 24), decI (pinW m 25), decI (pinW m 26),
      decI (pinW m 27), decI (pinW m 28), decI (pinW m 29)] : List NIdx).contains (decI c) =
      natOpWfSel (pinW m) c := by
  have hb : ∀ i, i < 51 → ((decI c : NIdx) == decI (pinW m (1 + i))) = decide (c = pinW m (1 + i)) :=
    fun i hi => decI_beq _ _ hc (h.names_lt i hi)
  have e22 : ((decI c : NIdx) == decI (pinW m 22)) = decide (c = pinW m 22) := hb 21 (by decide)
  have e23 : ((decI c : NIdx) == decI (pinW m 23)) = decide (c = pinW m 23) := hb 22 (by decide)
  have e24 : ((decI c : NIdx) == decI (pinW m 24)) = decide (c = pinW m 24) := hb 23 (by decide)
  have e25 : ((decI c : NIdx) == decI (pinW m 25)) = decide (c = pinW m 25) := hb 24 (by decide)
  have e26 : ((decI c : NIdx) == decI (pinW m 26)) = decide (c = pinW m 26) := hb 25 (by decide)
  have e27 : ((decI c : NIdx) == decI (pinW m 27)) = decide (c = pinW m 27) := hb 26 (by decide)
  have e28 : ((decI c : NIdx) == decI (pinW m 28)) = decide (c = pinW m 28) := hb 27 (by decide)
  have e29 : ((decI c : NIdx) == decI (pinW m 29)) = decide (c = pinW m 29) := hb 28 (by decide)
  simp only [List.contains, List.elem, natOpWfSel, e22, e23, e24, e25, e26, e27, e28, e29]
  generalize decide (c = pinW m 22) = x1
  generalize decide (c = pinW m 23) = x2
  generalize decide (c = pinW m 24) = x3
  generalize decide (c = pinW m 25) = x4
  generalize decide (c = pinW m 26) = x5
  generalize decide (c = pinW m 27) = x6
  generalize decide (c = pinW m 28) = x7
  generalize decide (c = pinW m 29) = x8
  revert x1 x2 x3 x4 x5 x6 x7 x8
  decide

/-- The model of `reduce_nat_wf`: `(flag, result, memory)` (`none` where the L code aborts). -/
def reduceNatWfW (p : Prog) (n : Nat) (m : Mem) (mode vis d c a b : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "nat_op_is_wf" [c] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "nat_lit_supported" [vis] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0 then
    match callW p n "whnf" [mode, vis, d, a] m₂ with
    | none => none
    | some (r₃, m₃) =>
    match callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
    | none => none
    | some (r₄, m₄) =>
    if r₄.headD 0 = 0 then some (0, 0, m₄)
    else
    match callW p n "whnf" [mode, vis, d, b] m₄ with
    | none => none
    | some (r₅, m₅) =>
    match callW p n "raw_nat_lit" [r₅.headD 0] m₅ with
    | none => none
    | some (r₆, m₆) =>
    if r₆.headD 0 = 0 then some (0, 0, m₆) else none
  else some (0, 0, m₂)

theorem reduceNatWf_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d c a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_wf" [mode, vis, d, c, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatWfW p n s₀.mem mode vis d c a b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatWf]
  simp only [callFn, reduceNatWfL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_op_is_wf", callW_spec p n "nat_lit_supported", callW_spec p n "whnf",
      callW_spec p n "raw_nat_lit"] <;>
  simp_all [reduceNatWfW, Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- The model of `reduce_nat_k`: `(flag, result, memory)`. -/
def reduceNatKW (p : Prog) (n : Nat) (m : Mem) (mode vis d f b : Word) :
    Option (Word × Word × Mem) :=
  if tcnt m CONST (tierW f) ≤ idxW f then none
  else
    match callW p n "pin_word" [52] m with
    | none => none
    | some (r₁, m₁) =>
      if tfld m CONST (tierW f) (idxW f) 1 ≠ r₁.headD 0 then some (0, 0, m₁)
      else
        match callW p n "reduce_nat_succ" [mode, vis, d, tfld m CONST (tierW f) (idxW f) 0,
            b] m₁ with
        | none => none
        | some (r₂, m₂) => some (r₂.headD 0, r₂.tail.headD 0, m₂)

theorem reduceNatK_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d f b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_k" [mode, vis, d, f, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatKW p n s₀.mem mode vis d f b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatK]
  simp only [callFn, reduceNatKL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "pin_word", callW_spec p n "reduce_nat_succ"] <;>
    finish (gen := 30) [reduceNatKW, tierW, idxW]

/-- The model of `reduce_nat_ap`: `(flag, result, memory)`. -/
def reduceNatApW (p : Prog) (n : Nat) (m : Mem) (mode vis d f b : Word) :
    Option (Word × Word × Mem) :=
  if tcnt m APP (tierW f) ≤ idxW f then none
  else if tfld m APP (tierW f) (idxW f) 0 >>> 28 ≠ 3 then some (0, 0, m)
  else if tierW (tfld m APP (tierW f) (idxW f) 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW (tfld m APP (tierW f) (idxW f) 0)) ≤
      idxW (tfld m APP (tierW f) (idxW f) 0) then none
  else
    match callW p n "pin_word" [52] m with
    | none => none
    | some (r₁, m₁) =>
      if tfld m CONST (tierW (tfld m APP (tierW f) (idxW f) 0)) (idxW (tfld m APP (tierW f) (idxW f) 0)) 1 ≠ r₁.headD 0 then
        some (0, 0, m₁)
      else
        match callW p n "nat_bin_op_name" [tfld m CONST (tierW (tfld m APP (tierW f) (idxW f) 0)) (idxW (tfld m APP (tierW f) (idxW f) 0)) 0] m₁ with
        | none => none
        | some (r₂, m₂) =>
        match callW p n "nat_op_stored" [vis, tfld m CONST (tierW (tfld m APP (tierW f) (idxW f) 0)) (idxW (tfld m APP (tierW f) (idxW f) 0)) 0] m₂ with
        | none => none
        | some (r₃, m₃) =>
        if r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0 then
          match callW p n "reduce_nat_op" [mode, vis, d, tfld m CONST (tierW (tfld m APP (tierW f) (idxW f) 0)) (idxW (tfld m APP (tierW f) (idxW f) 0)) 0,
              tfld m APP (tierW f) (idxW f) 1, b] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)
        else
          match callW p n "reduce_nat_wf" [mode, vis, d, tfld m CONST (tierW (tfld m APP (tierW f) (idxW f) 0)) (idxW (tfld m APP (tierW f) (idxW f) 0)) 0,
              tfld m APP (tierW f) (idxW f) 1, b] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)

set_option maxHeartbeats 4000000 in
theorem reduceNatAp_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d f b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_ap" [mode, vis, d, f, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatApW p n s₀.mem mode vis d f b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatAp]
  simp only [callFn, reduceNatApL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "pin_word", callW_spec p n "nat_bin_op_name", callW_spec p n "nat_op_stored",
      callW_spec p n "reduce_nat_op", callW_spec p n "reduce_nat_wf"] <;>
    finish (gen := 30) [reduceNatApW, tierW, idxW]

/-- The model of `reduce_nat_head`: `(flag, result, memory)`. -/
def reduceNatHeadW (p : Prog) (n : Nat) (m : Mem) (mode vis d f b : Word) :
    Option (Word × Word × Mem) :=
  if tierW f ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if f >>> 28 = 3 then
    (match callW p n "reduce_nat_k" [mode, vis, d, f, b] m with
      | none => none
      | some (r₁, m₁) => some (r₁.headD 0, r₁.tail.headD 0, m₁))
  else if f >>> 28 = 4 then
    (match callW p n "reduce_nat_ap" [mode, vis, d, f, b] m with
      | none => none
      | some (r₁, m₁) => some (r₁.headD 0, r₁.tail.headD 0, m₁))
  else if f >>> 28 = 0 then
    (if tcnt m BVAR (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 1 then
    (if tcnt m FVAR (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 2 then
    (if tcnt m SORT (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 5 then
    (if tcnt m LAM (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 6 then
    (if tcnt m FORALL (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 7 then
    (if tcnt m LET (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 8 then
    (if tcnt m LIT (tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 ≠ 9 then none
  else if tcnt m PROJ (tierW f) ≤ idxW f then none
  else some (0, 0, m)

theorem reduceNatHead_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d f b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_head" [mode, vis, d, f, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatHeadW p n s₀.mem mode vis d f b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatHead]
  simp only [callFn, reduceNatHeadL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "reduce_nat_k", callW_spec p n "reduce_nat_ap"] <;>
    finish (gen := 30) [reduceNatHeadW, tierW, idxW]

/-- The model of `reduce_nat`: `(flag, result, memory)`. -/
def reduceNatW (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word) :
    Option (Word × Word × Mem) :=
  if e >>> 28 ≠ 4 then some (0, 0, m)
  else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m APP (tierW e) ≤ idxW e then none
  else
    match callW p n "reduce_nat_head" [mode, vis, d, tfld m APP (tierW e) (idxW e) 0,
        tfld m APP (tierW e) (idxW e) 1] m with
    | none => none
    | some (r₁, m₁) => some (r₁.headD 0, r₁.tail.headD 0, m₁)

theorem reduceNat_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatW p n s₀.mem mode vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNat]
  simp only [callFn, reduceNatL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "reduce_nat_head"] <;>
    finish (gen := 30) [reduceNatW, tierW, idxW]

theorem natAddArm_run_internE {a₁ a₂ : AState} {x : EIdx} {u v : Nat}
    (h : (natAddArm u v).run a₁ = .ok (some x, a₂)) :
    (internE (.lit (.natVal (u + v)))).run a₁ = .ok (x, a₂) := by
  have e : (natAddArm u v).run a₁ =
      Except.map (fun q => (some q.1, q.2)) ((internE (.lit (.natVal (u + v)))).run a₁) := by
    simp only [natAddArm, StateT.run_bind]
    cases (internE (.lit (.natVal (u + v)))).run a₁ <;> rfl
  rw [e] at h
  cases hh : (internE (.lit (.natVal (u + v)))).run a₁ with
  | error e => rw [hh] at h; cases h
  | ok q =>
    rw [hh] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x', a'⟩ := q
    simp only at h1 h2
    rw [h1, h2]

theorem pinW_const_frame {m m' : Mem} (hf : MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m m') (k : Nat) :
    pinW m' k = pinW m k := by
  have : m'.arr64 PINS = m.arr64 PINS := hf.arr_eq PINS (by simp [CREC, CSLOT, CLP, PINS]) (by decide)
  simp only [pinW, this]

section refs18
variable (p : Prog)

theorem callW_reduceNatSucc (hp : WhnfDeltaProg' p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (hb : HW b) (r : List Word) (m' : Mem)
    (h : callW p n "reduce_nat_succ" [mode, vis, d, c, b] s₀.mem = some (r, m')) :
    CoreRef (redSuccT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatSucc_spec p hp.toWhnfDeltaProg n s₀ mode vis d c b) h
  unfold reduceNatSuccW at hW
  cases h1 : callW p n "nat_lit_supported" [vis] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, hS1, hres1, hfr1, hrh1⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  cases h2 : callW p n "pin_at" [3] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hm2, -, -, hr₂⟩ := callW_pinAt p hp.pinAt n m₁ 3 r₂ m₂ h2
  subst m₂
  simp only [show (3 : Word).toNat = 3 from rfl] at hr₂
  have hr₂' : r₂.headD 0 = pinW s₀.mem 4 := by rw [hr₂, pinW_const_frame hfr1]
  -- the twin's `natLitSupported`
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₁, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS1
  have hcw : HW (pinW s₀.mem 4) := hC.pins.names_lt 3 (by decide)
  have hskip : (c ≠ r₂.headD 0 ∨ r₁.headD 0 = 0) →
      ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = false := by
    intro hh
    rw [decI_beq _ _ hc hcw]
    rcases hh with hh | hh
    · rw [hr₂'] at hh
      have : decide (c = pinW s₀.mem 4) = false := decide_eq_false hh
      rw [this]; rfl
    · have : decBool r₁ = false := by simp only [decBool, hh]; rfl
      rw [this]; simp
  have hgo : (c = r₂.headD 0) → ¬ r₁.headD 0 = 0 →
      ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = true := by
    intro hh1 hh2
    rw [decI_beq _ _ hc hcw]
    have h1 : c = pinW s₀.mem 4 := by rw [← hr₂']; exact hh1
    have h2 : decBool r₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hh2
    rw [h2]; simp [h1]
  by_cases hcn : c ≠ r₂.headD 0
  · rw [ite_eq_left hcn] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redSucc_run_skip (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁
      s₀.mem hC.pins (decBool r₁) hsup (hskip (Or.inl hcn))
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₁) ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right hcn] at hW
  by_cases hs0 : r₁.headD 0 = 0
  · rw [ite_eq_left hs0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redSucc_run_skip (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁
      s₀.mem hC.pins (decBool r₁) hsup (hskip (Or.inr hs0))
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₁) ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right hs0] at hW
  have hcond := hgo (by simpa using hcn) hs0
  -- `whnf`
  cases h3 : callW p n "whnf" [mode, vis, d, b] m₁ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS1, hS.mode4, hS.eb_mode⟩
  have hkn : KnotOK p n := hk n (by omega)
  obtain ⟨hok3, ⟨M', hS3, hK3, hSt3⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode d b (by omega) (by omega) hSP1 hb) h3
  cases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  dsimp only at hW
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₁ = a₂ at hrun3 hS3
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M' eb _
    hS3 hrw3 r₄ m₄ h4
  subst m₄
  have hStK1 := StackKept.of_const_frame hfr1
  by_cases hf : r₄.headD 0 = 0
  · rw [ite_eq_left hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [ite_eq_left hf]
    rw [hnone] at hrun4
    have hz := redSucc_run_none (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁ a₂ a₂
      s₀.mem hC.pins (decBool r₁) hsup hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) hrun4
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M', hS3, hK3, hStK1.trans hSt3⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right hf] at hW
  obtain ⟨hsl, hnorm⟩ := hslice4 hf
  cases h5 : callW p n "nat_succ_lit" [r₄.tail.headD 0, r₄.tail.tail.headD 0] m₃ with
  | none => rw [h5] at hW; cases hW
  | some q₅ =>
  obtain ⟨r₅, m₅⟩ := q₅
  rw [h5] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  obtain ⟨hok5, hS5, hres5, hfr5, hhw5, hP5⟩ := callW_natSuccLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M' eb _ _
    hS3 hsl r₅ m₅ h5
  have hsome : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf]
  rw [hsome] at hrun4
  have hi := natAddArm_run_internE (u := pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) (v := 1) (by rw [AM.run_of_ok _ _ hok5, hres5])
  have hz := redSucc_run_some (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁ a₂ a₂ _
    s₀.mem hC.pins (decBool r₁) hsup hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) _ hrun4 _ hi
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M', hS5, hK3, (hStK1.trans hSt3).trans (StackKept.of_nat_frame hfr5 hP5)⟩
  · rw [hres']; simp only [decOptR, decOpt, ← hr0, ← hr1]; simp
  · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, hhw5⟩

end refs18

/-- **A slice below the old top survives a growth of the pool**: the slice, its value and its
normalisation. -/
theorem PoolGrew.slice {m m' : Mem} (hg : PoolGrew m m') {o l : Word} (hs : SliceOK m o l)
    (hn : Norm (vpool m) o.toNat l.toNat) :
    SliceOK m' o l ∧ pv (vpool m') o.toNat l.toNat = pv (vpool m) o.toNat l.toNat ∧
      Norm (vpool m') o.toNat l.toNat := by
  have hle := hs.le
  refine ⟨hs.poolGrew hg, Agree.pv _ _ _ _ _ hg.below hle, ?_⟩
  intro hpos
  have := hn hpos
  have hlt : o.toNat + (l.toNat - 1) < m.top.toNat := by omega
  rw [show (vpool m')[o.toNat + (l.toNat - 1)]? = (vpool m)[o.toNat + (l.toNat - 1)]? from
    hg.below _ hlt]
  exact this

theorem Grows.slice {m m' : Mem} (hg : Grows m m') {o l : Word} (hs : SliceOK m o l)
    (hn : Norm (vpool m) o.toNat l.toNat) :
    SliceOK m' o l ∧ L.Arena.pv (vpool m') o.toNat l.toNat = L.Arena.pv (vpool m) o.toNat l.toNat ∧
      Norm (vpool m') o.toNat l.toNat :=
  (PoolGrew.of_grows hg).slice hs hn

/-- `nat_op_result` refines `natOpResult` under `CoreS` (the `Nat` lane's: `PinsNatOp.lean`'s
`natOpResultL_refines`, at `ArenaD` and `CoreS`, in the whnf program). Taken as a hypothesis. -/
def NatOpResultOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb c oa la ob lb : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW c →
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    CoreSpec p n "nat_op_result" [c, oa, la, ob, lb]
      (natOpResult (decI c) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) decOptR s₀ a₀ dn vis fe MM eb (fun _ => True)

theorem hw_mask32 (y : Word) : HW (y &&& 4294967295) := and32_lt y

/-- `reduce_nat_op`'s normalised result reads as `nat_op_result`'s. -/
theorem decOpt_norm (x y : Word) :
    decOpt (Cmp.evalW .ne x 0) (BinOp.eval .and y 4294967295) = decOpt x y := by
  by_cases hx : x = 0
  · subst hx; simp [decOpt, Cmp.evalW, Cmp.eval]
  · simp [decOpt, Cmp.evalW, Cmp.eval, hx, BinOp.eval, decE_and32]

theorem resW_norm (x y : Word) : ResW [Cmp.evalW .ne x 0, BinOp.eval .and y 4294967295] := by
  refine ⟨?_, hw_mask32 y⟩
  unfold HW; simp only [List.headD_cons, Cmp.evalW]; split <;> decide

section refs19
variable (p : Prog)

theorem callW_reduceNatOp (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F)
    (hn2 : n ≤ 2 ^ 62) (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hc : HW c) (ha : HW a)
    (hb : HW b) (r : List Word) (m' : Mem)
    (h : callW p n "reduce_nat_op" [mode, vis, d, c, a, b] s₀.mem = some (r, m')) :
    CoreRef (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatOp_spec p hp.toWhnfDeltaProg n s₀ mode vis d c a b) h
  unfold reduceNatOpW at hW
  have hkn : KnotOK p n := hk n (by omega)
  -- first `whnf`
  cases h1 : callW p n "whnf" [mode, vis, d, a] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnf F s₀ a₀ dn vis fe MM eb mode d a (by omega) (by omega) hS ha) h1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₀ = a₁ at hrun1 hS₁
  cases h2 : callW p n "raw_nat_lit" [r₁.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hm2, hrun2, hres2, hslice2⟩ := callW_rawNatLit p hp n ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb _
    hS₁ hrw1 r₂ m₂ h2
  subst m₂
  by_cases hf2 : r₂.headD 0 = 0
  · rw [ite_eq_left hf2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : rawDec m₁ r₂ = none := by unfold rawDec; rw [ite_eq_left hf2]
    rw [hnone] at hrun2
    have hz := redOp_run_none1 (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b) a₀ a₁
      a₁ (decE (r₁.headD 0)) (by rw [hrun1]; rfl) hrun2
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₁, hS₁, hK₁, hSt₁⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right hf2] at hW
  obtain ⟨hsl2, hnorm2⟩ := hslice2 hf2
  have hsome2 : rawDec m₁ r₂ = some (pv (vpool m₁) (r₂.tail.headD 0).toNat
      (r₂.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf2]
  rw [hsome2] at hrun2
  -- second `whnf`
  cases h3 : callW p n "whnf" [mode, vis, d, b] m₁ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  have hSP₂ : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb) h3
  have hgrow : PoolGrew m₁ m₃ := hSt₃.pool
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₁ = a₂ at hrun3 hS₃
  cases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  dsimp only at hW
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
    hS₃ hrw3 r₄ m₄ h4
  subst m₄
  by_cases hf4 : r₄.headD 0 = 0
  · rw [ite_eq_left hf4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [ite_eq_left hf4]
    rw [hnone] at hrun4
    have hz := redOp_run_none2 (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b) a₀ a₁
      a₁ a₂ a₂ (decE (r₁.headD 0)) (decE (r₃.headD 0)) _ (by rw [hrun1]; rfl) hrun2
      (by rw [hrun3]; rfl) hrun4
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₃, hS₃, hK₁.trans hK₃, hSt₁.trans hSt₃⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right hf4] at hW
  obtain ⟨hsl4, hnorm4⟩ := hslice4 hf4
  have hsome4 : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf4]
  rw [hsome4] at hrun4
  obtain ⟨hsl2', hpv2, hnorm2'⟩ := hgrow.slice hsl2 hnorm2
  cases h5 : callW p n "nat_op_result" [c, r₂.tail.headD 0, r₂.tail.tail.headD 0, r₄.tail.headD 0,
      r₄.tail.tail.headD 0] m₃ with
  | none => rw [h5] at hW; cases hW
  | some q₅ =>
  obtain ⟨r₅, m₅⟩ := q₅
  rw [h5] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
    (hno n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb c _ _ _ _ hS₃ hc hsl2' hsl4 hnorm2' hnorm4) h5
  have hres5' := AM.run_of_ok _ _ hok5
  rw [hres5] at hres5'
  dsimp only at hres5' hS₅
  rw [hpv2] at hres5' hS₅
  have hz := redOp_run_some (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b) a₀ a₁
    a₁ a₂ a₂ (AM.st (natOpResult (decI c) (pv (vpool m₁) (r₂.tail.headD 0).toNat
      (r₂.tail.tail.headD 0).toNat) (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat)) a₂)
    (decE (r₁.headD 0)) (decE (r₃.headD 0))
    (pv (vpool m₁) (r₂.tail.headD 0).toNat (r₂.tail.tail.headD 0).toNat)
    (pv (vpool m₃) (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat)
    (decOptR r₅) (by rw [hrun1]; rfl) hrun2 (by rw [hrun3]; rfl) hrun4 hres5'
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M₅, hS₅, (hK₁.trans hK₃).trans hK₅, (hSt₁.trans hSt₃).trans hSt₅⟩
  · rw [hres']; simp only [decOptR, ← hr0, ← hr1, decOpt_norm]
  · have := resW_norm (r₅.headD 0) (r₅.tail.headD 0)
    unfold ResW at this ⊢; rw [← hr0, ← hr1]; exact this

end refs19

section refs20
variable (p : Prog)

theorem callW_reduceNatWf (hp : WhnfDeltaProg' p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (ha : HW a) (hb : HW b) (r : List Word) (m' : Mem)
    (h : callW p n "reduce_nat_wf" [mode, vis, d, c, a, b] s₀.mem = some (r, m')) :
    CoreRef (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)) a₀ decOptR
      dn s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatWf_spec p hp.toWhnfDeltaProg n s₀ mode vis d c a b) h
  unfold reduceNatWfW at hW
  have hkn : KnotOK p n := hk n (by omega)
  cases h1 : callW p n "nat_op_is_wf" [c] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨s₁', hs₁', hm₁, -, -, hwfsel, -⟩ := triple_of_callW
    (natOpIsWfL_spec p hp.natOpIsWf n ⟨s₀.mem, Locals.init []⟩ c) h1
  have hm1 : m₁ = s₀.mem := by rw [← hs₁', hm₁]
  subst hm1
  cases h2 : callW p n "nat_lit_supported" [vis] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok2, hS2, hres2, hfr2, hrh2⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₂ m₂ h2
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₂, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok2
    rw [hres2] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS2
  have hwf := natOpWfNames_run hC.pins
  have hcont := wfContains hC.pins c hc
  have hbool : ∀ (hh : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0), (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23),
      decI (pinW s₀.mem 24), decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27),
      decI (pinW s₀.mem 28), decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = true := by
    intro hh
    rw [hcont]
    have h1 : natOpWfSel (pinW s₀.mem) c = true := by rw [← hwfsel]; simpa using hh.1
    have h2 : decBool r₂ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hh.2
    rw [h1, h2]; rfl
  by_cases hgo : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  · rw [ite_eq_left hgo] at hW
    have hSP1 : SlotPre ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS2, hS.mode4, hS.eb_mode⟩
    cases h3 : callW p n "whnf" [mode, vis, d, a] m₂ with
    | none => rw [h3] at hW; cases hW
    | some q₃ =>
    obtain ⟨r₃, m₃⟩ := q₃
    rw [h3] at hW
    dsimp only at hW
    obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
      (hkn.whnf F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d a (by omega) (by omega) hSP1 ha) h3
    have hrun3 := AM.run_of_ok _ _ hok3
    rw [hres3] at hrun3
    generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₁ = a₂ at hrun3 hS₃
    cases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
    | none => rw [h4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [h4] at hW
    dsimp only at hW
    obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
      hS₃ hrw3 r₄ m₄ h4
    subst m₄
    by_cases hf4 : r₄.headD 0 = 0
    · rw [ite_eq_left hf4] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      rw [← hm]
      have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [ite_eq_left hf4]
      rw [hnone] at hrun4
      have hz := redWf_run_none1 (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)
        a₀ a₁ a₂ a₂ _ hwf (decBool r₂) hsup (hbool hgo) (decE (r₃.headD 0)) (by rw [hrun3]; rfl) hrun4
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
      refine ⟨hok', ?_, ?_, ?_⟩
      · rw [hst']; exact ⟨M₃, hS₃, hK₃, (StackKept.of_const_frame hfr2).trans hSt₃⟩
      · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
      · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
    rw [ite_eq_right hf4] at hW
    obtain ⟨hsl4, hnorm4⟩ := hslice4 hf4
    have hsome4 : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
        (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf4]
    rw [hsome4] at hrun4
    cases h5 : callW p n "whnf" [mode, vis, d, b] m₃ with
    | none => rw [h5] at hW; cases hW
    | some q₅ =>
    obtain ⟨r₅, m₅⟩ := q₅
    rw [h5] at hW
    dsimp only at hW
    have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode := ⟨hS₃, hS.mode4, hS.eb_mode⟩
    obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
      (hkn.whnf F ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode d b (by omega) (by omega) hSP3 hb) h5
    have hrun5 := AM.run_of_ok _ _ hok5
    rw [hres5] at hrun5
    generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₂ = a₃ at hrun5 hS₅
    cases h6 : callW p n "raw_nat_lit" [r₅.headD 0] m₅ with
    | none => rw [h6] at hW; cases hW
    | some q₆ =>
    obtain ⟨r₆, m₆⟩ := q₆
    rw [h6] at hW
    dsimp only at hW
    obtain ⟨hm6, hrun6, hres6, hslice6⟩ := callW_rawNatLit p hp n ⟨m₅, Locals.init []⟩ a₃ dn vis fe M₅ eb _
      hS₅ hrw5 r₆ m₆ h6
    subst m₆
    by_cases hf6 : r₆.headD 0 = 0
    · rw [ite_eq_left hf6] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      rw [← hm]
      have hnone : rawDec m₅ r₆ = none := by unfold rawDec; rw [ite_eq_left hf6]
      rw [hnone] at hrun6
      have hz := redWf_run_none2 (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)
        a₀ a₁ a₂ a₂ a₃ a₃ _ hwf (decBool r₂) hsup (hbool hgo) (decE (r₃.headD 0)) (decE (r₅.headD 0)) _
        (by rw [hrun3]; rfl) hrun4 (by rw [hrun5]; rfl) hrun6
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
      refine ⟨hok', ?_, ?_, ?_⟩
      · rw [hst']; exact ⟨M₅, hS₅, hK₃.trans hK₅, ((StackKept.of_const_frame hfr2).trans hSt₃).trans hSt₅⟩
      · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
      · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
    · rw [ite_eq_right hf6] at hW; cases hW
  · rw [ite_eq_right hgo] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hskip : (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23), decI (pinW s₀.mem 24),
        decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27), decI (pinW s₀.mem 28),
        decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = false := by
      rw [hcont]
      by_cases h1 : r₁.headD 0 = 0
      · have : natOpWfSel (pinW s₀.mem) c = false := by
          rw [← hwfsel, h1]; rfl
        rw [this]; rfl
      · have h2 : r₂.headD 0 = 0 := Classical.byContradiction fun h2 => hgo ⟨h1, h2⟩
        have : decBool r₂ = false := by simp only [decBool, h2]; rfl
        rw [this]; simp
    have hz := redWf_run_skip (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)
      a₀ a₁ _ hwf (decBool r₂) hsup hskip
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₂) ⟨hok', by rw [hst']; exact hS2, ?_, hfr2, ?_⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩

end refs20

end L.Arena
