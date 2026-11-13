module

import ConAgua.Arena.WhnfDeltaRefine2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.WhnfDeltaRefine
import all ConAgua.Arena.Refine
import all ConAgua.Arena.WhnfDelta

@[expose] public section

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 3 (`nat_succ_lit`, `reduce_nat`'s arms)

Split from `WhnfDeltaRefine.lean`. The twin's binary arm and the runs; the arms' refinements, for
both outcomes, are `Verdict/WhnfNatE.lean`'s.
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
  have hps := hA.base.lit.1.cap
  have htop := hA.base.lit.1.top
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨h1, h2, h3⟩ := internLit_D s.mem a₀ hA o l _ hq hn hq0 _ hI
  exact ⟨hloc, h1, h2, h3, internW_hw s.mem a₀ hA.base.lit o l _ _ hI⟩


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
  (hz : p.lookup "size_bytes" = some sizeBytesL)
  (hsr : p.lookup "nat_size_refused" = some natSizeRefusedL)
  (hls : p.lookup "lit_nat_sized" = some litNatSizedL)

include hpl hpc hpt hpa hpn hpool hgrow hI hg hz hsr hls in
/-- **`nat_succ_lit` refines the `Nat.add` arm at the literal `1`** (`litNatSized (n + 1)`): a
handle word, or the size refusal's sentinel (`NatRes`). -/
theorem natSuccLit_refines_hw (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize)
    (oa la : Word) (ha : SliceOK s₀.mem oa la) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_succ_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat) 1) a₀ (r.headD 0) s'.mem; ⊤⦄ := by
  have hI' : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
      SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
      (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
      ⦃fun s => s = s₀⦄
      invoke p (exec p n) "intern_lit" [o, l]
      ⦃fun r s' => LocEq s' s₀ ∧
        AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
        R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
        AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
          decE (r.headD 0); ⊤⦄ := fun a₀ n s₀ o l h1 h2 h3 h4 => by
    apply L.M.triple_of_run
    intro s r s' hs hrun
    obtain ⟨e1, e2, e3, e4, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun (hI a₀ n s₀ o l h1 h2 h3 h4)
    exact ⟨e1, e2, e3, e4⟩
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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        fun s => natAddLit_refines p hpl hpc hpt hpa hpn R hpool hgrow hI' hz hsr hls n s a₀] <;>
      finish (gen := 20) [natAddArm]

end succ

theorem keeps_cpl_natAddArm (a b : Nat) : Keeps cpl (natAddArm a b) := by
  unfold Keeps; intro a' r a'' h
  rw [natAddArm, litNatSized_run] at h
  split at h
  · cases h
  · exact Keeps.run (Keeps.bind (keeps_cpl_internLit _) (fun _ => Keeps.pure _)) h

theorem natAddArm_run_internE {a₁ a₂ : AState} {x : EIdx} {u v : Nat}
    (h : (natAddArm u v).run a₁ = .ok (some x, a₂)) :
    (internE (.lit (.natVal (u + v)))).run a₁ = .ok (x, a₂) := by
  rw [natAddArm, litNatSized_run] at h
  split at h
  · cases h
  have e : (do let x ← internE (.lit (.natVal (u + v))); pure (some x) : AM (Option EIdx)).run a₁ =
      Except.map (fun q => (some q.1, q.2)) ((internE (.lit (.natVal (u + v)))).run a₁) := by
    simp only [StateT.run_bind]
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

/-- **`nat_succ_lit` as a run**: a handle word (the arm's `some`) or the size refusal. -/
theorem callW_natSuccLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt) (r : List Word) (m' : Mem)
    (h : callW p n "nat_succ_lit" [o, cnt] s₀.mem = some (r, m')) :
    ((r.headD 0).toNat < 2 ^ 63 →
      AM.ok (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1) a₀ ∧
      CoreS dn m' (AM.st (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1) a₀) vis fe MM eb ∧
      AM.res (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1) a₀ = some (decE (r.headD 0)) ∧
      HW (r.headD 0) ∧ PoolGrew s₀.mem m') ∧
    (2 ^ 63 ≤ (r.headD 0).toNat →
      (natAddArm (pv (vpool s₀.mem) o.toNat cnt.toNat) 1).run a₀ = .error (natRefusal (r.headD 0))) ∧
    MemFrame natA natC s₀.mem m' := by
  have hag := hp.natAgree
  obtain ⟨s', rfl, -, hN⟩ := triple_of_callW
    (natSuccLit_refines_hw p hp.natLimb' hp.addCarry' hp.natTrim' hp.natAdd'
      ((hag "nat_add_lit" (by decide)).trans rfl)
      (fun m a => ArenaD m a ∧ PoolGrew s₀.mem m)
      (fun _ _ h => h.1.1.lit.1)
      (fun m m' a hA hg => ⟨ArenaD.grow m m' hg a hA.1, hA.2.trans (PoolGrew.of_grows hg)⟩)
      (natSuccLit_instP p hp s₀.mem) hp.natSuccLit ((hag "size_bytes" (by decide)).trans rfl)
      ((hag "nat_size_refused" (by decide)).trans rfl) ((hag "lit_nat_sized" (by decide)).trans rfl)
      n s₀ a₀ ⟨hC.arena, PoolGrew.refl _⟩ hC.pins.maxNatSize.symm o cnt hs hC.mode) h
  have hfr := callW_natFrame p hp.natClosed "nat_succ_lit" (by decide +kernel) n _ _ _ _ h
  refine ⟨fun hlt => ?_, hN.2, hfr⟩
  obtain ⟨hok, ⟨hD, hP⟩, hres, h32⟩ := hN.1 hlt
  have hrunI := natAddArm_run_internE (by rw [AM.run_of_ok _ _ hok, hres])
  exact ⟨hok, hC.of_nat hD (Keeps.run (keeps_cpl_natAddArm _ _) (AM.run_of_ok _ _ hok)) hfr
    (internNodeE_views (v := .lit _) (by rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h)
      (by simpa [internE] using hrunI)) hP, hres, h32, hP⟩

end refs17

/-! ## `reduce_nat`: the binary operation's arm -/

/-- The binary operation arm of `reduceNat`, once the operation `op` is found. -/
def redOpT (r : CoreFnsA) (depth : Nat) (op : NatBinOp) (a b : EIdx) : AM (Option EIdx) := do
  match ← rawNatLit? (← r.whnf depth a) with
  | some n₁ => do
    match ← rawNatLit? (← r.whnf depth b) with
    | some n₂ => natBinOpResult op n₁ n₂
    | none => pure none
  | none => pure none

theorem pinW_const_frame {m m' : Mem} (hf : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m') (k : Nat) :
    pinW m' k = pinW m k := by
  have : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS (by simp [tier1, CREC, CSLOT, CLP, PINS]) (by decide)
  simp only [pinW, this]

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

/-- `nat_bin_op_result` refines `natBinOpResult` under `CoreS` (`PinsNatOp.lean`'s
`natBinOpResultL_refines`, at `CoreS`, in the whnf program; `CoreNatOp.lean`). Taken as a
hypothesis. -/
def NatOpResultOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb : Word) (op : NatBinOp) (oa la ob lb : Word), CoreS dn s₀.mem a₀ vis fe MM eb →
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_bin_op_result" [natBinOpW op, oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      (r.headD 0 ≠ 2 → CoreRef (natBinOpResult op (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ decOptR dn s₀.mem vis fe MM eb r s'.mem
        (fun _ => True)) ∧
      (r.headD 0 = 2 → (natBinOpResult op (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)).run a₀ = .error (natRefusal (r.tail.headD 0))); ⊤⦄

/-- `reduce_nat_op`'s normalised result reads as `nat_bin_op_result`'s. -/
theorem decOpt_norm (x y : Word) :
    decOpt (if x ≠ 0 then 1 else 0) (y &&& 4294967295) = decOpt x y := by
  by_cases hx : x = 0
  · subst hx; simp [decOpt]
  · simp [decOpt, hx, decE_mask]

theorem resW_norm (x y : Word) : ResW [if x ≠ 0 then 1 else 0, y &&& 4294967295] := by
  refine ⟨?_, mask_lt y⟩
  unfold HW; simp only [List.headD_cons]; split <;> decide

end L.Arena
