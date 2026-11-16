module

public import ConAgua.Arena.WhnfCoreStep
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Verdict.WhnfModelsE
import ConAgua.Arena.RefWalk
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# The `whnf_core` loop and slot (phase 5, lane `whnf`; con-ron's #572 memo policy)

`whnf_core`'s unified model `whnfCoreE` is the loop: its iteration `whnfCoreE.loop1` refines
`whnfCoreLoop` from pending keys on the stack (`PendR`), both outcomes, iteration by iteration
through `whnf_core_step`'s (`step_ref`, both outcomes, over its unified model); the slot one level
up (`core_ref`) is the loop at `whnfCoreLoopFuel` from no pending keys (`knot_whnfCore_eq`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The dispatcher refines `whnfCoreStep` -/

/-- The views `whnfCoreStep` returns as they are. -/
def isDoneV : ENodeView → Bool
  | .sort _ | .fvar _ _ | .forallE _ _ | .lam _ _ | .const _ _ | .lit _ => true
  | _ => false

section stepRuns
variable {mode : ConLeche.CheckMode} {eager : Bool} {r : CoreFnsA} {fe : IFEnv} {cheap : Bool} {depth : Nat}
  {h e : EIdx} {a : AState}

theorem step_run_done (v : ENodeView) (hv : a.store.view e = some v) (hd : isDoneV v = true) :
    (whnfCoreStep mode r fe cheap depth h e).run a = .ok (.done e, a) := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v <;> simp [isDoneV] at hd <;> rfl

theorem step_run_app (f x : EIdx) (hv : a.store.view e = some (.app f x)) (hs : isStuckHead h = false) :
    (whnfCoreStep mode r fe cheap depth h e).run a = (whnfCoreStepApp mode r fe cheap depth e).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs]; try rfl

theorem step_run_stuck (f x : EIdx) (hv : a.store.view e = some (.app f x)) (hs : isStuckHead h = true) :
    (whnfCoreStep mode r fe cheap depth h e).run a = (whnfStuck mode r fe depth h e).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs]; try rfl

theorem step_run_proj (sn : NIdx) (i : Nat) (pe : EIdx) (hv : a.store.view e = some (.proj sn i pe)) :
    (whnfCoreStep mode r fe cheap depth h e).run a =
      (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_let (t v b : EIdx) (hv : a.store.view e = some (.letE t v b)) :
    (whnfCoreStep mode r fe cheap depth h e).run a =
      (do let e' ← instantiate1Fast coreWalkFuel b v 0; pure (WhnfStep.cont e') : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_bvar (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (whnfCoreStep mode r fe cheap depth h e).run a =
      (ConRon.Arena.fail (.notImplemented "whnf beyond the supported fragment") : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

end stepRuns

section step
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **`whnf_core_step` refines `whnfCoreStep`, both outcomes**: a bound variable declines (the
twin's `.bvar` arm); the `app` and `proj` arms' errors are `whnf_core_app`'s and
`whnf_core_step_proj`'s (`AppG`). -/
theorem step_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d h e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) (he : HW e) :
    RefE (AppG p n) (whnfCoreStepE p (n + 1) s₀.mem mode cheap vis d h e)
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
        (decE h) (decE e)) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  sorry

include hp hwc hcc in
/-- **`whnf_core_step` refines `whnfCoreStep`** (`step_ref`'s ok half). -/
theorem whnfCoreStep_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d h e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_step" [mode, cheap, vis, d, h, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
        (decE h) (decE e)) decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (whnfCoreStepE_spec p hp (n + 1) s₀ mode cheap vis d h e)
    (step_ref p hp hwc hcc n hk F hF hn s₀ a₀ dn vis fe MM eb mode cheap d h e hs hh he)

end step

/-- **`whnf_core_step`'s error claim** at every L fuel up to `n` (what the loop's errors claim
from; `step_ref`'s error half, `coreStepE_of`). -/
def CoreStepE (p : Prog) (n : Nat) : Prop :=
  ∀ j, j ≤ n → ∀ (F : Nat), j ≤ F → j ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d h e : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW h → HW e →
    CoreSpecE p (j + 1) "whnf_core_step" [mode, cheap, vis, d, h, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
        (decE h) (decE e)) s₀ a₀

/-! ## The pending keys -/

/-- **The loop's pending keys** at memory `m`: `pend` is the stack slice `SPN[pb, pb + pn)` right
below the top, `pendC` its suffix from `pc`. -/
structure PendR (m : Mem) (pb pn pc : Word) (pend pendC : Array EIdx) : Prop where
  slice : SpineR m pb pn pend
  pc_le : pc.toNat ≤ pn.toNat
  suffix : pend.extract pc.toNat pend.size = pendC
  top : spTop m = pb + pn

/-! ## The twin's loop, arm by arm -/

section twinLoop
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (depth K : Nat) (e : EIdx)
  (pend pendC : Array EIdx)

/-- The loop's step answer: the done arm stores the chain, the cont arm continues. -/
def loopS (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (depth K : Nat) (e : EIdx)
    (pend pendC : Array EIdx) (h : EIdx) : ConRon.Arena.WhnfStep → AM EIdx
  | .done v =>
    whnfCoreStoreChain cheap
      (pushKey (if cheap then false else whnfCoreStoresDone (whnfCoreKey h e) e v) e pend)
      (pushCheapKey (whnfCoreCheapSafe h e)
        (if cheap then false else whnfCoreStoresDone (whnfCoreKey h e) e v) e pendC) v >>= fun _ => pure v
  | .cont e' =>
    whnfCoreLoop mode r fe cheap depth K e'
      (pushKey (if cheap then false else whnfCoreKey h e) e pend)
      (pushCheapKey (whnfCoreCheapSafe h e) (if cheap then false else whnfCoreKey h e) e pendC)

/-- The loop past the lookup. -/
def loopO (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (depth K : Nat) (e : EIdx)
    (pend pendC : Array EIdx) (h : EIdx) : Option EIdx → AM EIdx
  | some x => whnfCoreStoreChain cheap pend #[] x >>= fun _ => pure x
  | none => whnfCoreStep mode r fe cheap depth h e >>= loopS mode r fe cheap depth K e pend pendC h

/-- The loop at a stuck tag: the chain stored, `e` answered. -/
theorem loop_stuck (ht : whnfCoreStuckTag e = true) :
    whnfCoreLoop mode r fe cheap depth (K + 1) e pend pendC =
      (whnfCoreStoreChain cheap pend pendC e >>= fun _ => pure e) := by
  rw [whnfCoreLoop]; simp only [ht, ite_true]

/-- The loop past the stuck test: the spine head, the lookup, `loopO`. -/
theorem loop_go (ht : whnfCoreStuckTag e = false) :
    whnfCoreLoop mode r fe cheap depth (K + 1) e pend pendC =
      (getAppFn coreWalkFuel e >>= fun h => whnfCoreLookupAt (whnfCoreKey h e) cheap e >>=
        loopO mode r fe cheap depth K e pend pendC h) := by
  rw [whnfCoreLoop]; simp only [ht, Bool.false_eq_true, ite_false]
  congr 1; funext h; congr 1; funext o
  cases o with
  | some x => rfl
  | none =>
    simp only [loopO]; congr 1; funext st
    cases st with
    | done v => cases cheap <;> simp [loopS]
    | cont e' => cases cheap <;> simp [loopS]

end twinLoop

/-! ## The loop's words and the pending keys -/

/-- The `stb` word's meaning. -/
theorem stb_iff (cheap kw st g rv e : Word) (hk : kw = 0 ∨ kw = 1) :
    ((if cheap = 0 then (1 : Word) else 0) &&& kw &&&
        (((if st ≠ 0 then (1 : Word) else 0) ||| if g ≠ 4 then (1 : Word) else 0) ||| if rv ≠ e then (1 : Word) else 0) ≠ 0) ↔
      (cheap = 0 ∧ kw = 1 ∧ (st ≠ 0 ∨ g ≠ 4 ∨ rv ≠ e)) := by
  rcases hk with rfl | rfl <;> by_cases h1 : cheap = 0 <;> by_cases h2 : st ≠ 0 <;> by_cases h3 : g ≠ 4 <;>
    by_cases h4 : rv ≠ e <;> simp_all

/-- What the loop keeps of the stack below the entry's top. -/
structure LoopInv (m₀ m : Mem) (pb : Word) : Prop where
  below : ∀ j : Word, j < pb → spW m j = spW m₀ j
  size : (m.arr64 SPN).size = (m₀.arr64 SPN).size
  bk : BKept m₀ m
  pg : PoolGrew m₀ m

theorem LoopInv.kept {m₀ m m' : Mem} {pb : Word} (h : LoopInv m₀ m pb) (hk : StackKept m m')
    (hle : pb ≤ spTop m) : LoopInv m₀ m' pb :=
  ⟨fun j hj => (hk.below j (UInt64.lt_of_lt_of_le hj hle)).trans (h.below j hj), hk.size.trans h.size,
    h.bk.trans hk.bstk, h.pg.trans hk.pool⟩

/-- The pending keys survive a run that kept the stack below the top. -/
theorem PendR.kept {m m' : Mem} {pb pn pc : Word} {pend pendC : Array EIdx} (h : PendR m pb pn pc pend pendC)
    (hk : StackKept m m') (hspn : (m.arr64 SPN).size < 2 ^ 63) : PendR m' pb pn pc pend pendC := by
  have hb := h.slice.bound
  refine ⟨h.slice.keep hk.size hk.below ?_ hspn, h.pc_le, h.suffix, hk.top.trans h.top⟩
  rw [h.top, L.toNat_add_of_lt _ _ (by omega)]; exact Nat.le_refl _

/-- The cheap keys emptied (`pushCheapKey` past an unsafe step). -/
theorem PendR.reset {m : Mem} {pb pn pc : Word} {pend pendC : Array EIdx} (h : PendR m pb pn pc pend pendC) :
    PendR m pb pn pn pend #[] :=
  ⟨h.slice, Nat.le_refl _, by rw [h.slice.size]; simp; omega, h.top⟩


/-- The push's capacity check passed: room on the stack, and the top's word exists. -/
theorem push_room {m : Mem} {pb pn : Word} (hspn : (m.arr64 SPN).size < 2 ^ 63)
    (hroom : ¬ (m.len64 SPN ≤ pb + pn ∨ m.len64 CTL ≤ 136)) (hpn : pb.toNat + pn.toNat < 2 ^ 63) :
    pb.toNat + pn.toNat < (m.arr64 SPN).size ∧ (136 : Word).toNat < (m.arr64 CTL).size := by
  simp only [not_or, UInt64.not_le] at hroom
  obtain ⟨h1, h2⟩ := hroom
  constructor
  · rw [UInt64.lt_iff_toNat_lt, L.toNat_add_of_lt _ _ (by omega)] at h1
    simp only [L.Mem.len64, UInt64.toNat_ofNat'] at h1
    rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
  · rw [UInt64.lt_iff_toNat_lt] at h2
    simp only [L.Mem.len64, UInt64.toNat_ofNat'] at h2
    have := Nat.mod_le (m.arr64 CTL).size (2 ^ 64)
    show 136 < _; have : (136 : Word).toNat = 136 := rfl; omega

/-- The pending keys past a push of `e` (the cheap keys keep their start). -/
theorem PendR.push {m : Mem} {pb pn pc : Word} {pend pendC : Array EIdx} (h : PendR m pb pn pc pend pendC)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) (hroom : ¬ (m.len64 SPN ≤ pb + pn ∨ m.len64 CTL ≤ 136))
    (e : Word) (he : HW e) :
    PendR ((m.set64 SPN (pb + pn) e).set64 CTL 136 (pb + (pn + 1))) pb (pn + 1) pc (pend.push (decE e))
      (pendC.push (decE e)) := by
  have hb := h.slice.bound
  obtain ⟨hr1, hr2⟩ := push_room hspn hroom (by omega)
  have hn1 : (pn + 1).toNat = pn.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨(h.slice.push hspn hr1 e he).setCtl 136 _, by rw [hn1]; have := h.pc_le; omega, ?_, ?_⟩
  · rw [← h.suffix]; have := h.pc_le; have := h.slice.size
    apply Array.toList_inj.mp; simp [Array.toList_extract, List.extract]
    rw [List.drop_append_of_le_length (by simp; omega)]
    rw [List.take_of_length_le (by simp; omega)]
    rw [List.take_of_length_le (l := List.drop _ _) (by simp)]
  · unfold spTop
    rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [L.Mem.size64_set64]; exact hr2⟩]

/-- **A chain's end**: the answer `x`, the top put back to the entry's. -/
theorem fin_post {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {a₁ : AState} {vis : Word} {fe : IFEnv}
    {MM₀ M₁ : ModeMaps} {eb pb x : Word} {y : EIdx} (hS : CoreS dn m₁ a₁ vis fe M₁ eb)
    (hK : KeptAll MM₀ M₁ eb) (hI : LoopInv m₀ m₁ pb) (htop₀ : spTop m₀ = pb) (hle : pb ≤ spTop m₁)
    (hx : HW x) (hy : y = decE x) :
    CorePost decH dn m₀ vis fe MM₀ eb ResH ([x], m₁.set64 CTL 136 pb) y a₁ := by
  subst htop₀
  exact ⟨⟨M₁, hS.frame_stk (MemFrame.setCtl m₁ 136 _) (by simp) (by simp), hK,
    StackKept.restoreTop hI.below hle hI.size hI.bk hI.pg⟩, hy, hx⟩


/-- Handle equality off the words. -/
theorem decE_beq_w (v e : Word) (hv : HW v) (he : HW e) : (decE v == decE e) = decide (v = e) := by
  rw [← evalW_eq_ne v e hv he]; by_cases h : v = e <;> simp [Cmp.evalW, Cmp.eval, h]

/-- The loop's `stb` word is the twin's store decision (`whnfCoreStoresDone` at a done step,
the key at a continued one; nothing in the cheap mode). -/
theorem stb_twin (cheap kw st rv e : Word) (hk : kw = 0 ∨ kw = 1) (hrv : HW rv) (he : HW e) :
    (if (cheap != 0) = true then false
      else if st = 0 then whnfCoreStoresDone (kw != 0) (decE e) (decE rv) else (kw != 0)) =
    decide ((if cheap = 0 then (1 : Word) else 0) &&& kw &&&
        (((if st ≠ 0 then (1 : Word) else 0) ||| if tagW e ≠ 4 then (1 : Word) else 0) |||
          if rv ≠ e then (1 : Word) else 0) ≠ 0) := by
  have ht : ((decE e).tag == ETag.app) = decide (tagW e = 4) := decE_tag_beq e he 4 (by decide)
  rw [Bool.eq_iff_iff, decide_eq_true_iff, stb_iff cheap kw st (tagW e) rv e hk]
  simp only [whnfCoreStoresDone, ht, decE_beq_w rv e hrv he]
  rcases hk with rfl | rfl <;> by_cases h1 : cheap = 0 <;> by_cases h2 : st = 0 <;>
    by_cases h3 : tagW e = 4 <;> by_cases h4 : rv = e <;> simp_all


section loopRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **The loop refines `whnfCoreLoop`, both outcomes**, at every twin loop fuel `K ≥ k`, from
pending keys `pend`/`pendC` (`PendR`) above the entry's top `pb`: each iteration is
`whnf_core_step`'s (`whnfCoreStep_refines'`, its error claim `CoreStepE`). -/
@[refines ConRon.Arena.whnfCoreLoop]
theorem coreLoop_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode cheap d pb : Word)
    (hmode : mode < 4) (m₀ : Mem) (MM₀ : ModeMaps) (eb : Word) (heb : eb = (mode >>> 1) &&& 1)
    (htop₀ : spTop m₀ = pb) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (e pn pc : Word)
      (pend pendC : Array EIdx),
      CoreS dn m a vis fe MM eb → KeptAll MM₀ MM eb → HW e → PendR m pb pn pc pend pendC →
      LoopInv m₀ m pb →
      RefE (CoreStepE p n) (whnfCoreE.loop1 p k m mode cheap vis d e pb pn pc)
        (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0)
          d.toNat K (decE e) pend pendC) a
        (CorePost decH dn m₀ vis fe MM₀ eb ResH) := by
  intro k
  induction k with
  | zero => intros; simp only [whnfCoreE.loop1]; exact RefE.of_cls0 rfl
  | succ k ih =>
  intro hkn K hK m a MM e pn pc pend pendC hS hKA he hP hI
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [whnfCoreE.loop1]
  rw [ite_eq_left trivial]
  cases k with
  | zero =>
    split
    · simp only [whnfCoreStoreChainE]; exact RefE.of_cls0 rfl
    · rw [callW_zero, liftE_none, whnfCoreE.k_get_app_fn.none]; exact RefE.of_cls0 (by simp)
  | succ j =>
  have hspn := hS.spn
  have hbd := hP.slice.bound
  have hpbn : (pb + pn).toNat = pb.toNat + pn.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hle : pb ≤ spTop m := by rw [hP.top, UInt64.le_iff_toNat_le, hpbn]; omega
  by_cases hst : (657 : Word) >>> tagW e &&& 1 = 0
  · rw [ite_eq_left hst]
    have ht : whnfCoreStuckTag (decE e) = true := by rw [stuckTag_w e he]; simp [hst]
    rw [loop_stuck _ _ _ _ _ _ _ _ _ ht]
    refine RefE.bindE (fun _ => whnfCoreE.k_whnf_core_store_chain.none ..) id
      (storeChain_ref p hp (CoreStepE p n) j dn vis fe mode cheap pb pn pc e pend pendC m a MM eb heb he hS
        hP.slice hP.pc_le hP.suffix (by rw [← hpbn, ← hP.top]; exact Nat.le_refl _)) fun ⟨r₁, m₁⟩ y a₁ _ hQ => ?_
    obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := hQ.after
    rw [whnfCoreE.k_whnf_core_store_chain.arm1]
    exact RefE.ret rfl (fin_post hS₁ (hKA.trans hK₁) (hI.kept hSt₁ hle) htop₀ (hSt₁.top ▸ hle) he rfl)
  rw [ite_eq_right hst]
  have ht : whnfCoreStuckTag (decE e) = false := by rw [stuckTag_w e he]; simp [hst]
  rw [loop_go _ _ _ _ _ _ _ _ _ ht]
  refine RefE.onlySim (K := whnfCoreE.k_get_app_fn p (j + 1) mode cheap vis d e pb pn pc (tagW e))
    (fun _ => whnfCoreE.k_get_app_fn.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨t₁, ht₁, hm₁, -, hhw, hrun1⟩ := triple_of_callW
    (getAppFn_refines p hp.spine (j + 1) ⟨m, Locals.init []⟩ a hS.arena.base e he) h1
  have hm1 : m₁ = m := by rw [← ht₁]; exact hm₁
  rw [hm1]
  rw [whnfCoreE.k_get_app_fn.arm1]
  refine RefE.bind_right hrun1 ?_
  generalize r₁.headD 0 = h at hhw ⊢
  rw [key_w h e hhw he]
  have hkw01 := key01 h e hhw he
  generalize hkw : ((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&&
    (1 - ((334 : Word) >>> tagW h &&& 1))) = kw at hkw01 ⊢
  refine RefE.bindE (fun _ => whnfCoreE.k_whnf_core_lookup_at.none ..) id
    (lookup_ref p hp (CoreStepE p n) j m a dn vis fe MM eb mode kw cheap e hS heb he)
    fun ⟨r₂, m₂⟩ o a₂ hrun2 hQ => ?_
  obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := hQ.after
  have hI₂ := hI.kept hSt₂ hle
  have hP₂ := hP.kept hSt₂ hspn
  have hle₂ : pb ≤ spTop m₂ := hSt₂.top ▸ hle
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hS₂.spn
  by_cases hf : r₂.headD 0 ≠ 0
  · -- a hit: the chain stored, the entry answered
    rw [whnfCoreE.k_whnf_core_lookup_at.arm1 (hc1 := hf)]
    have ho : o = some (decE (r₂.tail.headD 0)) := by rw [hQ.res]; simp only [decOptR, decOpt, hf, ite_false]
    subst ho
    simp only [loopO]
    have hbd₂ := hP₂.slice.bound
    refine RefE.bindE (fun _ => whnfCoreE.k_whnf_core_store_chain_2.none ..) id
      (storeChain_ref p hp (CoreStepE p n) j dn vis fe mode cheap pb pn pn _ pend #[] m₂ a₂ M₂ eb heb
        hQ.valid.2 hS₂ hP₂.slice (Nat.le_refl _) (by rw [hP₂.slice.size]; simp; omega)
        (by rw [← hpbn, ← hP₂.top]; exact Nat.le_refl _)) fun ⟨r₃, m₃⟩ y a₃ _ hQ₃ => ?_
    obtain ⟨M₃, hS₃, hK₃, hSt₃⟩ := hQ₃.after
    rw [whnfCoreE.k_whnf_core_store_chain_2.arm1]
    exact RefE.ret rfl (fin_post hS₃ ((hKA.trans hK₂).trans hK₃) (hI₂.kept hSt₃ hle₂) htop₀
      (hSt₃.top ▸ hle₂) hQ.valid.2 rfl)
  have hf : r₂.headD 0 = 0 := Classical.not_not.mp hf
  rw [whnfCoreE.k_whnf_core_lookup_at.arm2 (hc1 := hf)]
  have ho : o = none := by rw [hQ.res]; simp only [decOptR, decOpt, hf, ite_true]
  subst ho
  simp only [loopO]
  have hsw01 := safe_w h e hhw he
  generalize hsw : ((128 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&&
    (((334 : Word) >>> tagW h &&& 1) ||| (if tagW h = 5 then (1 : Word) else 0))) = sw at hsw01 ⊢
  have hkey := key_w h e hhw he
  rw [hkw] at hkey
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => whnfCoreE.k_whnf_core_step.none ..)
    (whnfCoreStep_refines' p hp hwc hcc j (hk.mono (by omega)) F (by omega) (by omega) _ a₂ dn vis fe M₂ eb
      mode cheap d h e ⟨hS₂, hmode, heb⟩ hhw he)
    (fun hG => hG j (by omega) F (by omega) (by omega) _ a₂ dn vis fe M₂ eb mode cheap d h e
      ⟨hS₂, hmode, heb⟩ hhw he) fun r₃ m₃ _ hR3 => ?_
  obtain ⟨-, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, hrw3⟩ := hR3
  generalize AM.st (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe
    (cheap != 0) d.toNat (decE h) (decE e)) a₂ = a₃ at hS₃ ⊢
  have hI₃ := hI₂.kept hSt₃ hle₂
  have hP₃ := hP₂.kept hSt₃ hspn₂
  have hle₃ : pb ≤ spTop m₃ := hSt₃.top ▸ hle₂
  have hspn₃ : (m₃.arr64 SPN).size < 2 ^ 63 := hS₃.spn
  have hK₃' := (hKA.trans hK₂).trans hK₃
  -- the rest of the iteration, from the pending keys past the push
  have tail : ∀ (m' : Mem) (pn' pc' : Word),
      CoreS dn m' a₃ vis fe M₃ eb → LoopInv m₀ m' pb →
      PendR m' pb pn' pc'
        (pushKey (if (cheap != 0) = true then false
          else if r₃.headD 0 = 0 then whnfCoreStoresDone (kw != 0) (decE e) (decE (r₃.tail.headD 0))
          else (kw != 0)) (decE e) pend)
        (pushCheapKey (sw != 0) (if (cheap != 0) = true then false
          else if r₃.headD 0 = 0 then whnfCoreStoresDone (kw != 0) (decE e) (decE (r₃.tail.headD 0))
          else (kw != 0)) (decE e) pendC) →
      RefE (CoreStepE p n) (whnfCoreE.j2 p (j + 1) mode cheap vis d pb pn' pc' (r₃.headD 0) (r₃.tail.headD 0) m')
        (loopS (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat K'
          (decE e) pend pendC (decE h) (decStep r₃)) a₃ (CorePost decH dn m₀ vis fe MM₀ eb ResH) := by
    intro m' pn' pc' hS' hI' hP'
    have hle' : pb ≤ spTop m' := by
      rw [hP'.top, UInt64.le_iff_toNat_le, L.toNat_add_of_lt _ _ (by have := hP'.slice.bound; have := hS'.spn; omega)]
      omega
    by_cases hs0 : r₃.headD 0 = 0
    · rw [whnfCoreE.j2.arm1 (hc1 := hs0)]
      simp only [hs0, ite_true] at hP'
      simp only [decStep, hs0, ite_true, loopS, hkey, hsw01]
      refine RefE.bindE (fun _ => whnfCoreE.k_whnf_core_store_chain_3.none ..) id
        (storeChain_ref p hp (CoreStepE p n) j dn vis fe mode cheap pb pn' pc' _ _ _ m' a₃ M₃ eb heb hrw3.2 hS'
          hP'.slice hP'.pc_le hP'.suffix (by
            rw [hP'.top, L.toNat_add_of_lt _ _ (by have := hP'.slice.bound; have := hS'.spn; omega)]; exact Nat.le_refl _)) fun ⟨r₄, m₄⟩ y a₄ _ hQ₄ => ?_
      obtain ⟨M₄, hS₄, hK₄, hSt₄⟩ := hQ₄.after
      rw [whnfCoreE.k_whnf_core_store_chain_3.arm1]
      exact RefE.ret rfl (fin_post hS₄ (hK₃'.trans hK₄) (hI'.kept hSt₄ hle') htop₀ (hSt₄.top ▸ hle')
        hrw3.2 rfl)
    · rw [whnfCoreE.j2.arm2 (hc1 := hs0)]
      simp only [hs0, ite_false] at hP'
      simp only [decStep, hs0, ite_false, loopS, hkey, hsw01]
      exact ih (by omega) K' (by omega) m' a₃ M₃ _ pn' pc' _ _ hS' hK₃' hrw3.2 hP' hI'
  have hstb := stb_twin cheap kw (r₃.headD 0) (r₃.tail.headD 0) e hkw01 hrw3.2 he
  rw [hstb] at tail
  by_cases hsb : ((if cheap = 0 then (1 : Word) else 0) &&& kw &&&
      (((if r₃.headD 0 ≠ 0 then (1 : Word) else 0) ||| if tagW e ≠ 4 then (1 : Word) else 0) |||
        if r₃.tail.headD 0 ≠ e then (1 : Word) else 0)) ≠ 0
  · by_cases hroom : m₃.len64 SPN ≤ pb + pn ∨ m₃.len64 CTL ≤ 136
    · rw [whnfCoreE.k_whnf_core_step.abort1 (hc1 := hsb) (hc2 := hroom)]; exact RefE.of_cls0 rfl
    rw [whnfCoreE.k_whnf_core_step.arm1 (hc1 := hsb) (hc2 := hroom)]
    rw [decide_eq_true hsb] at tail
    simp only [pushKey, ite_true, pushCheapKey] at tail
    have hP₄ := hP₃.push hspn₃ hroom e he
    have hbd₃ := hP₃.slice.bound
    obtain ⟨hr1, hr2⟩ := push_room hspn₃ hroom (by omega)
    have hfr := spnCtl_frame m₃ (pb + pn) e (pb + (pn + 1))
    have hS₄ := hS₃.frame_stk hfr (by simp) (by simp)
    have hI₄ : LoopInv m₀ ((m₃.set64 SPN (pb + pn) e).set64 CTL 136 (pb + (pn + 1))) pb :=
      ⟨fun i hi => by
        rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
          have := UInt64.lt_iff_toNat_lt.mp hi
          rw [← h, hpbn] at this; omega)]
        exact hI₃.below i hi,
       by simp only [L.Mem.size64_set64]; exact hI₃.size,
       hI₃.bk.trans (BKept.of_frame hfr (by decide) (by decide)),
       hI₃.pg.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩
    by_cases hs : sw = 0
    · rw [whnfCoreE.j1.arm1 (hc1 := hs)]
      simp only [hs, bne_self_eq_false, Bool.false_eq_true, ite_false] at tail
      exact tail _ _ _ hS₄ hI₄ hP₄.reset
    · rw [whnfCoreE.j1.arm2 (hc1 := hs)]
      simp only [hs, bne_iff_ne, ne_eq, not_false_eq_true, ite_true] at tail
      exact tail _ _ _ hS₄ hI₄ hP₄
  · rw [whnfCoreE.k_whnf_core_step.arm2 (hc1 := Classical.not_not.mp hsb)]
    rw [decide_eq_false hsb] at tail
    simp only [pushKey, Bool.false_eq_true, ite_false, pushCheapKey] at tail
    by_cases hs : sw = 0
    · rw [whnfCoreE.j1.arm1 (hc1 := hs)]
      simp only [hs, bne_self_eq_false, Bool.false_eq_true, ite_false] at tail
      exact tail _ _ _ hS₃ hI₃ hP₃.reset
    · rw [whnfCoreE.j1.arm2 (hc1 := hs)]
      simp only [hs, bne_iff_ne, ne_eq, not_false_eq_true, ite_true] at tail
      exact tail _ _ _ hS₃ hI₃ hP₃

end loopRef

/-! ## The slot: the loop at `whnfCoreLoopFuel`, no pending keys -/

/-- **The knot's `whnfCore` slot is the body** one level down (con-ron's #572: no stuck-tag test,
no memo in the slot). -/
theorem knot_whnfCore_eq (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (F : Nat) (c : Bool)
    (d : Nat) (e : EIdx) :
    (coreKnot mode eager fe id (F + 1)).whnfCore c d e =
      whnfCoreLoop mode (coreKnot mode eager fe id F) fe c d whnfCoreLoopFuel e #[] #[] := by
  simp only [coreKnot, whnfCoreBody, id]

section slot
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **`whnf_core` at `n + 1` refines the knot's `whnfCore` slot of `coreKnot mode eager fe id F`, both
outcomes**, `F ≥ n + 1`: the loop from no pending keys at the entry's top (`coreLoop_ref`). The
errors are the step's (`CoreStepE`). -/
theorem core_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (CoreStepE p n) (whnfCoreE p (n + 1) s₀.mem mode cheap vis d e)
      ((coreKnot (decMode mode) (decEager mode) fe id F).whnfCore (cheap != 0) d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hS := hs.rel
  have hspn := hS.spn
  by_cases hab : s₀.mem.len64 SPN < rdW (s₀.mem.arr64 CTL) 136
  · rw [whnfCoreE.abort1 (hc1 := hab)]; exact RefE.of_cls0 rfl
  rw [whnfCoreE.arm1 (hc1 := hab), knot_whnfCore_eq]
  have hpb : (spTop s₀.mem).toNat ≤ (s₀.mem.arr64 SPN).size := by
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at hab
    simp only [L.Mem.len64, UInt64.toNat_ofNat'] at hab
    rw [Nat.mod_eq_of_lt (by omega)] at hab; exact hab
  exact coreLoop_ref p hp hwc hcc n hk F' (by omega) (by omega) dn vis fe mode cheap d
    (spTop s₀.mem) hs.mode4 s₀.mem MM eb hs.eb_mode rfl (n + 1) (Nat.le_refl _) ConRon.Arena.whnfCoreLoopFuel
    (by simp only [ConRon.Arena.whnfCoreLoopFuel]; omega) s₀.mem a₀ MM e 0 0 #[] #[] hS (KeptAll.refl _ _) he
    ⟨⟨rfl, by simpa using hpb, fun _ h => by simp at h, fun _ h => by simp at h⟩, Nat.le_refl _,
      by simp, by simp⟩
    ⟨fun _ _ => rfl, rfl, BKept.refl _, PoolGrew.refl _⟩


include hp hwc hcc in
/-- **The knot's `whnfCore` slot, one level up** (`core_ref`'s ok half): given the knot at every
fuel up to `n` (for the body's callees), `whnf_core` at `n + 1` refines the slot. Over the bundles
`WhnfCallees` and `CoreCallees` (`DefEqKnot.lean` builds them from real proofs). -/
theorem whnfCoreSlot_step (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he =>
    RefE.coreSpec (whnfCoreE_spec p hp (n + 1) s₀ mode cheap vis d e)
      (core_ref p hp hwc hcc n hk F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he)

end slot

end L.Arena
