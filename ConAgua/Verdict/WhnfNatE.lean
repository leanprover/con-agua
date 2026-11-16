module

public import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.CoreNatOp
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfDeltaRefine2
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.KnotE
public import ConAgua.Arena.RefECore
public import ConAgua.Verdict.WhnfModels2E

@[expose] public section
/-!
# `reduce_nat`'s family: one model and one refinement for both outcomes

`reduceNatSuccE` … `reduceNatE` (`l_model … unified`, `WhnfModels2E`): the `whnf` slot through its
run (`callE`), the family's own callees through their unified models, every other callee (outside
the verdict closure) through its `Option` model. Each `…_ref` refines the twin's arm for both
outcomes (`RefE` with `CorePost`): the errors claim the twin's failures under the `whnf` slot's
claims (`KnotUpToE`). The ok
halves are `ReduceNatSpec'` (`reduceNat_refines`), the error half `ReduceNatE` (`reduceNatE_of`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem resW_zero : ResW [0, 0] := by unfold ResW HW; exact ⟨by decide, by decide⟩

/-- The callee's first two result words, after a run of constant frame (the caller's result). -/
theorem CorePost.relist {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv}
    {MM : ModeMaps} {eb : Word}
    (hfr : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m₀ m₁)
    (v : List Word × Mem) (y : Option EIdx) (a' : AState)
    (h : CorePost decOptR dn m₁ vis fe MM eb ResW v y a') :
    CorePost decOptR dn m₀ vis fe MM eb ResW ([v.1.headD 0, v.1.tail.headD 0], v.2) y a' :=
  ⟨CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr) h.after, h.res, h.valid⟩

/-! ## `reduceNat`'s arms at the new twin

con-ron's `reduceNat` (`ConRon/Arena/Core.lean`) split at the L code's functions: the successor
arm (`redSuccS`), the application arm (`redAppS`: the operation found once, `natBinOpOfName?`,
then `WhnfDeltaRefine3`'s `redOpT`). -/

/-- The successor arm of `reduceNat`. -/
def redSuccS (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let ns ← pinNatSucc
  if c == ns && fe.natLit then do
    match ← rawNatLit? (← r.whnf depth b) with
    | some n => litNatSized (n + 1)
    | none => pure none
  else pure none

/-- The `.const c us` arm of `reduceNat`'s `match ← view f`. -/
def redConstS (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us : LsIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let el ← emptyLevels
  if us != el then pure none else redSuccS r fe depth c b

/-- The `.app g a` arm of `reduceNat`'s `match ← view f`. -/
def redAppS (r : CoreFnsA) (depth : Nat) (g a b : EIdx) : AM (Option EIdx) := do
  if g.tag == ETag.const then
    match ← view g with
    | .const c us => do
      let el ← emptyLevels
      if us != el then pure none else
        match ← natBinOpOfName? c with
        | some op => redOpT r depth op a b
        | none => pure none
    | _ => pure none
  else pure none

/-- `reduceNat` past the application node. -/
def redHeadS (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) : AM (Option EIdx) := do
  match ← view f with
  | .const c us => redConstS r fe depth c us b
  | .app g a => redAppS r depth g a b
  | _ => pure none

/-- A refused `Nat` computation fails with the invalid class. -/
theorem natRefusal_cls1 (r : Word) : twinCls (natRefusal r) = 1 := by
  unfold natRefusal; repeat' split
  all_goals rfl

theorem natRefusal_cls (r : Word) : twinCls (natRefusal r) = (Err.abort R_THE_KERNEL_REFUSED).cls := by
  rw [natRefusal_cls1]; rfl

/-- An L refusal (an invalid-class code) against the twin's refusal. -/
theorem RefE.natRefused {α β : Type} {G : Prop} {T : AM β} {a : AState} {R : α → β → AState → Prop}
    {k x : Word} (hk : (Err.abort k).cls = 1) (h : T.run a = .error (natRefusal x)) :
    RefE G (.error (.abort k) : Except Err α) T a R :=
  fun _ _ => ⟨_, h, by rw [natRefusal_cls1, hk]⟩

theorem natRef_shr_ne {r : Word} (h : 2 ^ 63 ≤ r.toNat) : r >>> 63 ≠ 0 := by
  intro e; have := congrArg UInt64.toNat e
  rw [UInt64.toNat_shiftRight] at this; simp at this; omega

theorem natRef_shr_eq {r : Word} (h : r.toNat < 2 ^ 63) : r >>> 63 = 0 := by
  apply UInt64.toNat_inj.mp; rw [UInt64.toNat_shiftRight]; simp; omega

section refs
variable (p : Prog) (hp : WhnfDeltaProg' p)

include hp in
/-- **`reduce_nat_succ` refines `redSuccS`, both outcomes**: the errors are the argument's head
normalization's. -/
theorem reduceNatSucc_ref (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatSuccE p n s₀.mem mode vis d c b)
      (redSuccS (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatSuccE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatSuccE.arm1]; unfold redSuccS
  refine RefE.bind_right (pinNatSucc_run hC.pins) ?_
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_nat_lit_stored.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  rw [reduceNatSuccE.k_nat_lit_stored.arm1]
  have c1 := callW_natLitStored p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  refine RefE.bind_core (w := id) c1.core fun M₁ hS₁ _ => ?_
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_pin_at.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  obtain ⟨rfl, -, -, hr₂⟩ := callW_pinAt p hp.pinAt n m₁ 3 r₂ m₂ h2
  have hcw : HW (pinW s₀.mem 4) := hC.pins.names_lt 3 (by decide)
  have hb₁ : ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) =
      decide (c = r₂.headD 0 ∧ r₁.headD 0 ≠ 0) := by
    rw [decI_beq _ _ hc hcw, hr₂, show (3 : Word).toNat = 3 from rfl,
      pinW_const_frame c1.2.2.2.1]
    simp only [decBool]; grind
  by_cases hgo : c = r₂.headD 0 ∧ r₁.headD 0 ≠ 0
  case neg =>
    rw [show reduceNatSuccE.k_pin_at p n mode vis d c b (r₁.headD 0) (.ok (r₂, m₂)) = .ok ([0, 0], m₂) by
      by_cases hcn : c ≠ r₂.headD 0
      · exact reduceNatSuccE.k_pin_at.arm1 _ _ _ _ _ _ _ _ _ _ hcn
      · exact reduceNatSuccE.k_pin_at.arm2 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hcn)
          (Classical.byContradiction fun h => hgo ⟨Classical.not_not.mp hcn, h⟩)]
    exact RefE.ite_neg (by rw [hb₁, decide_eq_false hgo]; decide) (RefE.ret rfl (CorePost.ret hS₁ rfl resW_zero))
  rw [reduceNatSuccE.k_pin_at.arm3 _ _ _ _ _ _ _ _ _ _ hgo.1 hgo.2]
  refine RefE.ite_pos (by rw [hb₁, decide_eq_true hgo]) ?_
  have hSP₁ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => reduceNatSuccE.k_whnf.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₁ hb)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₁ hb)
    fun r₃ m₃ _ h3 => RefE.after_core (w := id) h3 fun M₃ hS₃ _ => ?_
  rw [reduceNatSuccE.k_whnf.arm1]
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_raw_nat_lit.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  obtain ⟨rfl, hrun4, -, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _
    hS₃ h3.resOk r₄ m₄ h4
  refine RefE.bind_right hrun4 ?_
  by_cases hf : r₄.headD 0 = 0
  · rw [reduceNatSuccE.k_raw_nat_lit.arm1 _ _ _ _ hf, show rawDec m₄ r₄ = none by unfold rawDec; rw [ite_eq_left hf]]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl resW_zero)
  rw [reduceNatSuccE.k_raw_nat_lit.arm2 _ _ _ _ hf, show rawDec m₄ r₄ = some (pv (vpool m₄)
    (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf]]
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_nat_succ_lit.none ..) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  obtain ⟨hok5, href5, hfr5⟩ := callW_natSuccLit p hp n ⟨m₄, Locals.init []⟩ _ dn vis fe M₃ eb _ _
    hS₃ (hslice4 hf).1 r₅ m₅ h5
  dsimp only
  by_cases hr5 : 2 ^ 63 ≤ (r₅.headD 0).toNat
  · rw [show reduceNatSuccE.k_nat_succ_lit p (.ok (r₅, m₅)) = .error (.abort R_THE_KERNEL_REFUSED) by
      simp only [reduceNatSuccE.k_nat_succ_lit, ne_eq, natRef_shr_ne hr5, not_false_eq_true, ↓reduceIte]]
    exact RefE.natRefused (by decide) (href5 hr5)
  obtain ⟨hok5', hS5, hres5, hhw5, hP5⟩ := hok5 (by omega)
  rw [reduceNatSuccE.k_nat_succ_lit.arm1 _ _ _ (natRef_shr_eq (by omega))]
  exact RefE.ret (by have h := AM.run_of_ok _ _ hok5'; rw [hres5] at h; exact h) ⟨⟨M₃, hS5, KeptAll.refl _ _, StackKept.of_nat_frame hfr5 hP5⟩,
    by simp [decOptR, decOpt], ⟨by unfold HW; simp, hhw5⟩⟩

include hp in
/-- **`reduce_nat_op` refines `redOpT`, both outcomes**: the errors are the operands' head
normalizations'. -/
theorem reduceNatOp_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d : Word) (op : NatBinOp) (a b : Word)
    (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatOpE p n s₀.mem mode vis d (natBinOpW op) a b)
      (redOpT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat op (decE a) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  cases n with
  | zero => rw [reduceNatOpE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatOpE.arm1]; unfold redOpT
  refine RefE.bind_callE (s₀ := s₀) (fun _ => reduceNatOpE.k_whnf.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe MM eb mode d a (by omega) (by omega) hS ha)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe MM eb mode d a (by omega) (by omega) hS ha)
    fun r₁ m₁ _ h1 => RefE.after_core (w := id) h1 fun M₁ hS₁ _ => ?_
  rw [reduceNatOpE.k_whnf.arm1]
  refine RefE.onlySim (fun _ => reduceNatOpE.k_raw_nat_lit.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  obtain ⟨rfl, hrun2, -, hslice2⟩ := callW_rawNatLit p hp n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb _
    hS₁ h1.resOk r₂ m₂ h2
  refine RefE.bind_right hrun2 ?_
  by_cases hf2 : r₂.headD 0 = 0
  · rw [reduceNatOpE.k_raw_nat_lit.arm1 _ _ _ _ _ _ _ _ _ hf2,
      show rawDec m₂ r₂ = none by unfold rawDec; rw [ite_eq_left hf2]]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl resW_zero)
  rw [reduceNatOpE.k_raw_nat_lit.arm2 _ _ _ _ _ _ _ _ _ hf2, show rawDec m₂ r₂ = some (pv (vpool m₂)
    (r₂.tail.headD 0).toNat (r₂.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf2]]
  have hSP₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => reduceNatOpE.k_whnf_2.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb)
    fun r₃ m₃ _ h3 => RefE.after_core (w := id) h3 fun M₃ hS₃ hSt₃ => ?_
  rw [reduceNatOpE.k_whnf_2.arm1]
  refine RefE.onlySim (fun _ => reduceNatOpE.k_raw_nat_lit_2.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  obtain ⟨rfl, hrun4, -, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _
    hS₃ h3.resOk r₄ m₄ h4
  refine RefE.bind_right hrun4 ?_
  by_cases hf4 : r₄.headD 0 = 0
  · rw [reduceNatOpE.k_raw_nat_lit_2.arm1 _ _ _ _ _ _ _ hf4,
      show rawDec m₄ r₄ = none by unfold rawDec; rw [ite_eq_left hf4]]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl resW_zero)
  rw [reduceNatOpE.k_raw_nat_lit_2.arm2 _ _ _ _ _ _ _ hf4, show rawDec m₄ r₄ = some (pv (vpool m₄)
    (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf4]]
  obtain ⟨hsl2', hpv2, hnorm2'⟩ := hSt₃.pool.slice (hslice2 hf2).1 (hslice2 hf2).2
  rw [← hpv2]
  refine RefE.onlySim (fun _ => reduceNatOpE.k_nat_bin_op_result.none ..) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  obtain ⟨s₅, hs₅, -, hok5, href5⟩ := triple_of_callW (hno n ⟨m₄, Locals.init []⟩ _ dn vis fe M₃ eb op _ _ _ _ hS₃
    hsl2' (hslice4 hf4).1 hnorm2' (hslice4 hf4).2) h5
  by_cases h2 : r₅.headD 0 = 2
  · have he := href5 h2
    simp only [reduceNatOpE.k_nat_bin_op_result, h2, ↓reduceIte]
    repeat' split
    all_goals exact RefE.natRefused (by decide) he
  rw [reduceNatOpE.k_nat_bin_op_result.arm1 _ _ _ h2]
  have hP5 := hok5 h2
  rw [hs₅] at hP5
  have hrun5 := AM.run_of_ok _ _ hP5.run
  rw [hP5.res] at hrun5
  exact RefE.ret hrun5 ⟨hP5.after, (by simp only [decOptR, id, List.headD_cons,
    List.tail_cons, decOpt_norm]), resW_norm _ _⟩

include hp in
/-- **`reduce_nat_k` refines `redHeadS` at a constant head, both outcomes** (`redConstS`; the
errors are `reduce_nat_succ`'s). -/
theorem reduceNatK_ref (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg3 : tagW f = 3)
    (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0)) :
    RefE (KnotUpToE p n) (reduceNatKE p n s₀.mem mode vis d f b)
      (redHeadS (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatKE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  by_cases hbd : tcnt s₀.mem CONST (tierW f) ≤ idxW f
  · rw [reduceNatKE.abort1 _ _ _ _ _ _ _ _ hbd]; exact RefE.of_cls0 (by simp)
  rw [reduceNatKE.arm1 _ _ _ _ _ _ _ _ hbd]
  obtain ⟨n_, us_, hview, rfl, rfl, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.base f hf ⟨hsc, by simpa using hbd⟩ hg3
  generalize tfld s₀.mem CONST (tierW f) (idxW f) 1 = uw at *
  unfold redHeadS redConstS
  refine RefE.bind_right (view_run _ _ _ hview) ?_
  refine RefE.onlySim (fun _ => reduceNatKE.k_pin_word.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨rfl, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  refine RefE.bind_right (pinEmptyLevels_run hC.pins) ?_
  have hb₁ : ((decI uw : LsIdx) != decI (pinW s₀.mem 52)) = !decide (uw = r₁.headD 0) := by
    rw [hr₁]; simp only [bne, decI_beq _ _ hul hC.pins.lv_lt.1]; rfl
  by_cases hne : uw ≠ r₁.headD 0
  · rw [reduceNatKE.k_pin_word.arm1 _ _ _ _ _ _ _ _ _ _ hne]
    exact RefE.ite_pos (by rw [hb₁, decide_eq_false hne]; rfl) (RefE.ret rfl (CorePost.ret hC rfl resW_zero))
  rw [reduceNatKE.k_pin_word.arm2 _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  refine RefE.ite_neg (by rw [hb₁]; simpa using hne) ?_
  exact RefE.tail_eq (reduceNatKE.k_reduce_nat_succ.none p) (fun v => reduceNatKE.k_reduce_nat_succ.arm1 p v.1 v.2)
    (fun h => h.mono (by omega)) rfl (CorePost.relist (MemFrame.refl _ _ _))
    (reduceNatSucc_ref p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d _ b hS
      hnl hb)

include hp in
/-- **`reduce_nat_ap` refines `redHeadS` at an application head, both outcomes** (`redAppS`; the
errors are `reduce_nat_op`'s). -/
theorem reduceNatAp_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg4 : tagW f = 4)
    (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0)) :
    RefE (KnotUpToE p n) (reduceNatApE p n s₀.mem mode vis d f b)
      (redHeadS (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatApE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatApE.eq_2]
  refine RefE.abort0 (by simp) fun hbd => ?_
  obtain ⟨hviewf, hgw, hxw⟩ := view_app s₀.mem a₀ hC.arena.base f hf ⟨hsc, by simpa using hbd⟩ hg4
  generalize tfld s₀.mem APP (tierW f) (idxA f) 0 = gw at hgw hviewf ⊢
  generalize tfld s₀.mem APP (tierW f) (idxA f) 1 = xw at hxw hviewf ⊢
  unfold redHeadS redAppS
  refine RefE.bind_right (view_run _ _ _ hviewf) ?_
  refine RefE.retIf (fun g3 => by rw [decE_const_tag _ hgw]; exact beq_eq_false_iff_ne.mpr g3)
    (fun ht => by rw [decE_const_tag _ hgw] at ht; simpa using ht) (fun _ => CorePost.ret hC rfl resW_zero)
    fun g3 _ => ?_
  refine RefE.abort0 (by simp) fun hs2 => ?_
  refine RefE.abort0 (by simp) fun hb2 => ?_
  obtain ⟨n_, us_, hview, rfl, rfl, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.base _ hgw
    ⟨hs2, by simpa using hb2⟩ (by simpa using g3)
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 0 = cw at *
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 1 = uw at *
  refine RefE.bind_right (view_run _ _ _ hview) ?_
  refine RefE.onlySim (fun _ => reduceNatApE.k_pin_word.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨rfl, hflag, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  refine RefE.bind_right (pinEmptyLevels_run hC.pins) ?_
  have hb₁ : ((decI uw : LsIdx) != decI (pinW s₀.mem 52)) = !decide (uw = r₁.headD 0) := by
    rw [hr₁]; simp only [bne, decI_beq _ _ hul hC.pins.lv_lt.1]; rfl
  by_cases hne : uw ≠ r₁.headD 0
  · rw [reduceNatApE.k_pin_word.arm1 _ _ _ _ _ _ _ _ _ _ _ hne]
    exact RefE.ite_pos (by rw [hb₁, decide_eq_false hne]; rfl) (RefE.ret rfl (CorePost.ret hC rfl resW_zero))
  rw [reduceNatApE.k_pin_word.arm2 _ _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  refine RefE.ite_neg (by rw [hb₁]; simpa using hne) ?_
  refine RefE.onlySim (fun _ => reduceNatApE.k_nat_bin_op_of_name.none ..) (fun _ _ h => h)
    fun r₂ m₂ h2 => ?_
  obtain ⟨t₂, ht₂, hm₂, -, hsel2⟩ := triple_of_callW
    (natBinOpOfNameL_spec p hp.natBinOpOfName n ⟨s₀.mem, Locals.init []⟩ hflag cw) h2
  obtain rfl : m₂ = s₀.mem := by rw [← ht₂, hm₂]
  refine RefE.bind_right (natBinOpOfName_run hC.pins cw hnl) ?_
  have hSP : SlotPre ⟨s₀.mem, Locals.init []⟩ _ dn vis fe MM eb mode := ⟨hC, hS.mode4, hS.eb_mode⟩
  cases hop : natBinOpOfSel (pinW s₀.mem) cw with
  | none =>
    rw [hop] at hsel2
    rw [reduceNatApE.k_nat_bin_op_of_name.arm1 _ _ _ _ _ _ _ _ _ (by rw [hsel2]; rfl)]
    exact RefE.ret rfl (CorePost.ret hC rfl resW_zero)
  | some op =>
    rw [hop] at hsel2
    rw [reduceNatApE.k_nat_bin_op_of_name.arm2 _ _ _ _ _ _ _ _ _
      (by rw [hsel2]; exact natBinOpW_ne_zero op)]
    simp only [hsel2, natBinOpOptW]
    exact RefE.tail_eq (reduceNatApE.k_reduce_nat_op.none p) (fun v => reduceNatApE.k_reduce_nat_op.arm1 p v.1 v.2)
      (fun h => h.mono (by omega)) rfl (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatOp_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega))
        ⟨s₀.mem, Locals.init []⟩ _ dn vis fe MM eb mode d op xw b hSP hxw hb)

include hp in
/-- **`reduce_nat_head` refines `redHeadS`, both outcomes** (the errors are `reduce_nat_k`'s or
`reduce_nat_ap`'s). -/
theorem reduceNatHead_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatHeadE p n s₀.mem mode vis d f b)
      (redHeadS (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatHeadE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatHeadE.eq_2]
  refine RefE.abort0 (by simp) fun hsc => ?_
  -- the tags that only check a bound
  have simple : ∀ (c : TRec), (tagW f = 0 ∧ c = BVAR) ∨ (tagW f = 1 ∧ c = FVAR) ∨
      (tagW f = 2 ∧ c = SORT) ∨ (tagW f = 5 ∧ c = LAM) ∨ (tagW f = 6 ∧ c = FORALL) ∨
      (tagW f = 7 ∧ c = LET) ∨ (tagW f = 8 ∧ c = LIT) ∨ (tagW f = 9 ∧ c = PROJ) →
      RefE (KnotUpToE p (n + 1)) (if tcnt s₀.mem c (tierW f) ≤ idxW f then .error (Err.abort 0) else
        .ok ([0, 0], s₀.mem))
        (redHeadS (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
        (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
    intro c hcg
    refine RefE.abort0 (by simp) fun hbd => ?_
    obtain ⟨v, hv, hc, hp'⟩ := view_nca s₀.mem a₀ hC.arena.base f hf c ⟨hsc, by simpa using hbd⟩ hcg
    unfold redHeadS
    refine RefE.bind_right (view_run _ _ _ hv) ?_
    cases v with
    | const c us => exact absurd rfl (hc c us)
    | app g x => exact absurd rfl (hp' g x)
    | _ => exact RefE.ret rfl (CorePost.ret hC rfl resW_zero)
  have hmono : KnotUpToE p (n + 1) → KnotUpToE p n := fun h => h.mono (by omega)
  by_cases g3 : tagW f = 3
  · rw [ite_eq_left g3]
    exact RefE.tail_eq (reduceNatHeadE.k_reduce_nat_k.none p)
      (fun v => reduceNatHeadE.k_reduce_nat_k.arm1 p v.1 v.2) hmono rfl
      (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatK_ref p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d f b
        hS hf hb g3 hsc)
  rw [ite_eq_right g3]
  by_cases g4 : tagW f = 4
  · rw [ite_eq_left g4]
    exact RefE.tail_eq (reduceNatHeadE.k_reduce_nat_k.none p)
      (fun v => reduceNatHeadE.k_reduce_nat_k.arm1 p v.1 v.2) hmono rfl
      (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatAp_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d
        f b hS hf hb g4 hsc)
  rw [ite_eq_right g4]
  by_cases g0 : tagW f = 0
  · rw [ite_eq_left g0]; exact simple BVAR (Or.inl ⟨g0, rfl⟩)
  rw [ite_eq_right g0]
  by_cases g1 : tagW f = 1
  · rw [ite_eq_left g1]; exact simple FVAR (Or.inr (Or.inl ⟨g1, rfl⟩))
  rw [ite_eq_right g1]
  by_cases g2 : tagW f = 2
  · rw [ite_eq_left g2]; exact simple SORT (Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩)))
  rw [ite_eq_right g2]
  by_cases g5 : tagW f = 5
  · rw [ite_eq_left g5]; exact simple LAM (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩))))
  rw [ite_eq_right g5]
  by_cases g6 : tagW f = 6
  · rw [ite_eq_left g6]; exact simple FORALL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩)))))
  rw [ite_eq_right g6]
  by_cases g7 : tagW f = 7
  · rw [ite_eq_left g7]
    exact simple LET (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩))))))
  rw [ite_eq_right g7]
  by_cases g8 : tagW f = 8
  · rw [ite_eq_left g8]
    exact simple LIT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g8, rfl⟩)))))))
  rw [ite_eq_right g8]
  refine RefE.abort0 (by simp) fun g9 => ?_
  exact simple PROJ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simpa using g9, rfl⟩)))))))

include hp in
/-- **`reduce_nat` refines `reduceNat`, both outcomes** (the errors are `reduce_nat_head`'s). -/
theorem reduceNat_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d e : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    RefE (KnotUpToE p n) (reduceNatE p n s₀.mem mode vis d e)
      (reduceNat (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatE.eq_2]; unfold reduceNat
  have hap : ((decE e).tag == ETag.app) = (tagW e == 4) := by
    by_cases g : tagW e = 4
    · have := (decE_tag_app e he).mpr g
      rw [beq_iff_eq.mpr this, beq_iff_eq.mpr g]
    · have : ¬ (decE e).tag = ETag.app := fun h' => g ((decE_tag_app e he).mp h')
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr g]
  refine RefE.retIf (fun g4 => by rw [hap]; exact beq_eq_false_iff_ne.mpr g4) (fun h => by simpa [hap] using h)
    (fun _ => CorePost.ret hC rfl resW_zero) fun g4 _ => ?_
  refine RefE.abort0 (by simp) fun hsc => ?_
  refine RefE.abort0 (by simp) fun hbd => ?_
  obtain ⟨hview, hfw, hbw⟩ := view_app s₀.mem a₀ hC.arena.base e he ⟨hsc, by simpa using hbd⟩
    (by simpa using g4)
  refine RefE.bind_right (view_run _ _ _ hview) ?_
  exact RefE.tail_eq (reduceNatE.k_reduce_nat_head.none p)
    (fun v => reduceNatE.k_reduce_nat_head.arm1 p v.1 v.2) (fun h => h.mono (by omega)) rfl
    (CorePost.relist (MemFrame.refl _ _ _))
    (reduceNatHead_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d
      _ _ hS hfw hbw)

end refs

/-! ## The halves -/

section halves
variable (p : Prog) (hp : WhnfDeltaProg' p)

include hp in
/-- **`reduce_nat` refines `reduceNat`** (`reduceNat_ref`'s ok half; the statement of
`reduceNat_refines`, with the fuel bound `n ≤ 2 ^ 62` the knot's `whnf` slot needs, and the
program/stub hypotheses explicit). -/
theorem reduceNat_refines' (hno : NatOpResultOK p) (n : Nat) : ReduceNatSpec' p n :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk =>
    RefE.coreSpec (reduceNatE_spec p hp.toWhnfDeltaProg n s₀ mode vis d e)
      (reduceNat_ref p hp hno n F hF hn2 hk s₀ a₀ dn vis fe MM eb mode d e hS he)

include hp in
@[refines ConRon.Arena.reduceNat]
theorem reduceNat_refines (n : Nat) : ReduceNatSpec' p n :=
  reduceNat_refines' p hp (natOpResultOK_of_agree hp.natAgree) n

/-- `reduce_nat`'s error claim at fuel `N` (the ok side's `ReduceNatSpec'` shape). -/
def ReduceNatE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word), N ≤ F → N ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    CoreSpecE p N "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) s₀ a₀

include hp in
/-- **`ReduceNatE`**: `reduce_nat`'s error claim (`reduceNat_ref`'s error half), the `whnf_step`
slot body's hypothesis. -/
theorem reduceNatE_of (hnv : closedNV p L.Checker.nvFns = true) : ReduceNatE p :=
  fun N hk hkE F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpecE (reduceNatE_spec p hp.toWhnfDeltaProg N s₀ mode vis d e) hnv hkE
      (reduceNat_ref p hp (natOpResultOK_of_agree hp.natAgree) N F hF hn hk s₀ a₀ dn vis fe MM eb
        mode d e hs he)

end halves

end L.Arena
