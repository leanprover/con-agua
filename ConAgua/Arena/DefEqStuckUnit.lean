module

import ConAgua.Arena.DefEqStuckCert
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.DefEqMidQuick
import ConAgua.Arena.FormerSortRef
import ConAgua.Arena.EtaRescueRef
import ConAgua.Arena.IndRecRead
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.L.WordOff
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `struct_unit_cert` refines `structUnitCert` (lane `defeq`, helper `defeq-top`)

In L's pieces: `struct_unit_cert` (`a`'s type, its unit-likeness by `unit_like_loop`) and
`struct_unit_tail` (`b`'s type against it). One refinement per piece for both outcomes (`RefE`
over its unified model, `Verdict/WhnfModels7E.lean`): the errors are the knot's slots'.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin in L's pieces -/

/-- `structUnitCert` once `a`'s type `wta` is unit-like, copied. -/
def suTailT (r : CoreFnsA) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  let gb ← if isForallE wtb then ioNeutral b else pure true
  if !gb then pure false
  else r.defeq depth wta wtb

/-- **`struct_unit_tail` refines `suTailT`, both outcomes**: the errors are the `infer_io`, `whnf`
and `defeq` slots'. -/
@[refines_part ConRon.Arena.structUnitCert "b's type against a's (suTailT)"]
theorem sut_ref (p : Prog) (hq : StuckProg p) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    RefE (KnotUpToE p n) (sutE p (n + 1) s₀.mem mode vis d b wta)
      (suTailT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE b) (decE wta)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [sutE]
  unfold suTailT
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d b hF hn hs hb)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d b hF hn hs hb)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [sutE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁ h₁.resOk)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁
      h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  have hh2 : HW (r₂.headD 0) := h₂.resOk
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  simp only [sutE.k_whnf, isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]
  by_cases h6 : tagW (r₂.headD 0) = 6
  · simp only [h6, decide_true, ↓reduceIte]
    refine RefE.bind_callW (fun _ => rfl) (ioNeutral_at p hq.leaf n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb b hS₂ hb)
      fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
    dsimp only [sutE.k_io_neutral]
    by_cases g0 : r₃.headD 0 = 0
    · rw [ite_eq_left g0, L.Arena.decBool_false_of g0]
      exact RefE.ret rfl (CorePost.ret hS₃ rfl hw0)
    rw [ite_eq_right g0, L.Arena.decBool_true_of g0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hs₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hs.mode4, hs.eb_mode⟩
    rw [← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeq _ _ _)]
    exact RefE.bind_callE (fun _ => rfl) (hK.defeq F _ _ dn vis fe M₃ eb mode d wta _ hF hn hs₃ hwta hh2)
      (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₃ eb mode d wta _ hF hn
        hs₃ hwta hh2)
      fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeq _ _ _)]
  exact RefE.bind_callE (fun _ => rfl) (hK.defeq F _ _ dn vis fe M₂ eb mode d wta _ hF hn hs₂ hwta hh2)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d wta _ hF hn
      hs₂ hwta hh2)
    fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩


/-! ## `is_prop_type`, `unit_like_shape(_at)`, the unit-like recursion -/

/-- **`is_prop_type` refines `isPropType`, both outcomes**: the errors are the `infer_io` and
`whnf` slots' and the level comparison's out-of-fuel decline. -/
theorem ipt_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d T : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hT : HW T) :
    RefE (KnotUpToE p n) (iptE p (n + 1) s₀.mem mode vis d T)
      (isPropType (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE T)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [iptE]
  unfold isPropType
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d T hF hn hs hT)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d T hF hn hs hT)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [iptE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁ h₁.resOk)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁
      h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  have hh2 : HW (r₂.headD 0) := h₂.resOk
  simp only [iptE.k_whnf, decH, decE_tag_sort_beq _ hh2]
  by_cases h2 : tagW (r₂.headD 0) ≠ 2
  · rw [ite_eq_left h2]
    simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl hw0)
  rw [ite_eq_right h2]
  have h2' : tagW (r₂.headD 0) = 2 := by simpa using h2
  simp only [h2', decide_true, ↓reduceIte]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ c => eView_callW_view (a := AM.st _ _) hq.eview
    hS₂.arena.base c) fun r₃ m₃ hx => ?_
  obtain ⟨e3, v, hv, hvr, htg⟩ := hx
  rw [e3]
  dsimp only [iptE.k_e_view]
  obtain ⟨rfl, hu⟩ := viewR_sort hvr (htg.trans h2')
  refine RefE.bind_right (L.Arena.viewSort_run (L.Arena.viewSort_of_view _ _ _
    ((decE_tag_sort _ hh2).mpr h2') hv)) ?_
  simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ c => callW_pinWord p hq.leaf.pinword _ _ _ _ _ c)
    fun r₄ m₄ hx => ?_
  obtain ⟨e4, -, hr4⟩ := hx
  rw [e4]
  dsimp only [iptE.k_pin_word]
  have hP := hS₂.pins
  refine RefE.bind_right (pinZeroLevel_run hP) ?_
  rw [show (53 : Word).toNat = 53 from rfl] at hr4
  have hz : HW (r₄.headD 0) := by rw [hr4]; exact hP.lv_lt.2.1
  have hden := hc.den dn m₂ _ vis fe M₂ eb hS₂
  obtain ⟨lu, hdu⟩ := hden.sort _ _ hv
  have hdz := hden.zero
  rw [hP.zeroLevel, ← hr4] at hdz
  rw [← hr4]
  rcases n with _ | _ | n₂
  · rw [callW_zero, liftE_none]; exact RefE.of_cls0 (by simp)
  · exact RefE.onlySim (Q := fun _ _ => False) (fun _ => rfl)
      (fun _ _ c3 => lvlEqC_one p hc.lvc _ _ _ _ _ c3) fun _ _ h => h.elim
  refine RefE.bind_callW (fun _ => rfl) (lvlEqC_refines p hc.lvc n₂ ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
    hS₂ _ _ hu hz lu .zero hdu hdz) fun rz m₅ _ e₅ => RefE.after_core (w := id) e₅ fun M₅ hS₅ _ => ?_
  dsimp only [iptE.k_lvl_eq_c]
  by_cases hzz : rz.headD 0 = 0
  · rw [ite_eq_left hzz, show decO (rz.headD 0) = none by unfold decO; rw [ite_eq_left hzz]]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [ite_eq_right hzz, decO_ne_zero hzz]
  have h3 := e₅.resOk
  unfold ResH HW at h3
  have hres : HW (rz.headD 0 - 1) := by
    unfold HW
    generalize rz.headD 0 = z at h3 hzz ⊢
    have hz' : z.toNat ≠ 0 := fun h' => hzz (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)),
      UInt64.toNat_one]
    omega
  exact RefE.ret rfl (CorePost.ret hS₅ rfl hres)

/-- `unit_like_shape(_at)`'s answer `(f, tele, n)`: `some (tele, n)` for a flag `f ≠ 0`. -/
def decShape (r : List Word) : Option (EIdx × Nat) :=
  if r.headD 0 = 0 then none else some (decE (r.tail.headD 0), (r.tail.tail.headD 0).toNat)

/-- The telescope of a found shape is a handle word. -/
def ShapeOK (r : List Word) : Prop := r.headD 0 ≠ 0 → HW (r.tail.headD 0)

/-- **`unit_like_shape_at` refines `unitLikeShapeAt`, both outcomes** (the arguments the slice
`(to, tn)` below the stack top; the errors are aborts and the callees' class-`0` failures). -/
theorem ulsa_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) {G : Prop} (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb us to tn tctor nP nF : Word) (targs : List EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hus : HW us) (htc : HW tctor)
    (hsp : SpineR s₀.mem to tn targs.toArray) (htop : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE G (ulsaE p n s₀.mem vis us to tn tctor nP nF)
      (unitLikeShapeAt fe (decI us) targs (decI tctor) nP.toNat nF.toNat) a₀
      (CorePost decShape dn s₀.mem vis fe M eb ShapeOK) := by
  have hR := hS.arena.base
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n =>
  simp only [ulsaE]
  unfold unitLikeShapeAt
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env htc h)
    fun r₁ m₁ hx => ?_
  obtain ⟨e1, hfind, hfound⟩ := hx
  rw [e1]
  dsimp only [ulsaE.k_env_find]
  have hl : ∀ (T : AM (Option (EIdx × Nat))), T.run a₀ = .ok (none, a₀) →
      RefE G (.ok ([0, 0, 0], s₀.mem) : Except Err (List Word × Mem)) T a₀
        (CorePost decShape dn s₀.mem vis fe M eb ShapeOK) :=
    fun T hT => RefE.ret hT (CorePost.ret hS rfl (fun h => absurd rfl h))
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI tctor) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    rw [hnone]; exact hl _ rfl
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hctor := L.Arena.decCI_ctorR (erRdOK _) hci
  rw [hfind']
  by_cases h4 : erRd s₀.mem (r₁.tail.headD 0) ≠ 4
  · erw [ite_eq_left h4]
    rcases ci with _ | _ | _ | _ | ⟨cv, np, nf, fam⟩ | _ | _ <;> try exact hl _ rfl
    exact absurd rfl (hctor.2 h4 cv np nf fam)
  erw [ite_eq_right h4]
  obtain ⟨cvc, hci_eq, -⟩ := hctor.1 (by simpa using h4)
  rw [hci_eq] at hci ⊢
  obtain ⟨-, -, hlp, -, htyw, hty⟩ := decCV_rd_ci (erRdOK s₀.mem) (decCI_ctorInfo_iff.mp hci).2.1
  simp only [L.Ind.erRd_foldN] at *
  rw [hty]
  refine RefE.bind_callW (fun _ => rfl) (hc.instLP n s₀ a₀ dn vis fe M eb _ _ us _ cvc.levelParams hS
    htyw hus hlp) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ hK₂ => ?_
  dsimp only [ulsaE.k_inst_lp]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (peelPis_refines' p hq.leaf.core.spine.peel n _ _ hS₂.arena.base nP _ h₂.resOk) h)
    fun r₃ m₃ hx => ?_
  obtain ⟨s3, hs3, hm3, -, hh3, hpp⟩ := hx
  have e3 : m₃ = m₂ := hs3.symm.trans hm3
  rw [e3]
  refine RefE.bind_right hpp ?_
  dsimp only [ulsaE.k_peel_pis]
  by_cases g0 : r₃.headD 0 = 0
  · rw [ite_eq_left g0]
    simp only [decOpt, g0, ↓reduceIte]
    exact RefE.ret rfl ⟨⟨M₂, hS₂, KeptAll.refl _ _, StackKept.refl _⟩, rfl, fun h => absurd rfl h⟩
  rw [ite_eq_right g0]
  simp only [decOpt, g0, ↓reduceIte]
  have hsp2 : SpineR m₂ to tn targs.toArray := hsp.keep hK₂.size hK₂.below htop hS.spn
  have htop2 : to.toNat + tn.toNat ≤ (spTop m₂).toNat := by rw [hK₂.top]; exact htop
  refine RefE.bind_callW (fun _ => rfl) (hc.instList n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb _ to tn 0
    targs.toArray hS₂ hh3 hsp2 htop2) fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [ulsaE.k_inst_list]
  exact RefE.ret rfl (CorePost.ret hS₄ rfl (fun _ => h₄.resOk))

/-- **`unit_like_shape` refines `unitLikeShape`, both outcomes** (the stack top put back; the
errors are aborts and the callees' class-`0` failures). -/
theorem uls_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) {G : Prop} (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb w : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hw : HW w) :
    RefE G (ulsE p n s₀.mem vis w) (unitLikeShape fe (decE w)) a₀
      (CorePost decShape dn s₀.mem vis fe M eb ShapeOK) := by
  have hR := hS.arena.base
  have hl : ∀ (T : AM (Option (EIdx × Nat))), T.run a₀ = .ok (none, a₀) →
      RefE G (.ok ([0, 0, 0], s₀.mem) : Except Err (List Word × Mem)) T a₀
        (CorePost decShape dn s₀.mem vis fe M eb ShapeOK) :=
    fun T hT => RefE.ret hT (CorePost.ret hS rfl (fun h => absurd rfl h))
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n =>
  simp only [ulsE]
  unfold unitLikeShape
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppFn_callW hq.leaf hR hw h)
    fun r₁ m₁ hx => ?_
  obtain ⟨e1, hh, hgaf⟩ := hx
  rw [e1]
  dsimp only [ulsE.k_get_app_fn]
  refine RefE.bind_right hgaf ?_
  generalize r₁.headD 0 = h at hh hgaf ⊢
  by_cases h3 : tagW h ≠ 3
  · rw [ite_eq_left h3, decE_tag_const_beq _ hh]
    simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact hl _ rfl
  rw [ite_eq_right h3]
  have h3' : tagW h = 3 := by simpa using h3
  refine RefE.abort0 (by decide) fun hsc => ?_
  refine RefE.abort0 (by decide) fun hcc => ?_
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  rw [decE_tag_const_beq _ hh]
  simp only [h3', decide_true, ↓reduceIte]
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hv ⊢
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us at huw hv ⊢
  try simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env hnw h)
    fun r₂ m₂ hx => ?_
  obtain ⟨e2, hfind, hfound⟩ := hx
  rw [e2]
  dsimp only [ulsE.k_env_find]
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    rw [hnone]; exact hl _ rfl
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK (erRdOK _) hci
  rw [hfind']
  by_cases h4 : erRd s₀.mem (r₂.tail.headD 0) ≠ 3
  · erw [ite_eq_left h4]
    rcases ci with _ | _ | _ | _ | _ | _ | _ <;> try exact hl _ rfl
    all_goals exact absurd rfl (hind.2 h4 _ _)
  erw [ite_eq_right h4]
  obtain ⟨cvS, caps, rfl⟩ := hind.1 (by simpa using h4)
  have hIR := decCI_indCaps (erRdOK s₀.mem) hci
  have hlpS : cvS.levelParams.length = (erRd s₀.mem (r₂.tail.headD 0 + 3)).toNat := hslice?_lenR hIR.lp
  simp only [L.Ind.erRd_foldN] at *
  try simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn n ⟨s₀.mem, Locals.init []⟩ us) h)
    fun r₃ m₃ hx => ?_
  obtain ⟨t₃, ht₃, ht₃s, hne, hr₃⟩ := hx
  have e3 : m₃ = s₀.mem := by rw [← ht₃, ht₃s]
  rw [e3]
  rw [hr₃] at hne
  have hvl := defeq_lsNodeW_viewLen hR huw hne
  rw [← hr₃] at hvl
  refine RefE.bind_right (viewLsLen_run _ _) ?_
  rw [hvl]
  dsimp only [ulsE.k_ls_node]
  have heta := hIR.eta
  by_cases g1 : erRd s₀.mem (r₂.tail.headD 0 + (CI.indCaps + Caps.eta)) = 0
  · erw [ite_eq_left g1]
    rw [show caps.eta = false by rw [heta, g1]; rfl]
    exact hl _ (by simp; rfl)
  erw [ite_eq_right g1]
  rw [show caps.eta = true by rw [heta]; simpa using g1, hlpS]
  by_cases g2 : r₃.tail.headD 0 ≠ erRd s₀.mem (r₂.tail.headD 0 + 3)
  · erw [ite_eq_left g2]
    rw [ite_eq_right (fun h => g2 (UInt64.toNat_inj.mp h.2))]
    exact hl _ rfl
  erw [ite_eq_right g2]
  rw [ite_eq_left ⟨rfl, congrArg UInt64.toNat (by simpa using g2)⟩]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (findTable_refines p hq.findTable n _ vis k hS.env hnw) h)
    fun r₄ m₄ hx => ?_
  obtain ⟨s4, hs4, hm4, -, htb, htbs⟩ := hx
  have e4 : m₄ = s₀.mem := hs4.symm.trans hm4
  rw [e4]
  dsimp only [ulsE.k_find_table]
  rw [htb]
  by_cases t0 : r₄.headD 0 = 0
  · rw [ite_eq_left t0]
    simp only [tblFound, t0, ↓reduceIte]; exact hl _ rfl
  rw [ite_eq_right t0]
  obtain ⟨tb, htb'⟩ := htbs t0
  have hT : tblFound s₀.mem (r₄.headD 0) = some tb := by simp only [tblFound, t0, ↓reduceIte]; exact htb'
  obtain ⟨-, hTp, hTcw, hTc, hTf⟩ := tblFound_words hT
  rw [hT]
  simp only [L.Ind.erRd_foldN] at *
  try simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppArgs_callW hq.leaf.core.spine hS hw h)
    fun r₅ m₅ hx => ?_
  obtain ⟨hf5, hg5, hr50, htop5, targs, hargs, hsp⟩ := hx
  refine RefE.bind_right hargs ?_
  dsimp only [ulsE.k_get_app_args]
  have hlen : targs.length = (r₅.tail.headD 0).toNat := by simpa using hsp.size
  by_cases g3 : r₅.tail.headD 0 ≠ erRd s₀.mem (r₄.headD 0 + 4)
  · rw [ite_eq_left g3, ite_eq_right (by rw [hlen, hTp]; exact fun h => g3 (UInt64.toNat_inj.mp h))]
    obtain ⟨hS', hK'⟩ := hS.restoreTop' hf5 hg5
    exact RefE.ret rfl ⟨⟨M, hS', KeptAll.refl _ _, hK'⟩, rfl, fun h => absurd rfl h⟩
  rw [ite_eq_right g3, ite_eq_left (by rw [hlen, hTp]; exact congrArg _ (by simpa using g3))]
  have hS₅ := hS.frame_stk hf5 (by simp) (by simp)
  have hsz5 : (m₅.arr64 SPN).size < 2 ^ 63 := hg5.size ▸ hS.spn
  have htop' : (r₅.headD 0).toNat + (r₅.tail.headD 0).toNat ≤ (spTop m₅).toNat := by
    have e := L.toNat_add_of_lt (r₅.headD 0) (r₅.tail.headD 0) (by have := hsp.bound; omega)
    rw [htop5, ← hr50]; omega
  rw [hTc, hTp, hTf]
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
    (fun v _ _ h => (GrowPost.mk (CoreAfterG.compK (KeptAll.refl _ _) hg5 h.after.toG) h.res
      h.valid).restore _ (by simp [decShape]) h.valid)
    (ulsa_ref p hq hc (G := G) n ⟨m₅, Locals.init []⟩ a₀ dn vis fe M eb us _ _ _ _ _ targs hS₅ huw hTcw hsp
      htop')

/-! ## The unit-like recursion -/

section ul
variable (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (F : Nat)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)

/-- **The unit-like group at L fuel `n`**: `unit_like_loop`, `unit_like_struct`, `unit_like_fields`
refine `unitLikeLoop`, `unitLikeStruct`, `unitLikeFields`, both outcomes. -/
def UL0 (n : Nat) : Prop :=
  (∀ (s₀ : St) (a₀ : AState) (M : ModeMaps) (fuel d T : Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW T →
    RefE (KnotUpToE p n) (ullE p n s₀.mem mode vis fuel d T)
      (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe fuel.toNat d.toNat (decE T)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH)) ∧
  (∀ (s₀ : St) (a₀ : AState) (M : ModeMaps) (ulf d w : Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW w →
    RefE (KnotUpToE p n) (ulstE p n s₀.mem mode vis ulf d w)
      (unitLikeStruct (coreKnot (decMode mode) (decEager mode) fe id F)
        (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe ulf.toNat) fe d.toNat (decE w)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH)) ∧
  (∀ (s₀ : St) (a₀ : AState) (M : ModeMaps) (ulf n' d tele : Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW tele →
    RefE (KnotUpToE p n) (ulfE p n s₀.mem mode vis ulf n' d tele)
      (unitLikeFields (coreKnot (decMode mode) (decEager mode) fe id F)
        (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe ulf.toNat) n'.toNat d.toNat
        (decE tele)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH))

theorem UL0_zero : UL0 p F dn vis fe eb mode 0 :=
  ⟨fun _ _ _ _ _ _ _ _ => by rw [ullE.eq_1]; exact RefE.of_cls0 (e := .outOfFuel) rfl,
   fun _ _ _ _ _ _ _ _ => by rw [ulstE.eq_1]; exact RefE.of_cls0 (e := .outOfFuel) rfl,
   fun _ _ _ _ _ _ _ _ _ => by rw [ulfE.eq_1]; exact RefE.of_cls0 (e := .outOfFuel) rfl⟩

include hq hc in
/-- `unit_like_fields`' opening (`j1`): the field at a fresh variable, then the next field. -/
theorem ulf_j1 (n : Nat) (ih : UL0 p F dn vis fe eb mode n) (s₁ : St) (a₁ : AState) (M₁ : ModeMaps)
    (ulf n' d dom body : Word) (hs : SlotPre s₁ a₁ dn vis fe M₁ eb mode) (hdom : HW dom) (hbody : HW body)
    (hd : d + 1 ≠ 0) :
    RefE (KnotUpToE p n) (ulfE.j1 p n mode vis ulf n' d dom body s₁.mem)
      (do
        let fv ← internE (.fvar d.toNat (decE dom))
        let body2 ← instantiate1Fast coreWalkFuel (decE body) fv 0
        unitLikeFields (coreKnot (decMode mode) (decEager mode) fe id F)
          (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe ulf.toNat) (n' - 1).toNat
          (d.toNat + 1) body2) a₁
      (CorePost decBool dn s₁.mem vis fe M₁ eb ResH) := by
  have hS := hs.rel
  rw [ulfE.j1.arm1]
  refine RefE.bind_callW (fun _ => ulfE.k_intern_fvar.none ..) (internFVar_coreSpec hq.body n s₁ hS d dom hdom)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₂ hS₁ _ => ?_
  rw [ulfE.k_intern_fvar.arm1]
  refine RefE.bind_callW (fun _ => ulfE.k_inst1.none ..)
    (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₂ eb body (r₁.headD 0) 0 hS₁ hbody h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₃ hS₂ _ => ?_
  rw [ulfE.k_inst1.arm1, ← L.toNat_add_one_of_ne _ hd]
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (ih.2.2 ⟨m₂, Locals.init []⟩ _ M₃ ulf (n' - 1) (d + 1) _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.resOk)

include hq hc in
/-- **`unit_like_fields`, one level**, from the group at the fuel below. -/
theorem ulf_step (n : Nat) (hk : KnotUpTo p n) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (ih : UL0 p F dn vis fe eb mode n) (s₀ : St) (a₀ : AState) (M : ModeMaps) (ulf n' d tele : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW tele) :
    RefE (KnotUpToE p n) (ulfE p (n + 1) s₀.mem mode vis ulf n' d tele)
      (unitLikeFields (coreKnot (decMode mode) (decEager mode) fe id F)
        (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe ulf.toNat) n'.toNat d.toNat
        (decE tele)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  by_cases hn0 : n' = 0
  · rw [ulfE.arm1 _ _ _ _ _ _ _ _ _ hn0, show n'.toNat = 0 by simp [hn0]]
    exact RefE.ret rfl (CorePost.ret hS rfl hw1)
  have hnn : n'.toNat = (n' - 1).toNat + 1 := by
    have : n'.toNat ≠ 0 := fun e => hn0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [ulfE.eq_2, ite_eq_right hn0, hnn]
  simp only [unitLikeFields]
  rw [decE_tag_forallE_beq _ ht]
  by_cases h6 : tagW tele ≠ 6
  · rw [ite_eq_left h6]
    simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS rfl hw0)
  rw [ite_eq_right h6]
  have h6' : tagW tele = 6 := by simpa using h6
  simp only [h6', decide_true, ↓reduceIte]
  refine RefE.abort0 (by decide) fun hd => ?_
  refine RefE.abort0 (by decide) fun htr => ?_
  refine RefE.abort0 (by decide) fun hi => ?_
  have hvo : viewOK s₀.mem tele FORALL := ⟨htr, by simpa using hi⟩
  obtain ⟨-, hdom, hbody⟩ := view_forall s₀.mem _ hS.arena.base tele ht hvo h6'
  refine RefE.bind_right (by rw [L.Arena.viewBind_run, viewBind_forall s₀.mem _ hS.arena.base tele ht hvo h6']) ?_
  simp only
  cases n with
  | zero => rw [iptE.eq_1, ulfE.k_is_prop_type.none]; exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  refine RefE.bindE (fun _ => ulfE.k_is_prop_type.none ..) (fun hG => hG.mono (Nat.le_succ N))
    (ipt_ref p hq hc N (hk.mono (Nat.le_succ N)) F s₀ a₀ dn vis fe M eb mode d _ (by omega) (by omega) hs hdom)
    fun v y a₂ _ hQ => ?_
  obtain ⟨r, m⟩ := v
  obtain ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, hy, -⟩ := hQ
  dsimp only at hy hS₂ hSt₂
  subst hy
  have hs₂ : SlotPre ⟨m, Locals.init []⟩ a₂ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  have hmono : ∀ {x : Except Err (List Word × Mem)} {T : AM Bool} {a : AState},
      RefE (KnotUpToE p (N + 1)) x T a (CorePost decBool dn m vis fe M₂ eb ResH) →
      RefE (KnotUpToE p (N + 1)) x T a (CorePost decBool dn s₀.mem vis fe M eb ResH) :=
    fun h => h.mono fun _ _ _ h => ⟨CoreAfter.comp hK₂ hSt₂ h.after, h.res, h.valid⟩
  by_cases g0 : r.headD 0 = 0
  · rw [ulfE.k_is_prop_type.arm1 _ _ _ _ _ _ _ _ _ _ _ g0, decBool_false_of g0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine RefE.bindE (fun _ => ulfE.k_unit_like_loop.none ..) id
      (ih.1 ⟨m, Locals.init []⟩ a₂ M₂ ulf d _ hs₂ hdom) fun v y a₃ _ hQ => ?_
    obtain ⟨r', m'⟩ := v
    obtain ⟨⟨M₃, hS₃, hK₃, hSt₃⟩, hy', -⟩ := hQ
    dsimp only at hy' hS₃ hSt₃
    subst hy'
    refine hmono ((?_ : RefE _ _ _ _ (CorePost decBool dn m' vis fe M₃ eb ResH)).mono
      fun _ _ _ h => ⟨CoreAfter.comp hK₃ hSt₃ h.after, h.res, h.valid⟩)
    by_cases g1 : r'.headD 0 = 0
    · rw [ulfE.k_unit_like_loop.arm1 _ _ _ _ _ _ _ _ _ _ _ g1, decBool_false_of g1]
      exact RefE.ret rfl (CorePost.ret hS₃ rfl hw0)
    rw [ulfE.k_unit_like_loop.arm2 _ _ _ _ _ _ _ _ _ _ _ g1, decBool_true_of g1]
    simp only [↓reduceIte]
    exact ulf_j1 p hq hc F dn vis fe eb mode (N + 1) ih ⟨m', Locals.init []⟩ a₃ M₃ ulf n' d _ _
      ⟨hS₃, hs.mode4, hs.eb_mode⟩ hdom hbody hd
  rw [ulfE.k_is_prop_type.arm2 _ _ _ _ _ _ _ _ _ _ _ g0, decBool_true_of g0]
  simp only [↓reduceIte]
  exact hmono (ulf_j1 p hq hc F dn vis fe eb mode (N + 1) ih ⟨m, Locals.init []⟩ a₂ M₂ ulf n' d _ _ hs₂
    hdom hbody hd)

include hq hc in
/-- **`unit_like_struct`, one level**, from the group at the fuel below. -/
theorem ulst_step (n : Nat) (ih : UL0 p F dn vis fe eb mode n) (s₀ : St) (a₀ : AState) (M : ModeMaps)
    (ulf d w : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hw : HW w) :
    RefE (KnotUpToE p n) (ulstE p (n + 1) s₀.mem mode vis ulf d w)
      (unitLikeStruct (coreKnot (decMode mode) (decEager mode) fe id F)
        (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe ulf.toNat) fe d.toNat (decE w)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  rw [ulstE.arm1]
  unfold unitLikeStruct
  refine RefE.bindE (fun _ => ulstE.k_unit_like_shape.none ..) id
    (uls_ref p hq hc (G := KnotUpToE p n) n s₀ a₀ dn vis fe M eb w hs.rel hw) fun v y a₂ _ hQ => ?_
  obtain ⟨r, m⟩ := v
  obtain ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, hy, hok⟩ := hQ
  dsimp only at hy hS₂ hSt₂ hok
  subst hy
  by_cases g0 : r.headD 0 = 0
  · rw [ulstE.k_unit_like_shape.arm1 _ _ _ _ _ _ _ _ g0]
    simp only [decShape, g0, ↓reduceIte]
    exact RefE.ret rfl ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, rfl, hw0⟩
  rw [ulstE.k_unit_like_shape.arm2 _ _ _ _ _ _ _ _ g0]
  simp only [decShape, g0, ↓reduceIte]
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
    (fun _ _ _ h => ⟨CoreAfter.comp hK₂ hSt₂ h.after, h.res, h.valid⟩)
    (ih.2.2 ⟨m, Locals.init []⟩ a₂ M₂ ulf _ d _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ (hok g0))

include hq hc in
/-- **`unit_like_loop`, one level**, from the group at the fuel below. -/
theorem ull_step (n : Nat) (hk : KnotUpTo p n) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (ih : UL0 p F dn vis fe eb mode n) (s₀ : St) (a₀ : AState) (M : ModeMaps) (fuel d T : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hT : HW T) :
    RefE (KnotUpToE p n) (ullE p (n + 1) s₀.mem mode vis fuel d T)
      (unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe fuel.toNat d.toNat (decE T)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  by_cases hf0 : fuel = 0
  · rw [ullE.arm1 _ _ _ _ _ _ _ _ hf0, show fuel.toNat = 0 by simp [hf0]]
    exact RefE.ret rfl (CorePost.ret hs.rel rfl hw0)
  have hff : fuel.toNat = (fuel - 1).toNat + 1 := by
    have : fuel.toNat ≠ 0 := fun e => hf0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [ullE.arm2 _ _ _ _ _ _ _ _ hf0, hff]
  simp only [unitLikeLoop]
  refine RefE.bind_callE (fun _ => ullE.k_whnf.none ..) (hK.whnf F s₀ a₀ dn vis fe M eb mode d T hF hn hs hT)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb mode d T hF hn hs hT)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  have hh1 : HW (r₁.headD 0) := h₁.resOk
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  simp only [decH, decE_tag_forallE_beq _ hh1]
  by_cases h6 : tagW (r₁.headD 0) = 6
  · simp only [h6, decide_true, ↓reduceIte]
    by_cases hd : d + 1 = 0
    · rw [ullE.k_whnf.abort1 _ _ _ _ _ _ _ _ h6 hd]; exact RefE.of_cls0 (by decide)
    by_cases ht : tierW (r₁.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
    · rw [ullE.k_whnf.abort2 _ _ _ _ _ _ _ _ h6 hd ht]; exact RefE.of_cls0 (by decide)
    by_cases hi : tcnt m₁ FORALL (tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0)
    · rw [ullE.k_whnf.abort3 _ _ _ _ _ _ _ _ h6 hd ht hi]; exact RefE.of_cls0 (by decide)
    rw [ullE.k_whnf.arm1 _ _ _ _ _ _ _ _ h6 hd ht hi]
    have hvo : viewOK m₁ (r₁.headD 0) FORALL := ⟨ht, by simpa using hi⟩
    obtain ⟨-, hdom, hbody⟩ := view_forall m₁ _ hS₁.arena.base _ hh1 hvo h6
    refine RefE.bind_right (by rw [L.Arena.viewBind_run, viewBind_forall m₁ _ hS₁.arena.base _ hh1 hvo h6]) ?_
    simp only
    refine RefE.bind_callW (fun _ => ullE.k_intern_fvar.none ..)
      (internFVar_coreSpec hq.body n ⟨m₁, Locals.init []⟩ hS₁ d _ hdom)
      fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
    rw [ullE.k_intern_fvar.arm1]
    refine RefE.bind_callW (fun _ => ullE.k_inst1.none ..)
      (hc.inst1 n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb _ (r₂.headD 0) 0 hS₂ hbody h₂.resOk)
      fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
    rw [ullE.k_inst1.arm1, ← L.toNat_add_one_of_ne _ hd]
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
      (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
      (ih.1 ⟨m₃, Locals.init []⟩ _ M₃ (fuel - 1) (d + 1) _ ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₃.resOk)
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [ullE.k_whnf.arm2 _ _ _ _ _ _ _ _ h6]
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (ih.2.1 ⟨m₁, Locals.init []⟩ _ M₁ (fuel - 1) d _ hs₁ hh1)

include hq hc in
/-- **The unit-like group at every L fuel** below the knot. -/
theorem UL0_all : ∀ (n : Nat), KnotUpTo p n → n ≤ F → n ≤ 2 ^ 62 → UL0 p F dn vis fe eb mode n
  | 0, _, _, _ => UL0_zero p F dn vis fe eb mode
  | n + 1, hk, hF, hn =>
    have ih := UL0_all n (hk.mono (Nat.le_succ n)) (by omega) (by omega)
    have hk' := hk.mono (Nat.le_succ n)
    ⟨fun s₀ a₀ M fuel d T hs hT => (ull_step p hq hc F dn vis fe eb mode n hk' (by omega) (by omega) ih s₀ a₀
        M fuel d T hs hT).monoG (fun hG => hG.mono (Nat.le_succ n)),
     fun s₀ a₀ M ulf d w hs hw => (ulst_step p hq hc F dn vis fe eb mode n ih s₀ a₀ M ulf d w hs
        hw).monoG (fun hG => hG.mono (Nat.le_succ n)),
     fun s₀ a₀ M ulf n' d tele hs ht => (ulf_step p hq hc F dn vis fe eb mode n hk' (by omega) (by omega) ih
        s₀ a₀ M ulf n' d tele hs ht).monoG (fun hG => hG.mono (Nat.le_succ n))⟩

end ul

/-! ## `struct_unit_cert` -/

/-- **`struct_unit_cert` refines `structUnitCert`, both outcomes**: the errors are the `infer_io`,
`whnf` slots' and `struct_unit_head`'s. -/
theorem suc_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (sucE p (n + 1) s₀.mem mode vis d a b)
      (structUnitCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [sucE]
  unfold structUnitCert
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [sucE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁ h₁.resOk)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁
      h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  have hh2 : HW (r₂.headD 0) := h₂.resOk
  have hfuel : unitLikeFuel = (4611686018427387904 : Word).toNat := rfl
  have hUL := UL0_all p hq hc F dn vis fe eb mode n hk hF hn
  -- `j1`: the unit-like test, then `b`'s side
  have hj1 : ∀ (m : Mem) (a' : AState) (M' : ModeMaps), CoreS dn m a' vis fe M' eb →
      RefE (KnotUpToE p n) (sucE.j1 p n mode vis d b (r₂.headD 0) m)
        (do
          if ← unitLikeLoop (coreKnot (decMode mode) (decEager mode) fe id F) fe unitLikeFuel d.toNat
              (decH r₂) then
            suTailT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE b) (decH r₂)
          else pure false) a'
        (CorePost decBool dn m vis fe M' eb ResH) := by
    intro m a' M' hS'
    have hs' : SlotPre ⟨m, Locals.init []⟩ a' dn vis fe M' eb mode := ⟨hS', hs.mode4, hs.eb_mode⟩
    simp only [sucE.j1]
    rw [hfuel]
    refine RefE.bindE (fun _ => rfl) id (hUL.1 ⟨m, Locals.init []⟩ a' M' _ d _ hs' hh2)
      fun v y a₃ _ hQ => ?_
    obtain ⟨r₃, m₃⟩ := v
    obtain ⟨⟨M₃, hS₃, hK₃, hSt₃⟩, hy, -⟩ := hQ
    dsimp only at hy hS₃ hSt₃
    subst hy
    dsimp only [sucE.k_unit_like_loop]
    by_cases g0 : r₃.headD 0 = 0
    · rw [ite_eq_left g0, L.Arena.decBool_false_of g0]
      exact RefE.ret rfl ⟨⟨M₃, hS₃, hK₃, hSt₃⟩, rfl, hw0⟩
    rw [ite_eq_right g0, L.Arena.decBool_true_of g0]
    simp only [↓reduceIte]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ N =>
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N)) rfl
      (fun _ _ _ h => ⟨CoreAfter.comp hK₃ hSt₃ h.after, h.res, h.valid⟩)
      (sut_ref p hq N (hk.mono (Nat.le_succ N)) F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d b _
        (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ hb hh2)
  simp only [sucE.k_whnf, isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]
  by_cases h6 : tagW (r₂.headD 0) = 6
  · simp only [h6, decide_true, ↓reduceIte]
    refine RefE.bind_callW (fun _ => rfl) (ioNeutral_at p hq.leaf n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb a hS₂ ha)
      fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
    dsimp only [sucE.k_io_neutral]
    by_cases g0 : r₃.headD 0 = 0
    · rw [ite_eq_left g0, L.Arena.decBool_false_of g0]
      exact RefE.ret rfl (CorePost.ret hS₃ rfl hw0)
    rw [ite_eq_right g0, L.Arena.decBool_true_of g0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hj1 m₃ _ M₃ hS₃
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine RefE.bind_right (x := (pure true : AM Bool)) rfl ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact hj1 m₂ _ M₂ hS₂

/-- **`struct_unit_cert` refines `structUnitCert`** at the knot (`suc_ref`'s ok half). -/
@[refines ConRon.Arena.structUnitCert]
theorem suCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (sucE_spec p hq.toCertProg (n + 1) s₀ mode vis d a b)
    (suc_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
