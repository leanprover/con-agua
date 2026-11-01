module

import ConAgua.Arena.DefEqStuckCert
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.DefEqStuck

@[expose] public section

/-!
# `struct_unit_cert` refines `structUnitCert` (lane `defeq`, helper `defeq-top`)

In L's pieces: `struct_unit_cert` (`a`'s type), `struct_unit_head` (its head, family and spine;
the record words read before any call after `env_find`, the twin's pure readers first),
`struct_unit_tail` (`b`'s type against it). One refinement per piece for both outcomes (`RefE`
over its unified model, `Verdict/WhnfModels7E.lean`): the errors are the knot's slots'.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin in L's pieces -/

/-- `structUnitCert` once the family is certified, copied. -/
def suTailT (r : CoreFnsA) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  if isForallE wtb then pure false
  else r.defeq depth wta wtb

/-- `structUnitCert` past `a`'s type `wta`, copied. -/
def suHeadT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel wta
  if hh.tag == ETag.const then
    view hh >>= fun v => match v with
      | .const T us' =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          let targs ← getAppArgs coreWalkFuel wta
          let reserved ← reservedBasisNames
          match ← viewLsLen us' with
          | none => failDanglingLs
          | some uslen =>
          if caps.unitlike = true ∧ reserved.contains T = false ∧
              targs.length = caps.unitParams ∧
              uslen = cvT.levelParams.length then
            suTailT r depth b wta
          else pure false
        | _ => pure false
      | _ => pure false
  else pure false

theorem structUnitCert_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    structUnitCert r fe depth a b = (do
      let ta ← r.inferIO depth a
      let wta ← r.whnf depth ta
      suHeadT r fe depth b wta) := rfl

section headRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b wta : EIdx) (st : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel wta).run st = .ok (hh, st))

include hgaf

theorem suHead_nonconst (ht : (hh.tag == ETag.const) = false) :
    (suHeadT r fe depth b wta).run st = .ok (false, st) := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem suHead_other (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const T us'))
    (hf : ∀ cv caps, fe.find? T ≠ some (.indInfo cv caps)) :
    (suHeadT r fe depth b wta).run st = .ok (false, st) := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? T with _ | ⟨_ | _ | _ | ⟨cv, caps⟩ | _ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv caps)

theorem suHead_ind (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (targs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel wta).run st = .ok (targs, st)) {m : Mem}
    (hP : PinsFull m st.pins) (uslen : Nat) (hvl : st.store.lss.viewLen us' = some uslen) :
    (suHeadT r fe depth b wta).run st =
      (if caps.unitlike = true ∧ st.pins.reserved.contains T = false ∧
          targs.length = caps.unitParams ∧ uslen = cvT.levelParams.length then
        suTailT r depth b wta
      else pure false).run st := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    hargs, reservedBasisNames_run hP, viewLsLen_run, hvl]

end headRuns

/-! ## `struct_unit_tail` -/

/-- **`struct_unit_tail` refines `suTailT`, both outcomes**: the errors are the `infer_io`, `whnf`
and `defeq` slots'. -/
@[refines_part ConRon.Arena.structUnitCert "b's type against a's (suTailT)"]
theorem sut_ref (p : Prog) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    RefE (KnotUpToE p n) (sutE p (n + 1) s₀.mem mode vis d b wta)
      (suTailT (coreKnot (decMode mode) fe id F) d.toNat (decE b) (decE wta)) a₀
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
  simp only [sutE.k_whnf, isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]
  by_cases h6 : tagW (r₂.headD 0) = 6
  · simp only [h6, decide_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl hw0)
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  rw [← bind_pure ((coreKnot (decMode mode) fe id F).defeq _ _ _)]
  exact RefE.bind_callE (fun _ => rfl) (hK.defeq F _ _ dn vis fe M₂ eb mode d wta _ hF hn hs₂ hwta hh2)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d wta _ hF hn
      hs₂ hwta hh2)
    fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩

/-! ## `struct_unit_head` -/

/-- The tests of `struct_unit_head`, all passed. -/
def uhOK (ul up lpn tn uslen : Word) (r : List Word) : Prop :=
  ul ≠ 0 ∧ r.headD 0 = 0 ∧ tn = up ∧ uslen = lpn

/-- **`struct_unit_head` refines `suHeadT`, both outcomes** (the top put back): the errors are
`struct_unit_tail`'s. -/
@[refines_part ConRon.Arena.structUnitCert "a's type's head, family and spine (suHeadT)"]
theorem suh_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    RefE (KnotUpToE p n) (suhE p (n + 1) s₀.mem mode vis d b wta)
      (suHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decE wta)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hR := hS.arena.base
  simp only [suhE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppFn_callW hq.leaf hR hwta h)
    fun r₁ m₁ ⟨e1, hh, hgaf⟩ => ?_
  subst e1
  dsimp only [suhE.k_get_app_fn]
  generalize r₁.headD 0 = h at hh hgaf
  by_cases h3 : tagW h ≠ 3
  · rw [ite_eq_left h3]
    exact RefE.ret (suHead_nonconst _ fe _ _ _ a₀ _ hgaf (by rw [decE_tag_const_beq _ hh]; simpa using h3))
      (CorePost.ret hS rfl hw0)
  rw [ite_eq_right h3]
  have h3' : tagW h = 3 := by simpa using h3
  refine RefE.abort0 (by decide) fun hsc => ?_
  refine RefE.abort0 (by decide) fun hcc => ?_
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  have hct : ((decE h).tag == ETag.const) = true := by rw [decE_tag_const_beq _ hh]; simp [h3']
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hv
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us2 at huw hv
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env hnw h)
    fun r₂ m₂ ⟨e2, hfind, hfound⟩ => ?_
  subst e2
  dsimp only [suhE.k_env_find]
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact RefE.ret (suHead_other _ fe _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => by rw [hnone] at e; cases e)) (CorePost.ret hS rfl hw0)
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK hci (erecP_ext _) hS.erec
  by_cases h4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) ≠ 3
  · rw [ite_eq_left h4]
    exact RefE.ret (suHead_other _ fe _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => hind.2 h4 cv caps (by rw [hfind'] at e; exact Option.some.inj e)))
      (CorePost.ret hS rfl hw0)
  rw [ite_eq_right h4]
  obtain ⟨cvT, caps, hci_eq⟩ := hind.1 (by simpa using h4)
  rw [hci_eq] at hci
  have hIR := decCI_indCaps hci (erecP_ext _) hS.erec
  -- the type's spine, the top put back
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppArgs_callW hq.leaf.core.spine hS hwta h)
    fun r₃ m₃ ⟨hf3, hg3, _, _, targs, hargs, hsp⟩ => ?_
  simp only [suhE.k_get_app_args]
  obtain ⟨hS₃, hK₃⟩ := hS.restoreTop' hf3 hg3
  have hlen : targs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  -- `ls_node`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW
    (s₀ := ⟨m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136), Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn n ⟨m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136), Locals.init []⟩
      us2) h) fun r₄ m₄ ⟨t₄, ht₄, ht₄s, hne, hr₄⟩ => ?_
  have em₄ : m₄ = m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136) := by rw [← ht₄, ht₄s]
  rw [hr₄] at hne
  have hvl := defeq_lsNodeW_viewLen hS₃.arena.base huw hne
  rw [← hr₄] at hvl
  subst em₄
  dsimp only [suhE.k_ls_node]
  -- `reserved_contains`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => reservedContains_callW hc hS₃ hnw h)
    fun r₅ m₅ ⟨hA₅, hr₅⟩ => ?_
  obtain ⟨M₅, hS₅, hK₅, hSt₅⟩ : CoreAfter dn s₀.mem m₅ a₀ vis fe M eb := by
    obtain ⟨M', hS', hK', hSt'⟩ := hA₅
    exact ⟨M', hS', hK', hK₃.trans hSt'⟩
  have hlpT : cvT.levelParams.length = (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3)).toNat :=
    hslice?_length hIR.lp
  have hiff : (caps.unitlike = true ∧ a₀.pins.reserved.contains (decI k) = false ∧
      targs.length = caps.unitParams ∧ (r₄.tail.headD 0).toNat = cvT.levelParams.length) ↔
      uhOK (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 9)) (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 10))
        (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3)) (r₃.tail.headD 0) (r₄.tail.headD 0) r₅ := by
    unfold uhOK
    rw [hIR.unitlike, ← hr₅, hlen, hIR.unitParams, hlpT]
    simp only [decBool, bne_iff_ne, ne_eq, bne_eq_false_iff_eq, UInt64.toNat_inj]
  refine RefE.of_run_eq (suHead_ind _ fe _ _ _ a₀ _ hgaf _ _ hct hv cvT caps
    (by rw [hfind', hci_eq]) targs hargs hS.pins _ hvl) ?_
  dsimp only [suhE.k_reserved_contains_w]
  by_cases hok : uhOK (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 9))
      (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 10)) (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3))
      (r₃.tail.headD 0) (r₄.tail.headD 0) r₅
  · obtain ⟨o1, o2, o3, o4⟩ := hok
    rw [ite_eq_left (hiff.mpr ⟨o1, o2, o3, o4⟩)]
    simp only [o1, o2, o3, o4, ne_eq, not_true_eq_false, ↓reduceIte]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ N =>
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (Nat.le_succ N)) rfl
      (fun _ _ _ h => ⟨CoreAfter.comp hK₅ hSt₅ h.after, h.res, h.valid⟩)
      (sut_ref p N (hk.mono (Nat.le_succ N)) F ⟨m₅, Locals.init []⟩ a₀ dn vis fe M₅ eb mode d b wta
        (by omega) (by omega) ⟨hS₅, hs.mode4, hs.eb_mode⟩ hb hwta)
  · rw [ite_eq_right (fun h => hok (hiff.mp h))]
    have hl : RefE (KnotUpToE p (n + 1)) (.ok ([0], m₅) : Except Err (List Word × Mem))
        (pure false : AM Bool) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) :=
      RefE.ret rfl ⟨⟨M₅, hS₅, hK₅, hSt₅⟩, rfl, hw0⟩
    unfold uhOK at hok
    by_cases o1 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 9) = 0
    · rw [ite_eq_left o1]; exact hl
    rw [ite_eq_right o1]
    by_cases o2 : r₅.headD 0 ≠ 0
    · rw [ite_eq_left o2]; exact hl
    rw [ite_eq_right o2]
    by_cases o3 : r₃.tail.headD 0 ≠ rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 10)
    · rw [ite_eq_left o3]; exact hl
    rw [ite_eq_right o3]
    by_cases o4 : r₄.tail.headD 0 ≠ rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3)
    · rw [ite_eq_left o4]; exact hl
    exact absurd ⟨o1, by simpa using o2, by simpa using o3, by simpa using o4⟩ hok

/-! ## `struct_unit_cert` -/

/-- **`struct_unit_cert` refines `structUnitCert`, both outcomes**: the errors are the `infer_io`,
`whnf` slots' and `struct_unit_head`'s. -/
theorem suc_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (sucE p (n + 1) s₀.mem mode vis d a b)
      (structUnitCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [sucE]
  rw [structUnitCert_eq]
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [sucE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁ h₁.resOk)
    (fun (hkE : KnotUpToE p n) => (hkE n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d _ hF hn hs₁
      h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [sucE.k_whnf]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (suh_ref p hq hc N (hk.mono (Nat.le_succ N)) F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d b
      (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb h₂.resOk)

/-- **`struct_unit_cert` refines `structUnitCert`** at the knot (`suc_ref`'s ok half). -/
@[refines ConRon.Arena.structUnitCert]
theorem suCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (sucE_spec p hq.sunit hq.suHead hq.suTail (n + 1) s₀ mode vis d a b)
    (suc_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
