import ConAgua.Arena.InferBodySpine
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.InferBodySpineFModels

/-!
# The full-grade application spine (lane `defeq`)

`infer_spine_arg` (one argument: its type, compared with the opened domain by `defeq_arg`),
`infer_spine` (the loop, as `infer_spine_io`'s in `InferBodySpine.lean` with the argument check),
`infer_app`, each with one unified model and one refinement for both outcomes. The twin fragment of
the argument check is `inferSpineArgT`; `spineArg_bind` splits it off the step of `inferSpine`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What the full-grade spine specs need of a program. -/
structure SpineFProg (p : Prog) : Prop where
  arg : p.lookup "infer_spine_arg" = some inferSpineArgL
  spine : p.lookup "infer_spine" = some inferSpineL
  app : p.lookup "infer_app" = some inferAppL

/-! ## `infer_spine_arg` -/

/-- **The argument check of `inferSpine`**, copied: the argument's type, compared with the opened
domain. -/
def inferSpineArgT (r : CoreFnsA) (depth : Nat) (a dom : EIdx) : AM Unit := do
  let ta ← r.infer depth a
  if !(← defeqArg r depth a ta dom) then
    fail (.invalid "application type mismatch")
  else pure ()

/-- `defeq_arg` at every L fuel up to `n + 1`. -/
theorem defeqArg_any (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (he : IsEagerReduceH p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a ta ty : Word), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW ta → HW ty →
    CoreSpec p n "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) decBool
      s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | k + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, ta, ty, hF, hn, hs, ha, hta, hty =>
      defeqArg_refines p hp hkp k he (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a ta ty
        (by omega) (by omega) hs ha hta hty

/-- **`infer_spine_arg` refines the argument check** (`inferSpineArgT`) at the knot, both
outcomes: the argument's type (the `infer` slot), `defeq_arg`'s, a mismatch rejects. -/
theorem isa_ref (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (he : IsEagerReduceH p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a dom : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hdom : HW dom) :
    RefE (InferG p n) (isaE p (n + 1) s₀.mem mode vis d a dom)
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) a₀
      (CorePost (fun _ => ()) dn s₀.mem vis fe M eb ResH) := by
  simp only [isaE, inferSpineArgT]
  rcases c1 : callE p n "infer" [mode, vis, d, a] s₀.mem with e1 | ⟨r₁, m₁⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE ((hG.knot n (Nat.le_refl _)).infer F s₀ a₀ dn
      vis fe M eb mode d a hF hn hs ha) c1
  have h₁ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode d a hF hn hs
    ha) (callW_of_callE c1)
  refine RefE.bind_core (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  simp only [isaE.k_infer]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rcases c2 : callE p n "defeq_arg" [mode, vis, d, a, r₁.headD 0, dom] m₁ with e2 | ⟨r₂, m₂⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (defeqArg_anyE p hp hkp he n hk hG F _ _ dn vis fe M₁ eb mode d a (r₁.headD 0) dom hF hn hs₁ ha
        h₁.2.2.2 hdom) c2
  have h₂ := CoreSpec.of_callW (defeqArg_any p hp hkp he n hk F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode d a (r₁.headD 0) dom hF hn hs₁ ha h₁.2.2.2 hdom) (callW_of_callE c2)
  refine RefE.bind_core (w := id) h₂ (fun M₂ hS₂ _ => ?_)
  simp only [isaE.k_defeq_arg]
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0]
    have hdb : decBool r₂ = false := by simp only [decBool, h0]; rfl
    simp only [hdb, Bool.not_false, ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [ite_eq_right h0]
  have hbt : decBool r₂ = true := by simp only [decBool, bne_iff_ne]; exact h0
  simp only [hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact RefE.ret rfl (CorePost.ret hS₂ rfl (by unfold ResH HW; decide))

/-- **`infer_spine_arg` refines the argument check** (`inferSpineArgT`) at the knot (`isa_ref`'s ok
half). -/
@[refines_part ConRon.Arena.inferSpine "argument check"]
theorem inferSpineArg_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p)
    (hq : SpineFProg p) (he : IsEagerReduceH p) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a dom : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hdom : HW dom) :
    CoreSpec p (n + 1) "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) (fun _ => ())
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (isaE_spec p hq.arg (n + 1) s₀ mode vis d a dom)
    (isa_ref p hp hkp he n hk F hF hn s₀ a₀ dn vis fe M eb mode d a dom hs ha hdom)

/-! ## `infer_spine` -/

/-- `infer_spine_arg` at every L fuel up to `n + 1`. -/
theorem inferSpineArg_any (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a dom : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW dom →
    CoreSpec p n "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) (fun _ => ())
      s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, dom, hs, ha, hdom =>
      inferSpineArg_refines p hp hkp hq he n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis
        fe M eb mode d a dom hs ha hdom

/-- `infer_spine_arg`'s error claim at every L fuel up to `n + 1` (`isa_ref`'s error half). -/
theorem inferSpineArg_anyE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a dom : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW dom →
    CoreSpecE p n "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, dom, hs, ha, hdom =>
      RefE.coreSpecE (isaE_spec p hq.arg (n + 1) s₀ mode vis d a dom) trivial (hG.mono (by omega))
        (isa_ref p hp hkp he n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb mode d
          a dom hs ha hdom)

/-- The argument check inside a step of `inferSpine` is `inferSpineArgT`, then the rest. -/
theorem spineArg_bind {β : Type} (r : CoreFnsA) (depth : Nat) (a dom : EIdx) (K : AM β) :
    (do
      let ta ← r.infer depth a
      if !(← defeqArg r depth a ta dom) then fail (.invalid "application type mismatch")
      else K) = (inferSpineArgT r depth a dom >>= fun _ => K) := by
  simp only [inferSpineArgT, bind_assoc]
  congr; funext ta; congr; funext b
  cases b <;> simp [fail_bindAM]

/-- **The full spine's loop refines `inferSpine`, both outcomes**, by induction on the loop fuel:
a step's argument check (`infer_spine_arg`'s errors), its `whnf` (the slot's) or its non-`∀` type
(a reject); the exit is `spTail_ref`. -/
theorem spLoop_ref (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) (N : Nat) (hk : KnotUpTo p N) (F : Nat)
    (hF : N ≤ F) (hN : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d ao an : Word) (args : Array EIdx) (eb co : Word) (hmode : mode < 4)
    (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) (har₀ : SpineR m₀ ao an args)
    (hco : co = spTop m₀) (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ k, k ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m →
      RefE (InferG p N) (ispE.k_loop1 p N co (ispE.loop1 p k m mode vis d ty ao an co cn i))
        (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args i.toNat) a
        (CorePost decH dn m₀ vis fe M eb ResH) := by
  intro k
  induction k with
  | zero =>
    intro _ m a M ty i cn acc _ _ _ _ _ _ _ _
    rw [ispE.loop1.eq_1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkN m a M ty i cn acc hS ht hacc htop hb hsz hbk hpg
    rw [ispE.loop1.eq_2]
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args := har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    have h0 : (0 : Word).toNat = 0 := rfl
    have hkeep : ∀ {m₂ : Mem}, StackKept m m₂ → (∀ j, j < co → spW m₂ j = spW m₀ j) := by
      intro m₂ hSt j hj
      have hj' : j < spTop m := by
        rw [htop, UInt64.lt_iff_toNat_lt, hadd]
        have := UInt64.lt_iff_toNat_lt.mp hj; omega
      exact (hSt.below j hj').trans (hb j hj)
    by_cases hlt : i < an
    · rw [ite_eq_left hlt]
      have hlt' : i.toNat < args.size := by rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'; rwa [hit] at h
      have hvv : HW (spW m (ao + i)) := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt'); rwa [hit] at h
      have hi1 := succ_toNat_of_lt hlt
      by_cases ht6 : ty >>> 28 = 6
      · -- the ∀ step: the domain opened, the argument checked and pushed
        rw [ite_eq_left ht6]
        by_cases c1 : tierW ty ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
        · rw [ite_eq_left c1]; exact RefE.of_cls0 rfl
        rw [ite_eq_right c1]
        by_cases c2 : tcnt m FORALL (tierW ty) ≤ idxW ty
        · rw [ite_eq_left c2]; exact RefE.of_cls0 rfl
        rw [ite_eq_right c2]
        have hv : viewOK m ty FORALL := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, hdom, hbody⟩ := view_forall m a hS.arena.base ty ht hv ht6
        have hvb := viewBind_forall m a hS.arena.base ty ht hv ht6
        rcases h1 : callW p k "inst_list" [tfld m FORALL (tierW ty) (idxW ty) 0, co, cn, 0] m with
          _ | ⟨r₁, m₁⟩
        · rw [liftE_none, ispE.k_inst_list_2.eq_1]; exact RefE.of_cls0 (by simp)
        rw [liftE_some, ispE.k_inst_list_2.eq_2]
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW (hil k ⟨m, Locals.init []⟩
          a dn vis fe M eb _ co cn 0 acc hS hdom hacc (by rw [hspT]; exact Nat.le_refl _)) h1
        rw [h0] at hok1 hres1 hS₁
        rw [inferSpine]
        simp only [hlt', dite_true, decE_tag_forallE_beq ty ht, ht6, decide_true, ite_true, hxi,
          spineArg_bind]
        refine RefE.bind_right (by rw [viewBind_run', hvb]) ?_
        dsimp only
        refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
        rw [hres1]
        have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hmode, heb⟩
        rcases h2 : callE p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), r₁.headD 0]
            m₁ with e2 | ⟨r₂, m₂⟩
        · rw [ispE.k_infer_spine_arg.eq_1]
          exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
            (inferSpineArg_anyE p hp hkp hq he k (hk.mono (by omega)) (hG.mono (by omega)) F
              (by omega) (by omega) _ _ dn vis fe M₁ eb mode d _ (r₁.headD 0) hs₁ hvv hrw1) h2
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, -, -⟩ := CoreSpec.of_callW (inferSpineArg_any p hp hkp hq he
          k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d _
          (r₁.headD 0) hs₁ hvv hrw1) (callW_of_callE h2)
        refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
        rw [ispE.k_infer_spine_arg.eq_2]
        by_cases g4 : m₂.len64 SPN ≤ co + cn
        · rw [ite_eq_left g4]; exact RefE.of_cls0 rfl
        rw [ite_eq_right g4, ispE.j1.eq_def]
        have g5 := lt_of_not_len64_le hS₂.spn g4
        have hSt12 := hSt₁.trans hSt₂
        have hacc₂ : SpineR m₂ co cn acc :=
          hacc.keep hSt12.size hSt12.below (by rw [hspT]; exact Nat.le_refl _) hspn
        obtain ⟨hacc', htop', hb', hsz', -, hbk', hpg'⟩ := spPush_step hS₂.spn hacc₂ (hkeep hSt12)
          (hSt12.size.trans hsz) (hbk.trans hSt12.bstk) (hpg.trans hSt12.pool) hS₂.ctl136 g5 hvv
        have hS' := hS₂.frame_stk (spnCtl_frame m₂ (co + cn) (spW m (ao + i)) (co + (cn + 1)))
          (by simp) (by simp)
        have hih := ih (by omega) _ _ M₂ _ (i + 1) (cn + 1) _ hS' hbody hacc' htop' hb' hsz' hbk' hpg'
        rw [hi1] at hih
        exact hih.mono fun _ _ _ h =>
          ⟨let ⟨M', hS', hK', hSt'⟩ := h.after; ⟨M', hS', hK₁.trans (hK₂.trans hK'), hSt'⟩,
            h.res, h.valid⟩
      · -- the `whnf` re-entry: the accumulator restarts at `#[a]`
        rw [ite_eq_right ht6]
        have hnfa : ((decE ty).tag == ETag.forallE) = false := by
          rw [decE_tag_forallE_beq ty ht]; simp [ht6]
        rcases h1 : callW p k "inst_list" [ty, co, cn, 0] m with _ | ⟨r₁, m₁⟩
        · rw [liftE_none, ispE.k_inst_list_3.eq_1]; exact RefE.of_cls0 (by simp)
        rw [liftE_some, ispE.k_inst_list_3.eq_2]
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW (hil k ⟨m, Locals.init []⟩
          a dn vis fe M eb ty co cn 0 acc hS ht hacc (by rw [hspT]; exact Nat.le_refl _)) h1
        rw [h0] at hok1 hres1 hS₁
        rw [inferSpine]
        simp only [hlt', dite_true, hnfa, Bool.false_eq_true, ite_false, hxi]
        refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
        rw [hres1]
        have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hmode, heb⟩
        rcases h2 : callE p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
        · rw [ispE.k_whnf.eq_1]
          exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
            ((hG.knot k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
              (by omega) (by omega) hs₁ hrw1) h2
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW ((hk k (by omega)).whnf F
          ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega) hs₁ hrw1)
          (callW_of_callE h2)
        refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
        simp only [decH] at hres2 ⊢
        simp only [hres2]
        rw [ispE.k_whnf.eq_2]
        by_cases g1 : r₂.headD 0 >>> 28 ≠ 6
        · rw [ite_eq_left g1]
          have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = false := by
            rw [decE_tag_forallE_beq _ hrw2]; simpa using g1
          simp only [hfa, Bool.false_eq_true, ↓reduceIte]
          exact fun _ => ErrClaim.fail _ _ rfl
        rw [ite_eq_right g1]
        have g1' : r₂.headD 0 >>> 28 = 6 := by simpa using g1
        by_cases g2 : tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0
        · rw [ite_eq_left g2]; exact RefE.of_cls0 rfl
        rw [ite_eq_right g2]
        by_cases g3 : tcnt m₂ FORALL (tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0)
        · rw [ite_eq_left g3]; exact RefE.of_cls0 rfl
        rw [ite_eq_right g3]
        have hv : viewOK m₂ (r₂.headD 0) FORALL := ⟨g2, UInt64.not_le.mp g3⟩
        obtain ⟨-, hdom, hbody⟩ := view_forall m₂ _ hS₂.arena.base (r₂.headD 0) hrw2 hv g1'
        have hvb := viewBind_forall m₂ _ hS₂.arena.base (r₂.headD 0) hrw2 hv g1'
        have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = true := by
          rw [decE_tag_forallE_beq _ hrw2]; exact decide_eq_true g1'
        simp only [hfa, ite_true]
        refine RefE.bind_right (by rw [viewBind_run', hvb]) ?_
        dsimp only
        rw [spineArg_bind]
        have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hmode, heb⟩
        rcases h3 : callE p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i),
            tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0] m₂ with e3 | ⟨r₃, m₃⟩
        · rw [ispE.k_infer_spine_arg_2.eq_1]
          exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
            (inferSpineArg_anyE p hp hkp hq he k (hk.mono (by omega)) (hG.mono (by omega)) F
              (by omega) (by omega) _ _ dn vis fe M₂ eb mode d _ _ hs₂ hvv hdom) h3
        obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, -⟩ := CoreSpec.of_callW (inferSpineArg_any p hp hkp hq he
          k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d _
          _ hs₂ hvv hdom) (callW_of_callE h3)
        refine RefE.bind_right (AM.run_of_ok _ _ hok3) ?_
        rw [ispE.k_infer_spine_arg_2.eq_2]
        by_cases g4 : m₃.len64 SPN ≤ co
        · rw [ite_eq_left g4]; exact RefE.of_cls0 rfl
        rw [ite_eq_right g4, ispE.j1.eq_def]
        have g5 := lt_of_not_len64_le hS₃.spn g4
        have hSt13 := hSt₁.trans (hSt₂.trans hSt₃)
        have hacc0 := SpineR.empty m₃ co (by omega)
        obtain ⟨hacc', htop', hb', hsz', -, hbk', hpg'⟩ := spPush_step (cn := 0) hS₃.spn hacc0
          (hkeep hSt13) (hSt13.size.trans hsz) (hbk.trans hSt13.bstk) (hpg.trans hSt13.pool)
          hS₃.ctl136 (by simpa using g5) hvv
        have hS' := hS₃.frame_stk (spnCtl_frame m₃ (co + 0) (spW m (ao + i)) (co + (0 + 1)))
          (by simp) (by simp)
        have hih := ih (by omega) (spPush m₃ co 0 (spW m (ao + i))) _ M₃ _ (i + 1) 1 _ hS' hbody hacc'
          htop' hb' hsz' hbk' hpg'
        rw [hi1, show spPush m₃ co 0 (spW m (ao + i)) =
          (m₃.set64 SPN co (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136 (co + 1) by
            simp [spPush, spW]] at hih
        exact hih.mono fun _ _ _ h =>
          ⟨let ⟨M', hS', hK', hSt'⟩ := h.after; ⟨M', hS', hK₁.trans (hK₂.trans (hK₃.trans hK')), hSt'⟩,
            h.res, h.valid⟩
    · rw [ite_eq_right hlt]
      have hnlt : ¬ i.toNat < args.size := by
        rw [har₀.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      refine RefE.of_run_eq (T' := instantiateListFast coreWalkFuel (decE ty) acc 0)
        (by rw [inferSpine, dite_eq_right hnlt]) ?_
      simp only [ispE.k_loop1]
      exact spTail_ref p hil N dn vis fe eb co m₀ hco (k := ispE.k_inst_list p co) (fun _ => rfl)
        (fun _ _ => rfl) m a M ty cn acc hS ht hacc htop hb hsz hbk hpg

/-- **`infer_spine` refines `inferSpine`, both outcomes**, at the knot, the head's type `ty` and the
arguments the slice `(ao, an)` below the top. -/
theorem isp_ref (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (InferG p n) (ispE p (n + 1) s₀.mem mode vis d ty ao an)
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  simp only [ispE]
  by_cases hc : s₀.mem.len64 SPN < rdW (s₀.mem.arr64 CTL) 136
  · rw [ite_eq_left hc]; exact RefE.of_cls0 rfl
  rw [ite_eq_right hc]
  have hcle := len64_not_lt hS.spn hc
  exact spLoop_ref p hp hkp hq he hil n hk F hF hn dn vis fe mode d ao an args eb _ hs.mode4
    hs.eb_mode s₀.mem har rfl hlo (n + 1) (Nat.le_refl _) s₀.mem a₀ M ty 0 0 #[] hS ht
    (SpineR.empty _ _ hcle) (by simp [spTop]) (fun _ _ => rfl) rfl (BKept.refl _) (PoolGrew.refl _)

/-- **`infer_spine` refines `inferSpine`** (`isp_ref`'s ok half). -/
@[refines ConRon.Arena.inferSpine]
theorem inferSpine_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) decH s₀ a₀ dn vis
        fe M eb :=
  RefE.coreSpec (ispE_spec p hq.spine (n + 1) s₀ mode vis d ty ao an)
    (isp_ref p hp hkp hq he hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty ao an args hs ht har hlo)

/-- `infer_spine` at every L fuel up to `n + 1`. -/
theorem inferSpine_any (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) decH s₀ a₀ dn
        vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      inferSpine_refines p hp hkp hq he hil n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis
        fe M eb mode d ty ao an args hs ht har hlo

/-- `infer_spine`'s error claim at every L fuel up to `n + 1` (`isp_ref`'s error half). -/
theorem inferSpine_anyE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p n "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      RefE.coreSpecE (ispE_spec p hq.spine (n + 1) s₀ mode vis d ty ao an) hG.nv (hG.mono (by omega))
        (isp_ref p hp hkp hq he hil n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
          mode d ty ao an args hs ht har hlo)

/-! ## `infer_app` -/

/-- `inferBody`'s `.app` arm is `inferApp`. -/
@[refines_part ConRon.Arena.inferBody "app"]
theorem inferBody_app (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (f x : EIdx) (hv : a.store.view e = some (.app f x)) :
    (inferBody r fe d e).run a = (inferApp r fe d e).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

/-- **`infer_app` refines `inferApp`, both outcomes**, at the knot, at an `app` handle: the head's
type (the `infer` slot), the spine's (`infer_spine`); `head_and_args` claims nothing. -/
theorem a_ref (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (hsp : SpineProg p) (he : IsEagerReduceH p) (hil : InstListOK p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hHe : HW e)
    (h4 : e >>> 28 = 4) :
    RefE (InferG p n) (aE p (n + 1) s₀.mem mode vis d e)
      (inferApp (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  simp only [aE]
  rcases hc1 : callW p n "head_and_args" [e] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [aE.k_head_and_args]
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, hha, hxs⟩ := triple_of_callW
    (headAndArgs_app p hsp n s₀ a₀ hS.arena.base e hHe h4 hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop1 hxs
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hb1 := hxs.bound
  have hspn₁ := hS₁.spn
  have hadd : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, hadd]
  simp only [inferApp]
  refine RefE.bind_right hha ?_
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rcases hc2 : callE p n "infer" [mode, vis, d, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).infer F _ a₀ dn vis fe M eb mode d (r₁.headD 0) hF hn hs₁ hhw) hc2
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW (hK.infer F ⟨m₁, Locals.init []⟩
    a₀ dn vis fe M eb mode d (r₁.headD 0) hF hn hs₁ hhw) (callW_of_callE hc2)
  refine RefE.bind_right (by rw [AM.run_of_ok _ _ hok2, hres2]) ?_
  simp only [aE.k_infer]
  have hxs₂ : SpineR m₂ (r₁.tail.headD 0) (r₁.tail.tail.headD 0) xs :=
    hxs.keep hSt₂.size hSt₂.below (by rw [htopN]; exact Nat.le_refl _) hspn₁
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  have hlo₂ : (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat ≤ (spTop m₂).toNat := by
    rw [hSt₂.1, htopN]; exact Nat.le_refl _
  rcases hc3 : callE p n "infer_spine" [mode, vis, d, r₂.headD 0, r₁.tail.headD 0,
      r₁.tail.tail.headD 0] m₂ with e3 | ⟨r₃, m₃⟩
  · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (inferSpine_anyE p hp hkp hq he hil
      n hk hG F hF hn _ _ dn vis fe M₂ eb mode d (r₂.headD 0) _ _ xs hs₂ hrw2 hxs₂ hlo₂) hc3
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW (inferSpine_any p hp hkp hq he
    hil n hk F hF hn ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0) _ _ xs hs₂ hrw2 hxs₂
    hlo₂) (callW_of_callE hc3)
  simp only [aE.k_infer_spine]
  exact RefE.ret (AM.run_of_ok _ _ hok3) ⟨⟨M₃, hS₃.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp)
    (by simp), hK₂.trans hK₃, StackKept.restoreG' (hg₁.trans (hSt₂.trans hSt₃).toGrew)⟩, hres3, hrw3⟩

/-- **`infer_app` refines `inferApp`** at the knot, at an `app` handle (`a_ref`'s ok half). -/
@[refines ConRon.Arena.inferApp]
theorem inferApp_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (hsp : SpineProg p) (he : IsEagerReduceH p) (hil : InstListOK p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hHe : HW e)
    (h4 : e >>> 28 = 4) :
    CoreSpec p (n + 1) "infer_app" [mode, vis, d, e]
      (inferApp (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (aE_spec p hq.app (n + 1) s₀ mode vis d e)
    (a_ref p hp hkp hq hsp he hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d e hs hHe h4)

end L.Arena
