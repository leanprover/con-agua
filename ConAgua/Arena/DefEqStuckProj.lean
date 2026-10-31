import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `ldpr_exit`, `lazy_delta_proj_reduction`, `defeq_proj_pair` (lane `defeq`, helper `defeq-top`)

The projection loop (`lazyDeltaProjReduction`) as a named block (`ldprLoopB`): one
`lazy_delta_step` per iteration, the exit on a verdict its own function (`ldprExitT`). The
unified model by L fuel (`ldprE`) refines the twin's loop, both outcomes, at every twin fuel
`K + 1 ≥` the L fuel (`ldpr_ref`, the shape of lane `whnf`'s `coreLoop_ref`); the twin's budget is
`2^62`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin -/

/-- The projection loop's exit on a verdict (`.eq`, or the projections tried on both sides). -/
def ldprExitT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (sn : NIdx)
    (i : Nat) (a b : EIdx) : DeltaStepA → AM Bool
  | .cont _ _ => pure false
  | .eq => pure true
  | .diff | .unknown => do
    match ← reduceProjCore mode r fe depth sn i a with
    | some x =>
      match ← reduceProjCore mode r fe depth sn i b with
      | some y => r.defeq depth x y
      | none => r.defeq depth a b
    | none => r.defeq depth a b

/-! ## `ldpr_exit` -/

/-- **`reduce_proj_core`'s error spec** (whnf family; the error half of `ReduceProjCoreH`). -/
def ReduceProjCoreE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d sn i c : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW sn → HW c →
    CoreSpecE p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) s₀ a₀

/-- **What `ldpr_exit`'s errors claim from**: the `defeq` slot's and `reduce_proj_core`'s. -/
structure ExitG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  rpc : ReduceProjCoreE p

/-- **`ldpr_exit`'s model, both outcomes** (generated; `reduce_proj_core` and the `defeq` slot
through their runs). -/
l_model exE_spec (p : Prog) (hf : p.lookup "ldpr_exit" = some ldprExitL)
  fns [hf ↦ exE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified

theorem decOptR_someS {r : List Word} (h : r.headD 0 ≠ 0) : decOptR r = some (decE (r.tail.headD 0)) := by
  simp only [decOptR, decOpt, h, ↓reduceIte]
theorem decOptR_noneS {r : List Word} (h : r.headD 0 = 0) : decOptR r = none := by
  simp only [decOptR, decOpt, h, ↓reduceIte]

theorem decDS_zero {r : List Word} (h : r.headD 0 = 0) :
    decDSs r = .cont (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) := by
  unfold decDSs; rw [ite_eq_left h]

theorem decDS_nz {r : List Word} (h : r.headD 0 ≠ 0) : decDSs r = decDSs [r.headD 0] := by
  unfold decDSs
  show (if r.headD 0 = 0 then _ else _) = (if r.headD 0 = 0 then _ else _)
  rw [ite_eq_right h, ite_eq_right h]
  rfl

theorem decDS_ne_cont {r : List Word} (h : r.headD 0 ≠ 0) (a b : EIdx) : decDSs r ≠ .cont a b := by
  unfold decDSs; rw [ite_eq_right h]
  split
  · exact fun e => by cases e
  split
  · exact fun e => by cases e
  · exact fun e => by cases e

/-- **`ldpr_exit` refines `ldprExitT`, both outcomes**, on a verdict word `k ≠ 0`: the errors are
`reduce_proj_core`'s and the `defeq` slot's. -/
theorem ex_ref (p : Prog) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d sn i a b k : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a) (hb : HW b)
    (hk0 : k ≠ 0) :
    RefE (ExitG p n) (exE p (n + 1) s₀.mem mode vis d sn i a b k)
      (ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) (decDSs [k])) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hdef : ∀ (st : AState) (m : Mem) (M' : ModeMaps) (x y : Word), CoreS dn m st vis fe M' eb →
      HW x → HW y →
      RefE (ExitG p n) (exE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m))
        ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) st
        (CorePost decBool dn m vis fe M' eb ResH) := by
    intro st m M' x y hS' hx hy
    have hs' : SlotPre ⟨m, Locals.init []⟩ st dn vis fe M' eb mode := ⟨hS', hs.mode4, hs.eb_mode⟩
    rw [← bind_pure ((coreKnot (decMode mode) fe id F).defeq _ _ _)]
    exact RefE.bind_callE (fun _ => rfl) ((hk n (Nat.le_refl _)).defeq F _ st dn vis fe M' eb mode d x y hF hn
        hs' hx hy)
      (fun (hG : ExitG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ st dn vis fe M' eb mode d x y hF hn hs'
        hx hy)
      fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩
  simp only [exE]
  by_cases h1 : k = 1
  · rw [ite_eq_left h1, show decDSs [k] = .eq by simp [decDSs, h1]]
    exact RefE.ret rfl (CorePost.ret hS rfl hw1)
  rw [ite_eq_right h1]
  have hst : decDSs [k] = (if k = 2 then .diff else .unknown) := by
    unfold decDSs; simp [hk0, h1]
  have hbody : ∀ st, (st = DeltaStepA.diff ∨ st = DeltaStepA.unknown) →
      ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) st =
      (do match ← reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
            (decI sn) i.toNat (decE a) with
          | some x =>
            match ← reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
                (decI sn) i.toNat (decE b) with
            | some y => (coreKnot (decMode mode) fe id F).defeq d.toNat x y
            | none => (coreKnot (decMode mode) fe id F).defeq d.toNat (decE a) (decE b)
          | none => (coreKnot (decMode mode) fe id F).defeq d.toNat (decE a) (decE b)) := by
    rintro st (rfl | rfl) <;> rfl
  rw [hbody _ (by rw [hst]; split <;> simp)]
  cases n with
  | zero => exact RefE.callE_zero (fun _ => rfl)
  | succ n' =>
  refine RefE.bind_callE (fun _ => rfl) (hc.reduceProjCore n' (hk.mono (by omega)) F (by omega) (by omega)
      s₀ a₀ dn vis fe M eb mode d sn i a hs hsn ha)
    (fun hG => hG.rpc n' (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis
      fe M eb mode d sn i a hs hsn ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [exE.k_reduce_proj_core]
  by_cases f1 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left f1, decOptR_someS f1]
    have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
    refine RefE.bind_callE (fun _ => rfl) (hc.reduceProjCore n' (hk.mono (by omega)) F (by omega)
        (by omega) _ _ dn vis fe M₁ eb mode d sn i b hs₁ hsn hb)
      (fun hG => hG.rpc n' (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega) _ _ dn
        vis fe M₁ eb mode d sn i b hs₁ hsn hb)
      fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
    dsimp only [exE.k_reduce_proj_core_2]
    by_cases f2 : r₂.headD 0 ≠ 0
    · rw [ite_eq_left f2, decOptR_someS f2]
      exact hdef _ m₂ M₂ _ _ hS₂ h₁.resOk.2 h₂.resOk.2
    · rw [ite_eq_right f2, decOptR_noneS (by simpa using f2)]
      exact hdef _ m₂ M₂ _ _ hS₂ ha hb
  · rw [ite_eq_right f1, decOptR_noneS (by simpa using f1)]
    exact hdef _ m₁ M₁ _ _ hS₁ ha hb

/-- **`ldpr_exit` refines `ldprExitT`** on a verdict word `k ≠ 0` (`ex_ref`'s ok half). -/
@[refines_part ConRon.Arena.lazyDeltaProjReduction "the exit on a verdict (ldprExitT)"]
theorem ldprExit_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d sn i a b k : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a) (hb : HW b)
    (hk0 : k ≠ 0) :
    CoreSpec p (n + 1) "ldpr_exit" [mode, vis, d, sn, i, a, b, k]
      (ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) (decDSs [k])) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (exE_spec p hq.ldprExit (n + 1) s₀ mode vis d sn i a b k)
    (ex_ref p hc n hk F s₀ a₀ dn vis fe M eb mode d sn i a b k hF hn hs hsn ha hb hk0)

/-! ## The loop -/

/-- **`lazy_delta_proj_reduction`'s model, both outcomes** (the loop `ldprE.loop1`: one
`lazy_delta_step` run per iteration, a final `ldpr_exit`, both `callE`). -/
l_model ldpr_specE (p : Prog) (hf : p.lookup "lazy_delta_proj_reduction" = some lazyDeltaProjReductionL)
  fns [hf ↦ ldprE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified

/-- **What the projection loop's errors claim from**: `lazy_delta_step`'s claims at every L fuel up
to `n` (its refinement is outside the stuck side), the `defeq` slot's and `reduce_proj_core`'s
(through `ldpr_exit`'s refinement). -/
structure LdprG (p : Prog) (n : Nat) : Prop where
  step : ∀ j, j ≤ n → ∀ (F : Nat), j ≤ F → j ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
      d.toNat < 2 ^ 63 →
      CoreSpecE p (j + 1) "lazy_delta_step" [mode, vis, d, a, b]
        (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        s₀ a₀
  knot : KnotUpToE p n
  rpc : ReduceProjCoreE p

theorem LdprG.mono {p : Prog} {n n' : Nat} (h : LdprG p n) (hn : n' ≤ n) : LdprG p n' :=
  ⟨fun j hj => h.step j (by omega), h.knot.mono hn, h.rpc⟩

/-- **The projection loop refines `lazyDeltaProjReduction`, both outcomes**, at every twin loop
fuel `K + 1 ≥ k`. -/
theorem ldpr_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d sn i : Word) (hmode : mode < 4) (hsn : HW sn) (hd : d.toNat < 2 ^ 63) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (eb x y : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW x → HW y →
      RefE (LdprG p n) (ldprE.loop1 p k m mode vis d sn i x y)
        (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
          (decI sn) i.toNat K (decE x) (decE y)) a
        (fun v y' a' => CorePost decBool dn m vis fe MM eb ResH ([v.1], v.2) y' a') := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _
    unfold ldprE.loop1; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkn K hK m a MM eb x y hS heb hx hy
    rw [ldprE.loop1.arm1 _ _ _ _ _ _ _ _ _ _ rfl]
    cases k with
    | zero => exact RefE.callE_zero (fun _ => ldprE.k_lazy_delta_step.none ..)
    | succ j =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hs : SlotPre ⟨m, Locals.init []⟩ a dn vis fe MM eb mode := ⟨hS, hmode, heb⟩
    rw [lazyDeltaProjReduction]
    refine RefE.bind_callE (fun _ => ldprE.k_lazy_delta_step.none ..)
      (hc.lazyDeltaStep j (hk.mono (by omega)) F (by omega) (by omega) _ a dn vis fe MM eb mode d x y hs
        hx hy hd)
      (fun hG => hG.step j (by omega) F (by omega) (by omega) _ a dn vis fe MM eb mode d x y hs hx hy hd)
      fun r m₁ _ h₁ => RefE.after_core (w := fun (v : Word × Mem) => ([v.1], v.2)) h₁ fun M₁ hS₁ _ => ?_
    by_cases h0 : r.headD 0 = 0
    · rw [ldprE.k_lazy_delta_step.arm2 _ _ _ _ _ _ _ _ _ _ _ h0, decDS_zero h0]
      exact ih (by omega) K' (by omega) m₁ _ M₁ eb _ _ hS₁ heb h₁.resOk.2.1 h₁.resOk.2.2
    rw [ldprE.k_lazy_delta_step.arm1 _ _ _ _ _ _ _ _ _ _ _ h0]
    refine RefE.of_run_eq (T' := ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
      (decI sn) i.toNat (decE x) (decE y) (decDSs [r.headD 0]) >>= pure) (by
        rw [bind_pure, ← decDS_nz h0]
        rcases hd : decDSs r with _ | _ | _ | _ <;> first | rfl | exact absurd hd (decDS_ne_cont h0 _ _)) ?_
    have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hmode, heb⟩
    refine RefE.bind_callE (fun _ => ldprE.k_ldpr_exit.none ..)
      (ldprExit_refines p hq hc j (hk.mono (by omega)) F _ _ dn vis fe M₁ eb mode d sn i x y (r.headD 0)
        (by omega) (by omega) hs₁ hsn hx hy h0)
      (fun hG => RefE.coreSpecE (exE_spec p hq.ldprExit (j + 1) _ mode vis d sn i x y (r.headD 0)) trivial
        ⟨hG.knot.mono (by omega), hG.rpc⟩ (ex_ref p hc j (hk.mono (by omega)) F _ _ dn vis fe M₁ eb mode d
          sn i x y (r.headD 0) (by omega) (by omega) hs₁ hsn hx hy h0))
      fun r' m₂ _ h₂ => ?_
    rw [ldprE.k_ldpr_exit.arm1]
    exact RefE.after_core (w := fun (v : Word × Mem) => ([v.1], v.2)) h₂ fun M₂ hS₂ _ =>
      RefE.ret rfl (CorePost.ret hS₂ rfl h₂.resOk)

/-- `lazy_delta_proj_reduction` from its run, both outcomes (`ldpr_ref` at the call's fuel). -/
theorem ldpr_refC (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d sn i a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a)
    (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (LdprG p n) (ldprE p (n + 1) s₀.mem mode vis d sn i a b)
      (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K (decE a) (decE b)) a₀
      (fun v y a' => CorePost decBool dn s₀.mem vis fe M eb ResH ([v.1], v.2) y a') := by
  rw [ldprE.arm1]
  exact ldpr_ref p hq hc n hk F hF hn dn vis fe mode d sn i hs.mode4 hsn hd (n + 1) (Nat.le_refl _) K
    (by omega) s₀.mem a₀ M eb a b hs.rel hs.eb_mode ha hb

/-- **`lazy_delta_proj_reduction` refines `lazyDeltaProjReduction`** at every twin loop fuel
`K ≥ n` (the twin's `defeqLoopFuel` is `2^62`; `ldpr_refC`'s ok half). -/
@[refines ConRon.Arena.lazyDeltaProjReduction]
theorem ldpr_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d sn i a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a)
    (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_delta_proj_reduction" [mode, vis, d, sn, i, a, b]
      (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K (decE a) (decE b)) decBool s₀ a₀ dn vis fe M eb :=
  CoreSpec.of_refE (w := fun (v : Word × Mem) => ([v.1], v.2))
    (ldpr_specE p hq.ldpr (n + 1) s₀ mode vis d sn i a b)
    (ldpr_refC p hq hc n hk F K hF hK hn s₀ a₀ dn vis fe M eb mode d sn i a b hs hsn ha hb hd)
    fun _ _ => ⟨rfl, by simp [decBool], id⟩

/-! ## `defeq_proj_pair` -/

/-- **`defeq_proj_pair`'s model, both outcomes** (generated; the projection loop by its unified
model). -/
l_model ppE_spec (p : Prog) (hf : p.lookup "defeq_proj_pair" = some defeqProjPairL)
    (hl : p.lookup "lazy_delta_proj_reduction" = some lazyDeltaProjReductionL)
  fns [hf ↦ ppE list]
  specs [ldpr_specE p hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified

section ppRuns
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx)
  (st : AState)

theorem pp_no (h : (a.tag == ETag.proj && b.tag == ETag.proj) = false) :
    (defeqProjPair mode r fe depth a b).run st = .ok (false, st) := by
  simp only [defeqProjPair, h, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem pp_both (h : (a.tag == ETag.proj && b.tag == ETag.proj) = true) (s₁ s₂ : NIdx) (i₁ i₂ : Nat)
    (e₁ e₂ : EIdx) (hva : st.store.view a = some (.proj s₁ i₁ e₁))
    (hvb : st.store.view b = some (.proj s₂ i₂ e₂)) :
    (defeqProjPair mode r fe depth a b).run st =
      (if (s₁ == s₂ && i₁ == i₂) = true then
        lazyDeltaProjReduction mode r fe depth s₁ i₁ defeqLoopFuel e₁ e₂
      else pure false).run st := by
  simp only [defeqProjPair, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb,
    except_ok_bind]

end ppRuns

/-- **`defeq_proj_pair` refines `defeqProjPair`, both outcomes**: the errors are the projection
loop's. -/
theorem pp_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hd : d.toNat < 2 ^ 63) :
    RefE (LdprG p n) (ppE p (n + 1) s₀.mem mode vis d a b)
      (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hR := hS.arena.base
  have htag : ∀ h : Word, HW h → ((decE h).tag == ETag.proj) = decide (h >>> 28 = 9) :=
    fun h hh => tag_beq_w _ hh 9 (by decide) ETag.proj rfl 9 rfl
  have hfalse : (((decE a).tag == ETag.proj && (decE b).tag == ETag.proj) = false) →
      RefE (LdprG p n) (.ok ([0], s₀.mem) : Except Err (List Word × Mem))
        (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := fun hno =>
    RefE.ret (pp_no _ _ fe _ _ _ a₀ hno) (CorePost.ret hS rfl hw0)
  simp only [ppE]
  by_cases g1 : a >>> 28 ≠ 9
  · rw [ite_eq_left g1]
    exact hfalse (by rw [htag a ha]; simp [g1])
  rw [ite_eq_right g1]
  by_cases g2 : b >>> 28 ≠ 9
  · rw [ite_eq_left g2]
    exact hfalse (by rw [htag a ha, htag b hb]; simp [g2])
  rw [ite_eq_right g2]
  have g1' : a >>> 28 = 9 := by simpa using g1
  have g2' : b >>> 28 = 9 := by simpa using g2
  refine RefE.abort0 (by rfl) fun c1 => ?_
  refine RefE.abort0 (by rfl) fun c2 => ?_
  refine RefE.abort0 (by rfl) fun c3 => ?_
  refine RefE.abort0 (by rfl) fun c4 => ?_
  obtain ⟨hva, hx1, hx3⟩ := view_proj s₀.mem a₀ hR a ha ⟨c1, by simpa using c2⟩ g1'
  obtain ⟨hvb, hy1, hy3⟩ := view_proj s₀.mem a₀ hR b hb ⟨c3, by simpa using c4⟩ g2'
  have hboth : ((decE a).tag == ETag.proj && (decE b).tag == ETag.proj) = true := by
    rw [htag a ha, htag b hb]; simp [g1', g2']
  refine RefE.of_run_eq (pp_both _ _ fe _ _ _ a₀ hboth _ _ _ _ _ _ hva hvb) ?_
  generalize tfld s₀.mem PROJ (tierW a) (idxW a) 0 = x1 at hx1 ⊢
  generalize tfld s₀.mem PROJ (tierW b) (idxW b) 0 = y1 at hy1 ⊢
  generalize tfld s₀.mem PROJ (tierW a) (idxW a) 1 = x2
  generalize tfld s₀.mem PROJ (tierW b) (idxW b) 1 = y2
  generalize tfld s₀.mem PROJ (tierW a) (idxW a) 2 = x3 at hx3 ⊢
  generalize tfld s₀.mem PROJ (tierW b) (idxW b) 2 = y3 at hy3 ⊢
  by_cases e1 : x1 ≠ y1
  · rw [ite_eq_left e1]
    have : ((decI x1 : NIdx) == decI y1 && x2.toNat == y2.toNat) = false := by
      rw [decI_beq _ _ hx1 hy1]; simp [e1]
    rw [this]
    exact RefE.ret rfl (CorePost.ret hS rfl hw0)
  rw [ite_eq_right e1]
  by_cases e2 : x2 ≠ y2
  · rw [ite_eq_left e2]
    have : ((decI x1 : NIdx) == decI y1 && x2.toNat == y2.toNat) = false := by
      have : x2.toNat ≠ y2.toNat := fun e => e2 (UInt64.toNat_inj.mp e)
      simp [this]
    rw [this]
    exact RefE.ret rfl (CorePost.ret hS rfl hw0)
  rw [ite_eq_right e2]
  have e1' : x1 = y1 := by simpa using e1
  have e2' : x2 = y2 := by simpa using e2
  subst e1' e2'
  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ k =>
  have H := ldpr_refC p hq hc k (hk.mono (by omega)) F defeqLoopFuel (by omega)
    (by unfold defeqLoopFuel; omega) (by omega) s₀ a₀ dn vis fe M eb mode d x1 x2 x3 y3 hs hx1 hx3 hy3 hd
  exact RefE.tailMap_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega)) rfl
    (fun _ _ _ h => h) H

/-- **`defeq_proj_pair` refines `defeqProjPair`** at the knot (`pp_ref`'s ok half). -/
@[refines ConRon.Arena.defeqProjPair]
theorem projPair_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "defeq_proj_pair" [mode, vis, d, a, b]
      (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ppE_spec p hq.projPair hq.ldpr (n + 1) s₀ mode vis d a b)
    (pp_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd)

end L.Arena
