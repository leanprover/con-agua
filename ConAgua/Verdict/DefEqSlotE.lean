import ConAgua.Verdict.DefEqBaseE
import ConAgua.Arena.DefEqKnot
import ConAgua.Arena.IndTwin

/-!
# The knot's `defeq` slot and `is_def_eq_core`: their error claims

The error halves of the unified refinements: the `defeq` slot's one level up (`dsl_ref`, at a memo
miss `defeq_body`'s, `body_ref`) and `is_def_eq_core`'s (`ice_ref`, the slot's).
-/

open ConRon.Arena

namespace L.Arena

/-- **The `defeq` slot's error half one level up** (`KnotStepE`'s `defeq` field), from the ok
knot, the error knot up to `n`, and the whnf family's claims `defeq_body`'s callees take. -/
theorem defeqSlotE_step (p : Prog) (hq : DefeqBodyProg p) (hc : DefeqBodyCallees p)
    (hnv : closedNV p L.Checker.nvFns = true) (hrn : ReduceNatE p) (hpi : ProofIrrelWE p)
    (hlst : DefeqLstWE p) (hrpc : ReduceProjCoreE p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) : DefeqSlotE p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d x y hF hn hs hx hy =>
    RefE.coreSpecE (dslE_spec p hq.knot.defeq (n + 1) s₀ mode vis d x y) hnv
      ⟨fun F s₀ a₀ dn vis fe MM eb mode d x y hF hn hs hx hy hk hkE =>
        RefE.coreSpecE (bodyE_spec p hq.body n s₀ mode vis d x y) hnv ⟨hkE, hnv, hrn, hpi, hlst, hrpc⟩
          (body_ref p hq hc n hk F s₀ a₀ dn vis fe MM eb mode d x y hF hn hs hx hy), hkE⟩
      (dsl_ref p hq.knot n hk (defeqBody_refines p hq hc n) F s₀ a₀ dn vis fe MM eb mode d x y hF hn hs
        hx hy)

/-- **`is_def_eq_core`'s error claim under `CoreS`** (`ice_ref`'s error half). -/
theorem isDefEqCore_refinesE (p : Prog) (hp : KnotEntryProg p) (n : Nat) (hd : DefeqSlot p n)
    (hdE : DefeqSlotE p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep x y : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hS : CoreS dn s₀.mem a₀ vis fe M 0) (hx : HW x) (hy : HW y) :
    CoreSpecE p (n + 1) "is_def_eq_core" [vis, dep, x, y]
      (isDefEqCore .verified fe F dep.toNat (decE x) (decE y)) s₀ a₀ :=
  RefE.coreSpecE (iceE_spec p hp.isDefEqCore (n + 1) s₀ vis dep x y) trivial hdE
    (ice_ref p n hd F s₀ a₀ dn vis fe M dep x y hF hn hS hx hy)

end L.Arena

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`is_def_eq_core`'s error claim under `StageT`** (`CoreStubsE.isDefEqCore`'s shape, the error
half of `isDefEqCore_simT`), from the `defeq` slot's refinement and error claim at every fuel. -/
theorem isDefEqCore_stageE {p : Prog} (hp : KnotEntryProg p) (hd : ∀ n, DefeqSlot p n)
    (hdE : ∀ n, DefeqSlotE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep x y : Word), H x → H y →
    ∀ e, callE p n "is_def_eq_core" [vis, dep, x, y] m = .error e →
      ErrClaim (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a e := by
  intro n hn dn vis fe m a hS dep x y hx hy e hc
  refine ErrClaim.of_callE_succ hc fun k hk hc' => ?_
  subst hk
  obtain ⟨M, hC⟩ := hS.core
  exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
    (isDefEqCore_refinesE p hp k (hd k) (hdE k) checkFuel ⟨m, Locals.init []⟩ a dn vis fe M dep x y
      (stage_fuel hn) (by omega) hC (hw_of_h hx) (hw_of_h hy)) hc'

end L.Ind
