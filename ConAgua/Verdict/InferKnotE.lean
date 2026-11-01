module

public import ConAgua.Verdict.InferArmsE

@[expose] public section

/-!
# The knot's `infer`, `infer_io` steps, error halves

The error halves of the slots' unified refinements (`isl_ref`, `islo_ref`, `KnotSlot.lean`) over
the bodies' (`ib_ref`, `ibo_ref`, `InferBodyDisp.lean`): `inferSlot_stepE`/`inferIOSlot_stepE`:
`KnotUpTo p n → KnotUpToE p n → InferSlotE p (n + 1)` (resp. `InferIOSlotE`), under the ok step's
program hypotheses (`InferAllProg`), its callees' ok specs (`InferCallees`) and their error claims
(`InferCalleesE`: the verdict closure and `infer_proj`'s).
-/

open ConRon.Arena

namespace L.Arena

/-- **The knot's `infer` slot one level up, error half** (`isl_ref`'s error half). -/
@[refines_part ConRon.Arena.coreKnot "infer (step, verdicts)"]
theorem inferSlot_stepE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) (hcE : InferCalleesE p)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) : InferSlotE p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpecE (islE_spec p hq.knot.infer (n + 1) s₀ mode vis d e) hcE.nv
      ⟨inferBody_refinesE p hq hc hcE.proj hcE.nv n, hkE⟩
      (isl_ref p hq.knot n hk (inferBody_refines p hq hc n) F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he)

/-- **The knot's `inferIO` slot one level up, error half** (`islo_ref`'s error half). -/
@[refines_part ConRon.Arena.coreKnot "inferIO (step, verdicts)"]
theorem inferIOSlot_stepE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hcE : InferCalleesE p) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    InferIOSlotE p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpecE (isloE_spec p hq.knot.inferIO (n + 1) s₀ mode vis d e) hcE.nv
      ⟨inferBodyIO_refinesE p hq hc hcE.proj hcE.nv n, hkE⟩
      (islo_ref p hq.knot n hk (inferBodyIO_refines p hq hc n) F s₀ a₀ dn vis fe MM eb mode d e hF hn
        hs he)

/-- **Both inference slots one level up, error halves.** -/
theorem inferSlots_stepE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hcE : InferCalleesE p) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → InferSlotE p (n + 1) ∧ InferIOSlotE p (n + 1) :=
  fun n hk hkE => ⟨inferSlot_stepE p hq hc hcE n hk hkE, inferIOSlot_stepE p hq hc hcE n hk hkE⟩

end L.Arena
