module

import ConAgua.Verdict.DefEqLoopsE
public import ConAgua.Arena.DefEqKnot
import ConAgua.Verdict.DefEqSlotE

@[expose] public section

/-!
# The `defeq` slot's error half one level up, assembled

`KnotAllProg.defeqSlotE_all`: the `defeq` field of the error knot's step (`KnotStepE`),
`∀ n, KnotUpTo p n → KnotUpToE p n → DefeqSlotE p (n + 1)`, from the family's unified refinements
(`defeqSlotE_step`) and the whnf family's claims they take (`DefeqWhnfE`).
-/

open ConRon.Arena

namespace L.Arena

/-- **The whnf family's error claims this family uses** (hypotheses: `reduce_proj_core`'s and
`proof_irrel`'s; `reduce_nat`'s and `defeq_lst`'s are proved here). -/
structure DefeqWhnfE (p : Prog) : Prop where
  reduceProjCore : ReduceProjCoreE p
  proofIrrel : ProofIrrelWE p

section all
variable {p : Prog} (hq : KnotAllProg p) (hw : DefeqWhnfE p) (hnv : closedNV p L.Checker.nvFns = true)

include hq hw hnv in
/-- **The `defeq` slot's error half one level up** (the `defeq` field of `KnotStepE`). -/
theorem KnotAllProg.defeqSlotE_all (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    DefeqSlotE p (n + 1) :=
  defeqSlotE_step p hq.body ⟨KnotAllProg.stuck hq, KnotAllProg.lazy hq⟩ hnv (reduceNatE_of p hq.delta hnv)
    hw.proofIrrel (defeqLst_refinesE p hq.lst) hw.reduceProjCore n hk hkE

end all

end L.Arena
