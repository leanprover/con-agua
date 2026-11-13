module

public import ConAgua.Arena.ErecRd
public import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# The record words the η readers read

An inductive record's level parameters and η cap (`decCI_indCaps`), as words L reads (`RdOK`).
-/

open ConRon.Arena

namespace L.Arena

/-! ## The records -/

/-- **An inductive record's level parameters and η cap.** -/
structure IndRecR (R : Nat → Option Word) (rd : Word → Word) (q : Word) (cv : IConstantVal) (caps : IIndCaps) :
    Prop where
  lp : hslice? R (rd (q + (CI.cv + CV.lpsOff))).toNat (rd (q + (CI.cv + CV.lpsLen))).toNat =
    some cv.levelParams
  eta : caps.eta = (rd (q + (CI.indCaps + Caps.eta)) != 0)

/-- An inductive record decodes to `IndRecR`. -/
theorem decCI_indCaps {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI R q.toNat = some (.indInfo cv caps))  :
    IndRecR R rd q cv caps :=
  ⟨(decCV_rd_ci hR (decCI_indInfo_kind_rd hR h).2).2.2.1, (decCI_indInfo_rd hR h).1⟩

end L.Arena
