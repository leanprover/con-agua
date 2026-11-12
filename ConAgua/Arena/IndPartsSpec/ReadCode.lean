module

public import ConAgua.Arena.IndIface
public import ConAgua.Arena.Reasons

@[expose] public section

/-!
# The reader's answers: a reason code beside the value

con-ron's reader (`readBlock`, `blockCounts`, `blockMemberCounts`) answers an `Except CheckError _`
whose every error is `.invalid`; L's answers a code first: `0` and the value after it, or the
reason (`Reasons.lean`, a reject: class `1`) of the twin's message. `ExcR R x r m`: the twin's
answer `x` as L's words `r` (at the memory `m`).
-/

namespace L.Ind

open ConRon.Arena
open L.Arena

/-- **A reader's reason**: a nonzero code of the reject class. -/
def RCode (w : Word) : Prop := w ≠ 0 ∧ w &&& 3 = 1

/-- **An `Except` of the reader as L's answer `r`**: `.ok v` is the code `0` and `R v` of the
words after it; an error is a reason (`RCode`) and the twin's error invalid. -/
def ExcR {α : Type} (R : α → List Word → Mem → Prop) : Except CheckError α → List Word → Mem → Prop
  | .ok v, r, m => r.headD 0 = 0 ∧ R v r.tail m
  | .error ce, r, _ => RCode (r.headD 0) ∧ ∃ s, ce = .invalid s

theorem ExcR.ok_iff {α : Type} {R : α → List Word → Mem → Prop} {x : Except CheckError α}
    {r : List Word} {m : Mem} (h : ExcR R x r m) : r.headD 0 = 0 ↔ ∃ v, x = .ok v := by
  cases x with
  | ok v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => h.1⟩
  | error e => exact ⟨fun h0 => absurd h0 h.1.1, fun ⟨_, h⟩ => by cases h⟩

theorem ExcR.mono {α : Type} {R R' : α → List Word → Mem → Prop} {x : Except CheckError α}
    {r : List Word} {m m' : Mem} (h : ExcR R x r m) (hR : ∀ v r', R v r' m → R' v r' m') :
    ExcR R' x r m' := by
  cases x with
  | ok v => exact ⟨h.1, hR _ _ h.2⟩
  | error e => exact h

/-- The reasons the reader answers are reasons (`decide` on each constant). -/
theorem rcode_reader :
    RCode R_INDUCTIVE_TYPE_DECLARES ∧ RCode R_NO_RECURSOR_OF ∧ RCode R_THE_ARGUMENT_COUNTS ∧
    RCode R_INDUCTIVE_TYPE_DECLARES_OTHER ∧ RCode R_CONSTRUCTOR_DECLARES_ANOTHER ∧
    RCode R_CONSTRUCTOR_DECLARES_OTHER ∧ RCode R_CONSTRUCTOR_DECLARES_OTHER_UNIVERSE ∧
    RCode R_INDUCTIVE_BLOCK_ITS ∧ RCode R_INDUCTIVE_BLOCK_DECLARES ∧ RCode R_INDUCTIVE_BLOCK_CARRIES := by
  simp only [RCode]; decide

end L.Ind
