import ConAgua.Front.FrontPreOK1
import ConAgua.Front.IndApplyTwin

/-!
# The frontend's records, word by word, II: an inductive line (lane `pipeline`)

`applyIndW_grow`: a successful `apply_ind` (on con-leche's `ok` path of the block's scan) appends
one record of kind `6` whose block offset is the old top of `DLP` plus one, and changes neither the
old records nor the pool up to its old top (`DGrow`). The facts are the frames of `installW_twin`'s
proof (`IndInstallRefine5.lean`), which go through the twin's install loop (`instGo_twin`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec DeclRec scanIndDecl)

namespace L.Front.Ind

/-- **`apply_ind` appends one inductive record.** -/
theorem applyIndW_grow {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) {v : USize}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {e : USize}
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e)
    (h : applyIndW n b.data m v.toUInt64 = some m') : DGrow m m' := by
  sorry

end L.Front.Ind
