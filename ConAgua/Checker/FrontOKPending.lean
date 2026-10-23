import ConAgua.Front.FrontPre
import ConAgua.Checker.HoistWalkRef
import ConAgua.Checker.FrontProg

/-!
# The frontend keeps the records' word bounds (lane `pipeline`, pending)

`prepare_prelude`'s refinement (`PrepRef.lean`) needs every record the frontend wrote to satisfy
`RecOK` (handle words below `2^32`, inductive blocks' offsets and pointers nonzero) and every
parsed block to have no tower entry (`WalkableDecl`). `frontRunOK_checker` states it for
`front_run` at `checkerProg`, from the state after the prelude (`frontAll_refines_pre` plus the
two facts). **Its proof is pending (`sorry`)**: a helper of lane `pipeline` is strengthening the
frontend's line step (`docs/design/pipeline.md`).
-/

namespace L.Checker

open L L.Arena L.Front
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

/-- **`front_run` after `D`, with the records' word bounds** (pending). -/
theorem frontRunOK_checker (D : Array IDeclaration) (b : ByteArray)
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b.data) (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState)
    (hA : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem (StateD.blank.pre D))
    (hok : ConRon.Bridge.StateOK a₀) (hoff : a₀.store.scratchOn = false)
    (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x)
    (hW : ∀ d ∈ D, WalkableDecl d) :
    ⦃fun s => s = s₀⦄
    invoke checkerProg (exec checkerProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧
      (∀ x < D.size + st'.decls.size, RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x) ∧
      ∀ d ∈ st'.decls, WalkableDecl d; ⊤⦄ := by
  sorry

end L.Checker
