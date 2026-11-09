module

public import ConAgua.Arena.KnotMono2

@[expose] public section

/-!
# The twin's store only grows across the knot

Every slot of `coreKnot` is `SMono` at every fuel (`knot_smono`: induction on the fuel, the slots'
bodies by `KnotMono1`/`KnotMono2`'s lemmas). So a successful knot run keeps every level handle's
readback (`knot_lkept`) and every expression node's view.
-/

open ConRon.Arena

namespace L.Arena

/-- **The knot's slots only extend the store**, at every fuel and eager flag. -/
theorem knot_smono (mode : ConLeche.CheckMode) (fe : IFEnv) :
    ∀ (F : Nat) (eager : Bool), RecSMono (coreKnot mode eager fe id F) := by
  intro F
  induction F with
  | zero =>
    intro eager
    exact ⟨fun _ _ _ => SMono.fail _, fun _ _ => SMono.fail _, fun _ _ => SMono.fail _,
      fun _ _ _ => SMono.fail _, fun _ _ _ => SMono.fail _, fun _ _ => SMono.fail _⟩
  | succ F ih =>
    intro eager
    have h0 := ih eager
    have h1 := ih true
    have h2 := h0.ioView
    refine ⟨fun c d e => ?_, fun d e => ?_, fun d e => ?_, fun d a b => ?_, fun d a b => ?_,
      fun d e => ?_⟩ <;> simp only [coreKnot, id] <;> smono_auto

theorem SMono.store {α : Type} {op : AM α} (h : SMono op) {a a' : AState} {x : α}
    (hr : op.run a = .ok (x, a')) : SExt a a' := h.run hr

end L.Arena
