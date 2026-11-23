module

public import ConAgua.Arena.JustifyRef5
import ConRon.Bridge.Pers
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# `justify_why` refines `justifyWhy` (lane compare, helper compare-cone)

The solution's constant of the statement's name (`sol_find`), the statements compared
(`same_cv_up_to_levels`), the type's names (`needs_reset`, `needs_expr`), then the cone from an
empty memo (`cs_clear`) over those names (`cone_push`, `cone_go` at the fuel `CTL[225] + 1`).

`0` is the twin's `none`, an accept. A nonzero result is a twin `some` *if the twin runs*: its
message reads a name back (`readNameM`), which for the cone's culprit (code `3`) needs that name
to denote; that is the rejection claim's guard (`JwRuns`, `check_justified`), not proved here.
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind L.Stubs

/-- A message built from a name read back: an `ok` run is a `some`. -/
theorem some_of_msg {α : Type} {x : AM α} {g : α → String} {a a' : AState} {y : Option String}
    (h : (x >>= fun s => pure (some (g s)) : AM (Option String)).run a = .ok (y, a')) :
    y.isSome := by
  obtain ⟨s, a1, -, h2⟩ := ConRon.Bridge.AM.bind_ok h
  cases h2; rfl

/-- **The walks' memory from the walks' states.** -/
theorem WalkMem.of_walks {m : Mem} (hN : ∃ x, NdR m x) (hW : ∃ s w, CnR m s w) : WalkMem m := by
  obtain ⟨x, hx⟩ := hN
  obtain ⟨s, w, hw⟩ := hW
  exact ⟨⟨_, hx.rel.seen⟩, ⟨_, hw.rel.seen⟩, hx.ctl, hw.ctl⟩

section jw
variable {p : Prog} (P : ConeProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`justify_why(vis, x + CI.cv)` refines `justifyWhy`** of the record `x`'s statement: `0`
exactly when the twin answers `none` (an accept, the context and the walks' memory kept); a
nonzero result is a twin `some` whenever the twin's run succeeds. -/
@[refines ConRon.Arena.justifyWhy]
theorem justifyWhy_ok {J : ISolution} {n : Nat} {m m' : Mem} {a : AState} {x : Word}
    {r : List Word} {ci : IConstantInfo}
    (h : callW p n "justify_why" [vis, x + CI.cv] m = some (r, m'))
    (hC : ConeT dn vis fe J m a) (hx : decCI (erecP m) x.toNat = some ci)
    (hden : ∃ C, Frontend.denoteCI a.store ci = some C) (hWM : WalkMem m)
    (hnx : J.idx.next + 1 < 2 ^ 64) :
    ∃ a', ConeT dn vis fe J m' a' ∧ IWGrow m m' ∧ WalkMem m' ∧
      (r.headD 0 = 0 → (ConRon.Arena.justifyWhy J fe ci.toConstantVal).run a = .ok (none, a')) ∧
      (r.headD 0 ≠ 0 → ∀ y a'', (ConRon.Arena.justifyWhy J fe ci.toConstantVal).run a = .ok (y, a'') →
        y.isSome) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (justifyWhy_specW p P.jw n _ vis (x + CI.cv)) h
  sorry

end jw

end L.Arena
