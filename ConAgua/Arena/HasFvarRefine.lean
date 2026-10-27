import ConAgua.Arena.HasFvar
import ConAgua.Arena.Abs1Refine
import ConAgua.Census.Attr

/-!
# `has_fvar_fast`/`has_fvar` refine `hasFvarFast`

`fvbW_ok` (`Abs1Refine.lean`) and the compare: the L word is `1` exactly when the twin's
`r != 0`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `hfK`'s result is a Boolean word. -/
theorem hfK_le (o : Option (Word × Mem)) (r : Word) (m' : Mem) (hb : hfK o = some (r, m')) :
    r ≤ 1 := by
  cases o with
  | none => cases hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    rw [hfK_some] at hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb)
    split <;> decide

/-- **`has_fvar_fast`'s model refines `hasFvarFast`**: `fvbW_ok` and the compare (the L word is
`1` exactly when the twin's `r != 0`). -/
theorem hfK_sim (n : Nat) (m : Mem) (a : AState) (hA : ArenaA m a) (e f : Word)
    (he : e.toNat < 2 ^ 32) :
    Sim (hfK (fvbW n m e f)) (hasFvarFast f.toNat (decE e)) a
      (fun r x m' a' => ArenaA m' a' ∧ x = (r != 0) ∧ r ≤ 1) :=
  Sim.bindD rfl (fun _ _ => rfl) (Sim.ofD fun x m₁ hb => fvbW_ok n m m₁ a hA e f x he hb)
    fun x m₁ a₁ hA₁ => Sim.ret ⟨hA₁, by
      by_cases h0 : x = 0
      · simp [h0]
      · have : x.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
        simp [h0, this], by split <;> decide⟩

/-- **`has_fvar_fast(f, e)` refines `hasFvarFast f.toNat e`** under `ArenaA`, at every L fuel (the
L argument `f` is the twin's fuel, the walk's depth counter). -/
@[refines ConRon.Arena.hasFvarFast]
theorem hasFvarFast_refines (p : Prog) (hp : AbsProg p)
    (hpf : p.lookup "has_fvar_fast" = some hasFvarFastL) (n : Nat) (s₀ : St)
    (a₀ : AState) (hA : ArenaA s₀.mem a₀) (f e : Word) (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "has_fvar_fast" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (hasFvarFast f.toNat (decE e)) a₀ ∧
      ArenaA s'.mem (AM.st (hasFvarFast f.toNat (decE e)) a₀) ∧
      AM.res (hasFvarFast f.toNat (decE e)) a₀ = (r.headD 0 != 0) ∧
      r.headD 0 ≤ 1; ⊤⦄ :=
  Sim.triple (hasFvarFastL_spec p hp hpf n s₀ f e) (hfK_sim n _ a₀ hA e f he)

/-- **`has_fvar(e)` refines `hasFvarFast coreWalkFuel e`** (the stub interface `HasFvarOK`'s fuel),
at every L fuel. -/
@[refines ConRon.Arena.hasFvarFast]
theorem hasFvar_refines (p : Prog) (hp : AbsProg p) (hpf : p.lookup "has_fvar" = some hasFvarL)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaA s₀.mem a₀) (e : Word)
    (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "has_fvar" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (hasFvarFast coreWalkFuel (decE e)) a₀ ∧
      ArenaA s'.mem (AM.st (hasFvarFast coreWalkFuel (decE e)) a₀) ∧
      AM.res (hasFvarFast coreWalkFuel (decE e)) a₀ = (r.headD 0 != 0) ∧
      r.headD 0 ≤ 1; ⊤⦄ :=
  Sim.triple (hasFvarL_spec p hp hpf n s₀ e)
      (coreWalkFuel_toNat ▸ hfK_sim n _ a₀ hA e 4000000000 he)

end L.Arena
