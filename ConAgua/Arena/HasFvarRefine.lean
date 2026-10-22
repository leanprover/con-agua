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

theorem hfK_ok (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaA m a)
    (e f r : Word) (he : e.toNat < 2 ^ 32) (hb : hfK (fvbW n m e f) = some (r, m')) :
    ∃ a', (hasFvarFast f.toNat (decE e)).run a = .ok (r != 0, a') ∧ ArenaA m' a' := by
  cases hw : fvbW n m e f with
  | none => simp [hw, hfK] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    rw [hw, hfK_some] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    obtain ⟨a', ha', hA'⟩ := fvbW_ok n m _ a hA e f x he hw
    refine ⟨a', ?_, hA'⟩
    simp only [hasFvarFast, StateT.run_bind, ha']
    by_cases h0 : x = 0
    · subst h0; rfl
    · have h0' : x.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
      simp [h0, h0', Functor.map, Except.map]

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
      AM.res (hasFvarFast f.toNat (decE e)) a₀ = (r.headD 0 != 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (hasFvarFastL_spec p hp hpf n s₀ f e)
  subst hs
  obtain ⟨a', ha', hA'⟩ := hfK_ok n _ _ a₀ hA e f _ he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres⟩

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
      AM.res (hasFvarFast coreWalkFuel (decE e)) a₀ = (r.headD 0 != 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (hasFvarL_spec p hp hpf n s₀ e)
  subst hs
  obtain ⟨a', ha', hA'⟩ := hfK_ok n _ _ a₀ hA e 4000000000 _ he hI
  rw [coreWalkFuel_toNat] at ha'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres⟩

end L.Arena
