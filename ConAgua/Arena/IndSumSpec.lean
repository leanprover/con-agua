import ConAgua.Arena.IndSum
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndStubs
import ConAgua.Arena.ArenaRel

/-!
# Refinements of `IndSum` (lane `induct`, worker C, round 2)

No existing file in the repo yet *consumes* a `RefAM`/`StageR`/`KeepPost`-shaped hypothesis (the
stubs in `IndStubs.lean` are the first to *state* one), so the chaining idiom for a stub-calling
function has no precedent to follow here; the functions proved below instead state their
refinement as a direct Hoare triple over `ArenaR` (as `IndView.lean`'s `eView_refines` and
`ArenaRel.lean`'s `intern*_refinesA` lemmas already do), which is enough for every target this file
reaches (none of them touch `core`/`pins`/`env`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_elim_level` -/

/-- **`struct_elim_level` refines `structElimLevel`** under `ArenaR`: the fresh parameter at the
large eliminator, `zero` at the small one. -/
@[refines ConRon.Arena.structElimLevel]
theorem structElimLevel_refines (p : Prog) (hpf1 : p.lookup "param_find" = some paramFind)
    (hpp1 : p.lookup "param_push" = some paramPush)
    (hp1 : p.lookup "intern_param" = some internParam)
    (hpf2 : p.lookup "zero_find" = some zeroFind) (hpp2 : p.lookup "zero_push" = some zeroPush)
    (hp2 : p.lookup "intern_zero" = some internZero)
    (hp : p.lookup "struct_elim_level" = some structElimLevelL)
    (a₀ : AState) (n : Nat) (s₀ : St) (elim large : Word) (hR : ArenaR s₀.mem a₀)
    (helim : elim.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "struct_elim_level" [elim, large]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structElimLevel (decI elim) (large != 0)) a₀ ∧
      ArenaR s'.mem (AM.st (structElimLevel (decI elim) (large != 0)) a₀) ∧
      AM.res (structElimLevel (decI elim) (large != 0)) a₀ = decI (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structElimLevelL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internParam_refinesA p hpf1 hpp1 hp1 a₀ n,
        internZero_refinesA p hpf2 hpp2 hp2 a₀ n] <;>
      finish [structElimLevel]

end L.Ind
