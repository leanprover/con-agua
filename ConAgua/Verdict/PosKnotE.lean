module

public import ConAgua.Verdict.DefEqBaseE
public import ConAgua.Arena.IndT.Lift

@[expose] public section

/-!
# `whnf_top`'s error claim under `StageT`

`whnfTop_stageE`: from the error knot.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`whnf_top`'s verdicts** are the `whnf` slot's (`whnfTop_ref`'s error half). -/
theorem whnfTop_refinesE (p : Prog) (hw : p.lookup "whnf_top" = some whnfTopL) (hK : ∀ n, KnotOK p n)
    (n : Nat) (hkE : KnotUpToE p n) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpecE p (n + 1) "whnf_top" [vis, dep, e]
      (whnf ConLeche.CheckMode.verified fe F dep.toNat (decE e)) s₀ a₀ :=
  RefE.coreSpecE (wtopE_spec p hw (n + 1) s₀ vis dep e) trivial hkE
    (whnfTop_ref p hK n hn F hF s₀ a₀ M dep e hS he)

/-- **`whnf_top`'s error claim under `StageT`** (`WhnfTopE`), from the error knot. -/
theorem whnfTop_stageE {p : Prog} (hw : p.lookup "whnf_top" = some whnfTopL)
    (hK : ∀ n, KnotOK p n) (hKE : ∀ n, KnotOKE p n) : WhnfTopE p := by
  intro n hn dn vis fe m a hS dep t ht e hc
  refine ErrClaim.of_callE_succ hc fun k hk hc' => ?_
  subst hk
  obtain ⟨M, hC⟩ := hS.core
  exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
    (whnfTop_refinesE p hw hK k (fun j _ => hKE j) hn checkFuel (stage_fuel hn) ⟨m, Locals.init []⟩ a dn vis fe M
      dep t hC (hw_of_h ht)) hc'

end L.Ind
