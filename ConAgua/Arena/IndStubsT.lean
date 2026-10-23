import ConAgua.Arena.StageTLift
import ConAgua.Arena.IndRealIpf

/-!
# Stub contracts under `StageT` (lane `indproofs3`)

`IndStubs.lean`'s contracts give `StageR` after the call; a caller under `StageT` needs `StageT`
after. These are the same contracts with `StageT` in the pre and the post (`KeepPostT`), `sorry`
like the originals, for the owning lanes: each is a property the real function has (it runs under
`CoreS` or leaves the twin's invariants alone). Delete a contract when its function's real
refinement lands. Asked for by lane `loopt2` (the declaration arms' `install_value_guards`).
-/

set_option linter.deprecated false

open ConRon.Arena

namespace L.Ind

open L.Arena

section specs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- `consts_resolve_ffast(vis, e)` under `StageT`. -/
theorem constsResolveFFastT_spec (e : Word) (he : H e) :
    RelAM "consts_resolve_ffast" [vis, e] (StageT dn vis fe)
      (constsResolveFFast fe (decI e)) (KeepPostT dn vis fe decW0B) := sorry

/-- `has_fvar_fast(fuel, e)` under `StageT`. -/
theorem hasFvarFastT_spec (f e : Word) (he : H e) :
    RelAM "has_fvar_fast" [f, e] (StageT dn vis fe)
      (hasFvarFast f.toNat (decI e)) (KeepPostT dn vis fe decW0B) := sorry

/-- `loose_bvars_bounded_fast(fuel, k, e)` under `StageT`. -/
theorem looseBVarsBoundedFastT_spec (f k e : Word) (he : H e) :
    RelAM "loose_bvars_bounded_fast" [f, k, e] (StageT dn vis fe)
      (looseBVarsBoundedFast f.toNat k.toNat (decI e)) (KeepPostT dn vis fe decW0B) := sorry

/-- `all_level_params_defined(lps.off, lps.len, e)` under `StageT`. -/
theorem allLevelParamsDefinedT_spec (o l e : Word) (he : H e) (lps : List NIdx) :
    RelAM "all_level_params_defined" [o, l, e]
      (fun m a => StageT dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps)
      (allLevelParamsDefined lps (decI e)) (KeepPostT dn vis fe decW0B) := sorry

end specs


open Std.WP in
/-- **The same under `StageT`** (replaces `IndStubsT.isProjFnShapeT_spec`): nothing changes. -/
theorem ipfF_okT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x : Word) (_hx : H x) :
    RelW ipfF [x] (StageT dn vis fe) (NIdx.isProjFnShape (decI x)) (KeepPostT dn vis fe decW0B) := by
  intro m m' a r hc hT
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => rw [callW_zero] at hc'; cases hc'
  | succ n =>
  obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (isProjFnShape_specW ipfProg rfl n _ x) hc'
  simp only at hm hW
  obtain ⟨hrun, hle⟩ := ipfW_run hT.stage.1.arena.1 hW
  subst hs'
  rw [hm]
  exact ⟨_, a, hrun, hT, IWGrow.refl _, rfl, hle⟩

end L.Ind
