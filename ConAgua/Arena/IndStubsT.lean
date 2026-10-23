import ConAgua.Arena.StageTLift

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


/-- `all_level_params_defined(lps.off, lps.len, e)` under `StageT`. -/
theorem allLevelParamsDefinedT_spec (o l e : Word) (he : H e) (lps : List NIdx) :
    RelAM "all_level_params_defined" [o, l, e]
      (fun m a => StageT dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps)
      (allLevelParamsDefined lps (decI e)) (KeepPostT dn vis fe decW0B) := sorry

/-- `is_proj_fn_shape(n)` under `StageT` (lane `loopt2`'s `install_header`). It has L code
(`isProjFnShapeL`) that only reads the name store: a real `Sim` through `StageT.lift_keep` from a
`StageR` refinement is the intended replacement. -/
theorem isProjFnShapeT_spec (n : Word) (hn : H n) :
    RelAM "is_proj_fn_shape" [n] (StageT dn vis fe)
      (NIdx.isProjFnShape (decI n)) (KeepPostT dn vis fe decW0B) := sorry

end specs

end L.Ind
