import ConAgua.Arena.StageTLift
import ConAgua.Arena.IndRealIpf
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealApdT

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

/-! The two contracts left. Their proven replacements exist: `crfF_okT` (`IndRealMemoCrT.lean`,
pre `StageT ∧ CrMemo`, post `KeepPostT ∧ CrMemo`) and `apdF_okT` (`IndRealApdT.lean`, pre `StageT`
with the slice and the parameters' names read back). The callers (`DeclCvgT`, `DeclValT`,
`DeclCrpT`, `DeclDivGateT1`) cannot switch yet: (1) their models (`ivgW`, `ihW`, `rpgW`, the
`Nat.div` gates' `DeclDivMod5`/`DeclDivMod6` models) read both calls through the opaque `stubM`, and
the same models serve the `StageR` proofs (`DeclCvg`, `DeclHeader`, `DeclReduceSpec`, `DeclDivMod5`,
`DeclDivMod6`, lane `indstaget`'s `RecGenSpec3`), which have no walk memos to give the real walks:
the models must read these two calls through their `CallM` (`stubCall` for `StageR`, `realCall p`
for `StageT`, with `ProgHas p crfP`/`ProgHas p apdP` in the bundles); (2) `crfF_okT` needs
`CrMemo` (array 155), which neither `StageT` nor the arms' contract (`ArmSpecT`, phase B's
`checkValueGroup_specT`, the inductive arm) carries: `LoopT.cr` has it but `CheckerT`'s loop runs
on `LoopR ∧ StageT ∧ CoreMemos`; it must be threaded through the `StageT` declaration theorems
(pre and post), across the core's calls (whose write set `coreStageA` includes array 155: a
closure check without it); (3) `apdF_okT` needs the level parameters' names to read back
(`cv.levelParams` in `DeclCvgT`/`DeclValT`; trivial for `lps = []` in `DeclCrpT`/`DeclDivGateT1`). -/

/-- `consts_resolve_ffast(vis, e)` under `StageT`. -/
theorem constsResolveFFastT_spec (e : Word) (he : H e) :
    RelAM "consts_resolve_ffast" [vis, e] (StageT dn vis fe)
      (constsResolveFFast fe (decI e)) (KeepPostT dn vis fe decW0B) := sorry


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
