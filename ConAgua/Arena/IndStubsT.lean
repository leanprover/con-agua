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
with the slice and the parameters' names read back). Users switched (helper `indproofs4-t2`): the
`all_level_params_defined` call of `reduce_pin_guard` (`rpgW`, `DeclCrpT`) and of the `Nat.div`
gates' guards (`dmPgW`, `dmCgW`, `DeclDivGateT1`), read through their `CallM` (`stubCall` for the
`StageR` proofs, `realCall p` with `ApdF p` in `CrpProg`/`DmProg5` under `StageT`; `lps = []`).
Users left:

* `install_header` (`ihW_okT`, `DeclValT`; both calls): `ihW` (`DeclHeader.lean`) is lane
  `indstaget`'s (its second reading parameter, `class_const_ok`'s `RecGen3`).
* `install_value_guards` (`ivgW_okT`, `DeclCvgT`; both calls): `apdF_okT` needs
  `cv.levelParams`' names read back, which none of `ivgW_okT`'s callers has (`ivW_genT`,
  `dvW_okT`, `tvW_okT`, `cvgW_okT`: the record's denotation is not threaded to them; phase B's
  could take it from `StoreDen.constLps`, the constant being in `fe`).
* every `consts_resolve_ffast` call (`ivgW`, `rpgW`, `dmPgW`, `dmCgW`): `crfF_okT` needs `CrMemo`
  (array 155, `CTL[158]`; `= CrOK`, `crMemo_iff_crOK`), which no caller has. `StageT`, `StageC`,
  `TwinMem`, `CoreMemos` say nothing of array 155 and phase A/B's loops run on
  `LoopR ∧ LoopMem ∧ CoreMemos` (not `LoopT`, whose `cr` has it), so it must be threaded as a pre
  and a post from the loop's start (`LoopStart.crOK`) through both loops, every arm (`ArmSpecT`,
  `IndArmSpec`: a hypothesis of `Final/Remaining.lean`), the value checks and gates. The core's
  calls keep it by frame (`coreStageA` excludes 155), but a leaf's frame does not (`leafA` has
  array 155: `consts_resolve_ffast` and `consts_resolve_all` are leaves), so the leaf calls on the
  way need a narrower leaf write set without the walk's functions, and `consts_resolve_all` (the
  `Nat.div` gate's, through its `StageR` stub contract) a refinement that keeps it. -/

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
