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
with the slice and the parameters' names read back). Users switched (helpers `indproofs4-t2`,
`indproofs4-sw2`), each reading the two walks through its model's `CallM` (`stubCall` for the
`StageR` proofs, `realCall p` under `StageT`):

* `reduce_pin_guard` (`rpgW`, `DeclCrpT`) and the `Nat.div` gates' guards (`dmPgW`, `dmCgW`,
  `DeclDivGateT1`): `lps = []`; `consts_resolve_ffast`'s memo `CrOK` taken at the arm's entry
  (`ArmSpecT`; the loop's `IndMemos.cr`) and carried across the program's calls (`CrKeep`,
  `CrOKFrame.lean`: `IndMemoClosed`'s write set) and the walks' frames;
* `install_value_guards` (`ivgW`, `DeclCvgT`), from `install_value` (`ivW_genT`), the value checks
  (`dvW_okT`, `tvW_okT`) and phase B (`cvgW_okT`): the parameters' names read back at the guards
  from the constant's denotation and the twin's store growing up to them (`installHeader_bridge`,
  `checkConstantVal_bridge_of_fold`, the theorem test's prefix `thmPrefix_ext`), `CrOK` as above
  (phase B carries it beside `CoreMemos`).

User left: `install_header` (`ihW_okT`, `DeclValT`; both calls): `ihW` (`DeclHeader.lean`) is lane
`indstaget`'s (its second reading parameter, `class_const_ok`'s `RecGen3`). The same switch applies
there: `ihW` reading the two walks through a `CallM`, `CrOK` threaded to `ihW_okT` (its callers
`ivW_genT` and `RecGen3` both run under `CrKeep`), the names read back from the constant's
denotation at the entry and the store's growth across the guards before the walk (con-ron's
`installHeader_bridge` route: `reservedBasisNames_run`'s `Ext`, the walks keeping the store). -/

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
