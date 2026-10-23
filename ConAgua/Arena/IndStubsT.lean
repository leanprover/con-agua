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

/-! The two walk contracts that were here (`constsResolveFFastT_spec`, `allLevelParamsDefinedT_spec`)
are gone: every caller reads `consts_resolve_ffast` and `all_level_params_defined` through its
model's `CallM` and, under `StageT`, uses the real refinements `crfF_okT` (`IndRealMemoCrT.lean`,
pre `StageT ∧ CrMemo`) and `apdF_okT` (`IndRealApdT.lean`, the parameters' names read back).
`reduce_pin_guard` and the `Nat.div` gates (helper `indproofs4-t2`), `install_value_guards`
(helper `indproofs4-sw2`), and `install_header` (`ihW_okT`, `DeclValT`; lane `indstaget`, helper
`rcB`: `CrOK` threaded to it from `check_constant_val`, `install_value` and `class_const_ok`, the
names read back from the constant's denotation at the entry, the guards before the walk keeping the
twin's store). -/


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
