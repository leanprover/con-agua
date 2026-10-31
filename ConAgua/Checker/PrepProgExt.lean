module

public import ConAgua.Checker.Prog

@[expose] public section

/-!
# The prelude stages' and the hoist's lookups at `checkerProg`, part 2 (lane `pipeline`)

`HoistExt` and `PrepExt` (`Checker/Prelude.lean`, `Checker/Hoist.lean`) at the checker's
program, as `PrepProgHoist.lean` (built in parallel with it).
-/

namespace L.Checker

open L

set_option Elab.async false

set_option maxRecDepth 100000 in
theorem checkerProg_hoistExt : HoistExt checkerProg := by
  unfold HoistExt hoistExtProg
  repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

set_option maxRecDepth 100000 in
theorem checkerProg_prepExt : PrepExt checkerProg := by
  unfold PrepExt prepExtProg
  repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

end L.Checker
