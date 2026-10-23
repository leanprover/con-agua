import ConAgua.Checker.Prog

/-!
# The prelude stages' and the hoist's lookups at `checkerProg` (lane `pipeline`)

`PrepProg`, `PrepExt`, `HoistProg`, `HoistExt` (`Checker/Prelude.lean`, `Checker/Hoist.lean`) at
the checker's program: one `rfl` lookup per function (`ProgHas.cons`), elaborated one after the
other (`Elab.async false`: in parallel the lookups' memory adds up).
-/

namespace L.Checker

open L

set_option Elab.async false

set_option maxRecDepth 100000 in
theorem checkerProg_hoistProg : HoistProg checkerProg := by
  unfold HoistProg hoistProg
  repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

set_option maxRecDepth 100000 in
theorem checkerProg_hoistExt : HoistExt checkerProg := by
  unfold HoistExt hoistExtProg
  repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

set_option maxRecDepth 100000 in
theorem checkerProg_prepExt : PrepExt checkerProg := by
  unfold PrepExt prepExtProg
  repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

set_option maxRecDepth 100000 in
theorem checkerProg_prepProg : PrepProg checkerProg := by
  unfold PrepProg preludeProg
  refine ProgHas.append ?_ checkerProg_hoistProg
  repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

end L.Checker
