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
set_option maxRecDepth 100000 in
end L.Checker
