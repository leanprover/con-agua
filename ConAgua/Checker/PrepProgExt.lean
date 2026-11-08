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

-- ronsync2 stage 2: the lookups come back with the regenerated `checkerProg`.

end L.Checker
