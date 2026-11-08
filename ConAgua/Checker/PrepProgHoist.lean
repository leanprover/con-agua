module

public import ConAgua.Checker.Prog

@[expose] public section

/-!
# The prelude stages' and the hoist's lookups at `checkerProg`, part 1 (lane `pipeline`)

`HoistProg` and `PrepProg` (`Checker/Prelude.lean`, `Checker/Hoist.lean`) at the checker's
program: one `rfl` lookup per function (`ProgHas.cons`), elaborated one after the other
(`Elab.async false`: in parallel the lookups' memory adds up). `PrepProgChecker.lean` collects
them with part 2 (`PrepProgExt.lean`, built in parallel).
-/

namespace L.Checker

open L

set_option Elab.async false

-- ronsync2 stage 2: the lookups come back with the regenerated `checkerProg`.

end L.Checker
