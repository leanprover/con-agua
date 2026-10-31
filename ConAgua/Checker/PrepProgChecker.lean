module

public import ConAgua.Checker.PrepProgHoist
public import ConAgua.Checker.PrepProgExt

@[expose] public section

/-!
# The prelude stages' and the hoist's lookups at `checkerProg` (lane `pipeline`)

`PrepProg`, `PrepExt`, `HoistProg`, `HoistExt` (`Checker/Prelude.lean`, `Checker/Hoist.lean`) at
the checker's program: `checkerProg_prepProg`, `checkerProg_hoistProg` (`PrepProgHoist.lean`),
`checkerProg_prepExt`, `checkerProg_hoistExt` (`PrepProgExt.lean`), in two modules that Lake
builds in parallel (each a few hundred `rfl` lookups, one after the other).
-/
