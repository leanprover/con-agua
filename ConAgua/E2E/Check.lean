module

public import ConAgua.Checker.Prog
public import ConAgua.E2E.Ser

@[expose] public section

/-!
# The e2e lane's test entries, and the program file `e2e-l` runs (lanes `e2e`, `integrate`)

The checker is `L.Checker.checkerProg` (`ConAgua/Checker/Prog.lean`, entry `check()` in
`ConAgua/Checker/Entry.lean`). The e2e runs add two test entries here: `check_np()`, the pipeline
without the two prelude stages (its reference is `e2e-ref --no-prelude`), and `e2e_front()`, the
stages before the fold (`e2e-diff`'s starting state). `writeChecker` writes both as the program
file `scripts/e2e.py` compiles (`Ser.lean`'s format).
-/

namespace L.E2E

open L

/-- `check_np()`: the pipeline without the prelude, both phases in one run (a test entry). -/
-- con-ron: none — the e2e lane's partial pipeline (no prelude), reference `e2e-ref --no-prelude`
@[no_expose] def checkNpL : FunDecl := lfn () locals (r, z, cnt, v, c) {
  z := call pb_check();
  z := call intern_reserved_pins();
  r := call front_run();
  if r != 0 { return 1 };
  z := call intern_all_pins();
  cnt := L.Front.DECL.u64[0];
  v := call install_fold_go(0, cnt, 0);
  c := L.Arena.CTL.u64[130];
  z := call check_pending_go(0, c, v);
  return 71757147230292
}

/-- `e2e_front()`: the stages before the fold (`e2e-diff`'s starting state, `ConAgua/E2E/Diff.lean`). -/
-- con-ron: none — the e2e lane's test entry (the first stages of `e2e-ref --no-prelude`)
@[no_expose] def e2eFrontL : FunDecl := lfn () locals (r, z) {
  z := call pb_check();
  z := call intern_reserved_pins();
  r := call front_run();
  if r != 0 { return r };
  z := call intern_all_pins();
  return 0
}

/-- The e2e lane's own functions; `scripts/e2e.py` gives them priority over every other binding. -/
def e2eProg : Prog := [("check_np", checkNpL), ("e2e_front", e2eFrontL)]

end L.E2E
