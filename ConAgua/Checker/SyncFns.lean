module

public import ConAgua.Arena.IndIface
public import ConAgua.Arena.StubNames
public import ConAgua.Arena.Infer
public import ConAgua.Arena.LevelZero

@[expose] public section

/-! # Bindings of L functions the sync added that no other program list names yet

(`scripts/checker_prog.py` assembles the program from the named bindings.) -/

namespace L.Checker

/-- The record pool's writer, the core's new readers and guards. -/
def syncFns : L.Prog :=
  [("erec_alloc", L.Ind.erecAlloc), ("erec_put", L.Ind.erecPut),
   ("nat_op_name", L.Stubs.natOpNameL), ("reserved_rec_bool", L.Stubs.reservedRecBoolL),
   ("check_proj_guard", L.Arena.checkProjGuardL), ("lv_never", L.Arena.lvNever),
   ("check_guard_rows", L.Arena.checkGuardRowsL), ("proj_guard_sort", L.Arena.projGuardSortL),
   ("proj_guard_rows_at", L.Arena.projGuardRowsAtL), ("proj_guard_rows", L.Arena.projGuardRowsL)]

end L.Checker
