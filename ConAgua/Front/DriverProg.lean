module

public import ConAgua.Front.Line
public import ConAgua.Front.Driver

@[expose] public section

/-! # The frontend's line and driver, as bindings (the assembled program's names) -/

namespace L.Front

/-- `front_line` and `front_run`. -/
def frontDriverProg : Prog := [("front_line", frontLine), ("front_run", frontRun)]

end L.Front
