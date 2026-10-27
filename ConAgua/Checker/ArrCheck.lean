import ConAgua.Checker.ParOwned
import ConAgua.Checker.CapCheck
import ConAgua.Arena.ArenaRel

/-!
# The checker's arrays, checked against the program

`checkerArrays` (`ConAgua/Layout.lean`) against `checkerProg` and the lists of array numbers the
entries and the parallel mode use. (Nothing proved depends on these checks: they keep the table
the memory layout of record.)

* the table is well formed: numbers distinct per kind and below `tierOff`;
* **the surface check**: every array operand of the program is a table array of its kind, a
  tiered access names a tiered array, and a plain word access names no tier-1 number; the only
  exception is `cap_check`, which checks the length of every slot by number;
* the program's extent (`Prog.arrs`, which sizes the descriptor table) is the table's;
* the frozen and owned arrays of the parallel mode, the store tier's arrays and the slot arrays
  are slots of the table.
-/

namespace L.Checker

open L L.Arena L.Compiler

#guard checkerArrays.wf
#guard checkerArrays.progOK ["cap_check"] checkerProg
#guard Prog.arrs checkerProg == checkerArrays.extent
#guard checkerArrays.extent.2 == wordArrays
#guard frozenIds.all checkerArrays.wordSlots.contains
#guard parOwned.all checkerArrays.wordSlots.contains
#guard storeArrs.all checkerArrays.wordSlots.contains
#guard memoArrs.all checkerArrays.wordSlots.contains
#guard slotArrs.all checkerArrays.wordSlots.contains

end L.Checker
