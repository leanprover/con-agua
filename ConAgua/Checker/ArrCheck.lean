module

public import ConAgua.Checker.ParOwned
public import ConAgua.Checker.CapCheck
public import ConAgua.Arena.ArenaRel
public import ConAgua.Checker.ProgTab
meta import ConAgua.Checker.ParOwned
meta import ConAgua.Checker.CapCheck
meta import ConAgua.Arena.ArenaRel
meta import ConAgua.Checker.ProgTab

@[expose] public section

/-!
# The checker's arrays, checked against the program

`checkerArrays` (`ConAgua/Layout.lean`) against `checkerProg` and the lists of array numbers the
entries and the parallel mode use. (Nothing proved depends on these checks: they keep the table
the memory layout of record.)

* the table is well formed: numbers distinct (one name space for both kinds);
* **the surface check**: every array operand of the program is a table array of its kind, a
  tiered access names a tiered array, and a plain word access names no tier-1 number, with no
  exception (`cap_check` reads the table's slots by name, a tier 1 by a tiered access);
* the compiler's layout (`checkerTab`) has every array of the table;
* the frozen and owned arrays of the parallel mode, the store tier's arrays and the slot arrays
  are slots of the table.
-/

namespace L.Checker

open L L.Arena L.Compiler

#guard checkerArrays.wf
#guard checkerArrays.progOK checkerProg
#guard checkerArrays.wordSlots.all checkerTab.dom64
#guard (checkerArrays.ids .byte).all checkerTab.dom8
#guard frozenIds.all checkerArrays.wordSlots.contains
#guard parOwned.all checkerArrays.wordSlots.contains
#guard storeArrs.all checkerArrays.wordSlots.contains
#guard memoArrs.all checkerArrays.wordSlots.contains
#guard slotArrs.all checkerArrays.wordSlots.contains

end L.Checker
