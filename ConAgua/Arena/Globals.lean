import ConAgua.L.Syntax

/-!
# The checker's global variables

Every global variable of the checker's program, with its id (`L.GVar`; the compiler puts global `g`
at `Tab.globOff g` in the table, a zero word in a fresh region). Pick a new id here. (Ids `0`‥`7`
are left to lane tierpool's pool globals.)

* `MODE` (`8`): the entry mode, written by the entry stubs (`ConAgua/Compiler/Abi.lean`): `0` (the
  region's zero, `ca_start`) the whole pipeline in one run; `1` (`ca_start_a`, entry 1) the stages,
  phase A and the compaction into the frozen buffer; `2` (`ca_check_b`, entry 2) one pending group
  over the frozen buffer (lane parmode, docs/design/parmode.md, `Checker/Entry.lean`).
* `PJ` (`9`): the pending group entry 2 checks (written by `ca_check_b`).
* `INIT` (`10`): `0` until entry 2 has copied the seed arrays into its worker region (the region's
  first call), then `1`.
-/

namespace L.Arena

abbrev MODE : L.GVar := ⟨8⟩
abbrev PJ : L.GVar := ⟨9⟩
abbrev INIT : L.GVar := ⟨10⟩

end L.Arena
