module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# The checker's global variables

Every global variable of the checker's program, with its id (`L.GVar`; the compiler puts global `g`
at `Tab.globOff g` in the table, a zero word in a fresh region). Pick a new id here. (Ids `4`‥`7`
are free.)

* `ETOP1` (`0`): the top of `EREC`'s tier 1, a job's own records (`erec_alloc`), `0` after the
  scratch tier is emptied.
* `EBELOW` (`1`), `EBELOWR` (`2`): the job's view of the frozen stream index, `IFBase.below` and
  `IFBase.belowRec` (the record's first counter and its position).
* `ESTAMP` (`3`): the job's stamp: an own-layer row of the environment is the job's only when it
  carries the current stamp (`Env.lean`).

* `MODE` (`8`): the entry mode, written by the entry stubs (`ConAgua/Compiler/Abi.lean`): `0` (the
  region's zero; no entry leaves it) aborts; `1` (`ca_start_a`, entry 1) the stages,
  phase A and the frozen buffer (header and images); `3` (the sequential driver's entry 1) the
  same with the header only (the images stay in place); `2` (`ca_check_b`, `ca_check_seq`,
  entry 2) the pending groups `PLO‥PHI-1` over the frozen arrays (lane parmode,
  docs/design/parmode.md, `Checker/Entry.lean`).
* `PLO` (`9`), `PHI` (`11`): the range of pending groups entry 2 checks.
* `INIT` (`10`): `0` until entry 2 has copied the seed arrays into its worker region (the region's
  first call), then `1`.
-/

namespace L.Arena

abbrev MODE : L.GVar := ⟨8⟩
abbrev PLO : L.GVar := ⟨9⟩
abbrev PHI : L.GVar := ⟨11⟩
abbrev INIT : L.GVar := ⟨10⟩
abbrev ETOP1 : L.GVar := ⟨0⟩
abbrev EBELOW : L.GVar := ⟨1⟩
abbrev EBELOWR : L.GVar := ⟨2⟩
abbrev ESTAMP : L.GVar := ⟨3⟩

end L.Arena
