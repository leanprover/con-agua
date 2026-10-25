import ConAgua.L.Syntax
import ConAgua.Arena.Reasons

/-!
# The checker's global variables

Every global variable of the checker's program, with its id (`L.GVar`; the compiler puts global `g`
at `Tab.globOff g` in the table, a zero word in a fresh region). Pick a new id here. (Ids `0`‥`6`
are free.)

* `MODE` (`8`): the entry mode, written by the entry stubs (`ConAgua/Compiler/Abi.lean`): `0` (the
  region's zero; no entry leaves it) aborts; `1` (`ca_start_a`, entry 1) the stages,
  phase A and the frozen buffer (header and images); `3` (the sequential driver's entry 1) the
  same with the header only (the images stay in place); `2` (`ca_check_b`, `ca_check_seq`,
  entry 2) the pending groups `PLO‥PHI-1` over the frozen arrays (lane parmode,
  docs/design/parmode.md, `Checker/Entry.lean`).
* `PLO` (`9`), `PHI` (`11`): the range of pending groups entry 2 checks.
* `ATT` (`7`, declared in `Arena/Reasons.lean` beside the reasons that read it): `3` while
  `check_div_mod_pin_loop` runs a pin-variant attempt, else `0`. Inside an
  attempt the twin recovers from an error (`orElseAttempt`) where L aborts, so a reject or decline
  site there (`fail R`) aborts with its class bits cleared (`R ^ (R & ATT)`): it claims nothing.
* `INIT` (`10`): `0` until entry 2 has copied the seed arrays into its worker region (the region's
  first call), then `1`.
-/

namespace L.Arena

abbrev MODE : L.GVar := ⟨8⟩
abbrev PLO : L.GVar := ⟨9⟩
abbrev PHI : L.GVar := ⟨11⟩
abbrev INIT : L.GVar := ⟨10⟩

end L.Arena
