import ConAgua.L.Semantics
import ConRon.Arena.Handle
import Std.WP.Assertion
import ConAgua.Arena.Reasons

/-!
# MW9

`MW9`, `MW10`, `MW11`, `MW13`, `MW14`, `MW19`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The block's models

The continuations take the block's functions they call (at the caller's fuel `n`) as arguments, so
that the block itself is a structural recursion on the exec fuel. -/

/-! Model types: a memory and `k` words. -/
abbrev MW9 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW10 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW11 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW13 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW14 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW19 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)

end L.Ind

end
