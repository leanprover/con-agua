module

public import ConAgua.Front.NatDec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Front.NatDec

@[expose] public section

/-!
# Long decimal literals: `nat_dec_split` and `nat_dec_big`

Word models over `callW` of every callee (`l_model`), for the value proofs in `NatDecBigVal.lean`.
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Front

open L.Arena

/-- **`nat_dec_split`** (generated): `splitW`, every call through `callW`. -/
l_model natDecSplit_spec (p : Prog) (hs : p.lookup "nat_dec_split" = some natDecSplit)
  fns [hs ↦ splitW list]
  specs [callW_spec p n "nat_dec_chunks", callW_spec p n "nat_dec_split", callW_spec p n "nat_mul",
    callW_spec p n "nat_add"]
  grind [arena_grind]

/-- **`nat_dec_big`** (generated): `bigW`, every call through `callW`. -/
l_model natDecBig_spec (p : Prog) (hb : p.lookup "nat_dec_big" = some natDecBig)
  fns [hb ↦ bigW list]
  specs [callW_spec p n "nat_dec_split", callW_spec p n "nat_mul"]
  grind [arena_grind]

end L.Front
