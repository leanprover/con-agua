module

public import ConAgua.Layout
public import ConAgua.L.Notation
import ConRon.Arena.Core
import ConAgua.Census.Attr

@[expose] public section

/-!
# The run's maximum `Nat` size: the refusals

The twin's `natSizeBytes` (`8 · (log2 n / 64 + 1)`) is read off a normalised slice's limb count,
`8 · max(l, 1)` (`NatCmpFacts.sizeBytes_pv`); the maximum is `PINS[72]` (`PinsFull.maxNatSize`).
`lit_nat_sized` refuses a computed numeral above it (`add`, `sub`, `mul`, `succ`), `pow_refused`
and `shift_left_refused` a `pow` or `shiftLeft` before computing (`natOpResult`'s guards).

**The refusals travel as sentinel handles.** The `Nat` arms are outside the verdict closure
(`nvFns`: they abort only with class-`0` codes), so a refusal is not a `fail` there: the arm
returns a sentinel word above every handle (`2^63 + k`, `natRefusedSize` … `natRefusedShlExp`)
and its caller in the verdict closure (`reduce_nat_op`, `reduce_nat_succ`) fails with the twin's
message at once. Nothing runs between the twin's `fail` and L's.
-/

namespace L.Arena

/-- The sentinel of a numeral above the maximum (`R_THE_KERNEL_REFUSED`). -/
abbrev natRefusedSize : Word := 9223372036854775809
/-- The sentinel of a `Nat.pow` exponent above `2^32 - 1` (`R_THE_KERNEL_REFUSED_TO`). -/
abbrev natRefusedPowExp : Word := 9223372036854775810
/-- The sentinel of a `Nat.pow` result above the maximum (`R_THE_KERNEL_REFUSED_TO_EVALUATE`). -/
abbrev natRefusedPowSize : Word := 9223372036854775811
/-- The sentinel of a `Nat.shiftLeft` amount above `2^32 - 1`
(`R_THE_KERNEL_REFUSED_TO_EVALUATE_NAT`). -/
abbrev natRefusedShlExp : Word := 9223372036854775812

/-- `size_bytes(l)`: the size in bytes of a normalised literal of `l` limbs, `8 · max(l, 1)`. -/
-- con-ron: ConRon/Arena/Core.lean:1051-1054 ConRon.Arena.natSizeBytes
@[no_expose, l_impl ConRon.Arena.natSizeBytes]
def sizeBytesL : FunDecl := lfn (l) locals () {
  if l == 0 { return 8 };
  return 8 * l
}

/-- `nat_size_refused(l)`: the literal of `l` limbs is above the run's maximum (`PINS[72]`). -/
-- con-ron: ConRon/Arena/Core.lean:1056-1061 ConRon.Arena.natSizeRefused
@[no_expose, l_impl ConRon.Arena.natSizeRefused]
def natSizeRefusedL : FunDecl := lfn (l) locals (s) {
  s := call size_bytes(l);
  return u64(PINS.u64[72] < s)
}

/-- `lit_nat_sized(o, l)`: a computed numeral, the slice `(o, l)`, refused above the run's maximum
(the sentinel `natRefusedSize`), otherwise interned (the handle word masked to its 32 bits, so a
handle is never a sentinel). -/
-- con-ron: ConRon/Arena/Core.lean:1063-1073 ConRon.Arena.litNatSized
@[no_expose, l_impl ConRon.Arena.litNatSized]
def litNatSizedL : FunDecl := lfn (o, l) locals (r, h) {
  r := call nat_size_refused(l);
  if r != 0 { return 9223372036854775809 };
  h := call intern_lit(o, l);
  return h & 4294967295
}

/-- `pow_refused(oa, la, e)`: `a ^ e` would be above the maximum (`natSizeBytes a > m / e`, as
`m < s · e` with the 128-bit product: L has no division); a base `≤ 1` (the empty slice, or the
one limb `1`) and the exponent `0` are never refused. -/
-- con-ron: ConRon/Arena/Core.lean:1075-1082 ConRon.Arena.powRefused
@[no_expose, l_impl ConRon.Arena.powRefused]
def powRefusedL : FunDecl := lfn (oa, la, e) locals (s) {
  if la == 0 { return 0 };
  if la == 1 && POOL⦃oa⦄ == 1 { return 0 };
  if e == 0 { return 0 };
  s := call size_bytes(la);
  if mulhi(s, e) != 0 { return 1 };
  return u64(PINS.u64[72] < s * e)
}

/-- `shift_left_refused(la, e)`: `a <<< e` would be above the maximum,
`natSizeBytes a + e / 8 + 1 > m`. -/
-- con-ron: ConRon/Arena/Core.lean:1096-1100 ConRon.Arena.shiftLeftRefused
@[no_expose, l_impl ConRon.Arena.shiftLeftRefused]
def shiftLeftRefusedL : FunDecl := lfn (la, e) locals (s) {
  s := call size_bytes(la);
  return u64(PINS.u64[72] < s + (e >> 3) + 1)
}

end L.Arena
