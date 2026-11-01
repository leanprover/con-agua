module

public import ConAgua.Arena.AppStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.ConsPresize

@[expose] public section

/-!
# The parse's large cons tables sized from the input length: `presize_tables()` (lane presize)

`check_a` calls `presize_tables()` before the first intern (`intern_reserved_pins`). It sizes the
persistent tier of the three tables the parse fills most, `app` (one slot per 64 input bytes),
`lam` (per 512) and `forallE` (per 1024), each rounded up to a power of two, with the cons
library's `X_presize(n)` (`consPresizeG`, `Arena/ConsPresize.lean`). The tables then do not double in
place (D38) during the parse: on `Init` the `app` table starts at 8 M slots, its size at the end
of the parse. The memory is all zero at that point, so the presized table is an empty one
(`consR_initM`) and nothing is zeroed or touched up front. con-ron's tables start empty (D42).
-/

namespace L.Checker

open L L.Arena

-- con-ron: none — `HashMap2::with_capacity` (`ron/hashmap2.rs`) at the `app` table; con-ron's starts empty (D42)
@[no_expose] def appPresizeL : FunDecl := consPresizeG appCS
-- con-ron: none — `HashMap2::with_capacity` (`ron/hashmap2.rs`) at the `lam` table; con-ron's starts empty (D42)
@[no_expose] def lamPresizeL : FunDecl := consPresizeG lamCS
-- con-ron: none — `HashMap2::with_capacity` (`ron/hashmap2.rs`) at the `forallE` table; con-ron's starts empty (D42)
@[no_expose] def forallPresizeL : FunDecl := consPresizeG forallCS

/-- `pow2_at_least(q)`: the least power of two `≥ q` (`0` for `q = 0` or `q > 2^63`, which
`X_presize` refuses): `q - 1` with its bits smeared right, plus one (con-ron's `pow2_at_least`,
`ron/hashmap2.rs`, by a loop). -/
-- con-ron: none — `pow2_at_least` (`ron/hashmap2.rs`), for `HashMap2::with_capacity` (D42)
@[no_expose] def pow2AtLeastL : FunDecl := lfn (q) locals (x) {
  x := q - 1;
  x := x | (x >> 1);
  x := x | (x >> 2);
  x := x | (x >> 4);
  x := x | (x >> 8);
  x := x | (x >> 16);
  x := x | (x >> 32);
  return x + 1
}

/-- `presize_tables()`: the `app`, `lam`, `forallE` tables' persistent tiers at the least power of
two `≥ len(IN0) / 64`, `/ 512`, `/ 1024` slots (lane internspeed's `szall`). -/
-- con-ron: none — sizes three cons tables up front (`HashMap2::with_capacity`); con-ron's start empty (D42)
@[no_expose] def presizeTablesL : FunDecl := lfn () locals (n, z) {
  n := call pow2_at_least(len(L.Front.IN0.u8) >> 6);
  z := call app_presize(n);
  n := call pow2_at_least(len(L.Front.IN0.u8) >> 9);
  z := call lam_presize(n);
  n := call pow2_at_least(len(L.Front.IN0.u8) >> 10);
  z := call forall_presize(n);
  return 0
}

end L.Checker
