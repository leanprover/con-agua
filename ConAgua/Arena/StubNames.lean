
/-!
# Former stubs: names, level lists, the fvar-range read (lane `stubs`)

L code for callees of the inductive stage that were `abortStub`s in `checkerProg` (their
`RelAM` contracts are lane `induct`'s, `IndStubs.lean`, still `sorry`):

* `fvar_b(f, e)`: the twin's `fvarB fuel e`, which `ab_fvb(e, f)` (`Abs1.lean`) already is; an
  adapter for the argument order of the inductive stage's calls.
* `reserved_rec_name(n)`: `reservedRecName`: the reserved basis names (`reserved_contains`),
  the ten literal-guard pins, the seven `Nat` operations, the eight `Nat` div/mod operations,
  each read off the pin table and compared as handles, in the twin's order.
* `name_rec(n)`, `name_rec_i(n, i)`: `internNNode (.str n "rec")`, `internNNode (.str n
  s!"rec_{i}")`: the string written at the pool top, one character per word (as
  `proj_table_name`), then `intern_nstr`.
* `intern_ls_iw(o, l)`: `internLsNode` of an `IW` slice of level handles: the slice copied to
  the pool top (as `spn_ls` does for a stack slice), then `intern_ls`.
-/

namespace L.Stubs

open L.Arena L.Ind

/-- con-ron: ConRon/Arena/ExprOps.lean:1574-1580 ConRon.Arena.fvarB -/
@[l_impl ConRon.Arena.fvarB]
def fvarBL : FunDecl := lfn (f, e) locals (r) {
  r := call ab_fvb(e, f);
  return r
}

/-! ## `reserved_rec_name(n)` -/

/-- `pin_range_has(n, k, hi)`: `n` is one of the pins `k ‥ hi - 1` (`pin_at`, in order). -/
-- con-ron: ConRon/Arena/Core.lean:876-882 ConRon.Arena.natOpNames
-- con-ron: ConRon/Arena/Core.lean:884-890 ConRon.Arena.natDivModNames
def pinRangeHas : FunDecl := lfn (n, k, hi) locals (w, r) {
  if hi <= k { return 0 };
  w := call pin_at(k);
  if w == n { return 1 };
  r := call pin_range_has(n, k + 1, hi);
  return r
}

/-- `lit_guard_has(n)`: `(← litGuardNames).contains n`: the pins `Nat`, `Nat.zero`, `Nat.succ`,
`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat` (slots 1, 2, 3,
5‥10, 12), all read first, as the twin builds its list. -/
-- con-ron: ConRon/Arena/Core.lean:1458-1474 ConRon.Arena.litGuardNames
@[l_impl ConRon.Arena.litGuardNames]
def litGuardHas : FunDecl := lfn (n) locals (a, b, c, d, f, g, h, i, j, k) {
  a := call pin_at(1); b := call pin_at(2); c := call pin_at(3); d := call pin_at(5);
  f := call pin_at(6); g := call pin_at(7); h := call pin_at(8); i := call pin_at(9);
  j := call pin_at(10); k := call pin_at(12);
  if n == a || n == b || n == c || n == d || n == f || n == g || n == h || n == i ||
    n == j || n == k { return 1 };
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:1476-1491 ConRon.Arena.reservedRecName -/
@[l_impl ConRon.Arena.reservedRecName]
def reservedRecNameL : FunDecl := lfn (n) locals (r) {
  r := call reserved_contains(n);
  if r != 0 { return 1 };
  r := call lit_guard_has(n);
  if r != 0 { return 1 };
  r := call pin_range_has(n, 14, 21);
  if r != 0 { return 1 };
  r := call pin_range_has(n, 21, 29);
  return r
}

/-! ## `name_rec(n)`, `name_rec_i(n, i)` -/

/-- `pool_room(k)`: `k` words at the pool top, reserved (the top raised): their offset. -/
-- con-ron: none — L scratch-array plumbing (the twin's strings are values)
def poolRoom : FunDecl := lfn (k) locals (o) {
  o := CTL.u64[0];
  if o + k < o { abort };
  if len(POOL⟨⦃o⦄.tier⟩) < ⦃o⦄.idx + k { abort };
  CTL.u64[0] := o + k;
  return o
}

/-- `name_rec(n)`: the name `n.rec`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:287-295 ConRon.Arena.blockRecNameSetOk
def nameRecL : FunDecl := lfn (n) locals (o, s, pt, pb) {
  o := call pool_room(3);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 114;
  POOL⟨pt⟩[pb + 1] := 101;
  POOL⟨pt⟩[pb + 2] := 99;
  s := call intern_nstr(n, o, 3);
  if s >= 4294967296 { abort };
  return s
}

/-- `dec_len(x)`: the number of decimal digits of `x` (`1` for `0`); `x / 10` is
`mulhi(x, ⌈2^67 / 10⌉) >> 3`, exact on every word. -/
-- con-ron: none — `Nat.repr`'s length (the twin's `s!"rec_{i + 1}"`)
def decLen : FunDecl := lfn (x) locals (k) {
  k := 1;
  while 9 < x {
    x := mulhi(x, 14757395258967641293) >> 3;
    k += 1
  };
  return k
}

/-- `name_rec_i(n, i)`: the name `n.rec_i` (`i` in decimal). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
def nameRecIL : FunDecl := lfn (n, i) locals (k, o, j, x, q, s, pt, pb) {
  k := call dec_len(i);
  o := call pool_room(k + 4);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 114;
  POOL⟨pt⟩[pb + 1] := 101;
  POOL⟨pt⟩[pb + 2] := 99;
  POOL⟨pt⟩[pb + 3] := 95;
  j := pb + 4 + k;
  x := i;
  while pb + 4 < j {
    j -= 1;
    q := mulhi(x, 14757395258967641293) >> 3;
    POOL⟨pt⟩[j] := 48 + (x - q * 10);
    x := q
  };
  s := call intern_nstr(n, o, k + 4);
  if s >= 4294967296 { abort };
  return s
}

/-! ## `intern_ls_iw(o, l)` -/

/-- `iw_pool(s, d, l)`: `POOL[d + j] := IW[s + j]` for `j < l`. -/
-- con-ron: none — L scratch-array plumbing (the twin's list is a value)
def iwPool : FunDecl := lfn (s, d, l) locals (u, pt, pb) {
  if l == 0 { return 0 };
  pt := ⦃d⦄.tier;
  pb := ⦃d⦄.idx;
  POOL⟨pt⟩[pb] := IW.u64[s];
  u := call iw_pool(s + 1, d + 1, l - 1);
  return 0
}

/-- `intern_ls_iw(o, l)`: the `IW` slice of level handles, copied to the pool top and interned
as a list node. -/
-- con-ron: ConRon/Arena/Monad.lean:499-515 ConRon.Arena.internLsNode
def internLsIwL : FunDecl := lfn (o, l) locals (top, u, h) {
  top := call pool_room(l);
  u := call iw_pool(o, top, l);
  h := call intern_ls(top, l);
  if h >= 4294967296 { abort };
  return h
}

end L.Stubs
