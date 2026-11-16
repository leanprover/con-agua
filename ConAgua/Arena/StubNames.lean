module

public import ConAgua.Arena.IndIface
import ConAgua.Census.Attr

@[expose] public section

/-!
# Former stubs: names, level lists, the fvar-range read (lane `stubs`)

L code for callees of the inductive stage that were `abortStub`s in `checkerProg` (their
`RelAM` contracts are lane `induct`'s, `IndStubs.lean`):

* `fvar_b(f, e)`: the twin's `fvarB fuel e`, which `ab_fvb(e, f)` (`Abs1.lean`) already is; an
  adapter for the argument order of the inductive stage's calls.
* `reserved_rec_name(n)`: `reservedRecName`: the ten literal-guard pins, the seven `Nat` operations, the eight `Nat` div/mod operations,
  `Bool` and its constructors, each read off the pin table and compared as handles, in the twin's
  order.
* `name_rec(n)`, `name_rec_i(n, i)`: `internNNode (.str n "rec")`, `internNNode (.str n
  s!"rec_{i}")`: the string written at the pool top, one character per word (as
  `proj_table_name`), then `intern_nstr`.
* `intern_ls_iw(o, l)`: `internLsNode` of an `IW` slice of level handles: the slice copied to
  the pool top (as `spn_ls` does for a stack slice), then `intern_ls`.
-/

namespace L.Stubs

open L.Arena L.Ind

/-- con-ron: ConRon/Arena/ExprOps.lean:1605-1611 ConRon.Arena.fvarB -/
@[no_expose, l_impl ConRon.Arena.fvarB]
def fvarBL : FunDecl := lfn (f, e) locals (r) {
  r := call ab_fvb(e, f);
  return r
}

/-! ## `reserved_rec_name(n)` -/

/-- `pin_range_has(n, k, hi)`: `n` is one of the pins `k ‥ hi - 1` (`pin_at`, in order). -/
-- con-ron: ConRon/Arena/Core.lean:954-960 ConRon.Arena.natOpNames
-- con-ron: ConRon/Arena/Core.lean:962-968 ConRon.Arena.natDivModNames
@[no_expose] def pinRangeHas : FunDecl := lfn (n, k, hi) locals (w, r) {
  if hi <= k { return 0 };
  w := call pin_at(k);
  if w == n { return 1 };
  r := call pin_range_has(n, k + 1, hi);
  return r
}

/-- `lit_guard_has(n)`: `(← litGuardNames).contains n`: the pins `Nat`, `Nat.zero`, `Nat.succ`,
`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat` (slots 1, 2, 3,
5‥10, 12), all read first, as the twin builds its list. -/
-- con-ron: ConRon/Arena/Core.lean:1571-1587 ConRon.Arena.litGuardNames
@[no_expose, l_impl ConRon.Arena.litGuardNames]
def litGuardHas : FunDecl := lfn (n) locals (a, b, c, d, f, g, h, i, j, k) {
  a := call pin_at(1); b := call pin_at(2); c := call pin_at(3); d := call pin_at(5);
  f := call pin_at(6); g := call pin_at(7); h := call pin_at(8); i := call pin_at(9);
  j := call pin_at(10); k := call pin_at(12);
  if n == a || n == b || n == c || n == d || n == f || n == g || n == h || n == i ||
    n == j || n == k { return 1 };
  return 0
}

/-- `nat_op_name(n)`: one of the certified operations' names (`natOpNames`, pins 14‥20, then
`natDivModNames`, pins 21‥28): only a definition may take one. -/
-- con-ron: ConRon/Arena/Core.lean:970-977 ConRon.Arena.natOpName
@[no_expose, l_impl ConRon.Arena.natOpName]
def natOpNameL : FunDecl := lfn (n) locals (r) {
  r := call pin_range_has(n, 14, 21);
  if r != 0 { return 1 };
  r := call pin_range_has(n, 21, 29);
  return r
}

/-- `reserved_rec_bool(n)`: `Bool` and its two constructors (pins 29, 30, 31), each read only when
the chain reaches it. -/
-- con-ron: ConRon/Arena/Core.lean:1589-1599 ConRon.Arena.reservedRecBool
@[no_expose, l_impl ConRon.Arena.reservedRecBool]
def reservedRecBoolL : FunDecl := lfn (n) locals (b) {
  b := call pin_at(29);
  if n == b { return 1 };
  b := call pin_at(30);
  if n == b { return 1 };
  b := call pin_at(31);
  return u64(n == b)
}

/-- con-ron: ConRon/Arena/Core.lean:1601-1616 ConRon.Arena.reservedRecName -/
@[no_expose, l_impl ConRon.Arena.reservedRecName]
def reservedRecNameL : FunDecl := lfn (n) locals (r) {
  r := call lit_guard_has(n);
  if r != 0 { return 1 };
  r := call pin_range_has(n, 14, 21);
  if r != 0 { return 1 };
  r := call pin_range_has(n, 21, 29);
  if r != 0 { return 1 };
  r := call reserved_rec_bool(n);
  return r
}

/-! ## `name_rec(n)`, `name_rec_i(n, i)` -/

/-- `pool_room(k)`: `k` words at the pool top, reserved (the top raised): their offset. -/
-- con-ron: none — L scratch-array plumbing (the twin's strings are values)
@[no_expose] def poolRoom : FunDecl := lfn (k) locals (o) {
  o := CTL.u64[0];
  if o + k < o { abort };
  if len(POOL⟨⦃o⦄.tier⟩) < ⦃o⦄.idx + k { abort };
  CTL.u64[0] := o + k;
  return o
}

/-- `name_rec(n)`: the name `n.rec`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:318-326 ConRon.Arena.blockRecNameSetOk
@[no_expose] def nameRecL : FunDecl := lfn (n) locals (o, s, pt, pb) {
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
@[no_expose] def decLen : FunDecl := lfn (x) locals (k) {
  k := 1;
  while 9 < x {
    x := mulhi(x, 14757395258967641293) >> 3;
    k += 1
  };
  return k
}

/-- `name_rec_i(n, i)`: the name `n.rec_i` (`i` in decimal). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:367-402 ConRon.Arena.targetRecPins
@[no_expose] def nameRecIL : FunDecl := lfn (n, i) locals (k, o, j, x, q, s, pt, pb) {
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
@[no_expose] def iwPool : FunDecl := lfn (s, d, l) locals (u, pt, pb) {
  if l == 0 { return 0 };
  pt := ⦃d⦄.tier;
  pb := ⦃d⦄.idx;
  POOL⟨pt⟩[pb] := IW.u64[s];
  u := call iw_pool(s + 1, d + 1, l - 1);
  return 0
}

/-- `intern_ls_iw(o, l)`: the `IW` slice of level handles, copied to the pool top and interned
as a list node. -/
-- con-ron: ConRon/Arena/Monad.lean:502-518 ConRon.Arena.internLsNode
@[no_expose] def internLsIwL : FunDecl := lfn (o, l) locals (top, u, h) {
  top := call pool_room(l);
  u := call iw_pool(o, top, l);
  h := call intern_ls(top, l);
  if h >= 4294967296 { abort };
  return h
}

end L.Stubs
