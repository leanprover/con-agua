import ConAgua.L.Notation
import ConAgua.Final.Statement
import ConAgua.Arena.Prelude
import ConAgua.Arena.NNumStore
import ConAgua.Arena.NStrStore
import ConAgua.Arena.IndIface
import ConAgua.Rom.PinRead
import ConAgua.Census.Attr

/-!
# The checker's entry `check()` and the integration glue (lane `integrate`)

`check()` is `ConAgua.Final.Statement`'s entry: no parameters, the input is byte array 0, the
pin-data buffer byte array 1. It runs `TwinAccepts`' stages in order (`pb_check`,
`internReservedPins`, `builtinPreludeE`, `parseChunks [b]`, `preparePrelude`, `internAllPins`,
`installThenCheck`); every twin error is an L `abort` inside its stage, and `check` returns
`ACCEPT` only after the last stage. `front_run` returns the number of the first line that did not
scan (`0` when all applied); then `check` returns `1`.

`entryProg` holds the functions the lanes' modules do not bind under one name to one body, and
the glue between the lanes' conventions; `scripts/checker_prog.py` gives its bindings priority
when it assembles `checkerProg` (`ConAgua/Checker/Prog.lean`). DESIGN.md, "The checker as one
program (lane `integrate`)".
-/

namespace L.Checker

open L L.Arena L.Ind

/-! ## Capacities at entry (ROADMAP §3, the driver lane's requirement) -/

/-- The word arrays the checker names (`0‥wordArrays - 1`; `checkerProg_arrs` checks it). -/
def wordArrays : Nat := 214

/-- The least `CTL` length `check` runs with: every fixed `CTL` slot the lanes use is below it
(the largest is `249`, the prelude parse's id tables), and `arenaR_init`'s `64 ≤ |CTL|`. -/
def ctlMin : Nat := 256

/-- The slot arrays of the 19 cons tables (`ConsLib.lean`): at least `consMinWords` words each
(the two tiers' initial tables, `consR_init`). -/
def slotArrs : List Nat := [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 26, 28, 30, 32, 34, 36, 38, 40]

/-- The slot arrays' least length, as a word. -/
def capMin : Word := UInt64.ofNat consMinWords

/-- `2^62 - consMinWords`, the slot arrays' wrapping bound. -/
def capLo : Word := UInt64.ofNat (2 ^ 62 - consMinWords)

/-- One array's capacity test: `2^62 ≤ len(b.u64)`, for a slot array also
`len(b.u64) < consMinWords` (as one wrapping comparison, `2^62 - consMinWords ≤ len - consMinWords`). -/
def capCond (b : Nat) : Cond :=
  if b ∈ slotArrs then .cmp .ule (.const capLo) (.bin .sub (.len64 b) (.const capMin))
  else .cmp .ule (.const 4611686018427387904) (.len64 b)

/-- The body of `cap_check()`: every word array shorter than `2^62` words (handles, offsets and
counts are words; `arenaR_init`'s pool bound, the inductive lines' scratch arrays), the slot
arrays at least `consMinWords` words long (`slotArrs`), `CTL` at
least `ctlMin` words, and the declaration arrays `DECL` (67) and `DLP` (68) not empty (their word
`0` is a count, `StateDR`). -/
def capCheckBody : Stmt :=
  (List.range wordArrays).foldr
    (fun b s => .seq (.ite (capCond b) .abort .skip) s)
    (.seq (.ite (.cmp .ult (.len64 CTL) (.const (UInt64.ofNat ctlMin))) .abort .skip)
      (.seq (.ite (.cmp .eq (.len64 67) (.const 0)) .abort .skip)
        (.seq (.ite (.cmp .eq (.len64 68) (.const 0)) .abort .skip)
          (.ret [.const 0]))))

/-- `cap_check()`: aborts unless the harness's capacities meet `ArenaR`'s minimums (a capacity
the checker cannot work with declines; any larger one is fine). -/
-- con-ron: none — the L memory's capacities (the twin's arrays grow; L's are fixed by the harness)
def capCheckL : FunDecl := { nparams := 0, nlocals := 0, body := capCheckBody }

/-- `check()`: the whole pipeline. -/
-- con-ron: ConRon/Arena/Main.lean:130-162 ConRon.Arena.runPipelineHead
-- con-ron: ConRon/Arena/Main.lean:164-190 ConRon.Arena.runPipelineTail
def checkL : FunDecl := lfn () locals (r, z) {
  z := call cap_check();
  z := call pb_check();
  z := call intern_reserved_pins();
  z := call builtin_prelude();
  r := call front_run();
  if r != 0 { return 1 };
  z := call prepare_prelude();
  z := call intern_all_pins();
  z := call install_then_check();
  return 71757147230292
}

example : (71757147230292 : Word) = ConAgua.Final.ACCEPT := rfl

/-! ## Adapters between the lanes' conventions

Lane `induct`'s callers pass the walk fuel first (`abstract1_fast(fuel, e, d, k)`,
`instantiate1_fast(fuel, e, v, d)`), lane `defeq`/`whnf`'s `inst1(e, v, d)` has no fuel; lane
`exprops4`'s entries are `abs_entry(e, d, k)` and `inst_entry(e, v, d)` (`Abs1Spec.lean`,
`Inst1Spec.lean`), which take none (their walks count their own). -/

/-- `abstract1_fast(fuel, e, d, k)`: `abs_entry(e, d, k)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1719-1725 ConRon.Arena.abstract1Fast
def abstract1FastA : FunDecl := lfn (f, e, d, k) locals (r) {
  r := call abs_entry(e, d, k);
  return r
}

/-- `instantiate1_fast(fuel, e, v, d)`: `inst_entry(e, v, d)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:377-384 ConRon.Arena.instantiate1Fast
def instantiate1FastA : FunDecl := lfn (f, e, v, d) locals (r) {
  r := call inst_entry(e, v, d);
  return r
}

/-- `inst1(e, v, d)`: `inst_entry(e, v, d)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:377-384 ConRon.Arena.instantiate1Fast
def inst1A : FunDecl := lfn (e, v, d) locals (r) {
  r := call inst_entry(e, v, d);
  return r
}

/-! ## `is_proj_fn_shape(n)` -/

/-- `is_proj_fn_shape(n)`: `NIdx.isProjFnShape` — `n` is `num (str _ s) _` with `s` `"proj"` or
`"projTable"`. The views abort where the twin's `viewN` throws (a handle past its tier's count, or
in the scratch tier while it is off). The string is compared byte by byte in the pool (one byte
per word, `NStrStore.lean`). -/
-- con-ron: ConRon/Arena/CheckerBase.lean:122-136 ConRon.Arena.NIdx.isProjFnShape
@[l_impl ConRon.Arena.NIdx.isProjFnShape]
def isProjFnShapeL : FunDecl := lfn (n) locals (t, i, p, o, l) {
  if 4294967295 < n { abort };
  if n >> 28 != 2 { return 0 };
  t := (n >> 27) & 1;
  i := n & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[38 + t] <= i { abort };
  p := NNREC.u64[i * 4 + t * 2];
  if 4294967295 < p { abort };
  if p >> 28 != 1 { return 0 };
  t := (p >> 27) & 1;
  i := p & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[36 + t] <= i { abort };
  o := NSREC.u64[i * 8 + t * 4 + 1];
  l := NSREC.u64[i * 8 + t * 4 + 2];
  if l != 4 && l != 9 { return 0 };
  if POOL.u64[o] != 112 || POOL.u64[o + 1] != 114 || POOL.u64[o + 2] != 111 ||
     POOL.u64[o + 3] != 106 { return 0 };
  if l == 4 { return 1 };
  if POOL.u64[o + 4] != 84 || POOL.u64[o + 5] != 97 || POOL.u64[o + 6] != 98 ||
     POOL.u64[o + 7] != 108 || POOL.u64[o + 8] != 101 { return 0 };
  return 1
}

/-! ## `basis_pin_hit(off, len)` -/

/-- `basis_pin_hit(off, len)` → `(ok, kind)`: `basisPinHit block` for the block `check_decl` built
(`ind_block_to_erec`: an `EREC` slice of `EREC` constant records) — the kinds `eqK`, `natK`,
`emptyK`, `falseK` (`0`‥`3`) in order, each pinned block interned first (`rom_basis_decls(kind)`, an
`IW` slice); the first kind whose member names equal the block's (the name pre-filter; a constant
record's name is its word `1`, `decCI`) decides by `canon_eq_list` (over `IW` slices: the block is
copied there, `er_to_iw`); no such kind is `(0, 0)`. -/
-- con-ron: ConRon/Arena/Basis.lean:53-69 ConRon.Arena.basisPinHitGo
-- con-ron: ConRon/Arena/Basis.lean:71-79 ConRon.Arena.basisPinHit
@[l_impl ConRon.Arena.basisPinHit]
def basisPinHitL : FunDecl := lfn (bo, bl) locals (k, o, l, j, e, q, ql) {
  k := 0;
  while k < 4 {
    (o, l) := call rom_basis_decls(k);
    if l == bl {
      j := 0;
      while j < l {
        if EREC.u64[IW.u64[o + j] + 1] != EREC.u64[EREC.u64[bo + j] + 1] { break };
        j += 1
      };
      if j == l {
        (q, ql) := call er_to_iw(bo, bl);
        e := call canon_eq_list(q, ql, o, l);
        if e != 0 { return (1, k) };
        return (0, 0)
      }
    };
    k += 1
  };
  return (0, 0)
}

/-! ## `ind_params_ok(nP, off, len)` -/

/-- `ind_params_ok(nP, off, len)`: `indParamsOk nP block` over the block's `EREC` slice of
constant records (`decCI`: an `indInfo` is `3, name, lps.off, lps.len, type, …`, a `ctorInfo`
`4, name, lps.off, lps.len, type, nP, nF`): a type former's telescope to a sort has at least `nP`
binders (no such telescope: fine), a constructor declares exactly `nP` parameters. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:425-438 ConRon.Arena.indParamsOk
@[l_impl ConRon.Arena.indParamsOk]
def indParamsOkL : FunDecl := lfn (np, o, l) locals (j, p, k, ok, n) {
  j := 0;
  while j < l {
    p := EREC.u64[o + j];
    k := EREC.u64[p];
    if k == 3 {
      (ok, n) := call pi_sort_tele_len(⟪CWF⟫, EREC.u64[p + 4]);
      if ok != 0 && n < np { return 0 }
    };
    if k == 4 {
      if EREC.u64[p + 5] != np { return 0 }
    };
    j += 1
  };
  return 1
}

/-- A function with no L code yet: it aborts (the checker declines). -/
-- con-ron: none — a placeholder for a function the lanes have not written (listed in `checkerStubs`)
def abortStub (n : Nat) : FunDecl := { nparams := n, nlocals := n, body := .abort }

/-- **The bindings `checkerProg` takes from here** (before any other module's). -/
def entryProg : Prog :=
  [("check", checkL), ("cap_check", capCheckL),
   -- the reserved pins at their ROM offset (lane `decls` binds it only parametrically, `IrpProg rom
   -- off p`; its readers read the pin-data buffer, `L.Rom.romProgPB`)
   ("intern_reserved_pins", L.Rom.internReservedPinsL),
   ("intern_all_pins", L.Rom.internAllPinsPB),
   ("abstract1_fast", abstract1FastA), ("instantiate1_fast", instantiate1FastA),
   ("inst1", inst1A),
   ("is_proj_fn_shape", isProjFnShapeL), ("basis_pin_hit", basisPinHitL),
   ("ind_params_ok", indParamsOkL)]

end L.Checker
