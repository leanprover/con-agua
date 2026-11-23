module

public import ConAgua.Arena.Freeze
public import ConAgua.Arena.Globals
public import ConAgua.Arena.RomPins
public import ConAgua.Checker.Presize

@[expose] public section

/-!
# The checker's entry `check()` and the integration glue (lane `integrate`)

`check()` is the compiled program's entry: no parameters, the input is byte array 0, the
pin-data buffer byte array 1. It dispatches on the mode word the entry stubs write (below):
entry 1 (`check_a`) runs `TwinAccepts`' stages in order (`pb_check`, the tables' presize
`presize_tables` (`Checker/Presize.lean`), `internReservedPins`,
`builtinPreludeE`, `parseChunks [b]`, `preparePrelude`, `internAllPins`) and phase A
(`installFold`); entry 2 (`check_b`) runs phase B's pending checks. Every twin error is an L
`abort` inside its stage, and only `check_b` returns `ACCEPT`. `front_run` returns the number of
the first line that did not scan (`0` when all applied); then `check_a` returns `1`.

`entryProg` holds the functions the lanes' modules do not bind under one name to one body, and
the glue between the lanes' conventions; `scripts/checker_prog.py` gives its bindings priority
when it assembles `checkerProg` (`ConAgua/Checker/Prog.lean`). DESIGN.md, "The checker as one
program (lane `integrate`)".
-/

namespace L.Checker

open L L.Arena L.Ind

/-! ## Capacities at entry (the arrays the driver lays out must be there and in range) -/

/-- The least `CTL` length `check` runs with: every fixed `CTL` slot the lanes use is below it
(the largest is `249`, the prelude parse's id tables), and `arenaR_init`'s `64 ≤ |CTL|`. -/
def ctlMin : Nat := 256

/-- The slot arrays of the 19 cons tables (`ConsLib.lean`), both tiers: at least
`consMinWords` words each (the initial table, `consR_init`) and below `2^61` (the growth's
offsets, `TierLay`). -/
def slotArrs : List TieredArray := tier0s [SLOT, ASLOT, SSLOT, ZSLOT, MSLOT, ISLOT, PSLOT, SOSLOT, CSLOT,
  LESLOT, BSLOT, FVSLOT, LASLOT, FASLOT, PJSLOT, NASLOT, NSSLOT, NNSLOT, LSSLOT] ++
  tier1s [SLOT, ASLOT, SSLOT, ZSLOT, MSLOT, ISLOT, PSLOT, SOSLOT, CSLOT, LESLOT, BSLOT, FVSLOT,
  LASLOT, FASLOT, PJSLOT, NASLOT, NSSLOT, NNSLOT, LSSLOT]

/-- The word slots `cap_check` tests, as (array, tier 1?) pairs: every word array of the table
(`(a, false)`), then the tier 1 of every tiered one (`(a, true)`). Their arrays (`capSlotA`) are
the table's word slots (`capSlots_arrs`). -/
def capSlots : List (ArrId × Bool) :=
  (checkerArrays.ids .word).map (·, false) ++ checkerArrays.tieredIds.map (·, true)

/-- A slot's array: `a` or `tier1 a`. -/
def capSlotA (p : ArrId × Bool) : TieredArray := if p.2 then tier1 p.1 else ↑p.1

/-- A slot's length as code: `len(a.u64)`, or for tier 1 the tiered access `len(a⟨1⟩.u64)`,
so that no tier-1 number appears in the program. -/
def capSlotE (p : ArrId × Bool) : Expr := if p.2 then .len64t p.1 (.const 1) else .len64 p.1

theorem capSlots_arrs : capSlots.map capSlotA = checkerArrays.wordSlots := by
  simp [capSlots, capSlotA, ArrTable.wordSlots, Function.comp_def]

/-- The slot arrays' least length, as a word. -/
def capMin : Word := UInt64.ofNat consMinWords

/-- `2^61 - consMinWords`, the slot arrays' wrapping bound. -/
def capLo : Word := UInt64.ofNat (2 ^ 61 - consMinWords)

/-- One slot's capacity test: `2^62 ≤ len`, for a slot array `len < consMinWords` or
`2^61 ≤ len` (as one wrapping comparison, `2^61 - consMinWords ≤ len - consMinWords`). -/
def capCond (p : ArrId × Bool) : Cond :=
  if capSlotA p ∈ slotArrs then .cmp .ule (.const capLo) (.bin .sub (capSlotE p) (.const capMin))
  else .cmp .ule (.const 4611686018427387904) (capSlotE p)

/-- One slot's check (the `foldr`'s step). -/
def capStep (p : ArrId × Bool) (s : Stmt) : Stmt :=
  .seq (.ite (capCond p) (.abort (.const R_CAP_REGION)) .skip) s

/-- The `CTL`, `DECL`, `DLP` checks, the pool's and the record pool's two tiers (tier 1 as the
tiered access `len(POOL⟨1⟩.u64)`, `len(EREC⟨1⟩.u64)`), and the return. -/
def capTail : Stmt :=
  .seq (.ite (.cmp .ult (.len64 CTL) (.const (UInt64.ofNat ctlMin))) (.abort (.const R_CAP_REGION)) .skip)
    (.seq (.ite (.cmp .eq (.len64 L.Front.DECL) (.const 0)) (.abort (.const R_CAP_REGION)) .skip)
      (.seq (.ite (.cmp .eq (.len64 L.Front.DLP) (.const 0)) (.abort (.const R_CAP_REGION)) .skip)
        (.seq (.ite (.cmp .ule (.const 1099511627776) (.len64 POOL)) (.abort (.const R_CAP_REGION)) .skip)
          (.seq (.ite (.cmp .ule (.const 1099511627776) (.len64t POOL (.const 1)))
              (.abort (.const R_CAP_REGION)) .skip)
            (.seq (.ite (.cmp .ule (.const 1099511627776) (.len64 EREC)) (.abort (.const R_CAP_REGION)) .skip)
              (.seq (.ite (.cmp .ule (.const 1099511627776) (.len64t EREC (.const 1)))
                  (.abort (.const R_CAP_REGION)) .skip)
                (.ret [.const 0])))))))

/-- The body of `cap_check()`, a fold over the table's word slots (`capSlots`): every word
array shorter than `2^62` words (handles, offsets and counts are words; `arenaR_init`'s pool
bound, the inductive lines' scratch arrays), the slot arrays at least `consMinWords` and below
`2^61` words long (`slotArrs`), `CTL` at least `ctlMin` words, the declaration arrays `DECL` and
`DLP` not empty (their word `0` is a count, `StateDR`), and the pool's and the record pool's two
tiers below `2^40` words (lane tierpool: a tagged address's index has 40 bits). -/
def capCheckBody : Stmt := capSlots.foldr capStep capTail

/-- `cap_check()`: aborts unless the harness's capacities meet `ArenaR`'s minimums (a capacity
the checker cannot work with declines; any larger one is fine). -/
-- con-ron: none — the L memory's capacities (the twin's arrays grow; L's are fixed by the harness)
@[no_expose] def capCheckL : FunDecl := { nparams := 0, nlocals := 0, body := capCheckBody }

/-! ## The parallel mode's entries (lane parmode, docs/design/parmode.md)

`check` reads the global `MODE`, which the entry stubs write (`Compiler/Abi.lean`): `0` (the
region's zero; no entry leaves it) aborts; `1` (`ca_start_a`, entry 1) is
`check_a(1)`: the stages, the stream index and `par_compact` (the frozen buffer in `OUT`,
`Arena/Freeze.lean`), returning `2^63 + k` for `k` records (jobs); `3` (the sequential driver's
entry 1) is `check_a(0)`, the same with the buffer's header only; `2` (`ca_check_b`,
`ca_check_seq`, entry 2) is `check_b`: the jobs `PLO‥PHI-1`; `4`‥`6` `--compare`'s runs. -/

/-- `check_a(c)`: `check`'s stages, then the stream index and the frozen buffer (`c ≠ 0`: header
and images; `c = 0`: the header only); returns `2^63 + k` for the `k` records (`1` if a line did
not scan). -/
-- con-ron: ConRon/Arena/Main.lean:142-174 ConRon.Arena.runPipelineHead
-- con-ron: ConRon/Arena/Checker.lean:101-111 ConRon.Arena.checkStream
@[no_expose] def checkAL : FunDecl := lfn (c) locals (r, z, cnt) {
  z := call cap_check();
  z := call pb_check();
  z := call presize_tables();
  z := call intern_reserved_pins();
  z := call builtin_prelude();
  r := call front_run();
  if r != 0 { return 1 };
  z := call prepare_prelude();
  z := call intern_all_pins();
  cnt := L.Front.DECL.u64[0];
  z := call build_index(cnt);
  z := call par_compact(c);
  return 9223372036854775808 + cnt
}

/-- `check_b()`: on the worker region's first call the seed (`CTL`) from the buffer; on every call
the core caches flushed (the worker's empty caches: in place, the index build's level-equality
entries would remain; between two calls they are empty already, every job ending in
`scratch_drop`), then the jobs `PLO‥PHI-1` (`PHI` at most the number of records), in order, from
the worker's state, as the pool's worker does (`checkJobList`); returns `ACCEPT`. -/
-- con-ron: ConRon/Arena/Checker.lean:65-73 ConRon.Arena.AState.worker
-- con-ron: ConRon/Arena/Pooled.lean:33-46 ConRon.Arena.PooledAccepts
@[no_expose, l_impl ConRon.Arena.AState.worker] def checkBL : FunDecl := lfn () locals (z, n) {
  if INIT == 0 {
    n := len(CTLF.u64);
    copy!(CTL.u64, 0, CTLF.u64, 0, n);
    INIT := 1
  };
  z := call flush_caches();
  if L.Front.DECL.u64[0] < PHI { abort };
  if PHI < PLO { abort };
  z := call check_jobs(PLO, PHI);
  return 71757147230292
}

/-- `check()`: one of the parallel mode's entries, by the mode word; any other mode aborts. -/
-- con-ron: none — the dispatch on the mode word the entry stubs write (`Compiler/Abi.lean`)
@[no_expose] def checkL : FunDecl := lfn () locals (r) {
  if MODE == 1 { r := call check_a(1); return r };
  if MODE == 3 { r := call check_a(0); return r };
  if MODE == 2 { r := call check_b(); return r };
  if MODE == 4 { r := call check_c1(); return r };
  if MODE == 5 { r := call check_c2(); return r };
  if MODE == 6 { r := call check_c3(); return r };
  abort
}

/-! ## Adapters between the lanes' conventions

Lane `induct`'s callers pass the walk fuel first (`abstract1_fast(fuel, e, d, k)`,
`instantiate1_fast(fuel, e, v, d)`), lane `defeq`/`whnf`'s `inst1(e, v, d)` has no fuel; lane
`exprops4`'s entries are `abs_entry(e, d, k)` and `inst_entry(e, v, d)` (`Abs1Spec.lean`,
`Inst1Spec.lean`), which take none (their walks count their own). -/

/-- `abstract1_fast(fuel, e, d, k)`: `abs_entry(e, d, k)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1750-1756 ConRon.Arena.abstract1Fast
@[no_expose] def abstract1FastA : FunDecl := lfn (f, e, d, k) locals (r) {
  r := call abs_entry(e, d, k);
  return r
}

/-- `instantiate1_fast(fuel, e, v, d)`: `inst_entry(e, v, d)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:378-385 ConRon.Arena.instantiate1Fast
@[no_expose] def instantiate1FastA : FunDecl := lfn (f, e, v, d) locals (r) {
  r := call inst_entry(e, v, d);
  return r
}

/-- `inst1(e, v, d)`: `inst_entry(e, v, d)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:378-385 ConRon.Arena.instantiate1Fast
@[no_expose] def inst1A : FunDecl := lfn (e, v, d) locals (r) {
  r := call inst_entry(e, v, d);
  return r
}

/-! ## `ind_params_ok(nP, off, len)` -/

/-- `ind_params_ok(nP, off, len)`: `indParamsOk nP block` over the block's `EREC` slice of
constant records (`decCI`: an `indInfo` is `3, name, lps.off, lps.len, type, …`, a `ctorInfo`
`4, name, lps.off, lps.len, type, nP, nF`): a type former's telescope to a sort has at least `nP`
binders (no such telescope: fine), a constructor declares exactly `nP` parameters. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:298-311 ConRon.Arena.indParamsOk
@[no_expose, l_impl ConRon.Arena.indParamsOk]
def indParamsOkL : FunDecl := lfn (np, o, l) locals (j, p, k, ok, n) {
  j := 0;
  for j < l {
    p := EREC⦃o + j⦄;
    k := EREC⦃p⦄;
    if k == 3 {
      (ok, n) := call pi_sort_tele_len(⟪CWF⟫, EREC⦃p + ⟪CI.cv + CV.type⟫⦄);
      if ok != 0 && n < np { return 0 }
    };
    if k == 4 {
      if EREC⦃p + ⟪CI.ctorNparams⟫⦄ != np { return 0 }
    }
  };
  return 1
}

/-- A function with no L code yet: it aborts (the checker declines). -/
-- con-ron: none — a placeholder for a function the lanes have not written (listed in `checkerStubs`)
def abortStub (n : Nat) : FunDecl := { nparams := n, nlocals := n, body := .abort (.const 0) }

/-- **The bindings `checkerProg` takes from here** (before any other module's). -/
def entryProg : Prog :=
  [("check", checkL), ("check_a", checkAL), ("check_b", checkBL), ("par_compact", parCompactL),
   -- the frozen buffer's image functions (`Arena/Freeze.lean`), one per frozen entry
   ("fz_0", fzF 0), ("fz_1", fzF 1), ("fz_2", fzF 2), ("fz_3", fzF 3), ("fz_4", fzF 4),
   ("fz_5", fzF 5), ("fz_6", fzF 6), ("fz_7", fzF 7), ("fz_8", fzF 8), ("fz_9", fzF 9),
   ("fz_10", fzF 10), ("fz_11", fzF 11), ("fz_12", fzF 12), ("fz_13", fzF 13), ("fz_14", fzF 14),
   ("fz_15", fzF 15), ("fz_16", fzF 16), ("fz_17", fzF 17), ("fz_18", fzF 18), ("fz_19", fzF 19),
   ("fz_20", fzF 20), ("fz_21", fzF 21), ("fz_22", fzF 22), ("fz_23", fzF 23), ("fz_24", fzF 24),
   ("fz_25", fzF 25), ("fz_26", fzF 26), ("fz_27", fzF 27), ("fz_28", fzF 28), ("fz_29", fzF 29),
   ("fz_30", fzF 30), ("fz_31", fzF 31), ("fz_32", fzF 32), ("fz_33", fzF 33), ("fz_34", fzF 34),
   ("fz_35", fzF 35), ("fz_36", fzF 36), ("fz_37", fzF 37), ("fz_38", fzF 38), ("fz_39", fzF 39),
   ("fz_40", fzF 40), ("fz_41", fzF 41), ("fz_42", fzF 42), ("fz_43", fzF 43), ("fz_44", fzF 44),
   ("fz_45", fzF 45), ("fz_46", fzF 46), ("fz_47", fzF 47), ("fz_48", fzF 48), ("fz_49", fzF 49),
   ("fz_50", fzF 50), ("fz_51", fzF 51), ("fz_52", fzF 52), ("fz_53", fzF 53), ("fz_54", fzF 54),
   ("fz_55", fzF 55), ("fz_56", fzF 56), ("fz_57", fzF 57), ("fz_58", fzF 58),
   ("fz_59", fzF 59), ("fz_60", fzF 60), ("fz_61", fzF 61), ("fz_62", fzF 62), ("fz_63", fzF 63),
   ("cap_check", capCheckL),
   -- the parse's large cons tables sized from the input length (`Checker/Presize.lean`)
   ("presize_tables", presizeTablesL), ("pow2_at_least", pow2AtLeastL),
   ("app_presize", appPresizeL), ("lam_presize", lamPresizeL), ("forall_presize", forallPresizeL),
   -- the reserved pins at their ROM offset (lane `decls` binds it only parametrically, `IrpProg rom
   -- off p`; its readers read the pin-data buffer, `L.Rom.romProgPB`)
   ("intern_reserved_pins", L.Rom.internReservedPinsL),
   ("intern_all_pins", L.Rom.internAllPinsPB),
   ("abstract1_fast", abstract1FastA), ("instantiate1_fast", instantiate1FastA),
   ("inst1", inst1A),
   ("ind_params_ok", indParamsOkL)]

end L.Checker
