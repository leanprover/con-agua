module

public import ConAgua.Arena.JustifyIface
public import ConAgua.Arena.StubNames
public import ConAgua.Arena.DeclArmsNat
meta import ConAgua.Arena.JustifyIface
meta import ConAgua.Arena.IndIface
import ConAgua.Census.Attr

@[expose] public section

/-!
# What a record reads, in L (lane compare, helper H1)

The L translation of `vendor/con-ron/ConRon/Arena/Needs.lean` (Rust:
`crates/con-ron-core/src/arena/needs.rs`): the names a term, a constant's laws and a projection
table read, one memoised walk of each expression's DAG (`needs_go`). Its reader is the
solution's justification (the cone walk).

**The walk's state** (`NeedsSt`, the relation `NeedsR` of `JustifyIface.lean`) is in memory, not
passed: `seen` is the memo `ndSch` (`NDM`, keys the expression handles, value `1`), the names so
far the stack `NACC[0‥CTL[227])`. A function that returns the twin's new state returns nothing
here: it changes the memo and pushes onto the stack. `needs_reset` starts a fresh walk.

**Lists.** A list of names or expressions the twin reads off a record (`caps.all`, a rule's pins,
a table's bodies, the rules) is an `EREC` slice of the record; `natOpDeps` is `nat_op_deps`' `IW`
slice. The twin's recursions over a list with a cursor (`nidxAppend`, `NeedsSt.exprs`,
`NeedsSt.rules`) are loops. `pinFootprint`'s list is pushed onto the stack as it is built (the
twin's `x.names (← pinFootprint n)` appends it in the same order).

**Fuel.** `needs_go` takes the twin's fuel as its first argument (`CWF` at the top, `needs_expr`)
and aborts at `0`, where the twin fails with `.internal`. Every error of these functions is of
class `0` (the fuel, a dangling handle, the pins, the stack's and the memo's capacity): the twin's
errors here are all `.internal`.
-/

namespace L.Arena

open L.Ind L.Stubs

/-! ## The state -/

/-- `needs_reset()`: a fresh walk, the memo cleared and the stack emptied. -/
-- con-ron: ConRon/Arena/Needs.lean:30-32 ConRon.Arena.NeedsSt.empty
@[no_expose, l_impl ConRon.Arena.NeedsSt.empty]
def needsResetL : FunDecl := lfn () locals (u) {
  u := call nd_clear();
  CTL.u64[⟪NTOPC⟫] := 0;
  return 0
}

/-- `needs_name(n)`: one name pushed onto the stack (`abort` when it is full). -/
-- con-ron: ConRon/Arena/Needs.lean:95-98 ConRon.Arena.NeedsSt.name
@[no_expose, l_impl ConRon.Arena.NeedsSt.name]
def needsNameL : FunDecl := lfn (n) locals (t) {
  t := CTL.u64[⟪NTOPC⟫];
  if len(NACC.u64) <= t { abort };
  NACC.u64[t] := n;
  CTL.u64[⟪NTOPC⟫] := t + 1;
  return 0
}

/-- `needs_names(o, l)`: the names of the `EREC` slice `(o, l)` pushed in order. -/
-- con-ron: ConRon/Arena/Needs.lean:91-93 ConRon.Arena.NeedsSt.names
@[no_expose, l_impl ConRon.Arena.NeedsSt.names]
def needsNamesL : FunDecl := lfn (o, l) locals (i, u) {
  i := 0;
  while i < l {
    u := call needs_name(EREC⦃o + i⦄);
    i := i + 1
  };
  return 0
}

/-- `needs_names_iw(o, l)`: the names of the `IW` slice `(o, l)` pushed in order (the twin's
`nidxAppend acc ns 0 ns.length` at `natOpDeps`' list). -/
-- con-ron: ConRon/Arena/Needs.lean:34-37 ConRon.Arena.nidxAppend
@[no_expose, l_impl ConRon.Arena.nidxAppend]
def needsNamesIwL : FunDecl := lfn (o, l) locals (i, u) {
  i := 0;
  while i < l {
    u := call needs_name(IW.u64[o + i]);
    i := i + 1
  };
  return 0
}

/-! ## The walk -/

/-- `lit_needs(h)`: the names the literal `h` reads, pushed: the literal guards' ten names
(`litGuardNames`, the pins `1, 2, 3, 5‥10, 12`, all read first as the twin builds its list), a
numeral's the first three. The literal's kind is read off its node (`e_view` has checked it). -/
-- con-ron: ConRon/Arena/Needs.lean:39-46 ConRon.Arena.litNeeds
@[no_expose, l_impl ConRon.Arena.litNeeds]
def litNeedsL : FunDecl := lfn (h) locals (a, b, c, d, f, g, k, i, j, q, t, x, u) {
  a := call pin_at(1); b := call pin_at(2); c := call pin_at(3); d := call pin_at(5);
  f := call pin_at(6); g := call pin_at(7); k := call pin_at(8); i := call pin_at(9);
  j := call pin_at(10); q := call pin_at(12);
  u := call needs_name(a); u := call needs_name(b); u := call needs_name(c);
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  if LIT⟨t, x⟩.kind == 0 { return 0 };
  u := call needs_name(d); u := call needs_name(f); u := call needs_name(g);
  u := call needs_name(k); u := call needs_name(i); u := call needs_name(j);
  u := call needs_name(q);
  return 0
}

/-- `needs_go(f, h)`: the names `h` reads, pushed, one memoised walk of its DAG: the twin's fuel
`f` (abort at `0`, the children at `f - 1`); a leaf (`bvar`, `sort`) reads nothing, a literal its
guards' names, a constant its name; a compound node already in the memo nothing more, else its
children in order (a projection's structure name first) and then the node into the memo (after its
children, as the twin's `s.insert h true`). -/
-- con-ron: ConRon/Arena/Needs.lean:48-84 ConRon.Arena.needsGo
@[no_expose, l_impl ConRon.Arena.needsGo]
def needsGoL : FunDecl := lfn (f, h) locals (g, x, y, z, fd, j, d, u) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 || g == 2 { return 0 };
  if g == 8 { u := call lit_needs(h); return 0 };
  if g == 3 { u := call needs_name(x); return 0 };
  (fd, j, d) := call nd_find(h, 0);
  if fd != 0 { return 0 };
  if g == 1 { u := call needs_go(f - 1, y) }
  else if g == 4 || g == 5 || g == 6 {
    u := call needs_go(f - 1, x);
    u := call needs_go(f - 1, y)
  } else if g == 7 {
    u := call needs_go(f - 1, x);
    u := call needs_go(f - 1, y);
    u := call needs_go(f - 1, z)
  } else {
    u := call needs_name(x);
    u := call needs_go(f - 1, z)
  };
  (fd, j, d) := call nd_find(h, 0);
  u := call nd_put(h, 0, 1, fd, j);
  return 0
}

/-- `needs_expr(e)`: one more expression's names, at the core's walk fuel. -/
-- con-ron: ConRon/Arena/Needs.lean:86-89 ConRon.Arena.NeedsSt.expr
@[no_expose, l_impl ConRon.Arena.NeedsSt.expr]
def needsExprL : FunDecl := lfn (e) locals (u) {
  u := call needs_go(⟪CWF⟫, e);
  return 0
}

/-- `needs_exprs(o, l)`: the expressions of the `EREC` slice `(o, l)`, in order. -/
-- con-ron: ConRon/Arena/Needs.lean:100-106 ConRon.Arena.NeedsSt.exprs
@[no_expose, l_impl ConRon.Arena.NeedsSt.exprs]
def needsExprsL : FunDecl := lfn (o, l) locals (i, u) {
  i := 0;
  while i < l {
    u := call needs_expr(EREC⦃o + i⦄);
    i := i + 1
  };
  return 0
}

/-! ## Rules, constants, tables -/

/-- `needs_rule(q)`: what the recursor rule at `EREC` address `q` reads: its right-hand side, its
constructor, a nested datum's pins (`Rule.fire = 1`). -/
-- con-ron: ConRon/Arena/Needs.lean:108-115 ConRon.Arena.NeedsSt.rule
@[no_expose, l_impl ConRon.Arena.NeedsSt.rule]
def needsRuleL : FunDecl := lfn (q) locals (u) {
  u := call needs_expr(EREC⦃q + ⟪Rule.rhs⟫⦄);
  u := call needs_name(EREC⦃q + ⟪Rule.ctor⟫⦄);
  if EREC⦃q + ⟪Rule.fire⟫⦄ == 1 {
    u := call needs_exprs(EREC⦃q + ⟪Rule.pinsOff⟫⦄, EREC⦃q + ⟪Rule.pinsOff⟫ + 1⦄)
  };
  return 0
}

/-- `needs_rules(o, l)`: the `l` rules of `Rule.size` words from `EREC` address `o`, in order. -/
-- con-ron: ConRon/Arena/Needs.lean:117-123 ConRon.Arena.NeedsSt.rules
@[no_expose, l_impl ConRon.Arena.NeedsSt.rules]
def needsRulesL : FunDecl := lfn (o, l) locals (i, u) {
  i := 0;
  while i < l {
    u := call needs_rule(o + ⟪Rule.size⟫ * i);
    i := i + 1
  };
  return 0
}

/-- `pin_footprint_reduce(n)`: a compiler-trust operation's element type pushed
(`reduceOpNames`, pins 43, 44; `reduceElemName`: `Nat`, pin 1, for `Lean.reduceNat`, else
`Bool`, pin 29). -/
-- con-ron: ConRon/Arena/Needs.lean:125-129 ConRon.Arena.pinFootprintReduce
@[no_expose, l_impl ConRon.Arena.pinFootprintReduce]
def pinFootprintReduceL : FunDecl := lfn (n) locals (a, b, r, e, u) {
  a := call pin_at(43);
  b := call pin_at(44);
  if n == a || n == b {
    r := call pin_at(43);
    if n == r { e := call pin_at(1) } else { e := call pin_at(29) };
    u := call needs_name(e)
  };
  return 0
}

/-- `pin_footprint_nat(n)`: the operation's dependencies (`nat_op_deps`), the `Nat` basis (the
literal guards' first three names, `litGuardNames`' ten pins read as the twin's), and `Bool`, its
constructors for `Nat.beq` (pin 19), `Nat.ble` (pin 20) and the division (`natDivModNames`,
`pin_range_has(n, 21, 29)`), pushed. -/
-- con-ron: ConRon/Arena/Needs.lean:131-145 ConRon.Arena.pinFootprintNat
@[no_expose, l_impl ConRon.Arena.pinFootprintNat]
def pinFootprintNatL : FunDecl :=
    lfn (n) locals (o, l, a, b, c, d, f, g, k, i, j, q, be, bl, r, u) {
  (o, l) := call nat_op_deps(n);
  a := call pin_at(1); b := call pin_at(2); c := call pin_at(3); d := call pin_at(5);
  f := call pin_at(6); g := call pin_at(7); k := call pin_at(8); i := call pin_at(9);
  j := call pin_at(10); q := call pin_at(12);
  u := call needs_names_iw(o, l);
  u := call needs_name(a); u := call needs_name(b); u := call needs_name(c);
  be := call pin_at(19);
  bl := call pin_at(20);
  r := 1;
  if n != be && n != bl { r := call pin_range_has(n, 21, 29) };
  if r != 0 {
    a := call pin_at(29); b := call pin_at(30); c := call pin_at(31);
    u := call needs_name(a); u := call needs_name(b); u := call needs_name(c)
  };
  return 0
}

/-- `pin_footprint(n)`: the names a pinned constant's fast path reads, pushed: a certified `Nat`
operation's (`natOpNames`, `natDivModNames`: `nat_op_name`), then a compiler-trust operation's. -/
-- con-ron: ConRon/Arena/Needs.lean:147-156 ConRon.Arena.pinFootprint
@[no_expose, l_impl ConRon.Arena.pinFootprint]
def pinFootprintL : FunDecl := lfn (n) locals (r, u) {
  r := call nat_op_name(n);
  if r != 0 { u := call pin_footprint_nat(n) };
  u := call pin_footprint_reduce(n);
  return 0
}

/-- `needs_const(c)`: what the constant record at `EREC` address `c` reads: its type, a
definition's value (kind `1`), a recursor's rules (kind `5`), a type former's block (kind `3`,
`caps.all`), and its pin's fast-path names. -/
-- con-ron: ConRon/Arena/Needs.lean:158-169 ConRon.Arena.NeedsSt.const
@[no_expose, l_impl ConRon.Arena.NeedsSt.const]
def needsConstL : FunDecl := lfn (c) locals (k, u) {
  u := call needs_expr(EREC⦃c + ⟪CI.cv + CV.type⟫⦄);
  k := EREC⦃c⦄;
  if k == 1 { u := call needs_expr(EREC⦃c + ⟪CI.defnValue⟫⦄) }
  else if k == 5 {
    u := call needs_rules(EREC⦃c + ⟪CI.recRulesOff⟫⦄, EREC⦃c + ⟪CI.recRulesLen⟫⦄)
  } else if k == 3 {
    u := call needs_names(EREC⦃c + ⟪CI.indCaps + Caps.allOff⟫⦄,
      EREC⦃c + ⟪CI.indCaps + Caps.allOff⟫ + 1⦄)
  };
  u := call pin_footprint(EREC⦃c + ⟪CI.cv + CV.name⟫⦄);
  return 0
}

/-- `needs_table(t)`: what the table record at `EREC` address `t` reads: its structure, its
constructor, its bodies. -/
-- con-ron: ConRon/Arena/Needs.lean:171-174 ConRon.Arena.NeedsSt.table
@[no_expose, l_impl ConRon.Arena.NeedsSt.table]
def needsTableL : FunDecl := lfn (t) locals (u) {
  u := call needs_name(EREC⦃t + ⟪ProjTbl.structName⟫⦄);
  u := call needs_name(EREC⦃t + ⟪ProjTbl.ctor⟫⦄);
  u := call needs_exprs(EREC⦃t + ⟪ProjTbl.bodiesOff⟫⦄, EREC⦃t + ⟪ProjTbl.bodiesOff⟫ + 1⦄);
  return 0
}

/-! ## The module's program -/

/-- This module's functions. -/
def needsProg : Prog :=
  [("needs_reset", needsResetL), ("needs_name", needsNameL), ("needs_names", needsNamesL),
   ("needs_names_iw", needsNamesIwL), ("lit_needs", litNeedsL), ("needs_go", needsGoL),
   ("needs_expr", needsExprL), ("needs_exprs", needsExprsL), ("needs_rule", needsRuleL),
   ("needs_rules", needsRulesL), ("pin_footprint_reduce", pinFootprintReduceL),
   ("pin_footprint_nat", pinFootprintNatL), ("pin_footprint", pinFootprintL),
   ("needs_const", needsConstL), ("needs_table", needsTableL)]

end L.Arena
