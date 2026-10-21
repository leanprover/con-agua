module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Scan.Common
public import ConAgua.Scan.Values
public import ConAgua.Scan.Member
public import ConAgua.Scan.Lit
public import ConAgua.Scan.Str
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The record loops (`scan_fast.rs:1434-3724`), validating only

One L function per record kind, as in Rust: `scan_X(i)` is Rust's `scan_X` (the opening brace)
with its `scan_X_loop` spliced in. The loop calls `next_member` and dispatches on the key code:
each key of the record checks its `seen` bit, scans its value, and sets the bit; any other key
is an error (`UnknownKey`). Each is proved against the generic model `objN` of
`ConAgua.Scan.Member` with the record's `bit`, `val`, `mask`.
-/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order

namespace L.Scan.Records

open L.Scan.Member
open L.Scan.Values

/-- The input buffer. -/
abbrev IN : ArrId := 0

grind_pattern [lang_grind] slotNatN_pos => slotNatN b ks v

/-- The end of a `true`/`false` at `v`, or `0`: what `scan_bool`'s three results
(`L.Scan.Lit.encBool`) say, read as the L code reads them. -/
def boolEndN (b : Array UInt8) (v : Word) : Word :=
  if (L.Scan.Lit.encBool (L.Scan.Lit.scanBoolN b v.toNat) v).headD 0 = 0 then 0
  else (L.Scan.Lit.encBool (L.Scan.Lit.scanBoolN b v.toNat) v).tail.tail.headD 0

attribute [local lang_grind] boolEndN


/-! ## `scan_str_name`: `{"pre":p,"str":s}` -/

def strNameLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 3) != 3 { return 0 };
      return ks + 1
    };
    if k == 47 {  -- `pre`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 56 {  -- `str`
      if (seen & 2) != 0 { return 0 };
      e := call scan_string(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanStrName : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪strNameLoop⟫
  };
  return 0
}

/-- The key bits of `{"pre":p,"str":s}`. -/
def strNameBit (k : Word) : Word :=
  if k = 47 then 1 else if k = 56 then 2 else 0
/-- The value scanners of `{"pre":p,"str":s}`. -/
def strNameVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 47 then slotNatN b ks v else if k = 56 then L.Scan.Str.scanStringN b v else 0
/-- `scan_str_name(i)`. -/
def strNameN (b : Array UInt8) (i : Word) : Word := objEntryN strNameBit (strNameVal b) 3 b i


/-! ## `scan_num_name`: `{"i":n,"pre":p}` -/

def numNameLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 3) != 3 { return 0 };
      return ks + 1
    };
    if k == 16 {  -- `i`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 47 {  -- `pre`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanNumName : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪numNameLoop⟫
  };
  return 0
}

/-- The key bits of `{"i":n,"pre":p}`. -/
def numNameBit (k : Word) : Word :=
  if k = 16 then 1 else if k = 47 then 2 else 0
/-- The value scanners of `{"i":n,"pre":p}`. -/
def numNameVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 16 then slotNatN b ks v else if k = 47 then slotNatN b ks v else 0
/-- `scan_num_name(i)`. -/
def numNameN (b : Array UInt8) (i : Word) : Word := objEntryN numNameBit (numNameVal b) 3 b i


/-! ## `scan_app`: `{"arg":A,"fn":F}` -/

def appLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 3) != 3 { return 0 };
      return ks + 1
    };
    if k == 3 {  -- `arg`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 13 {  -- `fn`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanApp : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪appLoop⟫
  };
  return 0
}

/-- The key bits of `{"arg":A,"fn":F}`. -/
def appBit (k : Word) : Word :=
  if k = 3 then 1 else if k = 13 then 2 else 0
/-- The value scanners of `{"arg":A,"fn":F}`. -/
def appVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 3 then slotNatN b ks v else if k = 13 then slotNatN b ks v else 0
/-- `scan_app(i)`. -/
def appN (b : Array UInt8) (i : Word) : Word := objEntryN appBit (appVal b) 3 b i


/-! ## `scan_binder`: a `lam` or `forallE` binder (con-leche's two loops have the same keys; Rust's `scan_binder_expr_loop`) -/

def binderLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 15) != 15 { return 0 };
      return ks + 1
    };
    if k == 5 {  -- `binderInfo`
      if (seen & 1) != 0 { return 0 };
      e := call scan_binder_info(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 6 {  -- `body`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else if k == 34 {  -- `name`
      if (seen & 4) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 4
    } else if k == 61 {  -- `type`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanBinder : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪binderLoop⟫
  };
  return 0
}

/-- The key bits of a `lam` or `forallE` binder (con-leche's two loops have the same keys; Rust's `scan_binder_expr_loop`). -/
def binderBit (k : Word) : Word :=
  if k = 5 then 1 else if k = 6 then 2 else if k = 34 then 4 else if k = 61 then 8 else 0
/-- The value scanners of a `lam` or `forallE` binder (con-leche's two loops have the same keys; Rust's `scan_binder_expr_loop`). -/
def binderVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 5 then binderInfoN b v else if k = 6 then slotNatN b ks v else if k = 34 then slotNatN b ks v else if k = 61 then slotNatN b ks v else 0
/-- `scan_binder(i)`. -/
def binderN (b : Array UInt8) (i : Word) : Word := objEntryN binderBit (binderVal b) 15 b i


/-! ## `scan_let`: a `letE` -/

def letELoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 27) != 27 { return 0 };
      return ks + 1
    };
    if k == 6 {  -- `body`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 34 {  -- `name`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else if k == 37 {  -- `nondep`
      if (seen & 4) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 61 {  -- `type`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else if k == 65 {  -- `value`
      if (seen & 16) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 16
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanLetE : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪letELoop⟫
  };
  return 0
}

/-- The key bits of a `letE`. -/
def letEBit (k : Word) : Word :=
  if k = 6 then 1 else if k = 34 then 2 else if k = 37 then 4 else if k = 61 then 8 else if k = 65 then 16 else 0
/-- The value scanners of a `letE`. -/
def letEVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 6 then slotNatN b ks v else if k = 34 then slotNatN b ks v else if k = 37 then boolEndN b v else if k = 61 then slotNatN b ks v else if k = 65 then slotNatN b ks v else 0
/-- `scan_let(i)`. -/
def letEN (b : Array UInt8) (i : Word) : Word := objEntryN letEBit (letEVal b) 27 b i


/-! ## `scan_const`: `{"name":N,"us":[…]}` -/

def constELoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 3) != 3 { return 0 };
      return ks + 1
    };
    if k == 34 {  -- `name`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 64 {  -- `us`
      if (seen & 2) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanConstE : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪constELoop⟫
  };
  return 0
}

/-- The key bits of `{"name":N,"us":[…]}`. -/
def constEBit (k : Word) : Word :=
  if k = 34 then 1 else if k = 64 then 2 else 0
/-- The value scanners of `{"name":N,"us":[…]}`. -/
def constEVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 34 then slotNatN b ks v else if k = 64 then (natListEntryN b v).1 else 0
/-- `scan_const(i)`. -/
def constEN (b : Array UInt8) (i : Word) : Word := objEntryN constEBit (constEVal b) 3 b i


/-! ## `scan_proj`: `{"idx":i,"struct":S,"typeName":T}` -/

def projLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 7) != 7 { return 0 };
      return ks + 1
    };
    if k == 17 {  -- `idx`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 58 {  -- `struct`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else if k == 62 {  -- `typeName`
      if (seen & 4) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 4
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanProj : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪projLoop⟫
  };
  return 0
}

/-- The key bits of `{"idx":i,"struct":S,"typeName":T}`. -/
def projBit (k : Word) : Word :=
  if k = 17 then 1 else if k = 58 then 2 else if k = 62 then 4 else 0
/-- The value scanners of `{"idx":i,"struct":S,"typeName":T}`. -/
def projVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 17 then slotNatN b ks v else if k = 58 then slotNatN b ks v else if k = 62 then slotNatN b ks v else 0
/-- `scan_proj(i)`. -/
def projN (b : Array UInt8) (i : Word) : Word := objEntryN projBit (projVal b) 7 b i


/-! ## `scan_rule`: a recursor rule -/

def ruleLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 7) != 7 { return 0 };
      return ks + 1
    };
    if k == 10 {  -- `ctor`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 36 {  -- `nfields`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else if k == 52 {  -- `rhs`
      if (seen & 4) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 4
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanRule : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪ruleLoop⟫
  };
  return 0
}

/-- The key bits of a recursor rule. -/
def ruleBit (k : Word) : Word :=
  if k = 10 then 1 else if k = 36 then 2 else if k = 52 then 4 else 0
/-- The value scanners of a recursor rule. -/
def ruleVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 10 then slotNatN b ks v else if k = 36 then slotNatN b ks v else if k = 52 then slotNatN b ks v else 0
/-- `scan_rule(i)`. -/
def ruleN (b : Array UInt8) (i : Word) : Word := objEntryN ruleBit (ruleVal b) 7 b i


/-! ## `scan_rules`: the `[…]` of rules -/

def rulesLoop : Stmt := lblk (i, cnt, w, c, e) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {
      i += 1
    } else if c == 93 {
      if w != 0 && cnt != 0 { return 0 };
      return i + 1
    } else if c == 44 {
      if w != 0 { return 0 };
      i += 1;
      w := 1
    } else if c == 123 {
      if w == 0 { return 0 };
      e := call scan_rule(i);
      if e == 0 { return 0 };
      if e <= i { return 0 };
      cnt += 1;
      i := e;
      w := 0
    } else {
      return 0
    }
  }
}

def scanRules : FunDecl := lfn (i) locals (cnt, w, c, e) {
  if i < len(IN.u8) && IN.u8[i] == 91 {
    i += 1;
    w := 1;
    ⟪rulesLoop⟫
  };
  return 0
}

/-- `scan_rules(i)`. -/
def rulesN (b : Array UInt8) (i : Word) : Word := objListEntryN (ruleN b) b i


/-! ## `scan_ind_rec`: a recursor of an inductive declaration -/

def indRecLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 2046) != 2046 { return 0 };
      return ks + 1
    };
    if k == 1 {  -- `all`
      if (seen & 1) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 26 {  -- `isUnsafe`
      if (seen & 2) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 27 {  -- `k`
      if (seen & 4) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 31 {  -- `levelParams`
      if (seen & 8) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 8
    } else if k == 34 {  -- `name`
      if (seen & 16) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 16
    } else if k == 40 {  -- `numIndices`
      if (seen & 32) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 32
    } else if k == 41 {  -- `numMinors`
      if (seen & 64) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 64
    } else if k == 42 {  -- `numMotives`
      if (seen & 128) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 128
    } else if k == 44 {  -- `numParams`
      if (seen & 256) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 256
    } else if k == 53 {  -- `rules`
      if (seen & 512) != 0 { return 0 };
      e := call scan_rules(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 512
    } else if k == 61 {  -- `type`
      if (seen & 1024) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1024
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanIndRec : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪indRecLoop⟫
  };
  return 0
}

/-- The key bits of a recursor of an inductive declaration. -/
def indRecBit (k : Word) : Word :=
  if k = 1 then 1 else if k = 26 then 2 else if k = 27 then 4 else if k = 31 then 8 else if k = 34 then 16 else if k = 40 then 32 else if k = 41 then 64 else if k = 42 then 128 else if k = 44 then 256 else if k = 53 then 512 else if k = 61 then 1024 else 0
/-- The value scanners of a recursor of an inductive declaration. -/
def indRecVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 1 then (natListEntryN b v).1 else if k = 26 then boolEndN b v else if k = 27 then boolEndN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 40 then slotNatN b ks v else if k = 41 then slotNatN b ks v else if k = 42 then slotNatN b ks v else if k = 44 then slotNatN b ks v else if k = 53 then rulesN b v else if k = 61 then slotNatN b ks v else 0
/-- `scan_ind_rec(i)`. -/
def indRecN (b : Array UInt8) (i : Word) : Word := objEntryN indRecBit (indRecVal b) 2046 b i


/-! ## `scan_ind_recs`: the `[…]` of recursors -/

def indRecsLoop : Stmt := lblk (i, cnt, w, c, e) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {
      i += 1
    } else if c == 93 {
      if w != 0 && cnt != 0 { return 0 };
      return i + 1
    } else if c == 44 {
      if w != 0 { return 0 };
      i += 1;
      w := 1
    } else if c == 123 {
      if w == 0 { return 0 };
      e := call scan_ind_rec(i);
      if e == 0 { return 0 };
      if e <= i { return 0 };
      cnt += 1;
      i := e;
      w := 0
    } else {
      return 0
    }
  }
}

def scanIndRecs : FunDecl := lfn (i) locals (cnt, w, c, e) {
  if i < len(IN.u8) && IN.u8[i] == 91 {
    i += 1;
    w := 1;
    ⟪indRecsLoop⟫
  };
  return 0
}

/-- `scan_ind_recs(i)`. -/
def indRecsN (b : Array UInt8) (i : Word) : Word := objListEntryN (indRecN b) b i


/-! ## `scan_ind_type`: a type of an inductive declaration -/

def indTypeLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 2046) != 2046 { return 0 };
      return ks + 1
    };
    if k == 1 {  -- `all`
      if (seen & 1) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 11 {  -- `ctors`
      if (seen & 2) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 24 {  -- `isRec`
      if (seen & 4) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 25 {  -- `isReflexive`
      if (seen & 8) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 8
    } else if k == 26 {  -- `isUnsafe`
      if (seen & 16) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 16
    } else if k == 31 {  -- `levelParams`
      if (seen & 32) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 32
    } else if k == 34 {  -- `name`
      if (seen & 64) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 64
    } else if k == 40 {  -- `numIndices`
      if (seen & 128) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 128
    } else if k == 43 {  -- `numNested`
      if (seen & 256) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 256
    } else if k == 44 {  -- `numParams`
      if (seen & 512) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 512
    } else if k == 61 {  -- `type`
      if (seen & 1024) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1024
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanIndType : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪indTypeLoop⟫
  };
  return 0
}

/-- The key bits of a type of an inductive declaration. -/
def indTypeBit (k : Word) : Word :=
  if k = 1 then 1 else if k = 11 then 2 else if k = 24 then 4 else if k = 25 then 8 else if k = 26 then 16 else if k = 31 then 32 else if k = 34 then 64 else if k = 40 then 128 else if k = 43 then 256 else if k = 44 then 512 else if k = 61 then 1024 else 0
/-- The value scanners of a type of an inductive declaration. -/
def indTypeVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 1 then (natListEntryN b v).1 else if k = 11 then (natListEntryN b v).1 else if k = 24 then boolEndN b v else if k = 25 then boolEndN b v else if k = 26 then boolEndN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 40 then slotNatN b ks v else if k = 43 then slotNatN b ks v else if k = 44 then slotNatN b ks v else if k = 61 then slotNatN b ks v else 0
/-- `scan_ind_type(i)`. -/
def indTypeN (b : Array UInt8) (i : Word) : Word := objEntryN indTypeBit (indTypeVal b) 2046 b i


/-! ## `scan_ind_types`: the `[…]` of types -/

def indTypesLoop : Stmt := lblk (i, cnt, w, c, e) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {
      i += 1
    } else if c == 93 {
      if w != 0 && cnt != 0 { return 0 };
      return i + 1
    } else if c == 44 {
      if w != 0 { return 0 };
      i += 1;
      w := 1
    } else if c == 123 {
      if w == 0 { return 0 };
      e := call scan_ind_type(i);
      if e == 0 { return 0 };
      if e <= i { return 0 };
      cnt += 1;
      i := e;
      w := 0
    } else {
      return 0
    }
  }
}

def scanIndTypes : FunDecl := lfn (i) locals (cnt, w, c, e) {
  if i < len(IN.u8) && IN.u8[i] == 91 {
    i += 1;
    w := 1;
    ⟪indTypesLoop⟫
  };
  return 0
}

/-- `scan_ind_types(i)`. -/
def indTypesN (b : Array UInt8) (i : Word) : Word := objListEntryN (indTypeN b) b i


/-! ## `scan_ind_ctor`: a constructor of an inductive declaration -/

def indCtorLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 252) != 252 { return 0 };
      return ks + 1
    };
    if k == 8 {  -- `cidx`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 22 {  -- `induct`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else if k == 26 {  -- `isUnsafe`
      if (seen & 4) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 31 {  -- `levelParams`
      if (seen & 8) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 8
    } else if k == 34 {  -- `name`
      if (seen & 16) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 16
    } else if k == 39 {  -- `numFields`
      if (seen & 32) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 32
    } else if k == 44 {  -- `numParams`
      if (seen & 64) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 64
    } else if k == 61 {  -- `type`
      if (seen & 128) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 128
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanIndCtor : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪indCtorLoop⟫
  };
  return 0
}

/-- The key bits of a constructor of an inductive declaration. -/
def indCtorBit (k : Word) : Word :=
  if k = 8 then 1 else if k = 22 then 2 else if k = 26 then 4 else if k = 31 then 8 else if k = 34 then 16 else if k = 39 then 32 else if k = 44 then 64 else if k = 61 then 128 else 0
/-- The value scanners of a constructor of an inductive declaration. -/
def indCtorVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 8 then slotNatN b ks v else if k = 22 then slotNatN b ks v else if k = 26 then boolEndN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 39 then slotNatN b ks v else if k = 44 then slotNatN b ks v else if k = 61 then slotNatN b ks v else 0
/-- `scan_ind_ctor(i)`. -/
def indCtorN (b : Array UInt8) (i : Word) : Word := objEntryN indCtorBit (indCtorVal b) 252 b i


/-! ## `scan_ind_ctors`: the `[…]` of constructors -/

def indCtorsLoop : Stmt := lblk (i, cnt, w, c, e) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {
      i += 1
    } else if c == 93 {
      if w != 0 && cnt != 0 { return 0 };
      return i + 1
    } else if c == 44 {
      if w != 0 { return 0 };
      i += 1;
      w := 1
    } else if c == 123 {
      if w == 0 { return 0 };
      e := call scan_ind_ctor(i);
      if e == 0 { return 0 };
      if e <= i { return 0 };
      cnt += 1;
      i := e;
      w := 0
    } else {
      return 0
    }
  }
}

def scanIndCtors : FunDecl := lfn (i) locals (cnt, w, c, e) {
  if i < len(IN.u8) && IN.u8[i] == 91 {
    i += 1;
    w := 1;
    ⟪indCtorsLoop⟫
  };
  return 0
}

/-- `scan_ind_ctors(i)`. -/
def indCtorsN (b : Array UInt8) (i : Word) : Word := objListEntryN (indCtorN b) b i


/-! ## `scan_axiom`: an `axiom` declaration -/

def axiomDLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 15) != 15 { return 0 };
      return ks + 1
    };
    if k == 26 {  -- `isUnsafe`
      if (seen & 1) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 31 {  -- `levelParams`
      if (seen & 2) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 34 {  -- `name`
      if (seen & 4) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 4
    } else if k == 61 {  -- `type`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanAxiomD : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪axiomDLoop⟫
  };
  return 0
}

/-- The key bits of an `axiom` declaration. -/
def axiomDBit (k : Word) : Word :=
  if k = 26 then 1 else if k = 31 then 2 else if k = 34 then 4 else if k = 61 then 8 else 0
/-- The value scanners of an `axiom` declaration. -/
def axiomDVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 26 then boolEndN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 61 then slotNatN b ks v else 0
/-- `scan_axiom(i)`. -/
def axiomDN (b : Array UInt8) (i : Word) : Word := objEntryN axiomDBit (axiomDVal b) 15 b i


/-! ## `scan_def`: a `def` declaration -/

def defDLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 124) != 124 { return 0 };
      return ks + 1
    };
    if k == 1 {  -- `all`
      if (seen & 1) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 15 {  -- `hints`
      if (seen & 2) != 0 { return 0 };
      e := call scan_hints(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 31 {  -- `levelParams`
      if (seen & 4) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 34 {  -- `name`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else if k == 54 {  -- `safety`
      if (seen & 16) != 0 { return 0 };
      e := call scan_string(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 16
    } else if k == 61 {  -- `type`
      if (seen & 32) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 32
    } else if k == 65 {  -- `value`
      if (seen & 64) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 64
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanDefD : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪defDLoop⟫
  };
  return 0
}

/-- The key bits of a `def` declaration. -/
def defDBit (k : Word) : Word :=
  if k = 1 then 1 else if k = 15 then 2 else if k = 31 then 4 else if k = 34 then 8 else if k = 54 then 16 else if k = 61 then 32 else if k = 65 then 64 else 0
/-- The value scanners of a `def` declaration. -/
def defDVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 1 then (natListEntryN b v).1 else if k = 15 then hintsN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 54 then L.Scan.Str.scanStringN b v else if k = 61 then slotNatN b ks v else if k = 65 then slotNatN b ks v else 0
/-- `scan_def(i)`. -/
def defDN (b : Array UInt8) (i : Word) : Word := objEntryN defDBit (defDVal b) 124 b i


/-! ## `scan_thm`: a `thm` declaration -/

def thmDLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 30) != 30 { return 0 };
      return ks + 1
    };
    if k == 1 {  -- `all`
      if (seen & 1) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 31 {  -- `levelParams`
      if (seen & 2) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 34 {  -- `name`
      if (seen & 4) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 4
    } else if k == 61 {  -- `type`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else if k == 65 {  -- `value`
      if (seen & 16) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 16
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanThmD : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪thmDLoop⟫
  };
  return 0
}

/-- The key bits of a `thm` declaration. -/
def thmDBit (k : Word) : Word :=
  if k = 1 then 1 else if k = 31 then 2 else if k = 34 then 4 else if k = 61 then 8 else if k = 65 then 16 else 0
/-- The value scanners of a `thm` declaration. -/
def thmDVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 1 then (natListEntryN b v).1 else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 61 then slotNatN b ks v else if k = 65 then slotNatN b ks v else 0
/-- `scan_thm(i)`. -/
def thmDN (b : Array UInt8) (i : Word) : Word := objEntryN thmDBit (thmDVal b) 30 b i


/-! ## `scan_opaque`: an `opaque` declaration -/

def opaqueDLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 62) != 62 { return 0 };
      return ks + 1
    };
    if k == 1 {  -- `all`
      if (seen & 1) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 26 {  -- `isUnsafe`
      if (seen & 2) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 31 {  -- `levelParams`
      if (seen & 4) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 34 {  -- `name`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else if k == 61 {  -- `type`
      if (seen & 16) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 16
    } else if k == 65 {  -- `value`
      if (seen & 32) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 32
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanOpaqueD : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪opaqueDLoop⟫
  };
  return 0
}

/-- The key bits of an `opaque` declaration. -/
def opaqueDBit (k : Word) : Word :=
  if k = 1 then 1 else if k = 26 then 2 else if k = 31 then 4 else if k = 34 then 8 else if k = 61 then 16 else if k = 65 then 32 else 0
/-- The value scanners of an `opaque` declaration. -/
def opaqueDVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 1 then (natListEntryN b v).1 else if k = 26 then boolEndN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 61 then slotNatN b ks v else if k = 65 then slotNatN b ks v else 0
/-- `scan_opaque(i)`. -/
def opaqueDN (b : Array UInt8) (i : Word) : Word := objEntryN opaqueDBit (opaqueDVal b) 62 b i


/-! ## `scan_quot`: a `quot` declaration -/

def quotDLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 15) != 15 { return 0 };
      return ks + 1
    };
    if k == 28 {  -- `kind`
      if (seen & 1) != 0 { return 0 };
      e := call scan_string(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 31 {  -- `levelParams`
      if (seen & 2) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 34 {  -- `name`
      if (seen & 4) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 4
    } else if k == 61 {  -- `type`
      if (seen & 8) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 8
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanQuotD : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪quotDLoop⟫
  };
  return 0
}

/-- The key bits of a `quot` declaration. -/
def quotDBit (k : Word) : Word :=
  if k = 28 then 1 else if k = 31 then 2 else if k = 34 then 4 else if k = 61 then 8 else 0
/-- The value scanners of a `quot` declaration. -/
def quotDVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 28 then L.Scan.Str.scanStringN b v else if k = 31 then (natListEntryN b v).1 else if k = 34 then slotNatN b ks v else if k = 61 then slotNatN b ks v else 0
/-- `scan_quot(i)`. -/
def quotDN (b : Array UInt8) (i : Word) : Word := objEntryN quotDBit (quotDVal b) 15 b i


/-! ## `scan_ind_decl`: an `inductive` declaration -/

def indDLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 26) != 26 { return 0 };
      return ks + 1
    };
    if k == 1 {  -- `all`
      if (seen & 1) != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 1
    } else if k == 11 {  -- `ctors`
      if (seen & 2) != 0 { return 0 };
      e := call scan_ind_ctors(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 2
    } else if k == 26 {  -- `isUnsafe`
      if (seen & 4) != 0 { return 0 };
      (ok, x, e) := call scan_bool(v);
      if ok == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 4
    } else if k == 50 {  -- `recs`
      if (seen & 8) != 0 { return 0 };
      e := call scan_ind_recs(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 8
    } else if k == 63 {  -- `types`
      if (seen & 16) != 0 { return 0 };
      e := call scan_ind_types(v);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      seen := seen | 16
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanIndD : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪indDLoop⟫
  };
  return 0
}

/-- The key bits of an `inductive` declaration. -/
def indDBit (k : Word) : Word :=
  if k = 1 then 1 else if k = 11 then 2 else if k = 26 then 4 else if k = 50 then 8 else if k = 63 then 16 else 0
/-- The value scanners of an `inductive` declaration. -/
def indDVal (b : Array UInt8) (k _ks v : Word) : Word :=
  if k = 1 then (natListEntryN b v).1 else if k = 11 then indCtorsN b v else if k = 26 then boolEndN b v else if k = 50 then indRecsN b v else if k = 63 then indTypesN b v else 0
/-- `scan_ind_decl(i)`. -/
def indDN (b : Array UInt8) (i : Word) : Word := objEntryN indDBit (indDVal b) 26 b i


/-! ## Specs -/

section specs
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpw : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hpd : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits)
    (hpk : p.lookup "key_end" = some L.Scan.Leaves.keyEnd)
    (hpn : p.lookup "num_end" = some L.Scan.Leaves.numEnd)
    (hpa1 : p.lookup "key_at_g1" = some L.Scan.Key.keyAtG1)
    (hpa2 : p.lookup "key_at_g2" = some L.Scan.Key.keyAtG2)
    (hpa3 : p.lookup "key_at_g3" = some L.Scan.Key.keyAtG3)
    (hpa4 : p.lookup "key_at_g4" = some L.Scan.Key.keyAtG4)
    (hpa5 : p.lookup "key_at_g5" = some L.Scan.Key.keyAtG5)
    (hpa6 : p.lookup "key_at_g6" = some L.Scan.Key.keyAtG6)
    (hpa : p.lookup "key_at" = some L.Scan.Key.keyAt)
    (hpv : p.lookup "value_at" = some L.Scan.Key.valueAt)
    (hpm : p.lookup "next_member" = some nextMember)
    (hps : p.lookup "slot_nat" = some slotNat)
    (hpmw : p.lookup "match_word" = some matchWord)
    (hpi : p.lookup "scan_binder_info" = some scanBinderInfo)
    (hph : p.lookup "scan_hints" = some scanHints)
    (hpl : p.lookup "scan_nat_list" = some scanNatList)
    (hpml : p.lookup "match_lit" = some L.Scan.Lit.matchLit)
    (hpb : p.lookup "scan_bool" = some L.Scan.Lit.scanBool)
    (hpc : p.lookup "utf8_char" = some L.Scan.Utf8.utf8Char)
    (hpu8 : p.lookup "utf8_valid" = some L.Scan.Str.utf8Valid)
    (hpbi : p.lookup "byte_in" = some L.Scan.Str.byteIn)
    (hphv : p.lookup "hex_val" = some L.Scan.Str.hexVal)
    (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4)
    (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
    (hpux : p.lookup "u_next" = some L.Scan.Str.uNext)
    (hpue : p.lookup "unescape" = some L.Scan.Str.unescape)
    (hpsc : p.lookup "str_close" = some L.Examples.strClose)
    (hpe : p.lookup "has_escape" = some L.Scan.Leaves.hasEscape)
    (hpt : p.lookup "scan_string" = some L.Scan.Str.scanString)
    (hp_strName : p.lookup "scan_str_name" = some scanStrName)
    (hp_numName : p.lookup "scan_num_name" = some scanNumName)
    (hp_app : p.lookup "scan_app" = some scanApp)
    (hp_binder : p.lookup "scan_binder" = some scanBinder)
    (hp_letE : p.lookup "scan_let" = some scanLetE)
    (hp_constE : p.lookup "scan_const" = some scanConstE)
    (hp_proj : p.lookup "scan_proj" = some scanProj)
    (hp_rule : p.lookup "scan_rule" = some scanRule)
    (hp_rules : p.lookup "scan_rules" = some scanRules)
    (hp_indRec : p.lookup "scan_ind_rec" = some scanIndRec)
    (hp_indRecs : p.lookup "scan_ind_recs" = some scanIndRecs)
    (hp_indType : p.lookup "scan_ind_type" = some scanIndType)
    (hp_indTypes : p.lookup "scan_ind_types" = some scanIndTypes)
    (hp_indCtor : p.lookup "scan_ind_ctor" = some scanIndCtor)
    (hp_indCtors : p.lookup "scan_ind_ctors" = some scanIndCtors)
    (hp_axiomD : p.lookup "scan_axiom" = some scanAxiomD)
    (hp_defD : p.lookup "scan_def" = some scanDefD)
    (hp_thmD : p.lookup "scan_thm" = some scanThmD)
    (hp_opaqueD : p.lookup "scan_opaque" = some scanOpaqueD)
    (hp_quotD : p.lookup "scan_quot" = some scanQuotD)
    (hp_indD : p.lookup "scan_ind_decl" = some scanIndD)
include hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD


attribute [local lang_grind] strNameBit strNameVal Mbr.err

theorem strNameLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n strNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN strNameBit (strNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := strNameLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem strNameLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) strNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN strNameBit (strNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (strNameLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanStrName_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_str_name" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [strNameN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_strName]
  simp only [callFn, scanStrName]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, strNameN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, strNameLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] numNameBit numNameVal Mbr.err

theorem numNameLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n numNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN numNameBit (numNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := numNameLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem numNameLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) numNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN numNameBit (numNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (numNameLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanNumName_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_num_name" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [numNameN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_numName]
  simp only [callFn, scanNumName]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, numNameN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, numNameLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] appBit appVal Mbr.err

theorem appLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n appLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN appBit (appVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := appLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem appLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) appLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN appBit (appVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (appLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanApp_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_app" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [appN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_app]
  simp only [callFn, scanApp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, appN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, appLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] binderBit binderVal Mbr.err

theorem binderLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n binderLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN binderBit (binderVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := binderLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        scanBinderInfo_spec p b hb ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem binderLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) binderLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN binderBit (binderVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (binderLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanBinder_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_binder" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [binderN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_binder]
  simp only [callFn, scanBinder]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, binderN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, binderLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] letEBit letEVal Mbr.err

theorem letELoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n letELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN letEBit (letEVal b) 27 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := letELoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem letELoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) letELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN letEBit (letEVal b) 27 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (letELoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanLetE_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_let" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [letEN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_letE]
  simp only [callFn, scanLetE]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, letEN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, letELoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] constEBit constEVal Mbr.err

theorem constELoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n constELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN constEBit (constEVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := constELoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem constELoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) constELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN constEBit (constEVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (constELoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanConstE_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_const" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [constEN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_constE]
  simp only [callFn, scanConstE]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, constEN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, constELoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] projBit projVal Mbr.err

theorem projLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n projLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN projBit (projVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := projLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem projLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) projLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN projBit (projVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (projLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanProj_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_proj" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [projN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_proj]
  simp only [callFn, scanProj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, projN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, projLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] ruleBit ruleVal Mbr.err

theorem ruleLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n ruleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN ruleBit (ruleVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := ruleLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem ruleLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) ruleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN ruleBit (ruleVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (ruleLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanRule_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_rule" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [ruleN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_rule]
  simp only [callFn, scanRule]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, ruleN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, ruleLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] Mbr.err

theorem rulesLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n rulesLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (ruleN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := rulesLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanRule_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish

theorem rulesLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) rulesLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (ruleN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (rulesLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanRules_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_rules" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [rulesN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_rules]
  simp only [callFn, scanRules]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, rulesN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, rulesLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] indRecBit indRecVal Mbr.err

-- eleven keys: all `finish` calls of the theorem share one heartbeat budget
set_option maxHeartbeats 800000 in
theorem indRecLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indRecBit (indRecVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indRecLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        scanRules_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem indRecLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indRecBit (indRecVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indRecLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_rec" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indRecN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indRec]
  simp only [callFn, scanIndRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indRecN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indRecLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] Mbr.err

theorem indRecsLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indRecsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indRecN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indRecsLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanIndRec_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish

theorem indRecsLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indRecsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indRecN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indRecsLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndRecs_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_recs" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indRecsN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indRecs]
  simp only [callFn, scanIndRecs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indRecsN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indRecsLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] indTypeBit indTypeVal Mbr.err

-- eleven keys: all `finish` calls of the theorem share one heartbeat budget
set_option maxHeartbeats 800000 in
theorem indTypeLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indTypeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indTypeBit (indTypeVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indTypeLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem indTypeLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indTypeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indTypeBit (indTypeVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indTypeLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndType_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_type" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indTypeN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indType]
  simp only [callFn, scanIndType]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indTypeN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indTypeLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] Mbr.err

theorem indTypesLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indTypesLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indTypeN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indTypesLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanIndType_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish

theorem indTypesLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indTypesLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indTypeN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indTypesLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndTypes_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_types" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indTypesN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indTypes]
  simp only [callFn, scanIndTypes]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indTypesN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indTypesLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] indCtorBit indCtorVal Mbr.err

theorem indCtorLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indCtorLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indCtorBit (indCtorVal b) 252 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indCtorLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem indCtorLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indCtorLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indCtorBit (indCtorVal b) 252 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indCtorLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndCtor_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_ctor" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indCtorN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indCtor]
  simp only [callFn, scanIndCtor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indCtorN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indCtorLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] Mbr.err

theorem indCtorsLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indCtorsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indCtorN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indCtorsLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanIndCtor_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish

theorem indCtorsLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indCtorsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indCtorN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indCtorsLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndCtors_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_ctors" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indCtorsN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indCtors]
  simp only [callFn, scanIndCtors]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indCtorsN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indCtorsLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] axiomDBit axiomDVal Mbr.err

theorem axiomDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n axiomDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN axiomDBit (axiomDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := axiomDLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem axiomDLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) axiomDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN axiomDBit (axiomDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (axiomDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanAxiomD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_axiom" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [axiomDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_axiomD]
  simp only [callFn, scanAxiomD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, axiomDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, axiomDLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] defDBit defDVal Mbr.err

theorem defDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n defDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN defDBit (defDVal b) 124 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := defDLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        scanHints_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem defDLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) defDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN defDBit (defDVal b) 124 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (defDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanDefD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_def" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [defDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_defD]
  simp only [callFn, scanDefD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, defDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, defDLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] thmDBit thmDVal Mbr.err

theorem thmDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n thmDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN thmDBit (thmDVal b) 30 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := thmDLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem thmDLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) thmDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN thmDBit (thmDVal b) 30 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (thmDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanThmD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_thm" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [thmDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_thmD]
  simp only [callFn, scanThmD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, thmDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, thmDLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] opaqueDBit opaqueDVal Mbr.err

theorem opaqueDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n opaqueDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN opaqueDBit (opaqueDVal b) 62 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := opaqueDLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem opaqueDLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) opaqueDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN opaqueDBit (opaqueDVal b) 62 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (opaqueDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanOpaqueD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_opaque" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [opaqueDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_opaqueD]
  simp only [callFn, scanOpaqueD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, opaqueDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, opaqueDLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] quotDBit quotDVal Mbr.err

theorem quotDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n quotDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN quotDBit (quotDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := quotDLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem quotDLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) quotDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN quotDBit (quotDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (quotDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanQuotD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_quot" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [quotDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_quotD]
  simp only [callFn, scanQuotD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, quotDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, quotDLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish




attribute [local lang_grind] indDBit indDVal Mbr.err

theorem indDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indDBit (indDVal b) 26 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indDLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanIndCtors_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n,
        scanIndRecs_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n,
        scanIndTypes_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n] <;> finish

theorem indDLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) indDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indDBit (indDVal b) 26 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (indDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)

theorem scanIndD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_decl" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indD]
  simp only [callFn, scanIndD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, indDLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish


end specs

end L.Scan.Records
