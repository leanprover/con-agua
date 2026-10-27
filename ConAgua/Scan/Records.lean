module

meta import ConAgua.L.Semantics
public import ConAgua.Scan.Values
public import ConAgua.Scan.Member
public import ConAgua.Scan.Str
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
public import ConAgua.Layout

@[expose] public section

/-!
# The record loops (`scan_fast.rs:1434-3724`), validating only

One L function per record kind, as in Rust: `scan_X(i)` is Rust's `scan_X` (the opening brace)
with its `scan_X_loop` spliced in. The loop calls `next_member` and dispatches on the key code:
each key of the record checks its `seen` bit, scans its value, and sets the bit; any other key
is an error (`UnknownKey`). Each is proved against the generic model `objN` of
`ConAgua.Scan.Member` with the record's `bit`, `val`, `mask` (the specs are in `ConAgua.Scan.RecordsSpec`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Records

open L.Scan.Member
open L.Scan.Values

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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:831-835 ConLeche.Frontend.scanStrName -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:781-829 ConLeche.Frontend.scanStrNameLoop
@[l_impl ConLeche.Frontend.scanStrName ConLeche.Frontend.scanStrNameLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:886-890 ConLeche.Frontend.scanNumName -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:837-884 ConLeche.Frontend.scanNumNameLoop
@[l_impl ConLeche.Frontend.scanNumName ConLeche.Frontend.scanNumNameLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:941-945 ConLeche.Frontend.scanAppExpr -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:892-939 ConLeche.Frontend.scanAppExprLoop
@[l_impl ConLeche.Frontend.scanAppExpr ConLeche.Frontend.scanAppExprLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1012-1017 ConLeche.Frontend.scanLamExpr
con-leche: ConLeche/Frontend/Scan/Fast.lean:1084-1088 ConLeche.Frontend.scanForallExpr -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:947-1010 ConLeche.Frontend.scanLamExprLoop
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1019-1082 ConLeche.Frontend.scanForallExprLoop
@[l_impl ConLeche.Frontend.scanLamExpr ConLeche.Frontend.scanForallExpr ConLeche.Frontend.scanLamExprLoop ConLeche.Frontend.scanForallExprLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1165-1169 ConLeche.Frontend.scanLetExpr -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1090-1163 ConLeche.Frontend.scanLetExprLoop
@[l_impl ConLeche.Frontend.scanLetExpr ConLeche.Frontend.scanLetExprLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1221-1225 ConLeche.Frontend.scanConstExpr -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1171-1219 ConLeche.Frontend.scanConstExprLoop
@[l_impl ConLeche.Frontend.scanConstExpr ConLeche.Frontend.scanConstExprLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1285-1289 ConLeche.Frontend.scanProjExpr -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1227-1283 ConLeche.Frontend.scanProjExprLoop
@[l_impl ConLeche.Frontend.scanProjExpr ConLeche.Frontend.scanProjExprLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1349-1353 ConLeche.Frontend.scanRule -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1291-1347 ConLeche.Frontend.scanRuleLoop
@[l_impl ConLeche.Frontend.scanRule ConLeche.Frontend.scanRuleLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1383-1387 ConLeche.Frontend.scanRules -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1355-1381 ConLeche.Frontend.scanRuleListLoop
@[l_impl ConLeche.Frontend.scanRules ConLeche.Frontend.scanRuleListLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1523-1527 ConLeche.Frontend.scanIndRec -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1389-1521 ConLeche.Frontend.scanIndRecLoop
@[l_impl ConLeche.Frontend.scanIndRec ConLeche.Frontend.scanIndRecLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1557-1561 ConLeche.Frontend.scanIndRecs -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1529-1555 ConLeche.Frontend.scanIndRecListLoop
@[l_impl ConLeche.Frontend.scanIndRecs ConLeche.Frontend.scanIndRecListLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1698-1702 ConLeche.Frontend.scanIndType -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1563-1696 ConLeche.Frontend.scanIndTypeLoop
@[l_impl ConLeche.Frontend.scanIndType ConLeche.Frontend.scanIndTypeLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1732-1736 ConLeche.Frontend.scanIndTypes -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1704-1730 ConLeche.Frontend.scanIndTypeListLoop
@[l_impl ConLeche.Frontend.scanIndTypes ConLeche.Frontend.scanIndTypeListLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1845-1851 ConLeche.Frontend.scanIndCtor -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1738-1843 ConLeche.Frontend.scanIndCtorLoop
@[l_impl ConLeche.Frontend.scanIndCtor ConLeche.Frontend.scanIndCtorLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1881-1885 ConLeche.Frontend.scanIndCtors -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1853-1879 ConLeche.Frontend.scanIndCtorListLoop
@[l_impl ConLeche.Frontend.scanIndCtors ConLeche.Frontend.scanIndCtorListLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1956-1960 ConLeche.Frontend.scanAxiomDecl -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1887-1954 ConLeche.Frontend.scanAxiomDeclLoop
@[l_impl ConLeche.Frontend.scanAxiomDecl ConLeche.Frontend.scanAxiomDeclLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2059-2065 ConLeche.Frontend.scanDefDecl -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1962-2057 ConLeche.Frontend.scanDefDeclLoop
@[l_impl ConLeche.Frontend.scanDefDecl ConLeche.Frontend.scanDefDeclLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2144-2148 ConLeche.Frontend.scanThmDecl -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2067-2142 ConLeche.Frontend.scanThmDeclLoop
@[l_impl ConLeche.Frontend.scanThmDecl ConLeche.Frontend.scanThmDeclLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2237-2241 ConLeche.Frontend.scanOpaqueDecl -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2150-2235 ConLeche.Frontend.scanOpaqueDeclLoop
@[l_impl ConLeche.Frontend.scanOpaqueDecl ConLeche.Frontend.scanOpaqueDeclLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2312-2316 ConLeche.Frontend.scanQuotDecl -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2243-2310 ConLeche.Frontend.scanQuotDeclLoop
@[l_impl ConLeche.Frontend.scanQuotDecl ConLeche.Frontend.scanQuotDeclLoop]
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2318-2395 ConLeche.Frontend.scanIndDeclLoop
@[l_impl ConLeche.Frontend.scanIndDecl ConLeche.Frontend.scanIndDeclLoop]
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

end L.Scan.Records
