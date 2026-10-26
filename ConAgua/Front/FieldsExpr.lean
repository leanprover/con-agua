module

public import ConAgua.Front.Fields
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The fields of expression lines

The expression analogue of `rec_line_loop` (`ConAgua.Front.Fields`): `rec_expr_loop(i)` walks an
accepted line's members again and returns the five words `(pl, idx, a, c, d)` of
`ConAgua.Front.ExprIface`'s table (`pl` `8`‥`17`, `0` for any other line or a failure).

* `rec_obj(i)`: one member loop for the six expression sub-objects (`app`, `lam`, `forallE`,
  `letE`, `const`, `proj`). It returns `(end, x0, x1, x2, x3)`, the slots by key: `fn`/`type`/
  `typeName` → `x0`; `arg`/`body`/`struct` → `x1`, `us` → `x1` the position of its `[`;
  `value`/`idx` → `x2`; `name` → `x3`; `binderInfo` and `nondep` are skipped. The value's end is
  `obj_val(ks, k, v)` (`exValN`): Stage B's scanner for the key's kind, `0` for a key no
  sub-object has.
* `expr_val(k, ks, v)`: one member of the line, `(end, pl, a, c, d)` (`exVN`); `pl = 0` with `a`
  the index for `in`/`il`/`ie`.
* `rec_expr_loop(i)`: the members, through `next_member` and `expr_val`.

As for name and level lines, the pass trusts the validator (no `seen` masks, no alternation), keeps
con-leche's progress guard, and reads every number with `read_nat` (`NONE` past 18 digits).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Records (boolEndN)

/-! ## `obj_val`: the end of a sub-object member's value -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def objVal : FunDecl := lfn (ks, k, v) locals (e, ok, x) {
  if k == 5 {  -- `binderInfo`
    e := call scan_binder_info(v);
    return e
  };
  if k == 37 {  -- `nondep`
    (ok, x, e) := call scan_bool(v);
    if ok == 0 { return 0 };
    return e
  };
  if k == 64 {  -- `us`
    (e, x) := call scan_nat_list(v);
    return e
  };
  if k == 13 || k == 61 || k == 62 || k == 3 || k == 6 || k == 58 || k == 65 || k == 17 ||
      k == 34 {
    e := call slot_nat(ks, v);
    return e
  };
  return 0
}

/-- A numeric key of a sub-object: `fn`, `type`, `typeName`, `arg`, `body`, `struct`, `value`,
`idx`, `name`. -/
def numKey (k : Word) : Prop :=
  k = 13 ∨ k = 61 ∨ k = 62 ∨ k = 3 ∨ k = 6 ∨ k = 58 ∨ k = 65 ∨ k = 17 ∨ k = 34

instance (k : Word) : Decidable (numKey k) := by unfold numKey; infer_instance

/-- The model of `obj_val(ks, k, v)`. -/
def exValN (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 5 then binderInfoN b v
  else if k = 37 then boolEndN b v
  else if k = 64 then (natListEntryN b v).1
  else if numKey k then slotNatN b ks v
  else 0

/-! ## `rec_obj` -/

def objLoop : Stmt := lblk (i, w, x0, x1, x2, x3, tag, ks, k, v, e, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0) };
    if tag == 1 { return (ks + 1, x0, x1, x2, x3) };
    e := call obj_val(ks, k, v);
    if e <= ks { return (0, 0, 0, 0, 0) };
    x := call read_nat(v, e);
    if k == 13 || k == 61 || k == 62 {
      x0 := x
    } else if k == 3 || k == 6 || k == 58 {
      x1 := x
    } else if k == 64 {
      x1 := v
    } else if k == 65 || k == 17 {
      x2 := x
    } else if k == 34 {
      x3 := x
    };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def recObj : FunDecl := lfn (i) locals (w, x0, x1, x2, x3, tag, ks, k, v, e, x) {
  i += 1;
  w := 1;
  ⟪objLoop⟫;
  return (0, 0, 0, 0, 0)
}

/-- Five words: an end and four slots (`rec_obj`), or an end and four fields (`expr_val`). -/
structure Obj where
  e : Word
  x0 : Word
  x1 : Word
  x2 : Word
  x3 : Word

/-- The five words. -/
def Obj.enc (o : Obj) : List Word := [o.e, o.x0, o.x1, o.x2, o.x3]

/-- A failure. -/
def Obj.none : Obj := ⟨0, 0, 0, 0, 0⟩

/-- The slots after the member `k` with value at `v`, read as `x`. -/
def objPut (k v x : Word) (o : Obj) : Obj :=
  if k = 13 ∨ k = 61 ∨ k = 62 then ⟨o.e, x, o.x1, o.x2, o.x3⟩
  else if k = 3 ∨ k = 6 ∨ k = 58 then ⟨o.e, o.x0, x, o.x2, o.x3⟩
  else if k = 64 then ⟨o.e, o.x0, v, o.x2, o.x3⟩
  else if k = 65 ∨ k = 17 then ⟨o.e, o.x0, o.x1, x, o.x3⟩
  else if k = 34 then ⟨o.e, o.x0, o.x1, o.x2, x⟩
  else o

/-- The sub-object loop. -/
def objRecN (b : Array UInt8) (i w : Word) (o : Obj) : Obj :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then
    ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩
  else if _h : (nextMemberN b i w).pos <
      exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
    objRecN b (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
      (objPut (nextMemberN b i w).key (nextMemberN b i w).val
        (rdNatN b (nextMemberN b i w).val
          (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)) o)
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `rec_obj(i)`, `i` at the `{`. -/
def recObjN (b : Array UInt8) (i : Word) : Obj := objRecN b (i + 1) 1 ⟨0, 0, 0, 0, 0⟩

section
variable (b : Array UInt8) (i w : Word) (o : Obj)
theorem objRecN_err (h : (nextMemberN b i w).tag = 0) : objRecN b i w o = .none := by
  rw [objRecN, ite_eq_left h]
theorem objRecN_close (h : (nextMemberN b i w).tag = 1) :
    objRecN b i w o = ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩ := by
  rw [objRecN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem objRecN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    objRecN b i w o =
      if (nextMemberN b i w).pos <
          exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
        objRecN b (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
          (objPut (nextMemberN b i w).key (nextMemberN b i w).val
            (rdNatN b (nextMemberN b i w).val
              (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)) o)
      else .none := by
  rw [objRecN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] objRecN_err => objRecN b i w o, nextMemberN b i w
grind_pattern [lang_grind] objRecN_close => objRecN b i w o, nextMemberN b i w
grind_pattern [lang_grind] objRecN_key => objRecN b i w o, nextMemberN b i w

/-! ## `expr_val`: one member of an expression line -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def exprVal : FunDecl := lfn (k, ks, v) locals (e, x, x0, x1, x2, x3, q) {
  if k == 21 || k == 19 || k == 18 {  -- `in`, `il`, `ie`
    e := call slot_nat(ks, v);
    x := call read_nat(v, e);
    return (e, 0, x, 0, 0)
  };
  if k == 7 || k == 55 {  -- `bvar`, `sort`
    e := call slot_nat(ks, v);
    x := call read_nat(v, e);
    if k == 7 { return (e, 8, x, 0, 0) };
    return (e, 9, x, 0, 0)
  };
  if k == 2 || k == 29 || k == 14 || k == 30 || k == 9 || k == 48 {
    (e, x0, x1, x2, x3) := call rec_obj(v);
    if k == 2 { return (e, 10, x0, x1, x1) };
    if k == 29 { return (e, 11, x0, x1, x1) };
    if k == 14 { return (e, 12, x0, x1, x1) };
    if k == 30 { return (e, 13, x0, x2, x1) };
    if k == 48 { return (e, 14, x0, x2, x1) };
    return (e, 15, x3, x1, x1)
  };
  if k == 35 {  -- `natVal`
    e := call scan_quoted_nat(v);
    x := call read_nat(v + 1, e - 1);
    return (e, 16, x, v + 1, e - 1)
  };
  if k == 57 {  -- `strVal`
    e := call scan_string(v);
    return (e, 17, 0, v + 1, e - 1)
  };
  return (0, 0, 0, 0, 0)
}

/-- The fields a sub-object's slots give, for the payload key `k`. -/
def objFld (k : Word) (o : Obj) : Obj :=
  if k = 2 then ⟨o.e, 10, o.x0, o.x1, o.x1⟩
  else if k = 29 then ⟨o.e, 11, o.x0, o.x1, o.x1⟩
  else if k = 14 then ⟨o.e, 12, o.x0, o.x1, o.x1⟩
  else if k = 30 then ⟨o.e, 13, o.x0, o.x2, o.x1⟩
  else if k = 48 then ⟨o.e, 14, o.x0, o.x2, o.x1⟩
  else ⟨o.e, 15, o.x3, o.x1, o.x1⟩

/-- The model of `expr_val(k, ks, v)`: the value's end, then `pl` (`0` for an index), `a`, `c`,
`d`. -/
def exVN (b : Array UInt8) (k ks v : Word) : Obj :=
  if k = 21 ∨ k = 19 ∨ k = 18 then ⟨slotNatN b ks v, 0, rdNatN b v (slotNatN b ks v), 0, 0⟩
  else if k = 7 ∨ k = 55 then
    ⟨slotNatN b ks v, if k = 7 then 8 else 9, rdNatN b v (slotNatN b ks v), 0, 0⟩
  else if k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 then objFld k (recObjN b v)
  else if k = 35 then
    ⟨quotedNatN b v, 16, rdNatN b (v + 1) (quotedNatN b v - 1), v + 1, quotedNatN b v - 1⟩
  else if k = 57 then ⟨L.Scan.Str.scanStringN b v, 17, 0, v + 1, L.Scan.Str.scanStringN b v - 1⟩
  else .none

/-! ## `rec_expr_loop` -/

def exprLoop : Stmt := lblk (i, w, pl, idx, a, c, d, tag, ks, k, v, e, q, x, y, z) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0) };
    if tag == 1 { return (pl, idx, a, c, d) };
    (e, q, x, y, z) := call expr_val(k, ks, v);
    if e <= ks { return (0, 0, 0, 0, 0) };
    if q == 0 {
      idx := x
    } else {
      pl := q;
      a := x;
      c := y;
      d := z
    };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
@[l_impl ConLeche.Frontend.scanLineLoop]
def recExprLoop : FunDecl := lfn (i) locals (w, pl, idx, a, c, d, tag, ks, k, v, e, q, x, y, z) {
  w := 1;
  ⟪exprLoop⟫;
  return (0, 0, 0, 0, 0)
}

/-- The fields after a member whose `expr_val` is `o`. -/
def fldPut (o : Obj) (f : Fld) : Fld :=
  if o.x0 = 0 then ⟨f.pl, o.x1, f.a, f.c, f.d⟩ else ⟨o.x0, f.idx, o.x1, o.x2, o.x3⟩

/-- The expression line loop. -/
def exprN (b : Array UInt8) (i w : Word) (f : Fld) : Fld :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then f
  else if _h : (nextMemberN b i w).pos <
      (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e then
    exprN b (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e 0
      (fldPut (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) f)
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `rec_expr_loop(i)`, `i` after the line's `{`. -/
def exprLineN (b : Array UInt8) (i : Word) : Fld := exprN b i 1 .none

section
variable (b : Array UInt8) (i w : Word) (f : Fld)
theorem exprN_err (h : (nextMemberN b i w).tag = 0) : exprN b i w f = .none := by
  rw [exprN, ite_eq_left h]
theorem exprN_close (h : (nextMemberN b i w).tag = 1) : exprN b i w f = f := by
  rw [exprN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem exprN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    exprN b i w f =
      if (nextMemberN b i w).pos <
          (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e then
        exprN b (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e 0
          (fldPut (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) f)
      else .none := by
  rw [exprN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] exprN_err => exprN b i w f, nextMemberN b i w
grind_pattern [lang_grind] exprN_close => exprN b i w f, nextMemberN b i w
grind_pattern [lang_grind] exprN_key => exprN b i w f, nextMemberN b i w

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
    (hpq : p.lookup "scan_quoted_nat" = some scanQuotedNat)
    (hpmw : p.lookup "match_word" = some matchWord)
    (hpi : p.lookup "scan_binder_info" = some scanBinderInfo)
    (hpl : p.lookup "scan_nat_list" = some scanNatList)
    (hpml : p.lookup "match_lit" = some L.Scan.Lit.matchLit)
    (hpbo : p.lookup "scan_bool" = some L.Scan.Lit.scanBool)
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
    (hprn : p.lookup "read_nat" = some readNat)
    (hpov : p.lookup "obj_val" = some objVal)
    (hpro : p.lookup "rec_obj" = some recObj)
    (hpev : p.lookup "expr_val" = some exprVal)
    (hpel : p.lookup "rec_expr_loop" = some recExprLoop)
include hb

include hpd hpn hps hpmw hpi hpl hpml hpbo hpov in
attribute [local lang_grind] exValN numKey boolEndN in
theorem objVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (ks k v : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "obj_val" [ks, k, v]
    ⦃fun r s' => s' = s₀ ∧ r = [exValN b k ks v]; ⊤⦄ := by
  rw [invoke_eq _ hpov]
  simp only [callFn, objVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        scanBinderInfo_spec p b hb hpmw hpi n, L.Scan.Lit.scanBool_spec p hpml hpbo b hb64 n,
        scanNatList_spec p b hb hpd hpn hpl n, slotNat_spec p b hb hpd hpn hps n] <;> finish

attribute [local lang_grind] objPut Obj.enc Obj.none

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hprn hpov in
set_option maxHeartbeats 2000000 in
theorem objLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n objLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Obj.none.enc = (objRecN b (s₀.loc 0) (s₀.loc 1)
        ⟨0, s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := objLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        objVal_spec p b hb hpd hpn hps hpmw hpi hpl hpml hpbo hpov n,
        readNat_spec p b hb hprn n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hprn hpov in
theorem objLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) objLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Obj.none.enc = (objRecN b (s₀.loc 0) (s₀.loc 1)
        ⟨0, s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5⟩).enc; ⊤⦄ :=
  Triple.step_exec (objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hprn hpov (n + 1) s₀)

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hprn hpov hpro in
attribute [local lang_grind] recObjN in
theorem recObj_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_obj" [i]
    ⦃fun r s' => s' = s₀ ∧ r = (recObjN b i).enc; ⊤⦄ := by
  rw [invoke_eq _ hpro]
  simp only [callFn, recObj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        objLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hprn hpov n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev in
attribute [local lang_grind] exVN objFld in
set_option maxHeartbeats 2000000 in
theorem exprVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (k ks v : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_val" [k, ks, v]
    ⦃fun r s' => s' = s₀ ∧ r = (exVN b k ks v).enc; ⊤⦄ := by
  rw [invoke_eq _ hpev]
  simp only [callFn, exprVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        slotNat_spec p b hb hpd hpn hps n, readNat_spec p b hb hprn n,
        scanQuotedNat_spec p b hb hpd hpq n,
        L.Scan.Str.scanString_spec p b hb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt n,
        recObj_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hprn hpov hpro n] <;>
        finish

attribute [local lang_grind] fldPut Fld.enc Fld.none Mbr.err

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev in
theorem exprLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n exprLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Fld.none.enc = (exprN b (s₀.loc 0) (s₀.loc 1)
        ⟨s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := exprLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        exprVal_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev in
theorem exprLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) exprLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Fld.none.enc = (exprN b (s₀.loc 0) (s₀.loc 1)
        ⟨s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6⟩).enc; ⊤⦄ :=
  Triple.step_exec (exprLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev (n + 1) s₀)

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev hpel in
attribute [local lang_grind] exprLineN in
theorem recExprLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_expr_loop" [i]
    ⦃fun r s' => s' = s₀ ∧ r = (exprLineN b i).enc; ⊤⦄ := by
  rw [invoke_eq _ hpel]
  simp only [callFn, recExprLoop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        exprLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpq hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpov hpro hpev n] <;>
        finish

end specs

end L.Front.Fields
