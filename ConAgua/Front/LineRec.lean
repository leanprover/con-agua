module

meta import ConAgua.L.Semantics
public import ConAgua.Front.FieldsExpr
import ConAgua.Census.Attr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# One pass over a line: the sub-objects

con-ron's `scan_line_fwd` reads a line once and builds its record. Here, in the same shape,
`sub_rec(o, kd, mk)` reads one object of a line's payload at `o`: an expression's sub-object
(`app`, `lam`/`forallE`, `letE`, `const`, `proj`, by the payload key `kd`) or a name
(`str`, `num`). It checks what Stage B's record loop for that object checks (the key set by its
bits `subBit kd`, each key once, the required keys `mk`, the comma alternation), and fills the
slots the record pass reads (`objRecN`, `strRecN`, `numRecN`): `(end, x0, x1, x2, x3)`, `end = 0`
when the object does not scan. Each value is read once (`sub_val`), each number's value once
(`read_nat`).

The model `subN` mirrors the code; `ConAgua.Front.LineRecLink` relates it to Stage B's `objN` and
to the record passes.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.LineRec

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Records
open L.Front.Fields

/-! ## The code -/

/-- The key bit of key `k` in the object of payload key `kd`, `0` if the object has no key `k`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def subBitF : FunDecl := lfn (kd, k) {
  if kd == 2 {  -- `app`: `arg`, `fn`
    if k == 3 { return 1 };
    if k == 13 { return 2 };
    return 0
  };
  if kd == 29 || kd == 14 {  -- `lam`, `forallE`: `binderInfo`, `body`, `name`, `type`
    if k == 5 { return 1 };
    if k == 6 { return 2 };
    if k == 34 { return 4 };
    if k == 61 { return 8 };
    return 0
  };
  if kd == 30 {  -- `letE`: `body`, `name`, `nondep`, `type`, `value`
    if k == 6 { return 1 };
    if k == 34 { return 2 };
    if k == 37 { return 4 };
    if k == 61 { return 8 };
    if k == 65 { return 16 };
    return 0
  };
  if kd == 9 {  -- `const`: `name`, `us`
    if k == 34 { return 1 };
    if k == 64 { return 2 };
    return 0
  };
  if kd == 48 {  -- `proj`: `idx`, `struct`, `typeName`
    if k == 17 { return 1 };
    if k == 58 { return 2 };
    if k == 62 { return 4 };
    return 0
  };
  if kd == 56 {  -- a `str` name: `pre`, `str`
    if k == 47 { return 1 };
    if k == 56 { return 2 };
    return 0
  };
  if kd == 38 {  -- a `num` name: `i`, `pre`
    if k == 16 { return 1 };
    if k == 47 { return 2 };
    return 0
  };
  return 0
}

/-- The end of key `k`'s value at `v` (its quote at `ks`), `0` if it does not scan. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def subValF : FunDecl := lfn (ks, k, v) locals (e, ok, x) {
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
  if k == 56 {  -- a name's `str`
    e := call scan_string(v);
    return e
  };
  e := call slot_nat(ks, v);  -- every other key has a number
  return e
}

def subLoop : Stmt := lblk (o, kd, mk, i, w, seen, x0, x1, x2, x3, tag, ks, k, v, e, x, bt) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0) };
    if tag == 1 {
      if w != 0 && seen != 0 { return (0, 0, 0, 0, 0) };
      if (seen & mk) != mk { return (0, 0, 0, 0, 0) };
      return (ks + 1, x0, x1, x2, x3)
    };
    bt := call sub_bit(kd, k);
    if bt == 0 { return (0, 0, 0, 0, 0) };
    if (seen & bt) != 0 { return (0, 0, 0, 0, 0) };
    e := call sub_val(ks, k, v);
    if e <= ks { return (0, 0, 0, 0, 0) };
    if k == 13 || k == 61 || k == 62 || k == 47 {
      x0 := call read_nat(v, e)
    } else if k == 3 || k == 6 || k == 58 || k == 16 {
      x1 := call read_nat(v, e)
    } else if k == 64 {
      x1 := v
    } else if k == 65 || k == 17 {
      x2 := call read_nat(v, e)
    } else if k == 34 {
      x3 := call read_nat(v, e)
    } else if k == 56 {
      x1 := v + 1;
      x2 := e - 1
    };
    seen := seen | bt;
    i := e;
    w := 0
  }
}

/-- The object of payload key `kd` at `o`, its required keys `mk`: `(end, x0, x1, x2, x3)`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def subRec : FunDecl := lfn (o, kd, mk) locals (i, w, seen, x0, x1, x2, x3, tag, ks, k, v, e, x, bt) {
  if !(o < len(IN.u8) && IN.u8[o] == 123) { return (0, 0, 0, 0, 0) };
  i := o + 1;
  w := 1;
  ⟪subLoop⟫;
  return (0, 0, 0, 0, 0)
}

/-! ## The models -/

/-- The key bits (`sub_bit`). -/
def subBit (kd k : Word) : Word :=
  if kd = 2 then appBit k
  else if kd = 29 ∨ kd = 14 then binderBit k
  else if kd = 30 then letEBit k
  else if kd = 9 then constEBit k
  else if kd = 48 then projBit k
  else if kd = 56 then strNameBit k
  else if kd = 38 then numNameBit k
  else 0

/-- A key with a number value. -/
def NumVal (k : Word) : Prop := k ≠ 5 ∧ k ≠ 37 ∧ k ≠ 64 ∧ k ≠ 56

/-- The value ends (`sub_val`). -/
def subVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 5 then binderInfoN b v
  else if k = 37 then boolEndN b v
  else if k = 64 then (natListEntryN b v).1
  else if k = 56 then L.Scan.Str.scanStringN b v
  else slotNatN b ks v

/-- The slots after key `k` with its value `[v, e)`. -/
def subPut (b : Array UInt8) (k v e : Word) (o : Obj) : Obj :=
  if k = 13 ∨ k = 61 ∨ k = 62 ∨ k = 47 then ⟨o.e, rdNatN b v e, o.x1, o.x2, o.x3⟩
  else if k = 3 ∨ k = 6 ∨ k = 58 ∨ k = 16 then ⟨o.e, o.x0, rdNatN b v e, o.x2, o.x3⟩
  else if k = 64 then ⟨o.e, o.x0, v, o.x2, o.x3⟩
  else if k = 65 ∨ k = 17 then ⟨o.e, o.x0, o.x1, rdNatN b v e, o.x3⟩
  else if k = 34 then ⟨o.e, o.x0, o.x1, o.x2, rdNatN b v e⟩
  else if k = 56 then ⟨o.e, o.x0, v + 1, e - 1, o.x3⟩
  else o

/-- The object loop (`subLoop`): the end and the slots, `Obj.none` when it does not scan. -/
def subN (b : Array UInt8) (kd mk i w seen : Word) (o : Obj) : Obj :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then
    if (nextMemberN b i w).w ≠ 0 ∧ seen ≠ 0 then .none
    else if seen &&& mk ≠ mk then .none
    else ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩
  else if subBit kd (nextMemberN b i w).key = 0 then .none
  else if seen &&& subBit kd (nextMemberN b i w).key ≠ 0 then .none
  else if _h : (nextMemberN b i w).pos <
      subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
    subN b kd mk (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)
      0 (seen ||| subBit kd (nextMemberN b i w).key)
      (subPut b (nextMemberN b i w).key (nextMemberN b i w).val
        (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) o)
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `sub_rec(o, kd, mk)`. -/
def subRecN (b : Array UInt8) (o kd mk : Word) : Obj :=
  if o < UInt64.ofNat b.size ∧ byteW b o = 123 then subN b kd mk (o + 1) 1 0 ⟨0, 0, 0, 0, 0⟩
  else .none

section
variable (b : Array UInt8) (kd mk i w seen : Word) (o : Obj)
theorem subN_err (h : (nextMemberN b i w).tag = 0) : subN b kd mk i w seen o = .none := by
  rw [subN, ite_eq_left h]
theorem subN_close (h : (nextMemberN b i w).tag = 1) :
    subN b kd mk i w seen o =
      if (nextMemberN b i w).w ≠ 0 ∧ seen ≠ 0 then .none
      else if seen &&& mk ≠ mk then .none
      else ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩ := by
  rw [subN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem subN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    subN b kd mk i w seen o =
      if subBit kd (nextMemberN b i w).key = 0 then .none
      else if seen &&& subBit kd (nextMemberN b i w).key ≠ 0 then .none
      else if (nextMemberN b i w).pos <
          subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
        subN b kd mk
          (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)
          0 (seen ||| subBit kd (nextMemberN b i w).key)
          (subPut b (nextMemberN b i w).key (nextMemberN b i w).val
            (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) o)
      else .none := by
  rw [subN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] subN_err => subN b kd mk i w seen o, nextMemberN b i w
grind_pattern [lang_grind] subN_close => subN b kd mk i w seen o, nextMemberN b i w
grind_pattern [lang_grind] subN_key => subN b kd mk i w seen o, nextMemberN b i w

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
    (hpsb : p.lookup "sub_bit" = some subBitF)
    (hpsv : p.lookup "sub_val" = some subValF)
    (hpsr : p.lookup "sub_rec" = some subRec)
include hb

omit hb in
include hpsb in
attribute [local lang_grind] subBit appBit binderBit letEBit constEBit projBit strNameBit
  numNameBit in
theorem subBit_spec (n : Nat) (s₀ : St) (kd k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_bit" [kd, k]
    ⦃fun r s' => s' = s₀ ∧ r = [subBit kd k]; ⊤⦄ := by
  rw [invoke_eq _ hpsb]
  simp only [callFn, subBitF]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq] at *
    all_goals subst_vars
    all_goals grind [subBit, appBit, binderBit, letEBit, constEBit, projBit, strNameBit,
      numNameBit, Sig.retVal, Sig.retOr]

include hpd hpn hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpsv in
attribute [local lang_grind] subVal boolEndN in
theorem subVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (ks k v : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_val" [ks, k, v]
    ⦃fun r s' => s' = s₀ ∧ r = [subVal b k ks v]; ⊤⦄ := by
  rw [invoke_eq _ hpsv]
  simp only [callFn, subValF]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        scanBinderInfo_spec p b hb hpmw hpi n, L.Scan.Lit.scanBool_spec p hpml hpbo b hb64 n,
        scanNatList_spec p b hb hpd hpn hpl n, slotNat_spec p b hb hpd hpn hps n,
        L.Scan.Str.scanString_spec p b hb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv in
attribute [local lang_grind] subPut Obj.enc Obj.none in
set_option maxHeartbeats 2000000 in
theorem subLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n subLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Obj.none.enc = (subN b (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        ⟨0, s₀.loc 6, s₀.loc 7, s₀.loc 8, s₀.loc 9⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := subLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        subBit_spec p hpsb n,
        subVal_spec p b hb hpd hpn hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpsv n,
        readNat_spec p b hprn n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv hpsr in
attribute [local lang_grind] subRecN Obj.enc Obj.none in
theorem subRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (o kd mk : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_rec" [o, kd, mk]
    ⦃fun r s' => s' = s₀ ∧ r = (subRecN b o kd mk).enc; ⊤⦄ := by
  rw [invoke_eq _ hpsr]
  simp only [callFn, subRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8,
        fun s₀ => Triple.step_exec (subLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv (n + 1) s₀)] <;>
        finish

end specs

end L.Front.LineRec
