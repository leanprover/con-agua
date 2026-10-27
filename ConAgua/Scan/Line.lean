module

meta import ConAgua.L.Semantics
public import ConAgua.Scan.Records
import ConAgua.Census.Attr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
public import ConAgua.Scan.Common
public import ConAgua.Scan.RecordsSpec
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The line (`scan_fast.rs:3767,4044`) and the driver, validating only

`scan_line_loop(i)` is Rust's `scan_line_loop`: the members of one line, at most one index key
(`in`/`il`/`ie`, `idx` = `1`/`2`/`3`) and exactly one payload key (`pl`: `1` name, `2` level,
`3` expression, `4` declaration, `5` the `meta` header), matched at the closing brace. It returns
the position after the brace, or `0`.

`scan_line(i)` is Rust's `scan_line_fwd`: `(1, next)` for a line (`next` is the position after
its newline, `0` when the buffer ends first), `(0, 0)` for an error.

`validate()` runs over the whole buffer as con-leche's `parseBytes` does (`feedChunk` and then
`applyFinalLine` on the tail), without applying the lines: `0` if every line scans, else the
number (from `1`) of the first line that does not. con-ron's `feed_chunk` asks `newline_from`
after a failed line, to tell a malformed line from one a chunk boundary cut; on the whole buffer
both answers end in the same error (the tail is scanned again by `applyFinalLine` and fails at
the same line), so the driver does not ask.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Line

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Records

/-! ## `scan_line_loop` -/

def lineLoop : Stmt := lblk (i, w, idx, pl, tag, ks, k, v, e, ok, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && (idx != 0 || pl != 0) { return 0 };
      if pl == 1 && idx == 1 { return ks + 1 };
      if pl == 2 && idx == 2 { return ks + 1 };
      if pl == 3 && idx == 3 { return ks + 1 };
      if pl == 4 && idx == 0 { return ks + 1 };
      if pl == 5 && idx == 0 { return ks + 1 };
      return 0
    };
    if k == 21 || k == 19 || k == 18 {  -- `in`, `il`, `ie`
      if idx != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      if k == 21 { idx := 1 } else if k == 19 { idx := 2 } else { idx := 3 }
    } else if k == 7 || k == 55 || k == 59 || k == 46 {  -- `bvar`, `sort`, `succ`, `param`
      if pl != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      if k == 7 || k == 55 { pl := 3 } else { pl := 2 }
    } else if k == 32 || k == 20 {  -- `max`, `imax`
      if pl != 0 { return 0 };
      (e, x) := call scan_nat_list(v);
      if e == 0 { return 0 };
      if x != 2 { return 0 };
      if e <= ks { return 0 };
      pl := 2
    } else if k == 56 || k == 38 {  -- `str`, `num`
      if pl != 0 { return 0 };
      if k == 56 { e := call scan_str_name(v) } else { e := call scan_num_name(v) };
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      pl := 1
    } else if k == 2 || k == 29 || k == 14 || k == 30 || k == 9 || k == 48 {
      -- `app`, `lam`, `forallE`, `letE`, `const`, `proj`
      if pl != 0 { return 0 };
      if k == 2 { e := call scan_app(v) }
      else if k == 29 || k == 14 { e := call scan_binder(v) }
      else if k == 30 { e := call scan_let(v) }
      else if k == 9 { e := call scan_const(v) }
      else { e := call scan_proj(v) };
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      pl := 3
    } else if k == 35 || k == 57 {  -- `natVal`, `strVal`
      if pl != 0 { return 0 };
      if k == 35 { e := call scan_quoted_nat(v) } else { e := call scan_string(v) };
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      pl := 3
    } else if k == 4 || k == 12 || k == 60 || k == 45 || k == 49 || k == 23 {
      -- `axiom`, `def`, `thm`, `opaque`, `quot`, `inductive`
      if pl != 0 { return 0 };
      if k == 4 { e := call scan_axiom(v) }
      else if k == 12 { e := call scan_def(v) }
      else if k == 60 { e := call scan_thm(v) }
      else if k == 45 { e := call scan_opaque(v) }
      else if k == 49 { e := call scan_quot(v) }
      else { e := call scan_ind_decl(v) };
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      pl := 4
    } else if k == 33 {  -- `meta`
      if pl != 0 { return 0 };
      if !(v < len(IN.u8) && IN.u8[v] == 123) { return 0 };
      e := call skip_braced(v + 1, 0);
      if e == 0 { return 0 };
      if e <= ks { return 0 };
      pl := 5
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2423-2425 ConLeche.Frontend.LinePayload.isAbsent
@[l_impl ConLeche.Frontend.scanLineLoop ConLeche.Frontend.LinePayload.isAbsent]
def scanLineLoop : FunDecl := lfn (i) locals (w, idx, pl, tag, ks, k, v, e, ok, x) {
  w := 1;
  ⟪lineLoop⟫;
  return 0
}

/-- Its code. -/
def idxCode (k : Word) : Word := if k = 21 then 1 else if k = 19 then 2 else 3
/-- The payload a key gives, `0` if it is not a payload key. -/
def lineKind (k : Word) : Word :=
  if k = 7 ∨ k = 55 then 3 else if k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 then 2
  else if k = 56 ∨ k = 38 then 1
  else if k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 then 3
  else if k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 then 4
  else if k = 33 then 5 else 0
/-- The value scanner of a payload key: the end of the value, or `0`. -/
def lineVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 then slotNatN b ks v
  else if k = 32 ∨ k = 20 then
    (if (natListEntryN b v).1 = 0 then 0
     else if (natListEntryN b v).2 = 2 then (natListEntryN b v).1 else 0)
  else if k = 56 then strNameN b v
  else if k = 38 then numNameN b v
  else if k = 2 then appN b v
  else if k = 29 ∨ k = 14 then binderN b v
  else if k = 30 then letEN b v
  else if k = 9 then constEN b v
  else if k = 48 then projN b v
  else if k = 35 then quotedNatN b v
  else if k = 57 then L.Scan.Str.scanStringN b v
  else if k = 4 then axiomDN b v
  else if k = 12 then defDN b v
  else if k = 60 then thmDN b v
  else if k = 45 then opaqueDN b v
  else if k = 49 then quotDN b v
  else if k = 23 then indDN b v
  else if k = 33 then
    (if v < UInt64.ofNat b.size ∧ byteW b v = 123 then
      UInt64.ofNat (L.Examples.skipBracedN b (v + 1).toNat 0) else 0)
  else 0

/-- con-leche's `scanLineLoop`, validating only: the position after the line's closing brace,
or `0`. -/
def lineN (b : Array UInt8) (i w idx pl : Word) : Word :=
  if (nextMemberN b i w).tag = 0 then 0
  else if (nextMemberN b i w).tag = 1 then
    if (nextMemberN b i w).w ≠ 0 ∧ (idx ≠ 0 ∨ pl ≠ 0) then 0
    else if (pl = 1 ∧ idx = 1) ∨ (pl = 2 ∧ idx = 2) ∨ (pl = 3 ∧ idx = 3) ∨ (pl = 4 ∧ idx = 0) ∨
        (pl = 5 ∧ idx = 0) then (nextMemberN b i w).pos + 1
    else 0
  else if ((nextMemberN b i w).key = 21 ∨ (nextMemberN b i w).key = 19 ∨ (nextMemberN b i w).key = 18) then
    if idx ≠ 0 then 0
    else if _h : (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
      lineN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        (idxCode (nextMemberN b i w).key) pl
    else 0
  else if lineKind (nextMemberN b i w).key = 0 then 0
  else if pl ≠ 0 then 0
  else if _h : (nextMemberN b i w).pos <
      lineVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
    lineN b (lineVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
      idx (lineKind (nextMemberN b i w).key)
  else 0
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
    have := L.Scan.lt_of_lt_ofNat hk.2
    rw [UInt64.le_iff_toNat_le] at hk
    rw [UInt64.lt_iff_toNat_lt] at _h
    omega

section
variable (b : Array UInt8) (i w idx pl : Word)

theorem lineN_err (h : (nextMemberN b i w).tag = 0) : lineN b i w idx pl = 0 := by
  rw [lineN, ite_eq_left h]
theorem lineN_close (h : (nextMemberN b i w).tag = 1) :
    lineN b i w idx pl =
      if (nextMemberN b i w).w ≠ 0 ∧ (idx ≠ 0 ∨ pl ≠ 0) then 0
      else if (pl = 1 ∧ idx = 1) ∨ (pl = 2 ∧ idx = 2) ∨ (pl = 3 ∧ idx = 3) ∨ (pl = 4 ∧ idx = 0) ∨
          (pl = 5 ∧ idx = 0) then (nextMemberN b i w).pos + 1
      else 0 := by
  rw [lineN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem lineN_idx (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1)
    (hk : ((nextMemberN b i w).key = 21 ∨ (nextMemberN b i w).key = 19 ∨ (nextMemberN b i w).key = 18)) :
    lineN b i w idx pl =
      if idx ≠ 0 then 0
      else if (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
        lineN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
          (idxCode (nextMemberN b i w).key) pl
      else 0 := by
  rw [lineN, ite_eq_right h0, ite_eq_right h1, ite_eq_left hk]
  simp only [dite_eq_ite]
theorem lineN_pay (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1)
    (hk : ¬ ((nextMemberN b i w).key = 21 ∨ (nextMemberN b i w).key = 19 ∨ (nextMemberN b i w).key = 18)) :
    lineN b i w idx pl =
      if lineKind (nextMemberN b i w).key = 0 then 0
      else if pl ≠ 0 then 0
      else if (nextMemberN b i w).pos <
          lineVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
        lineN b (lineVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
          idx (lineKind (nextMemberN b i w).key)
      else 0 := by
  rw [lineN, ite_eq_right h0, ite_eq_right h1, ite_eq_right hk]
  simp only [dite_eq_ite]

grind_pattern [lang_grind] lineN_err => lineN b i w idx pl, nextMemberN b i w
grind_pattern [lang_grind] lineN_close => lineN b i w idx pl, nextMemberN b i w
grind_pattern [lang_grind] lineN_idx => lineN b i w idx pl, nextMemberN b i w
grind_pattern [lang_grind] lineN_pay => lineN b i w idx pl, nextMemberN b i w

end

/-- A line's closing brace is inside the array. -/
theorem lineN_le (b : Array UInt8) (i w idx pl : Word) (h : lineN b i w idx pl ≠ 0) :
    (lineN b i w idx pl).toNat ≤ b.size := by
  fun_induction lineN b i w idx pl with
  | case3 i w idx pl h0 h1 _ _ =>
    have := L.Scan.lt_of_lt_ofNat (nextMemberN_pos_lt b i w (by simp [h1]))
    have := L.Scan.toNat_add_one_of_lt_ofNat (nextMemberN_pos_lt b i w (by simp [h1]))
    omega
  | case6 _ _ _ _ _ _ _ _ _ ih => exact ih h
  | case10 _ _ _ _ _ _ _ _ _ _ ih => exact ih h
  | _ => simp at h

/-- `scan_line_loop(i)`. -/
def lineLoopN (b : Array UInt8) (i : Word) : Word := lineN b i 1 0 0

/-! ## `scan_line` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2576-2599 ConLeche.Frontend.scanLineFwd -/
@[l_impl ConLeche.Frontend.scanLineFwd]
def scanLine : FunDecl := lfn (i) locals (s, j, q) {
  s := call skip_ws(i);
  if s < len(IN.u8) && IN.u8[s] == 10 { return (1, s + 1) };
  if len(IN.u8) <= s { return (1, 0) };
  if IN.u8[s] != 123 { return (0, 0) };
  j := call scan_line_loop(s + 1);
  if j == 0 { return (0, 0) };
  q := call skip_ws(j);
  if q < len(IN.u8) && IN.u8[q] == 10 { return (1, q + 1) };
  if len(IN.u8) <= q { return (1, 0) };
  return (0, 0)
}

/-- con-leche's `scanLineFwd`, validating only: `(1, next)` or `(0, 0)`. -/
def lineFwdN (b : Array UInt8) (i : Word) : Word × Word :=
  lineFwd2N b (UInt64.ofNat (L.Scan.Leaves.skipWsN b i.toNat))
where
  /-- From the first non-blank byte `s`. -/
  lineFwd2N (b : Array UInt8) (s : Word) : Word × Word :=
    if s < UInt64.ofNat b.size ∧ byteW b s = 10 then (1, s + 1)
    else if UInt64.ofNat b.size ≤ s then (1, 0)
    else if byteW b s ≠ 123 then (0, 0)
    else if lineLoopN b (s + 1) = 0 then (0, 0)
    else lineEndN b (UInt64.ofNat (L.Scan.Leaves.skipWsN b (lineLoopN b (s + 1)).toNat))
  /-- After the closing brace, at the first non-blank byte `q`. -/
  lineEndN (b : Array UInt8) (q : Word) : Word × Word :=
    if q < UInt64.ofNat b.size ∧ byteW b q = 10 then (1, q + 1)
    else if UInt64.ofNat b.size ≤ q then (1, 0)
    else (0, 0)

/-! ## `validate` -/

def validateLoop : Stmt := lblk (i, ln, ok, j) {
  while i < len(IN.u8) {
    (ok, j) := call scan_line(i);
    if ok == 0 { return ln + 1 };
    if j == 0 { return 0 };
    if j <= i { return ln + 1 };
    i := j;
    ln += 1
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2576-2599 ConLeche.Frontend.scanLineFwd -/
def validate : FunDecl := lfn () locals (i, ln, ok, j) {
  ⟪validateLoop⟫;
  return 0
}

/-- The driver from position `i`, `ln` lines read: `0` if every line from `i` on scans, else
the number of the first line that does not. -/
def validN (b : Array UInt8) (i ln : Word) : Word :=
  if h : i < UInt64.ofNat b.size then
    if (lineFwdN b i).1 = 0 then ln + 1
    else if (lineFwdN b i).2 = 0 then 0
    else if _h : i < (lineFwdN b i).2 then validN b (lineFwdN b i).2 (ln + 1)
    else ln + 1
  else 0
termination_by b.size - i.toNat
decreasing_by
  have := L.Scan.lt_of_lt_ofNat h
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

section
variable (b : Array UInt8) (i ln : Word)
theorem validN_end (h : ¬ i < UInt64.ofNat b.size) : validN b i ln = 0 := by
  rw [validN, dite_eq_right h]
theorem validN_step (h : i < UInt64.ofNat b.size) :
    validN b i ln =
      if (lineFwdN b i).1 = 0 then ln + 1
      else if (lineFwdN b i).2 = 0 then 0
      else if i < (lineFwdN b i).2 then validN b (lineFwdN b i).2 (ln + 1)
      else ln + 1 := by
  rw [validN, dite_eq_left h]; simp only [dite_eq_ite]
end
grind_pattern [lang_grind] validN_end => validN b i ln
grind_pattern [lang_grind] validN_step => validN b i ln, lineFwdN b i

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
    (hphn : p.lookup "hints_num" = some hintsNum)
    (hpho : p.lookup "hints_obj" = some hintsObj)
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
    (hpbr : p.lookup "skip_braced" = some L.Examples.skipBraced)
    (hpq : p.lookup "scan_quoted_nat" = some scanQuotedNat)
    (hpll : p.lookup "scan_line_loop" = some scanLineLoop)
    (hpln : p.lookup "scan_line" = some scanLine)
    (hpvd : p.lookup "validate" = some validate)
include hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD hpbr hpq hpll hpln hpvd

attribute [local lang_grind] Mbr.err idxCode lineKind lineVal

omit hpll hpln hpvd in
set_option maxHeartbeats 4000000 in
theorem lineLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n lineLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [lineN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lineLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        scanQuotedNat_spec p b hb ‹_› ‹_› n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        L.Examples.skipBraced_spec p ‹_› ‹_› b hb64 n,
        L.Scan.Records.scanStrName_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName n,
        L.Scan.Records.scanNumName_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hp_numName n,
        L.Scan.Records.scanApp_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hp_app n,
        L.Scan.Records.scanBinder_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hp_binder n,
        L.Scan.Records.scanLetE_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpml hpb hp_letE n,
        L.Scan.Records.scanConstE_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hp_constE n,
        L.Scan.Records.scanProj_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hp_proj n,
        L.Scan.Records.scanAxiomD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_axiomD n,
        L.Scan.Records.scanDefD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hphn hpho hph hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_defD n,
        L.Scan.Records.scanThmD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hp_thmD n,
        L.Scan.Records.scanOpaqueD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_opaqueD n,
        L.Scan.Records.scanQuotD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_quotD n,
        L.Scan.Records.scanIndD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n]
    all_goals try (intro h; cases h; done)
    all_goals clear ih hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD hpbr hpq
    all_goals subst_vars
    all_goals try rfl
    all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
      St.setLocs_cons, List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
    all_goals grind (splits := 40) [lang_grind, byteW]


omit hpln hpvd in
theorem scanLineLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_line_loop" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [lineLoopN b i]; ⊤⦄ := by
  rw [invoke_eq _ hpll]
  simp only [callFn, scanLineLoop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, lineLoopN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, fun s₀ => Triple.step_exec (lineLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD hpbr hpq (n + 1) s₀)] <;> finish

grind_pattern [lang_grind] lineN_le => lineN b i w idx pl

omit hpvd in
attribute [local lang_grind] lineFwdN lineFwdN.lineFwd2N lineFwdN.lineEndN lineLoopN in
theorem scanLine_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_line" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [(lineFwdN b i).1, (lineFwdN b i).2]; ⊤⦄ := by
  rw [invoke_eq _ hpln]
  simp only [callFn, scanLine]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.skipWs_spec p ‹_› b hb64 n,
        scanLineLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD hpbr hpq hpll n] <;> finish


omit hpvd in
theorem validateLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n validateLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [validN b (s₀.loc 0) (s₀.loc 1)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := validateLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, scanLine_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD hpbr hpq hpll hpln n] <;> finish

theorem validate_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "validate" []
    ⦃fun r s' => s' = s₀ ∧ r = [validN b 0 0]; ⊤⦄ := by
  rw [invoke_eq _ hpvd]
  simp only [callFn, validate]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, fun s₀ => Triple.step_exec (validateLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD hpbr hpq hpll hpln (n + 1) s₀)] <;> finish

end specs

end L.Scan.Line
