import ConAgua.Front.StateDR
import ConAgua.Front.FieldsLink

/-!
# One line of the export, applied: `front_line`

`front_line(i)` scans the line at `i` with Stage B's validator (`scan_line`), and, if it is a
name or level line, reads its fields (`rec_line_loop`, `ConAgua.Front.Fields`) and applies it to
the parse state (`apply_nstr`, `apply_nnum`, `apply_level`, `ConAgua.Front.Apply`). It returns
`(0, 0)` for a line that does not scan, `(1, next)` otherwise (`next` as `scan_line`'s). A blank
line and the `meta` header change nothing. An expression or declaration line, a number of more
than 18 digits, a string with an escape, a full pool or table abort: the frontend does not apply
them yet.

`frontLine_refines`: when `front_line(i)` returns `(1, next)`, con-leche's `scanLineFwd b i` is
`.ok r next'` with `next'` the word `next`, and con-ron's `applyLine st r` runs, its state is
related to the memory after by `ArenaR` and its parse state by `StateDR`.
-/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN hasEscapeN)

namespace L.Front

def frontLine : FunDecl := lfn (i) locals (ok, nx, s, pl, idx, a, c, d) {
  (ok, nx) := call scan_line(i);
  if ok == 0 { return (0, 0) };
  s := call skip_ws(i);
  if !(s < len(IN.u8) && IN.u8[s] == 123) { return (1, nx) };
  (pl, idx, a, c, d) := call rec_line_loop(s + 1);
  ok := call apply_rec(pl, idx, a, c, d);
  return (1, nx)
}

/-- A name or level line with fields `(pl, idx, a, c, d)`, applied. -/
def applyRec : FunDecl := lfn (pl, idx, a, c, d) locals (z) {
  if pl == 0 { abort };
  if pl == 7 { return 0 };
  if idx == 18446744073709551615 || a == 18446744073709551615 { abort };
  if pl == 1 {
    z := call apply_str(idx, a, c, d);
    return 0
  };
  if c == 18446744073709551615 && (pl == 2 || pl == 4 || pl == 5) { abort };
  if pl == 2 {
    z := call apply_nnum(idx, a, c);
    return 0
  };
  z := call apply_level(idx, pl - 2, a, c);
  return 0
}

/-- A `str` name line: the body `[c, d)` without escapes, copied to the pool and applied. -/
def applyStr : FunDecl := lfn (idx, a, c, d) locals (z, o, l) {
  if len(IN.u8) < c { abort };
  z := call has_escape(c, d);
  if z != 0 { abort };
  (o, l) := call str_put(c, d);
  z := call apply_nstr(idx, a, o, l);
  return 0
}

/-! ## The model -/

/-- `str_put`'s memory. -/
def strPutW (m : Mem) (vs ve : Word) : Mem :=
  (putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))

instance (m : Mem) (vs ve : Word) : Decidable (strPutOK m vs ve) := by
  unfold strPutOK; infer_instance

/-- A line applied: `(1, next)` and the memory. -/
def okRes (nx : Word) (m : Mem) : List Word × Mem := ([1, nx], m)

/-- The model of `apply_str`. -/
def applyStrW (b : Array UInt8) (m : Mem) (idx a c d : Word) : Option Mem :=
  if UInt64.ofNat b.size < c then none
  else if UInt64.ofNat (hasEscapeN b c.toNat d.toNat) ≠ 0 then none
  else if strPutOK m c d then applyNStrW (strPutW m c d) idx a m.top (d - c)
  else none

/-- A name or level line with fields `f`, applied. -/
def lineRecW (b : Array UInt8) (m : Mem) (pl idx a c d : Word) : Option Mem :=
  if pl = 0 then none
  else if pl = 7 then some m
  else if idx = NONE ∨ a = NONE then none
  else if pl = 1 then applyStrW b m idx a c d
  else if c = NONE ∧ (pl = 2 ∨ pl = 4 ∨ pl = 5) then none
  else if pl = 2 then applyNNumW m idx a c
  else applyLevelW m idx (pl - 2) a c

/-- The model of `front_line(i)`. -/
def frontLineW (b : Array UInt8) (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if (lineFwdN b i).1 = 0 then some ([0, 0], m)
  else if UInt64.ofNat (skipWsN b i.toNat) < UInt64.ofNat b.size ∧
      byteW b (UInt64.ofNat (skipWsN b i.toNat)) = 123 then
    (lineRecW b m (recLineN b (UInt64.ofNat (skipWsN b i.toNat) + 1)).pl
      (recLineN b (UInt64.ofNat (skipWsN b i.toNat) + 1)).idx (recLineN b (UInt64.ofNat (skipWsN b i.toNat) + 1)).a
      (recLineN b (UInt64.ofNat (skipWsN b i.toNat) + 1)).c (recLineN b (UInt64.ofNat (skipWsN b i.toNat) + 1)).d).map
      (okRes (lineFwdN b i).2)
  else some ([1, (lineFwdN b i).2], m)

theorem map_okRes (nx : Word) (m : Mem) : Option.map (okRes nx) (some m) = some ([1, nx], m) := rfl

/-- `str_put`'s memory has the pool's size, and the slice it wrote fits. -/
theorem strPut_room (m : Mem) (vs ve : Word) (hps : (m.arr64 POOL).size < 2 ^ 63)
    (h : strPutOK m vs ve) :
    (((putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))).arr64 POOL).size < 2 ^ 64 ∧
    m.top.toNat + (ve - vs).toNat ≤
      (((putW m m.top vs (ve - vs) 0).set64 CTL 0 (m.top + (ve - vs))).arr64 POOL).size := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hle := UInt64.le_iff_toNat_le.mp h1
  have hn : (ve - vs).toNat = ve.toNat - vs.toNat := UInt64.toNat_sub_of_le _ _ h1
  have hlen : (m.len64 POOL).toNat = (m.arr64 POOL).size := by
    simp only [Mem.len64]; exact toNat_ofNat_size _ hps
  have hroom : (ve - vs).toNat ≤ (m.arr64 POOL).size - m.top.toNat := by
    have := UInt64.le_iff_toNat_le.mp h4
    rwa [UInt64.toNat_sub_of_le _ _ h3, hlen] at this
  have ht := UInt64.le_iff_toNat_le.mp h3
  rw [hlen] at ht
  have hve := ve.toNat_lt
  obtain ⟨-, hsz, -⟩ := putW_facts m.top vs (ve - vs) (by omega) _ m 0 rfl
    (UInt64.le_iff_toNat_le.mpr (by simp)) (by omega) hps
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hsz]
  omega

/-! ## The spec -/

/-- Every function of the validator and of the fields pass, at its name in `p`. -/
structure ScanLookups (p : Prog) : Prop where
  skip_ws : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs
  skip_digits : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits
  key_end : p.lookup "key_end" = some L.Scan.Leaves.keyEnd
  num_end : p.lookup "num_end" = some L.Scan.Leaves.numEnd
  key_at_g1 : p.lookup "key_at_g1" = some L.Scan.Key.keyAtG1
  key_at_g2 : p.lookup "key_at_g2" = some L.Scan.Key.keyAtG2
  key_at_g3 : p.lookup "key_at_g3" = some L.Scan.Key.keyAtG3
  key_at_g4 : p.lookup "key_at_g4" = some L.Scan.Key.keyAtG4
  key_at_g5 : p.lookup "key_at_g5" = some L.Scan.Key.keyAtG5
  key_at_g6 : p.lookup "key_at_g6" = some L.Scan.Key.keyAtG6
  key_at : p.lookup "key_at" = some L.Scan.Key.keyAt
  value_at : p.lookup "value_at" = some L.Scan.Key.valueAt
  next_member : p.lookup "next_member" = some L.Scan.Member.nextMember
  slot_nat : p.lookup "slot_nat" = some L.Scan.Values.slotNat
  match_word : p.lookup "match_word" = some L.Scan.Values.matchWord
  scan_binder_info : p.lookup "scan_binder_info" = some L.Scan.Values.scanBinderInfo
  hints_num : p.lookup "hints_num" = some L.Scan.Values.hintsNum
  hints_obj : p.lookup "hints_obj" = some L.Scan.Values.hintsObj
  scan_hints : p.lookup "scan_hints" = some L.Scan.Values.scanHints
  scan_nat_list : p.lookup "scan_nat_list" = some L.Scan.Values.scanNatList
  match_lit : p.lookup "match_lit" = some L.Scan.Lit.matchLit
  scan_bool : p.lookup "scan_bool" = some L.Scan.Lit.scanBool
  utf8_char : p.lookup "utf8_char" = some L.Scan.Utf8.utf8Char
  utf8_valid : p.lookup "utf8_valid" = some L.Scan.Str.utf8Valid
  byte_in : p.lookup "byte_in" = some L.Scan.Str.byteIn
  hex_val : p.lookup "hex_val" = some L.Scan.Str.hexVal
  hex4 : p.lookup "hex4" = some L.Scan.Str.hex4
  hex3 : p.lookup "hex3" = some L.Scan.Str.hex3
  u_next : p.lookup "u_next" = some L.Scan.Str.uNext
  unescape : p.lookup "unescape" = some L.Scan.Str.unescape
  str_close : p.lookup "str_close" = some L.Examples.strClose
  has_escape : p.lookup "has_escape" = some L.Scan.Leaves.hasEscape
  scan_string : p.lookup "scan_string" = some L.Scan.Str.scanString
  scan_str_name : p.lookup "scan_str_name" = some L.Scan.Records.scanStrName
  scan_num_name : p.lookup "scan_num_name" = some L.Scan.Records.scanNumName
  scan_app : p.lookup "scan_app" = some L.Scan.Records.scanApp
  scan_binder : p.lookup "scan_binder" = some L.Scan.Records.scanBinder
  scan_let : p.lookup "scan_let" = some L.Scan.Records.scanLetE
  scan_const : p.lookup "scan_const" = some L.Scan.Records.scanConstE
  scan_proj : p.lookup "scan_proj" = some L.Scan.Records.scanProj
  scan_rule : p.lookup "scan_rule" = some L.Scan.Records.scanRule
  scan_rules : p.lookup "scan_rules" = some L.Scan.Records.scanRules
  scan_ind_rec : p.lookup "scan_ind_rec" = some L.Scan.Records.scanIndRec
  scan_ind_recs : p.lookup "scan_ind_recs" = some L.Scan.Records.scanIndRecs
  scan_ind_type : p.lookup "scan_ind_type" = some L.Scan.Records.scanIndType
  scan_ind_types : p.lookup "scan_ind_types" = some L.Scan.Records.scanIndTypes
  scan_ind_ctor : p.lookup "scan_ind_ctor" = some L.Scan.Records.scanIndCtor
  scan_ind_ctors : p.lookup "scan_ind_ctors" = some L.Scan.Records.scanIndCtors
  scan_axiom : p.lookup "scan_axiom" = some L.Scan.Records.scanAxiomD
  scan_def : p.lookup "scan_def" = some L.Scan.Records.scanDefD
  scan_thm : p.lookup "scan_thm" = some L.Scan.Records.scanThmD
  scan_opaque : p.lookup "scan_opaque" = some L.Scan.Records.scanOpaqueD
  scan_quot : p.lookup "scan_quot" = some L.Scan.Records.scanQuotD
  scan_ind_decl : p.lookup "scan_ind_decl" = some L.Scan.Records.scanIndD
  skip_braced : p.lookup "skip_braced" = some L.Examples.skipBraced
  scan_quoted_nat : p.lookup "scan_quoted_nat" = some L.Scan.Values.scanQuotedNat
  scan_line_loop : p.lookup "scan_line_loop" = some L.Scan.Line.scanLineLoop
  scan_line : p.lookup "scan_line" = some L.Scan.Line.scanLine
  validate : p.lookup "validate" = some L.Scan.Line.validate
  read_nat : p.lookup "read_nat" = some L.Front.Fields.readNat
  rec_nat_list : p.lookup "rec_nat_list" = some L.Front.Fields.recNatList
  rec_str_name : p.lookup "rec_str_name" = some L.Front.Fields.recStrName
  rec_num_name : p.lookup "rec_num_name" = some L.Front.Fields.recNumName
  rec_line_loop : p.lookup "rec_line_loop" = some L.Front.Fields.recLineLoop

section spec
variable (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
  (hpf : p.lookup "front_line" = some frontLine) (hps : p.lookup "str_put" = some strPut)
  (hpn : p.lookup "apply_nstr" = some applyNStr) (hpu : p.lookup "apply_nnum" = some applyNNum)
  (hpl : p.lookup "apply_level" = some applyLevel)
  (hpr : p.lookup "apply_rec" = some applyRec) (hpt : p.lookup "apply_str" = some applyStr)
  (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hS hL hpf hps hpn hpu hpl hpr hpt hb

attribute [local lang_grind =] map_okRes

theorem applyStr_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63)
    (idx a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_str" [idx, a, c, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyStrW b s₀.mem idx a c d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hpt]
  simp only [callFn, applyStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hroom := strPut_room s₀.mem c d hpool
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Leaves.hasEscape_spec p hS.has_escape b hb64 n,
        strPut_specW p hps n, applyNStr_spec p hL hpn n] <;> finish [applyStrW, strPutW]

theorem applyRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63)
    (pl idx a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_rec" [pl, idx, a, c, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ lineRecW b s₀.mem pl idx a c d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hpr]
  simp only [callFn, applyRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        applyStr_spec p hS hL hpf hps hpn hpu hpl hpr hpt b hb n,
        applyNNum_spec p hL hpu n, applyLevel_spec p hL hpl n] <;> finish [lineRecW, NONE]

theorem frontLine_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_line" [i]
    ⦃fun r s' => frontLineW b s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpf]
  simp only [callFn, frontLine]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Line.scanLine_spec p b hb hS.skip_ws hS.skip_digits hS.key_end hS.num_end hS.key_at_g1 hS.key_at_g2 hS.key_at_g3 hS.key_at_g4 hS.key_at_g5 hS.key_at_g6 hS.key_at hS.value_at hS.next_member hS.slot_nat hS.match_word hS.scan_binder_info hS.hints_num hS.hints_obj hS.scan_hints hS.scan_nat_list hS.match_lit hS.scan_bool hS.utf8_char hS.utf8_valid hS.byte_in hS.hex_val hS.hex4 hS.hex3 hS.u_next hS.unescape hS.str_close hS.has_escape hS.scan_string hS.scan_str_name hS.scan_num_name hS.scan_app hS.scan_binder hS.scan_let hS.scan_const hS.scan_proj hS.scan_rule hS.scan_rules hS.scan_ind_rec hS.scan_ind_recs hS.scan_ind_type hS.scan_ind_types hS.scan_ind_ctor hS.scan_ind_ctors hS.scan_axiom hS.scan_def hS.scan_thm hS.scan_opaque hS.scan_quot hS.scan_ind_decl hS.skip_braced hS.scan_quoted_nat hS.scan_line_loop hS.scan_line hS.validate n,
        L.Scan.Leaves.skipWs_spec p hS.skip_ws b hb64 n,
        L.Front.Fields.recLineLoop_spec p b hb hS.skip_ws hS.skip_digits hS.key_end hS.num_end hS.key_at_g1 hS.key_at_g2 hS.key_at_g3 hS.key_at_g4 hS.key_at_g5 hS.key_at_g6 hS.key_at hS.value_at hS.next_member hS.slot_nat hS.utf8_char hS.utf8_valid hS.byte_in hS.hex_val hS.hex4 hS.hex3 hS.u_next hS.unescape hS.str_close hS.has_escape hS.scan_string hS.skip_braced hS.read_nat hS.rec_nat_list hS.rec_str_name hS.rec_num_name hS.rec_line_loop n,
        applyRec_spec p hS hL hpf hps hpn hpu hpl hpr hpt b hb n] <;> finish [frontLineW, Fld.enc]

end spec

end L.Front
