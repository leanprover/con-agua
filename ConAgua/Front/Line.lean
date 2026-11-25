module

public import ConAgua.Front.ApplyExpr
public import ConAgua.L.ProgHas
public import ConAgua.Front.LineRec
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# One line of the export, applied: `front_line`

`front_line(i, first)` reads the line at `i` once, as con-ron's `scan_line_fwd` does (`line_rec`,
`ConAgua.Front.LineRec`): it validates the line and reads its record's fields in one pass, then
applies the record to the parse state if it stands where it may (`lineRecPlaced`: the `meta`
header only as the first line, every other record never there, a blank line nowhere; a misplaced
line aborts, the twin's `.internal` failure): a name or level line by `apply_rec` (`apply_nstr`,
`apply_nnum`, `apply_level`, `ConAgua.Front.Apply`), an expression line by `apply_expr`, a
declaration or inductive line by `apply_dline` (below). It returns `(0, 0)` for a line that does
not scan, `(1, next)` otherwise (`next` after the line's newline, `0` at the end of the input). The
`meta` header changes nothing. A number of more than 18 digits aborts
(`docs/deviations.md`, D2), as does a full pool or table.

The models here are the name and level steps' (`lineRecW` with `apply_rec`'s spec; `applyStrW`
with `apply_str`'s, generated); `front_line`'s own model is generated and refined in `LineRef.lean`
(`frontLine_ref`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN hasEscapeN)
open L.Front.Unescape (strPutEscW strPutEsc_specW escSur escOne utf8Put strPutEsc)

namespace L.Front

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:473-479 ConRon.Arena.Frontend.applyLine -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:457-464 ConRon.Arena.Frontend.lineRecPlaced
@[no_expose, l_impl ConRon.Arena.Frontend.applyLine ConRon.Arena.Frontend.lineRecPlaced]
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2576-2599 ConLeche.Frontend.scanLineFwd
def frontLine : FunDecl := lfn (i, first) locals (ok, nx, s, pl, idx, a, c, d, j, q) {
  s := call skip_ws(i);
  if s < len(IN.u8) && IN.u8[s] == 10 { abort };
  if len(IN.u8) <= s { abort };
  if IN.u8[s] != 123 { return (0, 0) };
  (j, pl, idx, a, c, d) := call line_rec(s + 1);
  if j == 0 { return (0, 0) };
  q := call skip_ws(j);
  if q < len(IN.u8) && IN.u8[q] == 10 { nx := q + 1 }
  else if len(IN.u8) <= q { nx := 0 }
  else { return (0, 0) };
  if pl == 7 { if first == 0 { abort } } else { if first != 0 { abort } };
  if pl == 0 { ok := call apply_dline(s + 1) }
  else if pl <= 7 { ok := call apply_rec(pl, idx, a, c, d) }
  else { ok := call apply_expr(pl, idx, a, c, d) };
  return (1, nx)
}

/-- A declaration line: its fields, applied (an inductive block by `apply_ind` at its value's
position `nm`, `IndApply.lean`; a line that does not read aborts). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:473-479 ConRon.Arena.Frontend.applyLine
@[no_expose] def applyDLine : FunDecl := lfn (j) locals (pl, nm, lps, ty, vl, hk, hn, fl, z) {
  (pl, nm, lps, ty, vl, hk, hn, fl) := call rec_decl_line(j);
  if pl == 0 { abort };
  if pl == 25 {
    z := call apply_ind(nm);
    return 0
  };
  z := call apply_decl(pl, nm, lps, ty, vl, hk, hn, fl);
  return 0
}

/-- A name or level line with fields `(pl, idx, a, c, d)`, applied. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:473-479 ConRon.Arena.Frontend.applyLine
@[no_expose] def applyRec : FunDecl := lfn (pl, idx, a, c, d) locals (z) {
  if pl == 0 { abort };
  if pl == 7 { return 0 };
  if idx == 18446744073709551615 || a == 18446744073709551615 { abort R_LONG_NUMBER };
  if pl == 1 {
    z := call apply_str(idx, a, c, d);
    return 0
  };
  if c == 18446744073709551615 && (pl == 2 || pl == 4 || pl == 5) { abort R_LONG_NUMBER };
  if pl == 2 {
    z := call apply_nnum(idx, a, c);
    return 0
  };
  z := call apply_level(idx, pl - 2, a, c);
  return 0
}

/-- A `str` name line: the body `[c, d)`, unescaped into the pool at its top and applied; when
the name node existed already (the `nstr` counts `CTL[36]`, `CTL[37]` unchanged) the slice is
dropped again (the top back to `o`), as the twin drops the string it interned. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:473-479 ConRon.Arena.Frontend.applyLine
@[no_expose] def applyStr : FunDecl := lfn (idx, a, c, d) locals (z, o, l, n0, n1) {
  if c == 0 { abort };
  (o, l) := call str_put_esc(c, d);
  if len(POOL⟨⦃o⦄.tier⟩) < o - ⦃o⦄.base { abort };
  if len(POOL⟨⦃o⦄.tier⟩) - (o - ⦃o⦄.base) < l { abort };
  n0 := CTL.u64[36];
  n1 := CTL.u64[37];
  z := call apply_nstr(idx, a, o, l);
  if CTL.u64[36] == n0 && CTL.u64[37] == n1 { CTL.u64[0] := o };
  return 0
}

/-! ## The spec -/

/-- The functions of `ScanLookups`. -/
def scanLookupsFns : Prog :=
  [("skip_ws", L.Scan.Leaves.skipWs), ("skip_digits", L.Scan.Leaves.skipDigits),
   ("key_end", L.Scan.Leaves.keyEnd), ("num_end", L.Scan.Leaves.numEnd),
   ("key_at_g1", L.Scan.Key.keyAtG1), ("key_at_g2", L.Scan.Key.keyAtG2),
   ("key_at_g3", L.Scan.Key.keyAtG3), ("key_at_g4", L.Scan.Key.keyAtG4),
   ("key_at_g5", L.Scan.Key.keyAtG5), ("key_at_g6", L.Scan.Key.keyAtG6),
   ("key_at", L.Scan.Key.keyAt), ("value_at", L.Scan.Key.valueAt),
   ("next_member", L.Scan.Member.nextMember), ("slot_nat", L.Scan.Values.slotNat),
   ("match_word", L.Scan.Values.matchWord), ("scan_binder_info", L.Scan.Values.scanBinderInfo),
   ("hints_num", L.Scan.Values.hintsNum), ("hints_obj", L.Scan.Values.hintsObj),
   ("scan_hints", L.Scan.Values.scanHints), ("scan_nat_list", L.Scan.Values.scanNatList),
   ("match_lit", L.Scan.Lit.matchLit), ("scan_bool", L.Scan.Lit.scanBool),
   ("utf8_char", L.Scan.Utf8.utf8Char), ("utf8_valid", L.Scan.Str.utf8Valid),
   ("byte_in", L.Scan.Str.byteIn), ("hex_val", L.Scan.Str.hexVal), ("hex4", L.Scan.Str.hex4),
   ("hex3", L.Scan.Str.hex3), ("u_next", L.Scan.Str.uNext), ("unescape", L.Scan.Str.unescape),
   ("str_close", L.Examples.strClose), ("has_escape", L.Scan.Leaves.hasEscape),
   ("scan_string", L.Scan.Str.scanString), ("scan_str_name", L.Scan.Records.scanStrName),
   ("scan_num_name", L.Scan.Records.scanNumName), ("scan_app", L.Scan.Records.scanApp),
   ("scan_binder", L.Scan.Records.scanBinder), ("scan_let", L.Scan.Records.scanLetE),
   ("scan_const", L.Scan.Records.scanConstE), ("scan_proj", L.Scan.Records.scanProj),
   ("scan_rule", L.Scan.Records.scanRule), ("scan_rules", L.Scan.Records.scanRules),
   ("scan_ind_rec", L.Scan.Records.scanIndRec), ("scan_ind_recs", L.Scan.Records.scanIndRecs),
   ("scan_ind_type", L.Scan.Records.scanIndType), ("scan_ind_types", L.Scan.Records.scanIndTypes),
   ("scan_ind_ctor", L.Scan.Records.scanIndCtor), ("scan_ind_ctors", L.Scan.Records.scanIndCtors),
   ("scan_axiom", L.Scan.Records.scanAxiomD), ("scan_def", L.Scan.Records.scanDefD),
   ("scan_thm", L.Scan.Records.scanThmD), ("scan_opaque", L.Scan.Records.scanOpaqueD),
   ("scan_quot", L.Scan.Records.scanQuotD), ("scan_ind_decl", L.Scan.Records.scanIndD),
   ("skip_braced", L.Examples.skipBraced), ("scan_quoted_nat", L.Scan.Values.scanQuotedNat),
   ("scan_line_loop", L.Scan.Line.scanLineLoop), ("scan_line", L.Scan.Line.scanLine),
   ("validate", L.Scan.Line.validate), ("read_nat", L.Front.Fields.readNat),
   ("rec_nat_list", L.Front.Fields.recNatList), ("sub_bit", L.Front.LineRec.subBitF),
   ("sub_val", L.Front.LineRec.subValF), ("sub_rec", L.Front.LineRec.subRec),
   ("line_rec", L.Front.LineRec.lineRec),
   ("esc_sur", escSur), ("esc_one", escOne), ("utf8_put", utf8Put), ("str_put_esc", strPutEsc)]

/-- Every function of the validator and of the single pass, at its name in `p`. -/
abbrev ScanLookups (p : Prog) : Prop := ProgHas p scanLookupsFns

/-- **The model of `apply_str`** (generated): `applyStrW`, the body `[c, d)` unescaped into the
pool (`str_put_esc`, its slice at the old top) and applied (`apply_nstr`), the top back to the
slice's start on a hit. -/
l_model applyStr_spec (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
    (hpn : p.lookup "apply_nstr" = some applyNStr) (hpt : p.lookup "apply_str" = some applyStr)
    (hE : ExprLookups p) (b : Array UInt8)
  fns [hpt ↦ applyStrW void]
  specs [strPutEsc_specW p b (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3")
      (hS.get "esc_sur") (hS.get "esc_one") (hS.get "utf8_put") (hS.get "str_put_esc") n,
    applyNStr_spec p hL hpn n]
  pre [s₀.mem.arr8 IN = b ∧ pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat ≤ pcap s₀.mem]
  keep [hE.no_st8]
  grind [arena_grind] finish [Keep.size]

/-- `apply_str`'s drop of the slice: the top back to `o` when the `nstr` counts are still `n0`,
`n1` (the name node existed). -/
def strDropW (o n0 n1 : Word) (m : Mem) : Mem :=
  if rdW (m.arr64 CTL) 36 = n0 ∧ rdW (m.arr64 CTL) 37 = n1 then m.set64 CTL 0 o else m

/-- `apply_str`'s tail after `apply_nstr`: the drop. -/
theorem applyStrW_kn (b : Array UInt8) (o n0 n1 : Word) (x : Option Mem) :
    applyStrW.k_apply_nstr b o n0 n1 x = x.map (strDropW o n0 n1) := by
  cases x with
  | none => rfl
  | some m => simp only [applyStrW.k_apply_nstr, strDropW, Option.map_some]; split <;> rfl

/-- A name or level line with fields `f`, applied. -/
def lineRecW (b : Array UInt8) (m : Mem) (pl idx a c d : Word) : Option Mem :=
  if pl = 0 then none
  else if pl = 7 then some m
  else if idx = NONE ∨ a = NONE then none
  else if pl = 1 then applyStrW b m idx a c d
  else if c = NONE ∧ (pl = 2 ∨ pl = 4 ∨ pl = 5) then none
  else if pl = 2 then applyNNumW m idx a c
  else applyLevelW m idx (pl - 2) a c

section spec
variable (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
  (hpn : p.lookup "apply_nstr" = some applyNStr) (hpu : p.lookup "apply_nnum" = some applyNNum)
  (hpl : p.lookup "apply_level" = some applyLevel)
  (hpr : p.lookup "apply_rec" = some applyRec) (hpt : p.lookup "apply_str" = some applyStr)
  (hE : ExprLookups p)
  (b : Array UInt8)
include hS hL hpn hpu hpl hpr hpt hE

theorem applyRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (hpool : pcap s₀.mem < 2 ^ 63)
    (htop : s₀.mem.top.toNat ≤ pcap s₀.mem)
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
        applyStr_spec p hS hL hpn hpt hE b n,
        applyNNum_spec p hL hpu n, applyLevel_spec p hL hpl n] <;> finish [lineRecW, NONE]

end spec

end L.Front
