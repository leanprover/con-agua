module

public import ConAgua.Scan.Line
public import ConAgua.Compiler.WF
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The Stage B validator as one L program

`valProg` is every function of the validator; its entry is `validate` (no arguments): `0` if every
line of the buffer scans as con-leche's `scanLineFwd` scans it, else the number of the first line
that does not.
-/

namespace L.Scan.Validator

open L L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line

/-- The validator. -/
def valProg : Prog := [
  ("skip_ws", L.Scan.Leaves.skipWs),
  ("skip_digits", L.Scan.Leaves.skipDigits),
  ("key_end", L.Scan.Leaves.keyEnd),
  ("num_end", L.Scan.Leaves.numEnd),
  ("key_at", L.Scan.Key.keyAt),
  ("value_at", L.Scan.Key.valueAt),
  ("next_member", nextMember),
  ("slot_nat", slotNat),
  ("match_word", matchWord),
  ("scan_binder_info", scanBinderInfo),
  ("scan_hints", scanHints),
  ("scan_nat_list", scanNatList),
  ("match_lit", L.Scan.Lit.matchLit),
  ("scan_bool", L.Scan.Lit.scanBool),
  ("utf8_char", L.Scan.Utf8.utf8Char),
  ("utf8_valid", L.Scan.Str.utf8Valid),
  ("byte_in", L.Scan.Str.byteIn),
  ("hex_val", L.Scan.Str.hexVal),
  ("hex4", L.Scan.Str.hex4),
  ("hex3", L.Scan.Str.hex3),
  ("unescape", L.Scan.Str.unescape),
  ("str_close", L.Examples.strClose),
  ("has_escape", L.Scan.Leaves.hasEscape),
  ("scan_string", L.Scan.Str.scanString),
  ("scan_str_name", scanStrName),
  ("scan_num_name", scanNumName),
  ("scan_app", scanApp),
  ("scan_binder", scanBinder),
  ("scan_let", scanLetE),
  ("scan_const", scanConstE),
  ("scan_proj", scanProj),
  ("scan_rule", scanRule),
  ("scan_rules", scanRules),
  ("scan_ind_rec", scanIndRec),
  ("scan_ind_recs", scanIndRecs),
  ("scan_ind_type", scanIndType),
  ("scan_ind_types", scanIndTypes),
  ("scan_ind_ctor", scanIndCtor),
  ("scan_ind_ctors", scanIndCtors),
  ("scan_axiom", scanAxiomD),
  ("scan_def", scanDefD),
  ("scan_thm", scanThmD),
  ("scan_opaque", scanOpaqueD),
  ("scan_quot", scanQuotD),
  ("scan_ind_decl", scanIndD),
  ("skip_braced", L.Examples.skipBraced),
  ("scan_quoted_nat", scanQuotedNat),
  ("scan_line_loop", scanLineLoop),
  ("scan_line", scanLine),
  ("validate", validate)]

/-- Run `validate` on `s` with the L interpreter. -/
def runValidate (s : String) (fuel : Nat := 100000) : Option Word :=
  match run valProg fuel "validate" [] { bytes := #[s.toUTF8.data] } with
  | .ok ([r], _) => some r
  | _ => none

/-- Run `scan_line` at `0` on `s`. -/
def runLine (s : String) (fuel : Nat := 100000) : Option (List Word) :=
  match run valProg fuel "scan_line" [0] { bytes := #[s.toUTF8.data] } with
  | .ok (r, _) => some r
  | _ => none

end L.Scan.Validator

namespace L.Scan.Validator

/-- The compiler's static check passes (`compile_correct` applies). -/
theorem valProg_wf : L.Compiler.Prog.wf (L.Compiler.Prog.tab valProg 1 0) valProg = true := by decide +kernel

end L.Scan.Validator
