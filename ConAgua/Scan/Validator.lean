module

public import ConAgua.Scan.Line

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
  ("key_at_g1", L.Scan.Key.keyAtG1),
  ("key_at_g2", L.Scan.Key.keyAtG2),
  ("key_at_g3", L.Scan.Key.keyAtG3),
  ("key_at_g4", L.Scan.Key.keyAtG4),
  ("key_at_g5", L.Scan.Key.keyAtG5),
  ("key_at_g6", L.Scan.Key.keyAtG6),
  ("key_at", L.Scan.Key.keyAt),
  ("value_at", L.Scan.Key.valueAt),
  ("next_member", nextMember),
  ("slot_nat", slotNat),
  ("match_word", matchWord),
  ("scan_binder_info", scanBinderInfo),
  ("hints_num", hintsNum),
  ("hints_obj", hintsObj),
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
  ("u_next", L.Scan.Str.uNext),
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

end L.Scan.Validator

namespace L.Scan.Validator

open L L.Scan.Line

end L.Scan.Validator
