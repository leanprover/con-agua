module

meta import ConAgua.L.Semantics
public import ConAgua.Front.FieldsDecl
public import ConAgua.L.ProgHas
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import ConAgua.Scan.RecordsSpec
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-! # The specs of the declaration fields pass (`ConAgua.Front.FieldsDecl`) -/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Lit (matchLitN encBool scanBoolN)
open L.Scan.Leaves (numEndN skipWsN keyEndN hasEscapeN)
open L.Scan.Key (valueAtN)
open L.Scan.Records (boolEndN)

/-! ## Specs -/

/-- The functions of `DeclFieldLookups`. -/
def declFieldLookupsFns : Prog :=
  [("skip_ws", L.Scan.Leaves.skipWs), ("skip_digits", L.Scan.Leaves.skipDigits),
   ("key_end", L.Scan.Leaves.keyEnd), ("num_end", L.Scan.Leaves.numEnd),
   ("key_at_g1", L.Scan.Key.keyAtG1), ("key_at_g2", L.Scan.Key.keyAtG2),
   ("key_at_g3", L.Scan.Key.keyAtG3), ("key_at_g4", L.Scan.Key.keyAtG4),
   ("key_at_g5", L.Scan.Key.keyAtG5), ("key_at_g6", L.Scan.Key.keyAtG6),
   ("key_at", L.Scan.Key.keyAt), ("value_at", L.Scan.Key.valueAt), ("next_member", nextMember),
   ("slot_nat", slotNat), ("read_nat", readNat), ("scan_nat_list", scanNatList),
   ("match_lit", L.Scan.Lit.matchLit), ("scan_bool", L.Scan.Lit.scanBool),
   ("match_word", matchWord), ("hints_num", hintsNum), ("hints_obj", hintsObj),
   ("scan_hints", scanHints), ("utf8_char", L.Scan.Utf8.utf8Char),
   ("utf8_valid", L.Scan.Str.utf8Valid), ("byte_in", L.Scan.Str.byteIn),
   ("hex_val", L.Scan.Str.hexVal), ("hex4", L.Scan.Str.hex4), ("hex3", L.Scan.Str.hex3),
   ("u_next", L.Scan.Str.uNext), ("unescape", L.Scan.Str.unescape),
   ("str_close", L.Examples.strClose), ("has_escape", L.Scan.Leaves.hasEscape),
   ("scan_string", L.Scan.Str.scanString), ("skip_braced", L.Examples.skipBraced),
   ("match_dlit", matchDlit), ("str_code", strCode), ("hints_val", hintsVal),
   ("d_member", dMember), ("decl_val", declVal), ("decl_code", declCodeF),
   ("rec_decl_obj", recDeclObj), ("rec_decl_line", recDeclLine),
   ("scan_binder_info", scanBinderInfo), ("scan_str_name", L.Scan.Records.scanStrName),
   ("scan_num_name", L.Scan.Records.scanNumName), ("scan_app", L.Scan.Records.scanApp),
   ("scan_binder", L.Scan.Records.scanBinder), ("scan_let", L.Scan.Records.scanLetE),
   ("scan_const", L.Scan.Records.scanConstE), ("scan_proj", L.Scan.Records.scanProj),
   ("scan_rule", L.Scan.Records.scanRule), ("scan_rules", L.Scan.Records.scanRules),
   ("scan_ind_rec", L.Scan.Records.scanIndRec), ("scan_ind_recs", L.Scan.Records.scanIndRecs),
   ("scan_ind_type", L.Scan.Records.scanIndType), ("scan_ind_types", L.Scan.Records.scanIndTypes),
   ("scan_ind_ctor", L.Scan.Records.scanIndCtor), ("scan_ind_ctors", L.Scan.Records.scanIndCtors),
   ("scan_axiom", L.Scan.Records.scanAxiomD), ("scan_def", L.Scan.Records.scanDefD),
   ("scan_thm", L.Scan.Records.scanThmD), ("scan_opaque", L.Scan.Records.scanOpaqueD),
   ("scan_quot", L.Scan.Records.scanQuotD), ("scan_ind_decl", L.Scan.Records.scanIndD)]

/-- Every function the declaration fields pass calls, at its name in `p`. -/
abbrev DeclFieldLookups (p : Prog) : Prop := ProgHas p declFieldLookupsFns

section specs
variable (p : Prog) (hL : DeclFieldLookups p) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hL hb

omit hL in
theorem matchDlitLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat + (s₀.loc 2).toNat < 2 ^ 64)
    (ho : (s₀.loc 1).toNat + (s₀.loc 2).toNat ≤ DLITS.length) (hk : (s₀.loc 3).toNat ≤ (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    exec p n matchDlitLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if matchLitN b (s₀.loc 0).toNat DLITS (s₀.loc 1).toNat (s₀.loc 2).toNat
        (s₀.loc 3).toNat then 1 else 0]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := matchDlitLoop) rfl]
    sym only [lang_grind, DLITS_length] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ldc, ih] <;> finish

omit hL in
theorem matchDlitLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat + (s₀.loc 2).toNat < 2 ^ 64)
    (ho : (s₀.loc 1).toNat + (s₀.loc 2).toNat ≤ DLITS.length) (hk : (s₀.loc 3).toNat ≤ (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) matchDlitLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if matchLitN b (s₀.loc 0).toNat DLITS (s₀.loc 1).toNat (s₀.loc 2).toNat
        (s₀.loc 3).toNat then 1 else 0]; ⊤⦄ :=
  Triple.step_exec (matchDlitLoop_spec p b hb (n + 1) s₀ hm hi ho hk)

theorem matchDlit_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i o l : Word)
    (hi : i.toNat + l.toNat < 2 ^ 64) (ho : o.toNat + l.toNat ≤ DLITS.length) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "match_dlit" [i, o, l]
    ⦃fun r s' => s' = s₀ ∧
      r = [if matchLitN b i.toNat DLITS o.toNat l.toNat 0 then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "match_dlit")]
  simp only [callFn, matchDlit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, matchDlitLoop_step_spec p b hb n] <;> finish

attribute [local lang_grind] strCodeN in
theorem strCode_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (c d k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_code" [c, d, k]
    ⦃fun r s' => s' = s₀ ∧ r = [strCodeN b c d k]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "str_code")]
  simp only [callFn, strCode]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind, DLITS_length] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Leaves.hasEscape_spec p (hL.get "has_escape") b hb64 n, matchDlit_spec p hL b hb n] <;> finish

attribute [local lang_grind] hkvN in
theorem hintsVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hints_val" [v]
    ⦃fun r s' => s' = s₀ ∧ r = [(hkvN b v).1, (hkvN b v).2]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "hints_val")]
  simp only [callFn, hintsVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hval := L.Scan.Key.valueAtN_le b
    have hws := L.Scan.Key.skipWsN_le b
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.skipWs_spec p (hL.get "skip_ws") b hb64 n,
        L.Scan.Leaves.keyEnd_spec p (hL.get "key_end") b hb64 n,
        L.Scan.Key.valueAt_spec p (hL.get "skip_ws") (hL.get "value_at") b hb n,
        L.Scan.Leaves.numEnd_spec p (hL.get "skip_digits") (hL.get "num_end") b hb64 n,
        readNat_spec p b hb (hL.get "read_nat") n] <;> finish

attribute [local lang_grind] dendN dnumN dlpsN dhkN dhnN dflagN boolValN in
set_option maxHeartbeats 1600000 in
theorem dMember_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (ks k v nm lp ty vl hk hn fl : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "d_member" [ks, k, v, nm, lp, ty, vl, hk, hn, fl]
    ⦃fun r s' => s' = s₀ ∧ r = [dendN b ks k v, dnumN b 34 ks k v nm, dlpsN k v lp,
      dnumN b 61 ks k v ty, dnumN b 65 ks k v vl, dhkN b k v hk, dhnN b k v hn, dflagN b k v fl]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "d_member")]
  simp only [callFn, dMember]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        slotNat_spec p b hb (hL.get "skip_digits") (hL.get "num_end") (hL.get "slot_nat") n, readNat_spec p b hb (hL.get "read_nat") n,
        scanNatList_spec p b hb (hL.get "skip_digits") (hL.get "num_end") (hL.get "scan_nat_list") n,
        L.Scan.Lit.scanBool_spec p (hL.get "match_lit") (hL.get "scan_bool") b hb64 n,
        scanHints_spec p b hb (hL.get "skip_ws") (hL.get "skip_digits") (hL.get "key_end") (hL.get "num_end") (hL.get "key_at_g1")
          (hL.get "key_at_g2") (hL.get "key_at_g3") (hL.get "key_at_g4") (hL.get "key_at_g5") (hL.get "key_at_g6") (hL.get "key_at") (hL.get "value_at")
          (hL.get "match_word") (hL.get "hints_num") (hL.get "hints_obj") (hL.get "scan_hints") n,
        hintsVal_spec p hL b hb n,
        L.Scan.Str.scanString_spec p b hb (hL.get "utf8_char") (hL.get "utf8_valid") (hL.get "byte_in") (hL.get "hex_val") (hL.get "hex4")
          (hL.get "hex3") (hL.get "u_next") (hL.get "unescape") (hL.get "str_close") (hL.get "has_escape") (hL.get "scan_string") n,
        strCode_spec p hL b hb n] <;> finish

attribute [local lang_grind] DFld.enc DFld.none dstepN in
set_option maxHeartbeats 4000000 in
theorem dobjLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n dobjLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr DFld.none.enc = (dobjN b (s₀.loc 0) (s₀.loc 1)
        ⟨0, s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6, s₀.loc 7, s₀.loc 8⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := dobjLoop) rfl]
    sym (gen := 16) (instances := 5000) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb (hL.get "skip_ws") (hL.get "key_end") (hL.get "key_at_g1") (hL.get "key_at_g2") (hL.get "key_at_g3")
          (hL.get "key_at_g4") (hL.get "key_at_g5") (hL.get "key_at_g6") (hL.get "key_at") (hL.get "value_at") (hL.get "next_member") n,
        dMember_spec p hL b hb n] <;> finish

theorem dobjLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) dobjLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr DFld.none.enc = (dobjN b (s₀.loc 0) (s₀.loc 1)
        ⟨0, s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6, s₀.loc 7, s₀.loc 8⟩).enc; ⊤⦄ :=
  Triple.step_exec (dobjLoop_spec p hL b hb (n + 1) s₀)

attribute [local lang_grind] dobjEntryN DFld.init DFld.none in
theorem recDeclObj_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_decl_obj" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [(dobjEntryN b i).pl, (dobjEntryN b i).name, (dobjEntryN b i).lps,
      (dobjEntryN b i).type, (dobjEntryN b i).value, (dobjEntryN b i).hk, (dobjEntryN b i).hn,
      (dobjEntryN b i).flag]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "rec_decl_obj")]
  simp only [callFn, recDeclObj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        dobjLoop_step_spec p hL b hb n] <;> finish [DFld.enc]

attribute [local lang_grind] declCode in
theorem declCode_spec (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "decl_code" [k]
    ⦃fun r s' => s' = s₀ ∧ r = [declCode k]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "decl_code")]
  simp only [callFn, declCodeF]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs] <;> finish

attribute [local lang_grind] dendDN dplN dpickN dnameN in
set_option maxHeartbeats 4000000 in
theorem declVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (ks k v pl nm lp ty vl hk hn fl : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "decl_val" [ks, k, v, pl, nm, lp, ty, vl, hk, hn, fl]
    ⦃fun r s' => s' = s₀ ∧ r = [dendDN b k v, dplN k pl, dnameN k (dobjEntryN b v).name v nm,
      dpickN k (dobjEntryN b v).lps lp, dpickN k (dobjEntryN b v).type ty,
      dpickN k (dobjEntryN b v).value vl, dpickN k (dobjEntryN b v).hk hk,
      dpickN k (dobjEntryN b v).hn hn, dpickN k (dobjEntryN b v).flag fl]; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "decl_val")]
  simp only [callFn, declVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs,
      recDeclObj_spec p hL b hb n, declCode_spec p hL b hb n,
      L.Scan.Records.scanIndD_spec p b hb (hL.get "skip_ws") (hL.get "skip_digits") (hL.get "key_end") (hL.get "num_end")
        (hL.get "key_at_g1") (hL.get "key_at_g2") (hL.get "key_at_g3") (hL.get "key_at_g4") (hL.get "key_at_g5") (hL.get "key_at_g6") (hL.get "key_at")
        (hL.get "value_at") (hL.get "next_member") (hL.get "slot_nat") (hL.get "match_word") (hL.get "scan_binder_info") (hL.get "hints_num")
        (hL.get "hints_obj") (hL.get "scan_hints") (hL.get "scan_nat_list") (hL.get "match_lit") (hL.get "scan_bool") (hL.get "utf8_char")
        (hL.get "utf8_valid") (hL.get "byte_in") (hL.get "hex_val") (hL.get "hex4") (hL.get "hex3") (hL.get "u_next") (hL.get "unescape") (hL.get "str_close")
        (hL.get "has_escape") (hL.get "scan_string") (hL.get "scan_str_name") (hL.get "scan_num_name") (hL.get "scan_app") (hL.get "scan_binder")
        (hL.get "scan_let") (hL.get "scan_const") (hL.get "scan_proj") (hL.get "scan_rule") (hL.get "scan_rules") (hL.get "scan_ind_rec")
        (hL.get "scan_ind_recs") (hL.get "scan_ind_type") (hL.get "scan_ind_types") (hL.get "scan_ind_ctor") (hL.get "scan_ind_ctors")
        (hL.get "scan_axiom") (hL.get "scan_def") (hL.get "scan_thm") (hL.get "scan_opaque") (hL.get "scan_quot") (hL.get "scan_ind_decl") n]
    -- The key test's `||` chain through `L.evalC_spec`: one path per `if`, not one per exit.
    all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, beq_iff_eq] at *)
    all_goals grind (gen := 16) (instances := 5000) [lang_grind]

attribute [local lang_grind] DFld.enc DFld.none dlvN in
set_option maxHeartbeats 4000000 in
theorem dlineLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n dlineLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr DFld.none.enc = (declN b (s₀.loc 0) (s₀.loc 1)
        ⟨s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6, s₀.loc 7, s₀.loc 8, s₀.loc 9⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := dlineLoop) rfl]
    sym (gen := 24) (instances := 5000) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb (hL.get "skip_ws") (hL.get "key_end") (hL.get "key_at_g1") (hL.get "key_at_g2") (hL.get "key_at_g3")
          (hL.get "key_at_g4") (hL.get "key_at_g5") (hL.get "key_at_g6") (hL.get "key_at") (hL.get "value_at") (hL.get "next_member") n,
        declVal_spec p hL b hb n] <;> finish

theorem dlineLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) dlineLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr DFld.none.enc = (declN b (s₀.loc 0) (s₀.loc 1)
        ⟨s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6, s₀.loc 7, s₀.loc 8, s₀.loc 9⟩).enc; ⊤⦄ :=
  Triple.step_exec (dlineLoop_spec p hL b hb (n + 1) s₀)

attribute [local lang_grind] declLineN in
/-- **`rec_decl_line(i)`** returns the model's eight words. -/
theorem recDeclLine_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_decl_line" [i]
    ⦃fun r s' => s' = s₀ ∧ r = (declLineN b i).enc; ⊤⦄ := by
  rw [invoke_eq _ (hL.get "rec_decl_line")]
  simp only [callFn, recDeclLine]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        dlineLoop_step_spec p hL b hb n] <;> finish [DFld.enc, DFld.none]

end specs

end L.Front.Fields
