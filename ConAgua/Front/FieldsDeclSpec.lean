module

public import ConAgua.Front.FieldsDecl
meta import ConAgua.L.Semantics

@[expose] public section

/-! # The specs of the declaration fields pass (`ConAgua.Front.FieldsDecl`) -/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false
set_option linter.deprecated false

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

/-- Every function the declaration fields pass calls, at its name in `p`. -/
structure DeclLookups (p : Prog) : Prop where
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
  next_member : p.lookup "next_member" = some nextMember
  slot_nat : p.lookup "slot_nat" = some slotNat
  read_nat : p.lookup "read_nat" = some readNat
  scan_nat_list : p.lookup "scan_nat_list" = some scanNatList
  match_lit : p.lookup "match_lit" = some L.Scan.Lit.matchLit
  scan_bool : p.lookup "scan_bool" = some L.Scan.Lit.scanBool
  match_word : p.lookup "match_word" = some matchWord
  hints_num : p.lookup "hints_num" = some hintsNum
  hints_obj : p.lookup "hints_obj" = some hintsObj
  scan_hints : p.lookup "scan_hints" = some scanHints
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
  skip_braced : p.lookup "skip_braced" = some L.Examples.skipBraced
  match_dlit : p.lookup "match_dlit" = some matchDlit
  str_code : p.lookup "str_code" = some strCode
  hints_val : p.lookup "hints_val" = some hintsVal
  d_member : p.lookup "d_member" = some dMember
  decl_val : p.lookup "decl_val" = some declVal
  decl_code : p.lookup "decl_code" = some declCodeF
  rec_decl_obj : p.lookup "rec_decl_obj" = some recDeclObj
  rec_decl_line : p.lookup "rec_decl_line" = some recDeclLine
  scan_binder_info : p.lookup "scan_binder_info" = some scanBinderInfo
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

section specs
variable (p : Prog) (hL : DeclLookups p) (b : Array UInt8) (hb : b.size < 2 ^ 63)
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
  rw [invoke_eq _ hL.match_dlit]
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
  rw [invoke_eq _ hL.str_code]
  simp only [callFn, strCode]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind, DLITS_length] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Leaves.hasEscape_spec p hL.has_escape b hb64 n, matchDlit_spec p hL b hb n] <;> finish

attribute [local lang_grind] hkvN in
theorem hintsVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hints_val" [v]
    ⦃fun r s' => s' = s₀ ∧ r = [(hkvN b v).1, (hkvN b v).2]; ⊤⦄ := by
  rw [invoke_eq _ hL.hints_val]
  simp only [callFn, hintsVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hval := L.Scan.Key.valueAtN_le b
    have hws := L.Scan.Key.skipWsN_le b
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.skipWs_spec p hL.skip_ws b hb64 n,
        L.Scan.Leaves.keyEnd_spec p hL.key_end b hb64 n,
        L.Scan.Key.valueAt_spec p hL.skip_ws hL.value_at b hb n,
        L.Scan.Leaves.numEnd_spec p hL.skip_digits hL.num_end b hb64 n,
        readNat_spec p b hb hL.read_nat n] <;> finish

attribute [local lang_grind] dendN dnumN dlpsN dhkN dhnN dflagN boolValN in
set_option maxHeartbeats 1600000 in
theorem dMember_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (ks k v nm lp ty vl hk hn fl : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "d_member" [ks, k, v, nm, lp, ty, vl, hk, hn, fl]
    ⦃fun r s' => s' = s₀ ∧ r = [dendN b ks k v, dnumN b 34 ks k v nm, dlpsN k v lp,
      dnumN b 61 ks k v ty, dnumN b 65 ks k v vl, dhkN b k v hk, dhnN b k v hn, dflagN b k v fl]; ⊤⦄ := by
  rw [invoke_eq _ hL.d_member]
  simp only [callFn, dMember]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        slotNat_spec p b hb hL.skip_digits hL.num_end hL.slot_nat n, readNat_spec p b hb hL.read_nat n,
        scanNatList_spec p b hb hL.skip_digits hL.num_end hL.scan_nat_list n,
        L.Scan.Lit.scanBool_spec p hL.match_lit hL.scan_bool b hb64 n,
        scanHints_spec p b hb hL.skip_ws hL.skip_digits hL.key_end hL.num_end hL.key_at_g1
          hL.key_at_g2 hL.key_at_g3 hL.key_at_g4 hL.key_at_g5 hL.key_at_g6 hL.key_at hL.value_at
          hL.match_word hL.hints_num hL.hints_obj hL.scan_hints n,
        hintsVal_spec p hL b hb n,
        L.Scan.Str.scanString_spec p b hb hL.utf8_char hL.utf8_valid hL.byte_in hL.hex_val hL.hex4
          hL.hex3 hL.u_next hL.unescape hL.str_close hL.has_escape hL.scan_string n,
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
        nextMember_spec p b hb hL.skip_ws hL.key_end hL.key_at_g1 hL.key_at_g2 hL.key_at_g3
          hL.key_at_g4 hL.key_at_g5 hL.key_at_g6 hL.key_at hL.value_at hL.next_member n,
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
  rw [invoke_eq _ hL.rec_decl_obj]
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
  rw [invoke_eq _ hL.decl_code]
  simp only [callFn, declCodeF]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs] <;> finish

attribute [local lang_grind] dendDN dplN dpickN in
set_option maxHeartbeats 4000000 in
theorem declVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (ks k v pl nm lp ty vl hk hn fl : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "decl_val" [ks, k, v, pl, nm, lp, ty, vl, hk, hn, fl]
    ⦃fun r s' => s' = s₀ ∧ r = [dendDN b k v, dplN k pl, dpickN k (dobjEntryN b v).name nm,
      dpickN k (dobjEntryN b v).lps lp, dpickN k (dobjEntryN b v).type ty,
      dpickN k (dobjEntryN b v).value vl, dpickN k (dobjEntryN b v).hk hk,
      dpickN k (dobjEntryN b v).hn hn, dpickN k (dobjEntryN b v).flag fl]; ⊤⦄ := by
  rw [invoke_eq _ hL.decl_val]
  simp only [callFn, declVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) (instances := 5000) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        recDeclObj_spec p hL b hb n, declCode_spec p hL b hb n,
        L.Scan.Records.scanIndD_spec p b hb hL.skip_ws hL.skip_digits hL.key_end hL.num_end
          hL.key_at_g1 hL.key_at_g2 hL.key_at_g3 hL.key_at_g4 hL.key_at_g5 hL.key_at_g6 hL.key_at
          hL.value_at hL.next_member hL.slot_nat hL.match_word hL.scan_binder_info hL.hints_num
          hL.hints_obj hL.scan_hints hL.scan_nat_list hL.match_lit hL.scan_bool hL.utf8_char
          hL.utf8_valid hL.byte_in hL.hex_val hL.hex4 hL.hex3 hL.u_next hL.unescape hL.str_close
          hL.has_escape hL.scan_string hL.scan_str_name hL.scan_num_name hL.scan_app hL.scan_binder
          hL.scan_let hL.scan_const hL.scan_proj hL.scan_rule hL.scan_rules hL.scan_ind_rec
          hL.scan_ind_recs hL.scan_ind_type hL.scan_ind_types hL.scan_ind_ctor hL.scan_ind_ctors
          hL.scan_axiom hL.scan_def hL.scan_thm hL.scan_opaque hL.scan_quot hL.scan_ind_decl n] <;>
        finish

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
        nextMember_spec p b hb hL.skip_ws hL.key_end hL.key_at_g1 hL.key_at_g2 hL.key_at_g3
          hL.key_at_g4 hL.key_at_g5 hL.key_at_g6 hL.key_at hL.value_at hL.next_member n,
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
  rw [invoke_eq _ hL.rec_decl_line]
  simp only [callFn, recDeclLine]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        dlineLoop_step_spec p hL b hb n] <;> finish [DFld.enc, DFld.none]

end specs

end L.Front.Fields
