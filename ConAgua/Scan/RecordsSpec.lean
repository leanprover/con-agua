module

meta import ConAgua.L.Semantics
public import ConAgua.Scan.Records
import ConAgua.Census.Attr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The record loops: specs

Each record scanner of `ConAgua.Scan.Records` against the generic model `objN` of
`ConAgua.Scan.Member` (moved out of `Records.lean`, which keeps the L code and the models).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Records

open L.Scan.Member
open L.Scan.Values

attribute [local lang_grind] boolEndN

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
include hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD


attribute [local lang_grind] strNameBit strNameVal Mbr.err

omit hpmw hpi hphn hpho hph hpl hpml hpb hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem strNameLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n strNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN strNameBit (strNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := strNameLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpml hpb hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanStrName "validity"]
theorem scanStrName_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_str_name" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [strNameN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_strName]
  simp only [callFn, scanStrName]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, strNameN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (strNameLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt (n + 1) s₀)] <;> finish




attribute [local lang_grind] numNameBit numNameVal Mbr.err

omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem numNameLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n numNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN numNameBit (numNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := numNameLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanNumName "validity"]
theorem scanNumName_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_num_name" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [numNameN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_numName]
  simp only [callFn, scanNumName]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, numNameN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (numNameLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps (n + 1) s₀)] <;> finish




attribute [local lang_grind] appBit appVal Mbr.err

omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem appLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n appLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN appBit (appVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := appLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanAppExpr "validity"]
theorem scanApp_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_app" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [appN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_app]
  simp only [callFn, scanApp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, appN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (appLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps (n + 1) s₀)] <;> finish




attribute [local lang_grind] binderBit binderVal Mbr.err

omit hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem binderLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n binderLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN binderBit (binderVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := binderLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        scanBinderInfo_spec p b hb ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanLamExpr "validity", refines_part ConLeche.Frontend.scanForallExpr "validity"]
theorem scanBinder_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_binder" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [binderN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_binder]
  simp only [callFn, scanBinder]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, binderN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (binderLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi (n + 1) s₀)] <;> finish




attribute [local lang_grind] letEBit letEVal Mbr.err

omit hpmw hpi hphn hpho hph hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem letELoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n letELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN letEBit (letEVal b) 27 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := letELoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanLetExpr "validity"]
theorem scanLetE_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_let" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [letEN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_letE]
  simp only [callFn, scanLetE]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, letEN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (letELoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpml hpb (n + 1) s₀)] <;> finish




attribute [local lang_grind] constEBit constEVal Mbr.err

omit hpmw hpi hphn hpho hph hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem constELoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n constELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN constEBit (constEVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := constELoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanConstExpr "validity"]
theorem scanConstE_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_const" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [constEN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_constE]
  simp only [callFn, scanConstE]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, constEN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (constELoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl (n + 1) s₀)] <;> finish




attribute [local lang_grind] projBit projVal Mbr.err

omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem projLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n projLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN projBit (projVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := projLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanProjExpr "validity"]
theorem scanProj_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_proj" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [projN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_proj]
  simp only [callFn, scanProj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, projN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (projLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps (n + 1) s₀)] <;> finish




attribute [local lang_grind] ruleBit ruleVal Mbr.err

omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem ruleLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n ruleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN ruleBit (ruleVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := ruleLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanRule "validity"]
theorem scanRule_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_rule" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [ruleN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_rule]
  simp only [callFn, scanRule]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, ruleN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (ruleLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem rulesLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n rulesLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (ruleN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := rulesLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanRule_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hp_rule n] <;> finish


omit hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanRules "validity"]
theorem scanRules_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_rules" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [rulesN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_rules]
  simp only [callFn, scanRules]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, rulesN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (rulesLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hp_rule (n + 1) s₀)] <;> finish




attribute [local lang_grind] indRecBit indRecVal Mbr.err

-- eleven keys: all `finish` calls of the theorem share one heartbeat budget
omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
set_option maxHeartbeats 800000 in
theorem indRecLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indRecBit (indRecVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indRecLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        scanRules_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hp_rule hp_rules n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


@[refines_part ConLeche.Frontend.scanIndRec "validity"]
theorem scanIndRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_rec" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indRecN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indRec]
  simp only [callFn, scanIndRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indRecN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indRecLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_rule hp_rules (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

theorem indRecsLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indRecsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indRecN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indRecsLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanIndRec_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish


@[refines_part ConLeche.Frontend.scanIndRecs "validity"]
theorem scanIndRecs_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_recs" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indRecsN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indRecs]
  simp only [callFn, scanIndRecs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indRecsN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indRecsLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] indTypeBit indTypeVal Mbr.err

-- eleven keys: all `finish` calls of the theorem share one heartbeat budget
omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
set_option maxHeartbeats 800000 in
theorem indTypeLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indTypeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indTypeBit (indTypeVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indTypeLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanIndType "validity"]
theorem scanIndType_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_type" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indTypeN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indType]
  simp only [callFn, scanIndType]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indTypeN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indTypeLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem indTypesLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indTypesLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indTypeN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indTypesLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanIndType_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_indType n] <;> finish


omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanIndTypes "validity"]
theorem scanIndTypes_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_types" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indTypesN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indTypes]
  simp only [callFn, scanIndTypes]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indTypesN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indTypesLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_indType (n + 1) s₀)] <;> finish




attribute [local lang_grind] indCtorBit indCtorVal Mbr.err

omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem indCtorLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indCtorLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indCtorBit (indCtorVal b) 252 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indCtorLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanIndCtor "validity"]
theorem scanIndCtor_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_ctor" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indCtorN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indCtor]
  simp only [callFn, scanIndCtor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indCtorN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indCtorLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem indCtorsLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indCtorsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN (indCtorN b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indCtorsLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        scanIndCtor_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_indCtor n] <;> finish


omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanIndCtors "validity"]
theorem scanIndCtors_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_ctors" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indCtorsN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indCtors]
  simp only [callFn, scanIndCtors]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indCtorsN, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indCtorsLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_indCtor (n + 1) s₀)] <;> finish




attribute [local lang_grind] axiomDBit axiomDVal Mbr.err

omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem axiomDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n axiomDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN axiomDBit (axiomDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := axiomDLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanAxiomDecl "validity"]
theorem scanAxiomD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_axiom" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [axiomDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_axiomD]
  simp only [callFn, scanAxiomD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, axiomDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (axiomDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb (n + 1) s₀)] <;> finish




attribute [local lang_grind] defDBit defDVal Mbr.err

omit hpi hpml hpb hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem defDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n defDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN defDBit (defDVal b) 124 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := defDLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        scanHints_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpi hpml hpb hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_thmD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanDefDecl "validity"]
theorem scanDefD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_def" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [defDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_defD]
  simp only [callFn, scanDefD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, defDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (defDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hphn hpho hph hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt (n + 1) s₀)] <;> finish




attribute [local lang_grind] thmDBit thmDVal Mbr.err

omit hpmw hpi hphn hpho hph hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem thmDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n thmDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN thmDBit (thmDVal b) 30 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := thmDLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_opaqueD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanThmDecl "validity"]
theorem scanThmD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_thm" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [thmDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_thmD]
  simp only [callFn, scanThmD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, thmDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (thmDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl (n + 1) s₀)] <;> finish




attribute [local lang_grind] opaqueDBit opaqueDVal Mbr.err

omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem opaqueDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n opaqueDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN opaqueDBit (opaqueDVal b) 62 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := opaqueDLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_quotD hp_indD in
@[refines_part ConLeche.Frontend.scanOpaqueDecl "validity"]
theorem scanOpaqueD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_opaque" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [opaqueDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_opaqueD]
  simp only [callFn, scanOpaqueD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, opaqueDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (opaqueDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb (n + 1) s₀)] <;> finish




attribute [local lang_grind] quotDBit quotDVal Mbr.err

omit hpmw hpi hphn hpho hph hpml hpb hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem quotDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n quotDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN quotDBit (quotDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := quotDLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


omit hpmw hpi hphn hpho hph hpml hpb hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_indD in
@[refines_part ConLeche.Frontend.scanQuotDecl "validity"]
theorem scanQuotD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_quot" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [quotDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_quotD]
  simp only [callFn, scanQuotD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, quotDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (quotDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt (n + 1) s₀)] <;> finish




attribute [local lang_grind] indDBit indDVal Mbr.err

theorem indDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indDBit (indDVal b) 26 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := indDLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n,
        scanIndCtors_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_indCtor hp_indCtors n,
        scanIndRecs_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n,
        scanIndTypes_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpb hp_indType hp_indTypes n,
        scanNatList_spec p b hb ‹_› ‹_› ‹_› n] <;> finish


@[refines_part ConLeche.Frontend.scanIndDecl "validity"]
theorem scanIndD_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_ind_decl" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [indDN b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_indD]
  simp only [callFn, scanIndD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, indDN, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish


end specs

end L.Scan.Records
