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
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order

namespace L.Scan.Records

open L.Scan.Member
open L.Scan.Values

attribute [local lang_grind] boolEndN

/-! ## The record loops, generically

Every record loop is `objLoop mask disp` (`*Loop_eq`, by `rfl`; the L code is unchanged): the
members of an object, and a key dispatch `disp` whose arms are of four kinds (`armSlot`,
`armList`, `armBool`, `armOne f`). Each kind has one spec (`arm*_spec`), the dispatch one spec
by induction over its arms (`dispOf_spec`), and the loop one spec against `objN`
(`objLoop_spec`). A record loop's spec is `objLoop_spec` with its arms (one proof over all
eleven keys took 26 s, now each record takes well under a second). -/

/-- The arm of a key read by `slot_nat`. -/
def armSlot (B : Word) : Stmt :=
  (Stmt.ite (Cond.cmp Cmp.ne (Expr.bin BinOp.and (Expr.var 2) (Expr.const B)) (Expr.const 0))
      (Stmt.ret [Expr.const 0]) Stmt.skip).seq
    ((Stmt.call [7] "slot_nat" [Expr.var 4, Expr.var 6]).seq
      ((Stmt.ite (Cond.cmp Cmp.eq (Expr.var 7) (Expr.const 0)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
        (Stmt.set 2 (Expr.bin BinOp.or (Expr.var 2) (Expr.const B)))))

/-- The arm of a key read by a one-result scanner `f`. -/
def armOne (f : FnName) (B : Word) : Stmt :=
  (Stmt.ite (Cond.cmp Cmp.ne (Expr.bin BinOp.and (Expr.var 2) (Expr.const B)) (Expr.const 0))
      (Stmt.ret [Expr.const 0]) Stmt.skip).seq
    ((Stmt.call [7] f [Expr.var 6]).seq
      ((Stmt.ite (Cond.cmp Cmp.eq (Expr.var 7) (Expr.const 0)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
        ((Stmt.ite (Cond.cmp Cmp.ule (Expr.var 7) (Expr.var 4)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
          (Stmt.set 2 (Expr.bin BinOp.or (Expr.var 2) (Expr.const B))))))

/-- The arm of a key read by `scan_nat_list`. -/
def armList (B : Word) : Stmt :=
  (Stmt.ite (Cond.cmp Cmp.ne (Expr.bin BinOp.and (Expr.var 2) (Expr.const B)) (Expr.const 0))
      (Stmt.ret [Expr.const 0]) Stmt.skip).seq
    ((Stmt.call [7, 9] "scan_nat_list" [Expr.var 6]).seq
      ((Stmt.ite (Cond.cmp Cmp.eq (Expr.var 7) (Expr.const 0)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
        ((Stmt.ite (Cond.cmp Cmp.ule (Expr.var 7) (Expr.var 4)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
          (Stmt.set 2 (Expr.bin BinOp.or (Expr.var 2) (Expr.const B))))))

/-- The arm of a key read by `scan_bool`. -/
def armBool (B : Word) : Stmt :=
  (Stmt.ite (Cond.cmp Cmp.ne (Expr.bin BinOp.and (Expr.var 2) (Expr.const B)) (Expr.const 0))
      (Stmt.ret [Expr.const 0]) Stmt.skip).seq
    ((Stmt.call [8, 9, 7] "scan_bool" [Expr.var 6]).seq
      ((Stmt.ite (Cond.cmp Cmp.eq (Expr.var 8) (Expr.const 0)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
        ((Stmt.ite (Cond.cmp Cmp.ule (Expr.var 7) (Expr.var 4)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
          (Stmt.set 2 (Expr.bin BinOp.or (Expr.var 2) (Expr.const B))))))

/-- The record loop with closing mask `mask` and key dispatch `disp`. -/
def objLoop (mask : Word) (disp : Stmt) : Stmt :=
  Stmt.while (Cond.cmp Cmp.eq (Expr.const 0) (Expr.const 0))
    ((Stmt.call [3, 4, 1, 5, 6] "next_member" [Expr.var 0, Expr.var 1]).seq
      ((Stmt.ite (Cond.cmp Cmp.eq (Expr.var 3) (Expr.const 0)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
        ((Stmt.ite (Cond.cmp Cmp.eq (Expr.var 3) (Expr.const 1))
              ((Stmt.ite ((Cond.cmp Cmp.ne (Expr.var 1) (Expr.const 0)).and
                    (Cond.cmp Cmp.ne (Expr.var 2) (Expr.const 0))) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
                ((Stmt.ite (Cond.cmp Cmp.ne (Expr.bin BinOp.and (Expr.var 2) (Expr.const mask))
                      (Expr.const mask)) (Stmt.ret [Expr.const 0]) Stmt.skip).seq
                  (Stmt.ret [Expr.bin BinOp.add (Expr.var 4) (Expr.const 1)])))
              Stmt.skip).seq
          (disp.seq ((Stmt.set 0 (Expr.var 7)).seq (Stmt.set 1 (Expr.const 0)))))))

/-- The key dispatch: the arm of the first listed key equal to `k`, else `return 0`. -/
def dispOf : List (Word × Stmt) → Stmt
  | [] => Stmt.ret [Expr.const 0]
  | (k, a) :: l => Stmt.ite (Cond.cmp Cmp.eq (Expr.var 5) (Expr.const k)) a (dispOf l)

/-- A key is accepted: it is known (`B ≠ 0`), not seen, and its value moves past the key. -/
def ObjOk (seen B ks e : Word) : Prop := B ≠ 0 ∧ seen &&& B = 0 ∧ ks < e

/-- What an arm (and the dispatch) does from `s₁`: the value `e` and bit `B` of the key. -/
def ObjArmPost (e B : Word) (s₁ : St) (r : Sig) (s' : St) : Prop :=
  s'.mem = s₁.mem ∧ r ≠ .brk ∧
  (r = .normal → s'.loc 7 = e ∧ s'.loc 2 = (s₁.loc 2 ||| B) ∧ ObjOk (s₁.loc 2) B (s₁.loc 4) e) ∧
  (r ≠ .normal → r.retOr [0] = [0] ∧ ¬ ObjOk (s₁.loc 2) B (s₁.loc 4) e)


/-- The key dispatch `disp` reads the key's value with `val` and sets its bit `bit`. -/
def DispOK (p : Prog) (b : Array UInt8) (bit : Word → Word) (val : Word → Word → Word → Word)
    (disp : Stmt) : Prop :=
  ∀ (n : Nat) (s₁ : St),
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) disp
    ⦃fun r s' => ObjArmPost (val (s₁.loc 5) (s₁.loc 4) (s₁.loc 6)) (bit (s₁.loc 5)) s₁ r s'; ⊤⦄

/-- An arm `a` reads the value `e ks v` and sets the bit `B`. -/
def ArmOK (p : Prog) (b : Array UInt8) (a : Stmt) (e : Word → Word → Word) (B : Word) : Prop :=
  ∀ (n : Nat) (s₁ : St),
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) a
    ⦃fun r s' => ObjArmPost (e (s₁.loc 4) (s₁.loc 6)) B s₁ r s'; ⊤⦄

/-- Every arm of the list reads its key's value and sets its key's bit. -/
def ArmsOK (p : Prog) (b : Array UInt8) (bit : Word → Word) (val : Word → Word → Word → Word) :
    List (Word × Stmt) → Prop
  | [] => True
  | (k, a) :: l => ArmOK p b a (val k) (bit k) ∧ ArmsOK p b bit val l

/-- The key dispatch of `strNameLoop`. -/
def strNameDisp : Stmt := dispOf [(47, armSlot 1), (56, armOne "scan_string" 2)]

theorem strNameLoop_eq : strNameLoop = objLoop 3 strNameDisp := rfl

/-- The key dispatch of `numNameLoop`. -/
def numNameDisp : Stmt := dispOf [(16, armSlot 1), (47, armSlot 2)]

theorem numNameLoop_eq : numNameLoop = objLoop 3 numNameDisp := rfl

/-- The key dispatch of `appLoop`. -/
def appDisp : Stmt := dispOf [(3, armSlot 1), (13, armSlot 2)]

theorem appLoop_eq : appLoop = objLoop 3 appDisp := rfl

/-- The key dispatch of `binderLoop`. -/
def binderDisp : Stmt := dispOf [(5, armOne "scan_binder_info" 1), (6, armSlot 2), (34, armSlot 4), (61, armSlot 8)]

theorem binderLoop_eq : binderLoop = objLoop 15 binderDisp := rfl

/-- The key dispatch of `letELoop`. -/
def letEDisp : Stmt := dispOf [(6, armSlot 1), (34, armSlot 2), (37, armBool 4), (61, armSlot 8), (65, armSlot 16)]

theorem letELoop_eq : letELoop = objLoop 27 letEDisp := rfl

/-- The key dispatch of `constELoop`. -/
def constEDisp : Stmt := dispOf [(34, armSlot 1), (64, armList 2)]

theorem constELoop_eq : constELoop = objLoop 3 constEDisp := rfl

/-- The key dispatch of `projLoop`. -/
def projDisp : Stmt := dispOf [(17, armSlot 1), (58, armSlot 2), (62, armSlot 4)]

theorem projLoop_eq : projLoop = objLoop 7 projDisp := rfl

/-- The key dispatch of `ruleLoop`. -/
def ruleDisp : Stmt := dispOf [(10, armSlot 1), (36, armSlot 2), (52, armSlot 4)]

theorem ruleLoop_eq : ruleLoop = objLoop 7 ruleDisp := rfl

/-- The key dispatch of `indRecLoop`. -/
def indRecDisp : Stmt := dispOf [(1, armList 1), (26, armBool 2), (27, armBool 4), (31, armList 8), (34, armSlot 16), (40, armSlot 32), (41, armSlot 64), (42, armSlot 128), (44, armSlot 256), (53, armOne "scan_rules" 512), (61, armSlot 1024)]

theorem indRecLoop_eq : indRecLoop = objLoop 2046 indRecDisp := rfl

/-- The key dispatch of `indTypeLoop`. -/
def indTypeDisp : Stmt := dispOf [(1, armList 1), (11, armList 2), (24, armBool 4), (25, armBool 8), (26, armBool 16), (31, armList 32), (34, armSlot 64), (40, armSlot 128), (43, armSlot 256), (44, armSlot 512), (61, armSlot 1024)]

theorem indTypeLoop_eq : indTypeLoop = objLoop 2046 indTypeDisp := rfl

/-- The key dispatch of `indCtorLoop`. -/
def indCtorDisp : Stmt := dispOf [(8, armSlot 1), (22, armSlot 2), (26, armBool 4), (31, armList 8), (34, armSlot 16), (39, armSlot 32), (44, armSlot 64), (61, armSlot 128)]

theorem indCtorLoop_eq : indCtorLoop = objLoop 252 indCtorDisp := rfl

/-- The key dispatch of `axiomDLoop`. -/
def axiomDDisp : Stmt := dispOf [(26, armBool 1), (31, armList 2), (34, armSlot 4), (61, armSlot 8)]

theorem axiomDLoop_eq : axiomDLoop = objLoop 15 axiomDDisp := rfl

/-- The key dispatch of `defDLoop`. -/
def defDDisp : Stmt := dispOf [(1, armList 1), (15, armOne "scan_hints" 2), (31, armList 4), (34, armSlot 8), (54, armOne "scan_string" 16), (61, armSlot 32), (65, armSlot 64)]

theorem defDLoop_eq : defDLoop = objLoop 124 defDDisp := rfl

/-- The key dispatch of `thmDLoop`. -/
def thmDDisp : Stmt := dispOf [(1, armList 1), (31, armList 2), (34, armSlot 4), (61, armSlot 8), (65, armSlot 16)]

theorem thmDLoop_eq : thmDLoop = objLoop 30 thmDDisp := rfl

/-- The key dispatch of `opaqueDLoop`. -/
def opaqueDDisp : Stmt := dispOf [(1, armList 1), (26, armBool 2), (31, armList 4), (34, armSlot 8), (61, armSlot 16), (65, armSlot 32)]

theorem opaqueDLoop_eq : opaqueDLoop = objLoop 62 opaqueDDisp := rfl

/-- The key dispatch of `quotDLoop`. -/
def quotDDisp : Stmt := dispOf [(28, armOne "scan_string" 1), (31, armList 2), (34, armSlot 4), (61, armSlot 8)]

theorem quotDLoop_eq : quotDLoop = objLoop 15 quotDDisp := rfl

/-- The key dispatch of `indDLoop`. -/
def indDDisp : Stmt := dispOf [(1, armList 1), (11, armOne "scan_ind_ctors" 2), (26, armBool 4), (50, armOne "scan_ind_recs" 8), (63, armOne "scan_ind_types" 16)]

theorem indDLoop_eq : indDLoop = objLoop 26 indDDisp := rfl

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

theorem armSlot_spec (B : Word) (hB : B ≠ 0) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) (armSlot B)
    ⦃fun r s' => ObjArmPost (slotNatN b (s₁.loc 4) (s₁.loc 6)) B s₁ r s'; ⊤⦄ := by
  dsimp only [armSlot]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      slotNat_spec p b hb ‹_› ‹_› ‹_› n]
  all_goals clear hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, beq_iff_eq, bne_iff_ne, ne_eq,
      Nat.reduceEqDiff, reduceIte] at *
  all_goals grind [lang_grind, ObjArmPost, ObjOk]


theorem armOne_spec (f : FnName) (fN : Word → Word)
    (hf : ∀ (n : Nat) (s₀ : St), s₀.mem.arr8 IN = b → ∀ i : Word,
      ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i] ⦃fun r s' => s' = s₀ ∧ r = [fN i]; ⊤⦄)
    (B : Word) (hB : B ≠ 0) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) (armOne f B)
    ⦃fun r s' => ObjArmPost (fN (s₁.loc 6)) B s₁ r s'; ⊤⦄ := by
  dsimp only [armOne]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs, hf n]
  all_goals clear hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, beq_iff_eq, bne_iff_ne, ne_eq,
      Nat.reduceEqDiff, reduceIte] at *
  all_goals grind [lang_grind, ObjArmPost, ObjOk]

theorem armList_spec (B : Word) (hB : B ≠ 0) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) (armList B)
    ⦃fun r s' => ObjArmPost (natListEntryN b (s₁.loc 6)).1 B s₁ r s'; ⊤⦄ := by
  dsimp only [armList]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      scanNatList_spec p b hb ‹_› ‹_› ‹_› n]
  all_goals clear hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, beq_iff_eq, bne_iff_ne, ne_eq,
      Nat.reduceEqDiff, reduceIte] at *
  all_goals grind [lang_grind, ObjArmPost, ObjOk]

theorem armBool_spec (B : Word) (hB : B ≠ 0) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) (armBool B)
    ⦃fun r s' => ObjArmPost (boolEndN b (s₁.loc 6)) B s₁ r s'; ⊤⦄ := by
  have hb64 : b.size < 2 ^ 64 := by omega
  dsimp only [armBool]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      L.Scan.Lit.scanBool_spec p ‹_› ‹_› b hb64 n]
  all_goals clear hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      Cmp.eval, BinOp.eval, beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind [lang_grind, ObjArmPost, ObjOk, boolEndN]

theorem objLoop_spec (bit : Word → Word) (val : Word → Word → Word → Word) (mask : Word)
    (disp : Stmt) (hd : DispOK p b bit val disp) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n (objLoop mask disp)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN bit val mask b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := objLoop mask disp) rfl]
    vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs, ih, hd n,
      nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n]
    all_goals clear hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD
    all_goals subst_vars
    all_goals try rfl
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, beq_iff_eq, bne_iff_ne, ne_eq,
        Nat.reduceEqDiff, reduceIte] at *
    all_goals grind [lang_grind, ObjArmPost, ObjOk]


theorem dispOf_spec (bit : Word → Word) (val : Word → Word → Word → Word) (l : List (Word × Stmt))
    (hl : ArmsOK p b bit val l) (n : Nat) (s₁ : St)
    (hz : s₁.loc 5 ∉ l.map Prod.fst → bit (s₁.loc 5) = 0) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 6).toNat ≤ b.size⦄
    step p (exec p n) (dispOf l)
    ⦃fun r s' => ObjArmPost (val (s₁.loc 5) (s₁.loc 4) (s₁.loc 6)) (bit (s₁.loc 5)) s₁ r s'; ⊤⦄ := by
  induction l with
  | nil =>
    simp only [dispOf]
    have hz := hz (by simp)
    vcgen [step, L.evalE_spec, evalArgs]
    all_goals grind [lang_grind, ObjArmPost, ObjOk, Expr.pval]
  | cons ka l ih =>
    obtain ⟨k, a⟩ := ka
    obtain ⟨ha, hl⟩ := hl
    by_cases hk : s₁.loc 5 = k
    · subst hk
      simp only [dispOf]
      vcgen [step, L.evalC_spec, ha n]
      all_goals grind [Cond.pval, Expr.pval, Cmp.eval]
    · have ih := ih hl (fun h => hz (by simp_all))
      simp only [dispOf]
      vcgen [step, L.evalC_spec, ih, ha n]
      all_goals grind [Cond.pval, Expr.pval, Cmp.eval]

theorem dispOf_ok (bit : Word → Word) (val : Word → Word → Word → Word) (l : List (Word × Stmt))
    (hl : ArmsOK p b bit val l) (hz : ∀ k, k ∉ l.map Prod.fst → bit k = 0) :
    DispOK p b bit val (dispOf l) :=
  fun n s₁ => dispOf_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD bit val l hl n s₁ (hz _)


theorem armSlot_ok (B B' : Word) (hB : B' = B ∧ B ≠ 0) (e : Word → Word → Word)
    (he : ∀ ks v, e ks v = slotNatN b ks v) : ArmOK p b (armSlot B) e B' := by
  intro n s₁
  obtain ⟨rfl, hB⟩ := hB
  rw [he]
  exact armSlot_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD B' hB n s₁

theorem armList_ok (B B' : Word) (hB : B' = B ∧ B ≠ 0) (e : Word → Word → Word)
    (he : ∀ ks v, e ks v = (natListEntryN b v).1) : ArmOK p b (armList B) e B' := by
  intro n s₁
  obtain ⟨rfl, hB⟩ := hB
  rw [he]
  exact armList_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD B' hB n s₁

theorem armBool_ok (B B' : Word) (hB : B' = B ∧ B ≠ 0) (e : Word → Word → Word)
    (he : ∀ ks v, e ks v = boolEndN b v) : ArmOK p b (armBool B) e B' := by
  intro n s₁
  obtain ⟨rfl, hB⟩ := hB
  rw [he]
  exact armBool_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD B' hB n s₁

theorem armOne_ok (f : FnName) (fN : Word → Word)
    (hf : ∀ (n : Nat) (s₀ : St), s₀.mem.arr8 IN = b → ∀ i : Word,
      ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i] ⦃fun r s' => s' = s₀ ∧ r = [fN i]; ⊤⦄)
    (B B' : Word) (hB : B' = B ∧ B ≠ 0) (e : Word → Word → Word)
    (he : ∀ ks v, e ks v = fN v) : ArmOK p b (armOne f B) e B' := by
  intro n s₁
  obtain ⟨rfl, hB⟩ := hB
  rw [he]
  exact armOne_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD f fN hf B' hB n s₁



attribute [local lang_grind] strNameBit strNameVal Mbr.err

theorem strNameLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n strNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN strNameBit (strNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [strNameLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [strNameVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [strNameVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [strNameBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (strNameLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] numNameBit numNameVal Mbr.err

theorem numNameLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n numNameLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN numNameBit (numNameVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [numNameLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [numNameVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [numNameVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [numNameBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (numNameLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] appBit appVal Mbr.err

theorem appLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n appLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN appBit (appVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [appLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [appVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [appVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [appBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (appLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] binderBit binderVal Mbr.err

theorem binderLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n binderLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN binderBit (binderVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [binderLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (scanBinderInfo_spec p b hb ‹_› ‹_›) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [binderVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [binderVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [binderVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [binderVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [binderBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (binderLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] letEBit letEVal Mbr.err

theorem letELoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n letELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN letEBit (letEVal b) 27 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [letELoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [letEVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [letEVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [letEVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [letEVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [letEVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [letEBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (letELoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] constEBit constEVal Mbr.err

theorem constELoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n constELoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN constEBit (constEVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [constELoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [constEVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [constEVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [constEBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (constELoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] projBit projVal Mbr.err

theorem projLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n projLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN projBit (projVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [projLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [projVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [projVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [projVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [projBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (projLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] ruleBit ruleVal Mbr.err

theorem ruleLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n ruleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN ruleBit (ruleVal b) 7 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [ruleLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [ruleVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [ruleVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [ruleVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [ruleBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (ruleLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

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
        scanRule_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (rulesLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] indRecBit indRecVal Mbr.err

theorem indRecLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indRecBit (indRecVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [indRecLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (scanRules_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indRecVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [indRecBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indRecLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




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

theorem indTypeLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indTypeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indTypeBit (indTypeVal b) 2046 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [indTypeLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indTypeVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [indTypeBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indTypeLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

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
        scanIndType_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indTypesLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] indCtorBit indCtorVal Mbr.err

theorem indCtorLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indCtorLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indCtorBit (indCtorVal b) 252 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [indCtorLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indCtorVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [indCtorBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indCtorLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] Mbr.err

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
        scanIndCtor_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD n] <;> finish


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (indCtorsLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] axiomDBit axiomDVal Mbr.err

theorem axiomDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n axiomDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN axiomDBit (axiomDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [axiomDLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [axiomDVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [axiomDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [axiomDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [axiomDVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [axiomDBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (axiomDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] defDBit defDVal Mbr.err

theorem defDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n defDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN defDBit (defDVal b) 124 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [defDLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (scanHints_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [defDVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [defDBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (defDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] thmDBit thmDVal Mbr.err

theorem thmDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n thmDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN thmDBit (thmDVal b) 30 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [thmDLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [thmDVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [thmDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [thmDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [thmDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [thmDVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [thmDBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (thmDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] opaqueDBit opaqueDVal Mbr.err

theorem opaqueDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n opaqueDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN opaqueDBit (opaqueDVal b) 62 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [opaqueDLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [opaqueDVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [opaqueDVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [opaqueDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [opaqueDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [opaqueDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [opaqueDVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [opaqueDBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (opaqueDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] quotDBit quotDVal Mbr.err

theorem quotDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n quotDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN quotDBit (quotDVal b) 15 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [quotDLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [quotDVal]),
      armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [quotDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [quotDVal]),
      armSlot_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [quotDVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [quotDBit, hk]


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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, fun s₀ => Triple.step_exec (quotDLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD (n + 1) s₀)] <;> finish




attribute [local lang_grind] indDBit indDVal Mbr.err

theorem indDLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n indDLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN indDBit (indDVal b) 26 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  rw [indDLoop_eq]
  refine objLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ _ (dispOf_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ _ ?_ ?_) n s₀
  · exact ⟨armList_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indDVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (scanIndCtors_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indDVal]),
      armBool_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indDVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (scanIndRecs_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indDVal]),
      armOne_ok p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD _ _ (scanIndTypes_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hphn hpho hph hpl hpml hpb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_strName hp_numName hp_app hp_binder hp_letE hp_constE hp_proj hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD) _ _ ⟨by decide, by decide⟩ _ (fun _ _ => by simp [indDVal]),
      trivial⟩
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or] at hk
    simp [indDBit, hk]


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
