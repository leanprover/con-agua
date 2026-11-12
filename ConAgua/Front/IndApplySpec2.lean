module

public import ConAgua.Front.IndApplySpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.L.ModelGen
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The apply step of an `inductive` line: word models and specs, II (`installIndD`'s side)

The models of the install functions (`IndApply.lean`): the constant records are allocated in
`DLP`'s pool (`allocW m DLP`, `dind_alloc` is `ifl_alloc`'s code on `DIND = DLP`), a constant's
universe parameters by `lp_put` (`lpPutW`), the block pushed by `decl_push` (`pushW`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena

namespace L.Front.Ind

/-- Every install function, at its name in `p`. -/
structure IndInstallLookups (p : Prog) : Prop where
  dind_alloc : p.lookup "dind_alloc" = some dindAlloc
  ind_cv : p.lookup "ind_cv" = some indCv
  ind_caps : p.lookup "ind_caps" = some indCaps
  parse_rule_d : p.lookup "parse_rule_d" = some parseRuleD
  ind_rules_go : p.lookup "ind_rules_go" = some indRulesGo
  ind_rules : p.lookup "ind_rules" = some indRules
  ind_type : p.lookup "ind_type" = some indType
  ind_ctor : p.lookup "ind_ctor" = some indCtor
  ind_rec : p.lookup "ind_rec" = some indRec
  inst_types : p.lookup "inst_types" = some instTypes
  inst_ctors : p.lookup "inst_ctors" = some instCtors
  inst_recs : p.lookup "inst_recs" = some instRecs
  install_ind_d : p.lookup "install_ind_d" = some installIndD

/-! ## Models -/

/-- The constant value's four words at `q`. -/
def cvM (m : Mem) (q n o l t : Word) : Mem :=
  (((m.set64 DLP q n).set64 DLP (q + 1) (o + 1)).set64 DLP (q + 2) l).set64 DLP (q + 3) t

/-- **The model of `ind_caps(q)`**: the ten words the capabilities' decoder reads. -/
def capsM (m : Mem) (q : Word) : Mem :=
  (((((((((m.set64 DLP q 0).set64 DLP (q + 6) 0).set64 DLP (q + 7) 0).set64 DLP (q + 8) 0).set64 DLP (q + 9) 0).set64 DLP (q + 10) 0).set64 DLP (q + 11) 0).set64 DLP (q + 12) 0).set64 DLP (q + 13) 0).set64 DLP (q + 14) 0

/-- The eleven words of a rule at `q`. -/
def ruleM (m : Mem) (q n nf e : Word) : Mem :=
  ((((((((((((m.set64 DLP q n).set64 DLP (q + 1) nf).set64 DLP (q + 2) 0).set64 DLP (q + 3) 0)
    |>.set64 DLP (q + 4) 0).set64 DLP (q + 5) 0).set64 DLP (q + 6) 0).set64 DLP (q + 7) 0)
    |>.set64 DLP (q + 8) e).set64 DLP (q + 9) 0).set64 DLP (q + 10) 0))

/-- The last four words of a `recInfo` record at `q`. -/
def recTailM (m : Mem) (q r lo ln : Word) : Mem :=
  ((((m.set64 DLP (q + 5) (rdW (m.arr64 IFR) (r + 8) + rdW (m.arr64 IFR) (r + 7) +
      rdW (m.arr64 IFR) (r + 6) + rdW (m.arr64 IFR) (r + 5))).set64 DLP (q + 6)
      (rdW (m.arr64 IFR) (r + 8) + rdW (m.arr64 IFR) (r + 7) + rdW (m.arr64 IFR) (r + 6))).set64
    DLP (q + 7) lo).set64 DLP (q + 8) ln).set64 DLP (q + 9) (rdW (m.arr64 IFR) (r + 4))

/-! ## Specs -/

section specs
variable (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
  (hb : b.size < 2 ^ 63)
include hL hI

omit hL in
theorem dindAlloc_spec (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "dind_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ allocW s₀.mem DLP k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hI.dind_alloc]
  simp only [callFn, dindAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;> finish [allocW]

end specs

/-! ## Generated models -/

/-- **The model of `ind_cv(q, nm, lps, ty)`** (`cvM`). -/
l_model cv_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.ind_cv ↦ cvW void]
  specs [nameGet_spec p hL.decl.expr.front n, exprGet_spec p hL.decl.expr n,
    lpPut_spec p hL.decl b hb n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind] guards ["name_get", "expr_get"]

/-- **The model of `parse_rule_d(q, rp)`** (`ruleM`). -/
l_model rule_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p)
  fns [hI.parse_rule_d ↦ ruleW void]
  specs [nameGet_spec p hL.decl.expr.front n, exprGet_spec p hL.decl.expr n]
  grind [arena_grind] guards ["name_get", "expr_get"]

/-- `cvW` in the users' shape: the two lookups, `lp_put`, the four words (`cvM`). -/
theorem cvW_eq (b : Array UInt8) (m : Mem) (q nm lps ty : Word) : cvW b m q nm lps ty =
    wK (fun nh => wK (fun th => mK (fun m₁ =>
      some (cvM m₁ q nh (rdW (m.arr64 DLP) 0) (lsCntN b (lps + 1) 0) th)) (lpPutW b m lps))
      (lkW m EID ty)) (lkW m NID nm) := by
  unfold cvW; simp only [lkW]
  split <;> (try split) <;> simp_all [wK] <;> cases lpPutW b m lps <;> rfl

/-- `ruleW` in the users' shape: the two lookups, the eleven words (`ruleM`). -/
theorem ruleW_eq (m : Mem) (q rp : Word) : ruleW m q rp =
    wK (fun nh => wK (fun eh => some (ruleM m q nh (rdW (m.arr64 IFL) (rp + 1)) eh))
      (lkW m EID (rdW (m.arr64 IFL) (rp + 2)))) (lkW m NID (rdW (m.arr64 IFL) rp)) := by
  unfold ruleW; simp only [lkW]
  split <;> (try split) <;> simp_all [wK] <;> rfl

/-- **The model of `ind_caps(q)`**: the fifteen words (`capsM`). -/
l_model caps_spec (p : Prog) (hI : IndInstallLookups p)
  fns [hI.ind_caps ↦ capsW void]
  grind [arena_grind]

/-- `capsW` by its memory `capsM`. -/
theorem capsW_eq (m : Mem) (q : Word) : capsW m q = some (capsM m q) := rfl

/-- **The model of `ind_rules_go(lo, o, l, j)`.** -/
l_model rulesGo_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p)
  fns [hI.ind_rules_go ↦ rulesGoW void]
  specs [rule_spec p hL hI n]
  grind [arena_grind]

theorem rulesGoW.k_ind_rules_go_id (x : Option Mem) : rulesGoW.k_ind_rules_go x = x := by cases x <;> rfl

/-- **The model of `ind_rules(o, l)`**: the slice `(lo, l)`. -/
l_model rules_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p)
  fns [hI.ind_rules ↦ rulesW tuple]
  specs [dindAlloc_spec p hI n, rulesGo_spec p hL hI n]
  grind [arena_grind]


/-- **The model of `ind_type(t)`**: the record's pointer. -/
l_model type_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.ind_type ↦ typeW]
  specs [dindAlloc_spec p hI n, cv_spec p hL hI b hb n, caps_spec p hI n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]

/-- **The model of `ind_ctor(c)`**: the record's pointer. -/
l_model ctorR_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.ind_ctor ↦ ctorRW]
  specs [dindAlloc_spec p hI n, cv_spec p hL hI b hb n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]

/-- **The model of `ind_rec(r)`**: the record's pointer. -/
l_model recR_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.ind_rec ↦ recRW]
  specs [dindAlloc_spec p hI n, rules_spec p hL hI n, cv_spec p hL hI b hb n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]


/-- **The model of `inst_types(bo, to, tn, j)`.** -/
l_model instTypes_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.inst_types ↦ instTypesW void]
  specs [type_spec p hL hI b hb n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]

theorem instTypesW.k_inst_types_id (b : Array UInt8) (x : Option Mem) : instTypesW.k_inst_types b x = x := by cases x <;> rfl

/-- **The model of `inst_ctors(bo, oo, on, j)`.** -/
l_model instCtors_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.inst_ctors ↦ instCtorsW void]
  specs [ctorR_spec p hL hI b hb n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]

theorem instCtorsW.k_inst_ctors_id (b : Array UInt8) (x : Option Mem) : instCtorsW.k_inst_ctors b x = x := by cases x <;> rfl

/-- **The model of `inst_recs(bo, ro, rn, j)`.** -/
l_model instRecs_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.inst_recs ↦ instRecsW void]
  specs [recR_spec p hL hI b hb n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]

theorem instRecsW.k_inst_recs_id (b : Array UInt8) (x : Option Mem) : instRecsW.k_inst_recs b x = x := by cases x <;> rfl

/-- **The model of `install_ind_d(to, tn, oo, on, ro, rn, np)`.** -/
l_model install_spec (p : Prog) (hL : IndApplyLookups p) (hI : IndInstallLookups p) (b : Array UInt8)
    (hb : b.size < 2 ^ 63)
  fns [hI.install_ind_d ↦ installW void]
  specs [dindAlloc_spec p hI n, instTypes_spec p hL hI b hb n, instCtors_spec p hL hI b hb n,
    instRecs_spec p hL hI b hb n, declPush_spec p hL.decl n]
  pre [s₀.mem.arr8 IN = b]
  keep [hL.decl.expr.no_st8]
  grind [arena_grind]

theorem installW.k_decl_push_id (b : Array UInt8) (x : Option Mem) : installW.k_decl_push b x = x := by
  cases x <;> rfl

end L.Front.Ind
