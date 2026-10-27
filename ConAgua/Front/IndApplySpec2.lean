import ConAgua.Front.IndApplySpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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

/-- **The model of `ind_cv(q, nm, lps, ty)`.** -/
def cvW (b : Array UInt8) (m : Mem) (q nm lps ty : Word) : Option Mem :=
  wK (fun nh => wK (fun th => mK (fun m₁ =>
      some (cvM m₁ q nh (rdW (m.arr64 DLP) 0) (lsCntN b (lps + 1) 0) th)) (lpPutW b m lps))
    (lkW m EID ty)) (lkW m NID nm)

/-- **The model of `ind_caps(q)`**: the fifteen words. -/
def capsM (m : Mem) (q : Word) : Mem :=
  (((((((((((((((m.set64 DLP q 0).set64 DLP (q + 1) 0).set64 DLP (q + 2) 0).set64 DLP (q + 3) 0)
    |>.set64 DLP (q + 4) 0).set64 DLP (q + 5) 0).set64 DLP (q + 6) 0).set64 DLP (q + 7) 1)
    |>.set64 DLP (q + 8) 0).set64 DLP (q + 9) 0).set64 DLP (q + 10) 0).set64 DLP (q + 11) 0)
    |>.set64 DLP (q + 12) 0).set64 DLP (q + 13) 0).set64 DLP (q + 14) 0)

/-- The eleven words of a rule at `q`. -/
def ruleM (m : Mem) (q n nf e : Word) : Mem :=
  ((((((((((((m.set64 DLP q n).set64 DLP (q + 1) nf).set64 DLP (q + 2) 0).set64 DLP (q + 3) 0)
    |>.set64 DLP (q + 4) 0).set64 DLP (q + 5) 0).set64 DLP (q + 6) 0).set64 DLP (q + 7) 0)
    |>.set64 DLP (q + 8) e).set64 DLP (q + 9) 0).set64 DLP (q + 10) 0))

/-- **The model of `parse_rule_d(q, rp)`.** -/
def ruleW (m : Mem) (q rp : Word) : Option Mem :=
  wK (fun nh => wK (fun eh => some (ruleM m q nh (rdW (m.arr64 IFL) (rp + 1)) eh))
    (lkW m EID (rdW (m.arr64 IFL) (rp + 2)))) (lkW m NID (rdW (m.arr64 IFL) rp))

/-- **The model of `ind_rules_go(lo, o, l, j)`.** -/
def rulesGoW : Nat → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _ => none
  | n + 1, m, lo, o, l, j =>
    if l ≤ j then some m
    else mK (fun m₁ => rulesGoW n m₁ lo o l (j + 1)) (ruleW m (lo + 11 * j) (o + 3 * j))

/-- **The model of `ind_rules(o, l)`**: the slice `(lo, l)`. -/
def rulesW : Nat → Mem → Word → Word → Option ((Word × Word) × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if 4294967296 ≤ l then none
    else allocK (fun lo m₁ => sliceK lo l (rulesGoW n m₁ lo o l 0)) (allocW m DLP (11 * l))

/-- **The model of `ind_type(t)`**: the record's pointer. -/
def typeW (b : Array UInt8) (m : Mem) (t : Word) : Option (Word × Mem) :=
  allocK (fun q m₁ => mK (fun m₂ => some (q, capsM m₂ (q + 5)))
      (cvW b (m₁.set64 DLP q 3) (q + 1) (rdW (m₁.arr64 IFR) t) (rdW (m₁.arr64 IFR) (t + 1))
        (rdW (m₁.arr64 IFR) (t + 2))))
    (allocW m DLP 20)

/-- **The model of `ind_ctor(c)`**: the record's pointer. -/
def ctorRW (b : Array UInt8) (m : Mem) (c : Word) : Option (Word × Mem) :=
  allocK (fun q m₁ => mK (fun m₂ =>
      some (q, (m₂.set64 DLP (q + 5) (rdW (m₂.arr64 IFR) (c + 5))).set64 DLP (q + 6)
        (rdW (m₂.arr64 IFR) (c + 4))))
      (cvW b (m₁.set64 DLP q 4) (q + 1) (rdW (m₁.arr64 IFR) c) (rdW (m₁.arr64 IFR) (c + 1))
        (rdW (m₁.arr64 IFR) (c + 2))))
    (allocW m DLP 7)

/-- The last four words of a `recInfo` record at `q`. -/
def recTailM (m : Mem) (q r lo ln : Word) : Mem :=
  (((m.set64 DLP (q + 5) (rdW (m.arr64 IFR) (r + 8) + rdW (m.arr64 IFR) (r + 7) +
      rdW (m.arr64 IFR) (r + 6) + rdW (m.arr64 IFR) (r + 5))).set64 DLP (q + 6)
      (rdW (m.arr64 IFR) (r + 8) + rdW (m.arr64 IFR) (r + 7) + rdW (m.arr64 IFR) (r + 6))).set64
    DLP (q + 7) lo).set64 DLP (q + 8) ln

/-- **The model of `ind_rec(r)`**: the record's pointer. -/
def recRW : Nat → Array UInt8 → Mem → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, b, m, r =>
    allocK (fun q m₁ => pmK (fun lo ln m₃ => mK (fun m₄ => some (q, recTailM m₄ q r lo ln))
        (cvW b m₃ (q + 1) (rdW (m₃.arr64 IFR) r) (rdW (m₃.arr64 IFR) (r + 1)) (rdW (m₃.arr64 IFR) (r + 2))))
      (rulesW n (m₁.set64 DLP q 5) (rdW (m₁.arr64 IFR) (r + 9)) (rdW (m₁.arr64 IFR) (r + 10))))
    (allocW m DLP 9)

/-- **The model of `inst_types(bo, to, tn, j)`.** -/
def instTypesW : Nat → Array UInt8 → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _ => none
  | n + 1, b, m, bo, to, tn, j =>
    if tn ≤ j then some m
    else allocK (fun q m₁ => instTypesW n b (m₁.set64 DLP (bo + j) q) bo to tn (j + 1))
      (typeW b m (to + 11 * j))

/-- **The model of `inst_ctors(bo, oo, on, j)`.** -/
def instCtorsW : Nat → Array UInt8 → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _ => none
  | n + 1, b, m, bo, oo, on, j =>
    if on ≤ j then some m
    else allocK (fun q m₁ => instCtorsW n b (m₁.set64 DLP (bo + j) q) bo oo on (j + 1))
      (ctorRW b m (rdW (m.arr64 IFL) (oo + j)))

/-- **The model of `inst_recs(bo, ro, rn, j)`.** -/
def instRecsW : Nat → Array UInt8 → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _ => none
  | n + 1, b, m, bo, ro, rn, j =>
    if rn ≤ j then some m
    else allocK (fun q m₁ => instRecsW n b (m₁.set64 DLP (bo + j) q) bo ro rn (j + 1))
      (recRW n b m (ro + 11 * j))

/-- **The model of `install_ind_d(to, tn, oo, on, ro, rn, np)`.** -/
def installW : Nat → Array UInt8 → Mem → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, b, m, to, tn, oo, on, ro, rn, np =>
    if 4294967296 ≤ tn ∨ 4294967296 ≤ on ∨ 4294967296 ≤ rn then none
    else allocK (fun bo m₁ => mK (fun m₂ => mK (fun m₃ => mK (fun m₄ =>
          pushW m₄ 6 0 bo (tn + on + rn) np 0 0 0)
        (instRecsW n b m₃ (bo + tn + on) ro rn 0)) (instCtorsW n b m₂ (bo + tn) oo on 0))
        (instTypesW n b m₁ bo to tn 0))
      (allocW m DLP (tn + on + rn))

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

include hb in
theorem cv_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (q nm lps ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_cv" [q, nm, lps, ty]
    ⦃fun _ s' => LocEq s' s₀ ∧ cvW b s₀.mem q nm lps ty = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hI.ind_cv]
  simp only [callFn, indCv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        nameGet_spec p hL.decl.expr.front n, exprGet_spec p hL.decl.expr n,
        lpPut_spec p hL.decl b hb n] <;> finish [cvW, cvM, lkW]

omit hL in
theorem caps_spec (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_caps" [q]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = capsM s₀.mem q; ⊤⦄ := by
  rw [invoke_eq _ hI.ind_caps]
  simp only [callFn, indCaps]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, st64] <;> finish [capsM]

theorem rule_spec (n : Nat) (s₀ : St) (q rp : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "parse_rule_d" [q, rp]
    ⦃fun _ s' => LocEq s' s₀ ∧ ruleW s₀.mem q rp = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hI.parse_rule_d]
  simp only [callFn, parseRuleD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        nameGet_spec p hL.decl.expr.front n, exprGet_spec p hL.decl.expr n] <;>
        finish [ruleW, ruleM, lkW]

theorem rulesGo_spec (n : Nat) : ∀ (s₀ : St) (lo o l j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_rules_go" [lo, o, l, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rulesGoW n s₀.mem lo o l j = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ lo o l j; rw [invoke_eq _ hI.ind_rules_go]; simp only [callFn, indRulesGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ lo o l j
    rw [invoke_eq _ hI.ind_rules_go]
    simp only [callFn, indRulesGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih, rule_spec p hL hI n] <;>
        finish [rulesGoW]

theorem rules_spec (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_rules" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ rulesW n s₀.mem o l = some ((r.headD 0, r.tail.headD 0), s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hI.ind_rules]
  simp only [callFn, indRules]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, dindAlloc_spec p hI n,
        rulesGo_spec p hL hI n] <;> finish [rulesW]

include hb in
theorem type_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_type" [t]
    ⦃fun r s' => LocEq s' s₀ ∧ typeW b s₀.mem t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hI.ind_type]
  simp only [callFn, indType]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have ha : ∀ (s₁ : St) (k : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "dind_alloc" [k]
        ⦃fun r s' => (LocEq s' s₁ ∧ allocW s₁.mem DLP k = some (r.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ k => Triple.keep hL.decl.expr.no_st8 (dindAlloc_spec p hI n s₁ k)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ha, cv_spec p hL hI b hb n, caps_spec p hI n] <;> finish [typeW]

include hb in
theorem ctorR_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_ctor" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ ctorRW b s₀.mem c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hI.ind_ctor]
  simp only [callFn, indCtor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have ha : ∀ (s₁ : St) (k : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "dind_alloc" [k]
        ⦃fun r s' => (LocEq s' s₁ ∧ allocW s₁.mem DLP k = some (r.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ k => Triple.keep hL.decl.expr.no_st8 (dindAlloc_spec p hI n s₁ k)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ha, cv_spec p hL hI b hb n] <;> finish [ctorRW]

include hb in
theorem recR_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_rec" [r]
    ⦃fun res s' => LocEq s' s₀ ∧ recRW n b s₀.mem r = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hI.ind_rec]
  simp only [callFn, indRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hr : ∀ (s₁ : St) (o l : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "ind_rules" [o, l]
        ⦃fun r s' => (LocEq s' s₁ ∧ rulesW n s₁.mem o l = some ((r.headD 0, r.tail.headD 0), s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ o l => Triple.keep hL.decl.expr.no_st8 (rules_spec p hL hI n s₁ o l)
    have ha : ∀ (s₁ : St) (k : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "dind_alloc" [k]
        ⦃fun r s' => (LocEq s' s₁ ∧ allocW s₁.mem DLP k = some (r.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ k => Triple.keep hL.decl.expr.no_st8 (dindAlloc_spec p hI n s₁ k)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ha, hr, cv_spec p hL hI b hb n] <;>
        finish [recRW, recTailM]

include hb in
theorem instTypes_spec (n : Nat) : ∀ (s₀ : St), s₀.mem.arr8 IN = b → ∀ (bo to tn j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_types" [bo, to, tn, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ instTypesW n b s₀.mem bo to tn j = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ hm bo to tn j; rw [invoke_eq _ hI.inst_types]; simp only [callFn, instTypes]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hm bo to tn j
    have ht : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (t : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "ind_type" [t]
        ⦃fun r s' => (LocEq s' s₁ ∧ typeW b s₁.mem t = some (r.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ t => Triple.keep hL.decl.expr.no_st8 (type_spec p hL hI b hb n s₁ hm₁ t)
    rw [invoke_eq _ hI.inst_types]
    simp only [callFn, instTypes]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, ht] <;>
        finish [instTypesW]

include hb in
theorem instCtors_spec (n : Nat) : ∀ (s₀ : St), s₀.mem.arr8 IN = b → ∀ (bo oo on j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_ctors" [bo, oo, on, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ instCtorsW n b s₀.mem bo oo on j = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ hm bo oo on j; rw [invoke_eq _ hI.inst_ctors]; simp only [callFn, instCtors]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hm bo oo on j
    have ht : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (c : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "ind_ctor" [c]
        ⦃fun r s' => (LocEq s' s₁ ∧ ctorRW b s₁.mem c = some (r.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ c => Triple.keep hL.decl.expr.no_st8 (ctorR_spec p hL hI b hb n s₁ hm₁ c)
    rw [invoke_eq _ hI.inst_ctors]
    simp only [callFn, instCtors]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, ht] <;>
        finish [instCtorsW]

include hb in
theorem instRecs_spec (n : Nat) : ∀ (s₀ : St), s₀.mem.arr8 IN = b → ∀ (bo ro rn j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_recs" [bo, ro, rn, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ instRecsW n b s₀.mem bo ro rn j = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ hm bo ro rn j; rw [invoke_eq _ hI.inst_recs]; simp only [callFn, instRecs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hm bo ro rn j
    have ht : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (r : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "ind_rec" [r]
        ⦃fun res s' => (LocEq s' s₁ ∧ recRW n b s₁.mem r = some (res.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ r => Triple.keep hL.decl.expr.no_st8 (recR_spec p hL hI b hb n s₁ hm₁ r)
    rw [invoke_eq _ hI.inst_recs]
    simp only [callFn, instRecs]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, ht] <;>
        finish [instRecsW]

include hb in
theorem install_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (to tn oo on ro rn np : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_ind_d" [to, tn, oo, on, ro, rn, np]
    ⦃fun _ s' => LocEq s' s₀ ∧ installW n b s₀.mem to tn oo on ro rn np = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hI.install_ind_d]
  simp only [callFn, installIndD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hno := hL.decl.expr.no_st8
    have ha : ∀ (s₁ : St) (k : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "dind_alloc" [k]
        ⦃fun r s' => (LocEq s' s₁ ∧ allocW s₁.mem DLP k = some (r.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ k => Triple.keep hno (dindAlloc_spec p hI n s₁ k)
    have h1 : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (bo to tn j : Word),
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "inst_types" [bo, to, tn, j]
        ⦃fun _ s' => (LocEq s' s₁ ∧ instTypesW n b s₁.mem bo to tn j = some s'.mem) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ bo to tn j => Triple.keep hno (instTypes_spec p hL hI b hb n s₁ hm₁ bo to tn j)
    have h2 : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (bo oo on j : Word),
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "inst_ctors" [bo, oo, on, j]
        ⦃fun _ s' => (LocEq s' s₁ ∧ instCtorsW n b s₁.mem bo oo on j = some s'.mem) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ bo oo on j => Triple.keep hno (instCtors_spec p hL hI b hb n s₁ hm₁ bo oo on j)
    have h3 : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ (bo ro rn j : Word),
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "inst_recs" [bo, ro, rn, j]
        ⦃fun _ s' => (LocEq s' s₁ ∧ instRecsW n b s₁.mem bo ro rn j = some s'.mem) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ :=
      fun s₁ hm₁ bo ro rn j => Triple.keep hno (instRecs_spec p hL hI b hb n s₁ hm₁ bo ro rn j)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ha, h1, h2, h3,
        declPush_spec p hL.decl n] <;> finish (gen := 20) [installW]

end specs

end L.Front.Ind
