module

public import ConAgua.Arena.DeclHeader
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon
import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
import ConAgua.Arena.StoreFields

@[expose] public section

/-!
# Record equalities in L, word models and specs (lane `decls3`, helper `decls3-canon`)

`DeclArmsCanon.lean`'s `er_sl_eq`, `b_eq`, `cv_eq`, `hint_eq`, `pw_eq`, `caps_eq`,
`rule_eq_but_rhs`, `rules_eq`, `ci_eq`. Their word models are **total
`Bool` functions of the record pool's reader** `a : Word → Word` (at `erRdT m`: the tagged reads `EREC⦃·⦄`; the functions read only `EREC`, never write,
and a slice comparison recurses on its length, not on a fuel): `slEqN`, `erSlEqB`, `cvEqB`, …
`ciEqB`. Each spec says a returning call answers `if model then 1 else 0` and leaves the memory
alone; the relation to decoded records (`DeclCanonEq.lean`) is proved against the models.

`CanonProg p`: the lookups of every function the whole canonical-form chain reaches (the real master
functions, not the stubs of `armsMasterFns`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The functions of `CanonProg` (ronsync2: without the removed `pw_eq`, `env_ix`). -/
def canonProgFns : Prog :=
  [("er_sl_eq", L.Ind.erSlEq),
   ("b_eq", L.Ind.bEq),
   ("cv_eq", L.Ind.cvEq),
   ("hint_eq", L.Ind.hintEq),
   ("caps_eq", L.Ind.capsEq),
   ("rule_eq_but_rhs", L.Ind.ruleEqButRhs),
   ("rules_eq", L.Ind.rulesEq),
   ("ci_eq", L.Ind.ciEq),
   ("er_sl_at", L.Ind.erSlAt),
   ("caps_eq_a", L.Ind.capsEqA),
   ("caps_eq_b", L.Ind.capsEqB),
   ("caps_eq_c", L.Ind.capsEqC),
   ("rule_eq_a", L.Ind.ruleEqA),
   ("rule_eq_b", L.Ind.ruleEqB),
   ("ci_eq_rest", L.Ind.ciEqRest),
   ("canon_ctx", L.Ind.canonCtx),
   ("ci_canon_defn", L.Ind.ciCanonDefn),
   ("ci_canon_rec", L.Ind.ciCanonRec),
   ("env_find", envFindL),
   ("env_row_get", envRowGetL),
   ("ci_to_cv", L.Ind.ciToCv),
   ("intern_zero", internZero),
   ("zero_find", zeroFind),
   ("zero_push", zeroPush),
   ("intern_succ", internSucc),
   ("succ_find", succFind),
   ("succ_push", succPush),
   ("intern_sort", internSort),
   ("sort_find", sortFind),
   ("sort_push", sortPush),
   ("cv_new", cvNew),
   ("erec_alloc", erecAlloc),
   ("canon_names_go", L.Ind.canonNamesGo),
   ("canon_names", L.Ind.canonNames),
   ("intern_nanon", internNAnon),
   ("nanon_find", nanonFind),
   ("nanon_push", nanonPush),
   ("intern_nnum", internNNum),
   ("nnum_find", nnumFind),
   ("nnum_push", nnumPush),
   ("sl_cons", slCons),
   ("iw_alloc", iwAlloc),
   ("iw_copy", iwCopy),
   ("sl_find", slFind),
   ("sl_getd", slGetD),
   ("canon_name_map", L.Ind.canonNameMap),
   ("canon_level_eq", L.Ind.canonLevelEq),
   ("lv_node", lvNode),
   ("canon_level_list_eq", L.Ind.canonLevelListEq),
   ("canon_levels_eq", L.Ind.canonLevelsEq),
   ("view_ls", viewLsL),
   ("ls_node", lsNode),
   ("pool_copy", poolCopy),
   ("canon_expr_eq", L.Ind.canonExprEq),
   ("e_view", eView),
   ("cv_canon_eq", L.Ind.cvCanonEq),
   ("cv_lps", cvLps),
   ("er_to_iw", erToIw),
   ("er_copy", erCopy),
   ("canon_rules_eq", L.Ind.canonRulesEq),
   ("ci_canon_eq", L.Ind.ciCanonEq),
   ("canon_eq_list", L.Ind.canonEqListL)]

/-- **The lookups of every function the canonical-form chain reaches.** -/
abbrev CanonProg (p : Prog) : Prop := ProgHas p canonProgFns

/-! ## The models -/

/-- `n` words from `o1` and `o2` agree. -/
def slEqN (a : Word → Word) : Nat → Word → Word → Bool
  | 0, _, _ => true
  | c + 1, o1, o2 => a o1 == a o2 && slEqN a c (o1 + 1) (o2 + 1)

/-- **`er_sl_eq`**: the same length, and the words agree. -/
def erSlEqB (a : Word → Word) (o1 l1 o2 l2 : Word) : Bool := l1 == l2 && slEqN a l1.toNat o1 o2

/-- **`b_eq`**: both zero or both nonzero. -/
def bEqB (x y : Word) : Bool := (x != 0) == (y != 0)

/-- **`cv_eq`**. -/
def cvEqB (a : Word → Word) (q r : Word) : Bool :=
  if a q ≠ a r ∨
      erSlEqB a (a (q + 1)) (a (q + 2)) (a (r + 1)) (a (r + 2)) = false then false
  else a (q + 3) == a (r + 3)

/-- **`hint_eq`**. -/
def hintEqB (a : Word → Word) (h g : Word) : Bool :=
  if a h ≠ a g then false
  else if a h = 2 then a (h + 1) == a (g + 1)
  else true

/-- `er_sl_at`. -/
def erSlAtB (a : Word → Word) (p q i : Word) : Bool :=
  erSlEqB a (a (p + i)) (a (p + i + 1)) (a (q + i)) (a (q + i + 1))

/-- **`caps_eq_a`**. -/
def capsEqAB (a : Word → Word) (q r : Word) : Bool :=
  bEqB (a q) (a r) && a (q + 1) == a (r + 1) && a (q + 2) == a (r + 2) &&
    a (q + 3) == a (r + 3) && bEqB (a (q + 4)) (a (r + 4))

/-- **`caps_eq_b`**. -/
def capsEqBB (a : Word → Word) (q r : Word) : Bool :=
  a (q + 5) == a (r + 5) && a (q + 6) == a (r + 6)

/-- **`caps_eq_c`**. -/
def capsEqCB (a : Word → Word) (q r : Word) : Bool :=
  erSlAtB a q r 10 && a (q + 12) == a (r + 12) && erSlAtB a q r 13

/-- **`caps_eq`**. -/
def capsEqAll (a : Word → Word) (q r : Word) : Bool := capsEqAB a q r && capsEqBB a q r && capsEqCB a q r

/-- **`rule_eq_a`**. -/
def ruleEqAB (a : Word → Word) (q r : Word) : Bool :=
  a q == a r && a (q + 1) == a (r + 1) && a (q + 3) == a (r + 3)

/-- **`rule_eq_b`**. -/
def ruleEqBB (a : Word → Word) (q r : Word) : Bool :=
  if a (q + 3) = 1 then erSlAtB a q r 4 && erSlAtB a q r 6
  else if a (q + 3) = 2 then erSlAtB a q r 4 else true

/-- **`rule_eq_but_rhs`**. -/
def ruleEqButRhsB (a : Word → Word) (q r : Word) : Bool :=
  ruleEqAB a q r && ruleEqBB a q r

/-- `c` rules from `o1` and `o2` agree. -/
def rulesEqN (a : Word → Word) : Nat → Word → Word → Bool
  | 0, _, _ => true
  | c + 1, o1, o2 =>
    ruleEqButRhsB a o1 o2 && a (o1 + 8) == a (o2 + 8) && rulesEqN a c (o1 + 11) (o2 + 11)

/-- **`rules_eq`**. -/
def rulesEqB (a : Word → Word) (o1 l1 o2 l2 : Word) : Bool :=
  l1 == l2 && rulesEqN a l1.toNat o1 o2

/-- **`ci_eq_rest`**. -/
def ciEqRestB (a : Word → Word) (p q k : Word) : Bool :=
  if k = 1 then a (p + 5) == a (q + 5) && hintEqB a (p + 6) (q + 6)
  else if k = 3 then capsEqAll a (p + 5) (q + 5)
  else if k = 4 then a (p + 5) == a (q + 5) && a (p + 6) == a (q + 6)
  else if k = 5 then
    a (p + 5) == a (q + 5) && a (p + 6) == a (q + 6) &&
      rulesEqB a (a (p + 7)) (a (p + 8)) (a (q + 7)) (a (q + 8)) && bEqB (a (p + 9)) (a (q + 9))
  else true

/-- **`ci_eq`** (`5 < kind` aborts in L; the model is arbitrary there). -/
def ciEqB (a : Word → Word) (p q : Word) : Bool :=
  if a p ≠ a q then false
  else if 5 < a p then false
  else cvEqB a (p + 1) (q + 1) && ciEqRestB a p q (a p)

theorem toNat_pred {l : Word} (h0 : l ≠ 0) : l.toNat = (l - 1).toNat + 1 := by
  have : 0 < l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
    · exact h
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
  simp; omega

section arms
variable (a : Word → Word) (c : Nat) (o1 o2 l1 l2 : Word) (x y q r h g p : Word)

theorem slEqN_succ : slEqN a (c + 1) o1 o2 = (a o1 == a o2 && slEqN a c (o1 + 1) (o2 + 1)) :=
  rfl
theorem rulesEqN_succ : rulesEqN a (c + 1) o1 o2 =
    (ruleEqButRhsB a o1 o2 && a (o1 + 8) == a (o2 + 8) &&
      rulesEqN a c (o1 + 11) (o2 + 11)) := rfl

/-- One step of the slice comparison, as the L code takes it. -/
theorem erSlEqB_step (hl : l1 = l2) (h0 : l1 ≠ 0) :
    erSlEqB a o1 l1 o2 l2 = (a o1 == a o2 && erSlEqB a (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)) := by
  subst hl
  have hc : l1.toNat = (l1 - 1).toNat + 1 := toNat_pred h0
  simp only [erSlEqB, beq_self_eq_true, Bool.true_and]
  rw [hc, slEqN_succ]

theorem erSlEqB_len (hl : l1 ≠ l2) : erSlEqB a o1 l1 o2 l2 = false := by
  simp only [erSlEqB]
  have : (l1 == l2) = false := by simpa using hl
  rw [this]; rfl

theorem erSlEqB_nil (hl : l1 = l2) (h0 : l1 = 0) : erSlEqB a o1 l1 o2 l2 = true := by
  subst hl; subst h0; simp [erSlEqB, slEqN]

theorem rulesEqB_len (hl : l1 ≠ l2) : rulesEqB a o1 l1 o2 l2 = false := by
  simp only [rulesEqB]
  have : (l1 == l2) = false := by simpa using hl
  rw [this]; rfl

theorem rulesEqB_nil (hl : l1 = l2) (h0 : l1 = 0) : rulesEqB a o1 l1 o2 l2 = true := by
  subst hl; subst h0; simp [rulesEqB, rulesEqN]

theorem rulesEqB_step (hl : l1 = l2) (h0 : l1 ≠ 0) :
    rulesEqB a o1 l1 o2 l2 = (ruleEqButRhsB a o1 o2 && a (o1 + 8) == a (o2 + 8) &&
      rulesEqB a (o1 + 11) (l1 - 1) (o2 + 11) (l2 - 1)) := by
  subst hl
  have hc : l1.toNat = (l1 - 1).toNat + 1 := toNat_pred h0
  simp only [rulesEqB, beq_self_eq_true, Bool.true_and]
  rw [hc, rulesEqN_succ]

end arms

grind_pattern [ind_grind] erSlEqB_step => erSlEqB a o1 l1 o2 l2
grind_pattern [ind_grind] erSlEqB_len => erSlEqB a o1 l1 o2 l2
grind_pattern [ind_grind] erSlEqB_nil => erSlEqB a o1 l1 o2 l2
grind_pattern [ind_grind] rulesEqB_len => rulesEqB a o1 l1 o2 l2
grind_pattern [ind_grind] rulesEqB_nil => rulesEqB a o1 l1 o2 l2
grind_pattern [ind_grind] rulesEqB_step => rulesEqB a o1 l1 o2 l2

/-! ## The specs -/

section specs
variable (p : Prog) (hp : CanonProg p)
include hp

theorem erSlEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if erSlEqB (erRdT s₀.mem) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ (hp.get "er_sl_eq")]; simp only [callFn, erSlEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "er_sl_eq")]
    simp only [callFn, erSlEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bEq_spec (n : Nat) (s₀ : St) (x y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "b_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = if bEqB x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "b_eq")]
  simp only [callFn, bEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      finish [bEqB]

set_option maxHeartbeats 1000000 in
theorem cvEq_spec' (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if cvEqB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "cv_eq")]
  simp only [callFn, cvEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, erSlEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, cvEqB]

theorem hintEq_spec (n : Nat) (s₀ : St) (h : Word) (g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "hint_eq" [h, g]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if hintEqB (erRdT s₀.mem) h g then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "hint_eq")]
  simp only [callFn, hintEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE] <;>
      finish (gen := 20) [rdW_eq, hintEqB]

theorem erSlAt_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_at" [x, y, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if erSlAtB (erRdT s₀.mem) x y i then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "er_sl_at")]
  simp only [callFn, erSlAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, erSlEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, erSlAtB]

theorem capsEqA_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq_a" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqAB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq_a")]
  simp only [callFn, capsEqA]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, bEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqAB]

theorem capsEqB_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq_b" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqBB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq_b")]
  simp only [callFn, capsEqB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE] <;>
      finish (gen := 20) [rdW_eq, capsEqBB]

theorem capsEqC_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq_c" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqCB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq_c")]
  simp only [callFn, capsEqC]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, erSlAt_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqCB]

theorem capsEq_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqAll (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq")]
  simp only [callFn, capsEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, capsEqA_spec p hp n, capsEqB_spec p hp n, capsEqC_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqAll]

theorem ruleEqA_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_eq_a" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ruleEqAB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_eq_a")]
  simp only [callFn, ruleEqA]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE] <;>
      finish (gen := 20) [rdW_eq, ruleEqAB]

theorem ruleEqB_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_eq_b" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ruleEqBB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_eq_b")]
  simp only [callFn, ruleEqB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, erSlAt_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ruleEqBB]

theorem ruleEqButRhs_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_eq_but_rhs" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ruleEqButRhsB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_eq_but_rhs")]
  simp only [callFn, ruleEqButRhs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, ruleEqA_spec p hp n, ruleEqB_spec p hp n, bEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ruleEqButRhsB]

end specs

set_option experimental.vcgen true in
/-- **The model of `rules_eq`**. -/
l_model rulesEq_specW (p : Prog) (hp : p.lookup "rules_eq" = some rulesEq)
  fns [hp ↦ rulesEqW list]
  specs [callW_spec p n "rule_eq_but_rhs"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

section specs
variable (p : Prog) (hp : CanonProg p)
include hp

/-- `rules_eq`'s model decides `rulesEqB` (memory untouched). -/
theorem rulesEqW_ok : ∀ (n : Nat) (m : Mem) (o1 l1 o2 l2 : Word) (r : List Word) (m' : Mem),
    rulesEqW p n m o1 l1 o2 l2 = some (r, m') →
    m' = m ∧ r.headD 0 = if rulesEqB (erRdT m) o1 l1 o2 l2 then 1 else 0 := by
  intro n
  induction n with
  | zero => intro m o1 l1 o2 l2 r m' h; simp [rulesEqW] at h
  | succ n ih =>
  intro m o1 l1 o2 l2 r m' h
  by_cases hne : l1 ≠ l2
  · rw [rulesEqW.arm1 p n m o1 l1 o2 l2 hne] at h; cases h
    have : (l1 == l2) = false := by simpa using hne
    simp [rulesEqB, this]
  have he : l1 = l2 := Classical.not_not.mp hne
  subst he
  by_cases h0 : l1 = 0
  · rw [rulesEqW.arm2 p n m o1 l1 o2 l1 rfl h0] at h; cases h
    subst h0
    simp [rulesEqB, rulesEqN]
  rw [rulesEqW.arm3 p n m o1 l1 o2 l1 rfl h0] at h
  obtain ⟨k, hk⟩ : ∃ k, l1.toNat = k + 1 :=
    ⟨l1.toNat - 1, by have : l1.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e); omega⟩
  have hk1 : (l1 - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  have hB : rulesEqB (erRdT m) o1 l1 o2 l1 = (ruleEqButRhsB (erRdT m) o1 o2 &&
      erRdT m (o1 + 8) == erRdT m (o2 + 8) &&
      rulesEqB (erRdT m) (o1 + 11) (l1 - 1) (o2 + 11) (l1 - 1)) := by
    simp only [rulesEqB, beq_self_eq_true, Bool.true_and, hk, hk1, rulesEqN]
  cases h1 : callW p n "rule_eq_but_rhs" [o1, o2] m with
  | none => rw [h1] at h; simp [rulesEqW.k_rule_eq_but_rhs] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  obtain ⟨s1, rfl, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ruleEqButRhs_spec p hp n _ o1 o2) h1
  rw [h1] at h
  simp only at hm1 hr1
  rw [hm1] at h
  by_cases hz : r1.headD 0 = 0
  · rw [rulesEqW.k_rule_eq_but_rhs.arm1 p n _ _ _ _ _ _ hz] at h; cases h
    have : ruleEqButRhsB (erRdT m) o1 o2 = false := by
      cases e : ruleEqButRhsB (erRdT m) o1 o2 <;> simp_all
    simp [hB, this]
  have ht : ruleEqButRhsB (erRdT m) o1 o2 = true := by
    cases e : ruleEqButRhsB (erRdT m) o1 o2 <;> simp_all
  by_cases h8 : erRdT m (o1 + 8) ≠ erRdT m (o2 + 8)
  · rw [rulesEqW.k_rule_eq_but_rhs.arm2 p n _ _ _ _ _ _ hz h8] at h; cases h
    have : (erRdT m (o1 + 8) == erRdT m (o2 + 8)) = false := by simpa using h8
    simp [hB, this]
  rw [rulesEqW.k_rule_eq_but_rhs.arm3 p n _ _ _ _ _ _ hz (Classical.not_not.mp h8)] at h
  cases h2 : rulesEqW p n m (o1 + 11) (l1 - 1) (o2 + 11) (l1 - 1) with
  | none => rw [h2] at h; simp [rulesEqW.k_rules_eq] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, rulesEqW.k_rules_eq.eq_2] at h; cases h
  obtain ⟨e2, hr2⟩ := ih _ _ _ _ _ _ _ h2
  refine ⟨e2, ?_⟩
  have : (erRdT m (o1 + 8) == erRdT m (o2 + 8)) = true := by simpa using h8
  simp only [List.headD_cons, hr2, hB, ht, this, Bool.true_and]

theorem rulesEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if rulesEqB (erRdT s₀.mem) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  intro s₀ o1 l1 o2 l2
  refine triple_post (rulesEq_specW p (hp.get "rules_eq") n s₀ o1 l1 o2 l2) ?_
  rintro r s' ⟨hl, hW⟩
  obtain ⟨e, hr⟩ := rulesEqW_ok p hp n _ _ _ _ _ _ _ hW
  exact ⟨hl, e, hr⟩

theorem ciEqRest_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_eq_rest" [x, y, k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ciEqRestB (erRdT s₀.mem) x y k then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_eq_rest")]
  simp only [callFn, ciEqRest]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, hintEq_spec p hp n, capsEq_spec p hp n, rulesEq_spec p hp n, bEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ciEqRestB]

theorem ciEq_spec' (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ciEqB (erRdT s₀.mem) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_eq")]
  simp only [callFn, ciEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, cvEq_spec' p hp n, ciEqRest_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ciEqB]

end specs

end L.Ind
