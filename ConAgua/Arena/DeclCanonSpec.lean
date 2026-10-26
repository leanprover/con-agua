import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclMasterStage
import ConAgua.L.ProgHas

/-!
# Record equalities in L, word models and specs (lane `decls3`, helper `decls3-canon`)

`DeclArmsCanon.lean`'s `er_sl_eq`, `b_eq`, `cv_eq`, `hint_eq`, `pw_eq`, `caps_eq`,
`rule_eq_but_rhs`, `rules_eq`, `ci_eq`, `find_is`. Their word models are **total
`Bool` functions of the record pool** `a : Array Word` (the functions read only `EREC`, never write,
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

/-- The functions of `CanonProg`. -/
def canonProgFns : Prog :=
  [("er_sl_eq", L.Ind.erSlEq), ("b_eq", L.Ind.bEq), ("cv_eq", L.Ind.cvEq),
   ("hint_eq", L.Ind.hintEq), ("pw_eq", L.Ind.pwEq), ("caps_eq", L.Ind.capsEq),
   ("rule_eq_but_rhs", L.Ind.ruleEqButRhs), ("rules_eq", L.Ind.rulesEq),
   ("ci_eq", L.Ind.ciEq), ("er_sl_at", L.Ind.erSlAt), ("caps_eq_a", L.Ind.capsEqA),
   ("caps_eq_b", L.Ind.capsEqB), ("caps_eq_c", L.Ind.capsEqC), ("rule_eq_a", L.Ind.ruleEqA),
   ("rule_eq_b", L.Ind.ruleEqB), ("ci_eq_rest", L.Ind.ciEqRest),
   ("canon_ctx", L.Ind.canonCtx), ("ci_canon_defn", L.Ind.ciCanonDefn),
   ("ci_canon_rec", L.Ind.ciCanonRec), ("find_is", L.Ind.findIs), ("env_find", envFindL),
   ("env_row_get", envRowGetL), ("env_ix", envIxL), ("ci_to_cv", L.Ind.ciToCv),
   ("intern_zero", internZero), ("zero_find", zeroFind), ("zero_push", zeroPush),
   ("intern_succ", internSucc), ("succ_find", succFind), ("succ_push", succPush),
   ("intern_sort", internSort), ("sort_find", sortFind), ("sort_push", sortPush),
   ("cv_new", cvNew), ("erec_alloc", erecAlloc), ("canon_names_go", L.Ind.canonNamesGo),
   ("canon_names", L.Ind.canonNames), ("intern_nanon", internNAnon), ("nanon_find", nanonFind),
   ("nanon_push", nanonPush), ("intern_nnum", internNNum), ("nnum_find", nnumFind),
   ("nnum_push", nnumPush), ("sl_cons", slCons), ("iw_alloc", iwAlloc), ("iw_copy", iwCopy),
   ("sl_find", slFind), ("sl_getd", slGetD), ("canon_name_map", L.Ind.canonNameMap),
   ("canon_level_eq", L.Ind.canonLevelEq), ("lv_node", lvNode),
   ("canon_level_list_eq", L.Ind.canonLevelListEq), ("canon_levels_eq", L.Ind.canonLevelsEq),
   ("view_ls", viewLsL), ("ls_node", lsNode), ("pool_copy", poolCopy),
   ("canon_expr_eq", L.Ind.canonExprEq), ("e_view", eView), ("cv_canon_eq", L.Ind.cvCanonEq),
   ("cv_lps", cvLps), ("er_to_iw", erToIw), ("er_copy", erCopy),
   ("canon_rules_eq", L.Ind.canonRulesEq), ("ci_canon_eq", L.Ind.ciCanonEq),
   ("canon_eq_list", L.Ind.canonEqListL)]

/-- **The lookups of every function the canonical-form chain reaches.** -/
abbrev CanonProg (p : Prog) : Prop := ProgHas p canonProgFns

/-! ## The models -/

/-- `n` words from `o1` and `o2` agree. -/
def slEqN (a : Array Word) : Nat → Word → Word → Bool
  | 0, _, _ => true
  | c + 1, o1, o2 => rdW a o1 == rdW a o2 && slEqN a c (o1 + 1) (o2 + 1)

/-- **`er_sl_eq`**: the same length, and the words agree. -/
def erSlEqB (a : Array Word) (o1 l1 o2 l2 : Word) : Bool := l1 == l2 && slEqN a l1.toNat o1 o2

/-- **`b_eq`**: both zero or both nonzero. -/
def bEqB (x y : Word) : Bool := (x != 0) == (y != 0)

/-- **`cv_eq`**. -/
def cvEqB (a : Array Word) (q r : Word) : Bool :=
  if rdW a q ≠ rdW a r ∨
      erSlEqB a (rdW a (q + 1)) (rdW a (q + 2)) (rdW a (r + 1)) (rdW a (r + 2)) = false then false
  else rdW a (q + 3) == rdW a (r + 3)

/-- **`hint_eq`**. -/
def hintEqB (a : Array Word) (h g : Word) : Bool :=
  if rdW a h ≠ rdW a g then false
  else if rdW a h = 2 then rdW a (h + 1) == rdW a (g + 1)
  else true

/-- **`pw_eq`**. -/
def pwEqB (a : Array Word) (q r : Word) : Bool :=
  if rdW a q ≠ rdW a r then false
  else if rdW a q ≠ 1 then true
  else erSlEqB a (rdW a (q + 1)) (rdW a (q + 2)) (rdW a (r + 1)) (rdW a (r + 2))

/-- `er_sl_at`. -/
def erSlAtB (a : Array Word) (p q i : Word) : Bool :=
  erSlEqB a (rdW a (p + i)) (rdW a (p + i + 1)) (rdW a (q + i)) (rdW a (q + i + 1))

/-- **`caps_eq_a`**. -/
def capsEqAB (a : Array Word) (q r : Word) : Bool :=
  bEqB (rdW a q) (rdW a r) && rdW a (q + 1) == rdW a (r + 1) && rdW a (q + 2) == rdW a (r + 2) &&
    rdW a (q + 3) == rdW a (r + 3) && bEqB (rdW a (q + 4)) (rdW a (r + 4))

/-- **`caps_eq_b`**. -/
def capsEqBB (a : Array Word) (q r : Word) : Bool :=
  rdW a (q + 5) == rdW a (r + 5) && bEqB (rdW a (q + 6)) (rdW a (r + 6)) && pwEqB a (q + 7) (r + 7)

/-- **`caps_eq_c`**. -/
def capsEqCB (a : Array Word) (q r : Word) : Bool :=
  erSlAtB a q r 10 && rdW a (q + 12) == rdW a (r + 12) && erSlAtB a q r 13

/-- **`caps_eq`**. -/
def capsEqAll (a : Array Word) (q r : Word) : Bool := capsEqAB a q r && capsEqBB a q r && capsEqCB a q r

/-- **`rule_eq_a`**. -/
def ruleEqAB (a : Array Word) (q r : Word) : Bool :=
  rdW a q == rdW a r && rdW a (q + 1) == rdW a (r + 1) && rdW a (q + 2) == rdW a (r + 2) &&
    rdW a (q + 3) == rdW a (r + 3)

/-- **`rule_eq_b`**. -/
def ruleEqBB (a : Array Word) (q r : Word) : Bool :=
  if rdW a (q + 3) = 1 then erSlAtB a q r 4 && erSlAtB a q r 6 else true

/-- **`rule_eq_but_rhs`**. -/
def ruleEqButRhsB (a : Array Word) (q r : Word) : Bool :=
  ruleEqAB a q r && ruleEqBB a q r && bEqB (rdW a (q + 9)) (rdW a (r + 9)) &&
    bEqB (rdW a (q + 10)) (rdW a (r + 10))

/-- `c` rules from `o1` and `o2` agree. -/
def rulesEqN (a : Array Word) : Nat → Word → Word → Bool
  | 0, _, _ => true
  | c + 1, o1, o2 =>
    ruleEqButRhsB a o1 o2 && rdW a (o1 + 8) == rdW a (o2 + 8) && rulesEqN a c (o1 + 11) (o2 + 11)

/-- **`rules_eq`**. -/
def rulesEqB (a : Array Word) (o1 l1 o2 l2 : Word) : Bool :=
  l1 == l2 && rulesEqN a l1.toNat o1 o2

/-- **`ci_eq_rest`**. -/
def ciEqRestB (a : Array Word) (p q k : Word) : Bool :=
  if k = 1 then rdW a (p + 5) == rdW a (q + 5) && hintEqB a (p + 6) (q + 6)
  else if k = 3 then capsEqAll a (p + 5) (q + 5)
  else if k = 4 then rdW a (p + 5) == rdW a (q + 5) && rdW a (p + 6) == rdW a (q + 6)
  else if k = 5 then
    rdW a (p + 5) == rdW a (q + 5) && rdW a (p + 6) == rdW a (q + 6) &&
      rulesEqB a (rdW a (p + 7)) (rdW a (p + 8)) (rdW a (q + 7)) (rdW a (q + 8))
  else true

/-- **`ci_eq`** (`5 < kind` aborts in L; the model is arbitrary there). -/
def ciEqB (a : Array Word) (p q : Word) : Bool :=
  if rdW a p ≠ rdW a q then false
  else if 5 < rdW a p then false
  else cvEqB a (p + 1) (q + 1) && ciEqRestB a p q (rdW a p)

/-- **`find_is`**: `env_find`'s row, then `ci_eq` against `pin`. -/
def findIsW (m : Mem) (n vis pin : Word) : Option Word :=
  match envFindW m n vis with
  | none => none
  | some (rr, _) =>
    if rr.headD 0 = 0 then some 0
    else some (if ciEqB (m.arr64 EREC) (rr.tail.headD 0) pin then 1 else 0)

theorem toNat_pred {l : Word} (h0 : l ≠ 0) : l.toNat = (l - 1).toNat + 1 := by
  have : 0 < l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
    · exact h
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
  simp; omega

section arms
variable (a : Array Word) (c : Nat) (o1 o2 l1 l2 : Word) (x y q r h g p : Word)

theorem slEqN_succ : slEqN a (c + 1) o1 o2 = (rdW a o1 == rdW a o2 && slEqN a c (o1 + 1) (o2 + 1)) :=
  rfl
theorem rulesEqN_succ : rulesEqN a (c + 1) o1 o2 =
    (ruleEqButRhsB a o1 o2 && rdW a (o1 + 8) == rdW a (o2 + 8) &&
      rulesEqN a c (o1 + 11) (o2 + 11)) := rfl

/-- One step of the slice comparison, as the L code takes it. -/
theorem erSlEqB_step (hl : l1 = l2) (h0 : l1 ≠ 0) :
    erSlEqB a o1 l1 o2 l2 = (rdW a o1 == rdW a o2 && erSlEqB a (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)) := by
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
    rulesEqB a o1 l1 o2 l2 = (ruleEqButRhsB a o1 o2 && rdW a (o1 + 8) == rdW a (o2 + 8) &&
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

theorem cnEnvFindW_mem {m m1 : Mem} {w vis : Word} {r : List Word}
    (h : envFindW m w vis = some (r, m1)) : m1 = m := by
  unfold envFindW at h
  repeat' split at h
  all_goals first | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm) | cases h

/-! ## The specs -/

section specs
variable (p : Prog) (hp : CanonProg p)
include hp

theorem erSlEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if erSlEqB (s₀.mem.arr64 EREC) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ (hp.get "er_sl_eq")]; simp only [callFn, erSlEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "er_sl_eq")]
    simp only [callFn, erSlEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
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
      r.headD 0 = if cvEqB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "cv_eq")]
  simp only [callFn, cvEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erSlEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, cvEqB]

theorem hintEq_spec (n : Nat) (s₀ : St) (h : Word) (g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "hint_eq" [h, g]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if hintEqB (s₀.mem.arr64 EREC) h g then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "hint_eq")]
  simp only [callFn, hintEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish (gen := 20) [rdW_eq, hintEqB]

theorem pwEq_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pw_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if pwEqB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pw_eq")]
  simp only [callFn, pwEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erSlEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, pwEqB]

theorem erSlAt_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_at" [x, y, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if erSlAtB (s₀.mem.arr64 EREC) x y i then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "er_sl_at")]
  simp only [callFn, erSlAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erSlEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, erSlAtB]

theorem capsEqA_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq_a" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqAB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq_a")]
  simp only [callFn, capsEqA]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, bEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqAB]

theorem capsEqB_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq_b" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqBB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq_b")]
  simp only [callFn, capsEqB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, bEq_spec p hp n, pwEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqBB]

theorem capsEqC_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq_c" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqCB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq_c")]
  simp only [callFn, capsEqC]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erSlAt_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqCB]

theorem capsEq_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if capsEqAll (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_eq")]
  simp only [callFn, capsEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, capsEqA_spec p hp n, capsEqB_spec p hp n, capsEqC_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, capsEqAll]

theorem ruleEqA_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_eq_a" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ruleEqAB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_eq_a")]
  simp only [callFn, ruleEqA]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish (gen := 20) [rdW_eq, ruleEqAB]

theorem ruleEqB_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_eq_b" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ruleEqBB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_eq_b")]
  simp only [callFn, ruleEqB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erSlAt_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ruleEqBB]

theorem ruleEqButRhs_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_eq_but_rhs" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ruleEqButRhsB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_eq_but_rhs")]
  simp only [callFn, ruleEqButRhs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ruleEqA_spec p hp n, ruleEqB_spec p hp n, bEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ruleEqButRhsB]

theorem rulesEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if rulesEqB (s₀.mem.arr64 EREC) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ (hp.get "rules_eq")]; simp only [callFn, rulesEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "rules_eq")]
    simp only [callFn, rulesEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        ruleEqButRhs_spec p hp n] <;>
      finish (gen := 20) [rdW_eq]

theorem ciEqRest_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_eq_rest" [x, y, k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ciEqRestB (s₀.mem.arr64 EREC) x y k then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_eq_rest")]
  simp only [callFn, ciEqRest]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hintEq_spec p hp n, capsEq_spec p hp n, rulesEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ciEqRestB]

theorem ciEq_spec' (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ciEqB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_eq")]
  simp only [callFn, ciEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, cvEq_spec' p hp n, ciEqRest_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ciEqB]

theorem findIs_spec' (n : Nat) (s₀ : St) (nm vis pin : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "find_is" [vis, nm, pin]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ findIsW s₀.mem nm vis pin = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "find_is")]
  simp only [callFn, findIs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p (hp.get "env_ix") (hp.get "env_row_get") (hp.get "env_find") n, ciEq_spec' p hp n] <;>
      finish (gen := 20) [findIsW, cnEnvFindW_mem]

end specs

end L.Ind
