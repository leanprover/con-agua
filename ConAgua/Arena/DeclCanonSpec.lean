import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclMasterStage

/-!
# Record equalities in L, word models and specs (lane `decls3`, helper `decls3-canon`)

`DeclArmsCanon.lean`'s `er_sl_eq`, `b_eq`, `cv_eq`, `hint_eq`, `pw_eq`, `caps_eq`,
`rule_eq_but_rhs`, `rules_eq`, `tbl_eq`, `ci_eq`, `find_is`. Their word models are **total
`Bool` functions of the record pool** `a : Array Word` (the functions read only `EREC`, never write,
and a slice comparison recurses on its length, not on a fuel): `slEqN`, `erSlEqB`, `cvEqB`, …
`ciEqB`. Each spec says a returning call answers `if model then 1 else 0` and leaves the memory
alone; the relation to decoded records (`DeclCanonEq.lean`) is proved against the models.

`CanonProg p`: the lookups of every function the whole canonical-form chain reaches (the real master
functions, not the stubs of `armsMasterFns`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The lookups of every function the canonical-form chain reaches.** -/
structure CanonProg (p : Prog) : Prop where
  er_sl_eq : p.lookup "er_sl_eq" = some L.Ind.erSlEq
  b_eq : p.lookup "b_eq" = some L.Ind.bEq
  cv_eq : p.lookup "cv_eq" = some L.Ind.cvEq
  hint_eq : p.lookup "hint_eq" = some L.Ind.hintEq
  pw_eq : p.lookup "pw_eq" = some L.Ind.pwEq
  caps_eq : p.lookup "caps_eq" = some L.Ind.capsEq
  rule_eq_but_rhs : p.lookup "rule_eq_but_rhs" = some L.Ind.ruleEqButRhs
  rules_eq : p.lookup "rules_eq" = some L.Ind.rulesEq
  tbl_eq : p.lookup "tbl_eq" = some L.Ind.tblEq
  ci_eq : p.lookup "ci_eq" = some L.Ind.ciEq
  er_sl_at : p.lookup "er_sl_at" = some L.Ind.erSlAt
  caps_eq_a : p.lookup "caps_eq_a" = some L.Ind.capsEqA
  caps_eq_b : p.lookup "caps_eq_b" = some L.Ind.capsEqB
  caps_eq_c : p.lookup "caps_eq_c" = some L.Ind.capsEqC
  rule_eq_a : p.lookup "rule_eq_a" = some L.Ind.ruleEqA
  rule_eq_b : p.lookup "rule_eq_b" = some L.Ind.ruleEqB
  tbl_eq_a : p.lookup "tbl_eq_a" = some L.Ind.tblEqA
  ci_eq_rest : p.lookup "ci_eq_rest" = some L.Ind.ciEqRest
  canon_ctx : p.lookup "canon_ctx" = some L.Ind.canonCtx
  ci_canon_defn : p.lookup "ci_canon_defn" = some L.Ind.ciCanonDefn
  ci_canon_rec : p.lookup "ci_canon_rec" = some L.Ind.ciCanonRec
  find_is : p.lookup "find_is" = some L.Ind.findIs
  env_find : p.lookup "env_find" = some envFindL
  env_row_get : p.lookup "env_row_get" = some envRowGetL
  env_ix : p.lookup "env_ix" = some envIxL
  ci_to_cv : p.lookup "ci_to_cv" = some L.Ind.ciToCv
  intern_zero : p.lookup "intern_zero" = some internZero
  zero_find : p.lookup "zero_find" = some zeroFind
  zero_push : p.lookup "zero_push" = some zeroPush
  intern_succ : p.lookup "intern_succ" = some internSucc
  succ_find : p.lookup "succ_find" = some succFind
  succ_push : p.lookup "succ_push" = some succPush
  intern_sort : p.lookup "intern_sort" = some internSort
  sort_find : p.lookup "sort_find" = some sortFind
  sort_push : p.lookup "sort_push" = some sortPush
  cv_new : p.lookup "cv_new" = some cvNew
  erec_alloc : p.lookup "erec_alloc" = some erecAlloc
  canon_names_go : p.lookup "canon_names_go" = some L.Ind.canonNamesGo
  canon_names : p.lookup "canon_names" = some L.Ind.canonNames
  intern_nanon : p.lookup "intern_nanon" = some internNAnon
  nanon_find : p.lookup "nanon_find" = some nanonFind
  nanon_push : p.lookup "nanon_push" = some nanonPush
  intern_nnum : p.lookup "intern_nnum" = some internNNum
  nnum_find : p.lookup "nnum_find" = some nnumFind
  nnum_push : p.lookup "nnum_push" = some nnumPush
  sl_cons : p.lookup "sl_cons" = some slCons
  iw_alloc : p.lookup "iw_alloc" = some iwAlloc
  iw_copy : p.lookup "iw_copy" = some iwCopy
  sl_find : p.lookup "sl_find" = some slFind
  sl_getd : p.lookup "sl_getd" = some slGetD
  canon_name_map : p.lookup "canon_name_map" = some L.Ind.canonNameMap
  canon_level_eq : p.lookup "canon_level_eq" = some L.Ind.canonLevelEq
  lv_node : p.lookup "lv_node" = some lvNode
  canon_level_list_eq : p.lookup "canon_level_list_eq" = some L.Ind.canonLevelListEq
  canon_levels_eq : p.lookup "canon_levels_eq" = some L.Ind.canonLevelsEq
  view_ls : p.lookup "view_ls" = some viewLsL
  ls_node : p.lookup "ls_node" = some lsNode
  pool_copy : p.lookup "pool_copy" = some poolCopy
  canon_expr_eq : p.lookup "canon_expr_eq" = some L.Ind.canonExprEq
  e_view : p.lookup "e_view" = some eView
  cv_canon_eq : p.lookup "cv_canon_eq" = some L.Ind.cvCanonEq
  cv_lps : p.lookup "cv_lps" = some cvLps
  er_to_iw : p.lookup "er_to_iw" = some erToIw
  er_copy : p.lookup "er_copy" = some erCopy
  canon_rules_eq : p.lookup "canon_rules_eq" = some L.Ind.canonRulesEq
  ci_canon_eq : p.lookup "ci_canon_eq" = some L.Ind.ciCanonEq
  canon_eq_list : p.lookup "canon_eq_list" = some L.Ind.canonEqListL

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

/-- **`tbl_eq_a`**. -/
def tblEqAB (a : Array Word) (p q : Word) : Bool :=
  rdW a (p + 1) == rdW a (q + 1) && rdW a (p + 2) == rdW a (q + 2) && erSlAtB a p q 3 &&
    rdW a (p + 5) == rdW a (q + 5) && rdW a (p + 6) == rdW a (q + 6) &&
    rdW a (p + 7) == rdW a (q + 7) && rdW a (p + 8) == rdW a (q + 8)

/-- **`tbl_eq`**. -/
def tblEqB (a : Array Word) (p q : Word) : Bool :=
  tblEqAB a p q && erSlAtB a p q 9 && erSlAtB a p q 11 && rdW a (p + 13) == rdW a (q + 13)

/-- **`ci_eq_rest`**. -/
def ciEqRestB (a : Array Word) (p q k : Word) : Bool :=
  if k = 1 then rdW a (p + 5) == rdW a (q + 5) && hintEqB a (p + 6) (q + 6)
  else if k = 3 then capsEqAll a (p + 5) (q + 5)
  else if k = 4 then rdW a (p + 5) == rdW a (q + 5) && rdW a (p + 6) == rdW a (q + 6)
  else if k = 5 then
    rdW a (p + 5) == rdW a (q + 5) && rdW a (p + 6) == rdW a (q + 6) &&
      rulesEqB a (rdW a (p + 7)) (rdW a (p + 8)) (rdW a (q + 7)) (rdW a (q + 8))
  else true

/-- **`ci_eq`** (`6 < kind` aborts in L; the model is arbitrary there). -/
def ciEqB (a : Array Word) (p q : Word) : Bool :=
  if rdW a p ≠ rdW a q then false
  else if 6 < rdW a p then false
  else if rdW a p = 6 then tblEqB a p q
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

theorem slEqN_zero : slEqN a 0 o1 o2 = true := rfl
theorem slEqN_succ : slEqN a (c + 1) o1 o2 = (rdW a o1 == rdW a o2 && slEqN a c (o1 + 1) (o2 + 1)) :=
  rfl
theorem rulesEqN_zero : rulesEqN a 0 o1 o2 = true := rfl
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

theorem envFindW_mem {m m1 : Mem} {w vis : Word} {r : List Word}
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
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ hp.er_sl_eq]; simp only [callFn, erSlEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ hp.er_sl_eq]
    simp only [callFn, erSlEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bEq_spec (n : Nat) (s₀ : St) (x y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "b_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = if bEqB x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ hp.b_eq]
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
  rw [invoke_eq _ hp.cv_eq]
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
  rw [invoke_eq _ hp.hint_eq]
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
  rw [invoke_eq _ hp.pw_eq]
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
  rw [invoke_eq _ hp.er_sl_at]
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
  rw [invoke_eq _ hp.caps_eq_a]
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
  rw [invoke_eq _ hp.caps_eq_b]
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
  rw [invoke_eq _ hp.caps_eq_c]
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
  rw [invoke_eq _ hp.caps_eq]
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
  rw [invoke_eq _ hp.rule_eq_a]
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
  rw [invoke_eq _ hp.rule_eq_b]
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
  rw [invoke_eq _ hp.rule_eq_but_rhs]
  simp only [callFn, ruleEqButRhs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ruleEqA_spec p hp n, ruleEqB_spec p hp n, bEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ruleEqButRhsB]

theorem tblEqA_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "tbl_eq_a" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if tblEqAB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ hp.tbl_eq_a]
  simp only [callFn, tblEqA]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erSlAt_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, tblEqAB]

theorem tblEq_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "tbl_eq" [x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if tblEqB (s₀.mem.arr64 EREC) x y then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ hp.tbl_eq]
  simp only [callFn, tblEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, tblEqA_spec p hp n, erSlAt_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, tblEqB]

theorem rulesEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if rulesEqB (s₀.mem.arr64 EREC) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ hp.rules_eq]; simp only [callFn, rulesEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ hp.rules_eq]
    simp only [callFn, rulesEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        ruleEqButRhs_spec p hp n] <;>
      finish (gen := 20) [rdW_eq]

theorem ciEqRest_spec (n : Nat) (s₀ : St) (x : Word) (y : Word) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_eq_rest" [x, y, k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if ciEqRestB (s₀.mem.arr64 EREC) x y k then 1 else 0; ⊤⦄ := by
  rw [invoke_eq _ hp.ci_eq_rest]
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
  rw [invoke_eq _ hp.ci_eq]
  simp only [callFn, ciEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, tblEq_spec p hp n, cvEq_spec' p hp n, ciEqRest_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, ciEqB]

theorem findIs_spec' (n : Nat) (s₀ : St) (nm vis pin : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "find_is" [vis, nm, pin]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ findIsW s₀.mem nm vis pin = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp.find_is]
  simp only [callFn, findIs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p hp.env_ix hp.env_row_get hp.env_find n, ciEq_spec' p hp n] <;>
      finish (gen := 20) [findIsW, envFindW_mem]

end specs

end L.Ind
