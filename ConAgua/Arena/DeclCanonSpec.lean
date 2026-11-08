module

public import ConAgua.Arena.DeclHeader
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

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

/-! ## The specs -/

section specs
include hp

set_option maxHeartbeats 1000000 in
end specs

end L.Ind
