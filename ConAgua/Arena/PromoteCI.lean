import ConAgua.Arena.PromoteRecRef

/-!
# The constant side of the promotion: models and specs

`erec_rd1‥5`, `erec_wr1‥5`, `erec_cp`, then `promote_fire`, `promote_rule`, `promote_rules`,
`promote_caps`, `promote_proj_table`, and the entries' table side. As `PromoteRec.lean`: models whose callees are `callW` runs,
one `vcgen` per spec.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Reads, writes, copies of `EREC` words -/

/-- A sequence of stores `EREC[d + o] := v` (offset, value), bounds checked. -/
def stP (d : Word) : Mem → List (Word × Word) → Option Mem
  | m, [] => some m
  | m, (o, v) :: ps =>
    if (m.arr64 EREC).size ≤ (d + o).toNat then none else stP d (m.set64 EREC (d + o) v) ps

/-- The 1 word(s) at `s`, or `[]` out of bounds (`erec_rd1`'s model). -/
def rd1W (m : Mem) (s : Word) : List Word :=
  if (m.arr64 EREC).size ≤ s.toNat then [] else [rdW (m.arr64 EREC) s]

/-- The 2 word(s) at `s`, or `[]` out of bounds (`erec_rd2`'s model). -/
def rd2W (m : Mem) (s : Word) : List Word :=
  if (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat then [] else [rdW (m.arr64 EREC) s, rdW (m.arr64 EREC) (s + 1)]

/-- The 3 word(s) at `s`, or `[]` out of bounds (`erec_rd3`'s model). -/
def rd3W (m : Mem) (s : Word) : List Word :=
  if (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat ∨ (m.arr64 EREC).size ≤ (s + 2).toNat then [] else [rdW (m.arr64 EREC) s, rdW (m.arr64 EREC) (s + 1), rdW (m.arr64 EREC) (s + 2)]

/-- The 4 word(s) at `s`, or `[]` out of bounds (`erec_rd4`'s model). -/
def rd4W (m : Mem) (s : Word) : List Word :=
  if (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat ∨ (m.arr64 EREC).size ≤ (s + 2).toNat ∨ (m.arr64 EREC).size ≤ (s + 3).toNat then [] else [rdW (m.arr64 EREC) s, rdW (m.arr64 EREC) (s + 1), rdW (m.arr64 EREC) (s + 2), rdW (m.arr64 EREC) (s + 3)]

/-- The 5 word(s) at `s`, or `[]` out of bounds (`erec_rd5`'s model). -/
def rd5W (m : Mem) (s : Word) : List Word :=
  if (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat ∨ (m.arr64 EREC).size ≤ (s + 2).toNat ∨ (m.arr64 EREC).size ≤ (s + 3).toNat ∨ (m.arr64 EREC).size ≤ (s + 4).toNat then [] else [rdW (m.arr64 EREC) s, rdW (m.arr64 EREC) (s + 1), rdW (m.arr64 EREC) (s + 2), rdW (m.arr64 EREC) (s + 3), rdW (m.arr64 EREC) (s + 4)]

/-- **The model of `erec_cp(d, s, l)`.** -/
def cpW (p : Prog) (n : Nat) (m : Mem) (d s l : Word) : Option Mem :=
  if l = 0 then some m
  else if (m.arr64 EREC).size ≤ s.toNat then none
  else if (m.arr64 EREC).size ≤ d.toNat then none
  else memK (callW p n "erec_cp" [d + 1, s + 1, l - 1] (m.set64 EREC d (rdW (m.arr64 EREC) s)))

section specs
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem erecRd1_spec (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_rd1" [s]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = rd1W s₀.mem s; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_rd1")]
  simp only [callFn, erecRd1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rd1W]

theorem erecRd2_spec (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_rd2" [s]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = rd2W s₀.mem s; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_rd2")]
  simp only [callFn, erecRd2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rd2W]

theorem erecRd3_spec (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_rd3" [s]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = rd3W s₀.mem s; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_rd3")]
  simp only [callFn, erecRd3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rd3W]

theorem erecRd4_spec (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_rd4" [s]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = rd4W s₀.mem s; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_rd4")]
  simp only [callFn, erecRd4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rd4W]

theorem erecRd5_spec (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_rd5" [s]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = rd5W s₀.mem s; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_rd5")]
  simp only [callFn, erecRd5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rd5W]

theorem erecWr1_spec (d a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_wr1" [d, a]
    ⦃fun _ s' => LocEq s' s₀ ∧ stP d s₀.mem [(0, a)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_wr1")]
  simp only [callFn, erecWr1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP, UInt64.add_zero]

theorem erecWr2_spec (d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_wr2" [d, a, b]
    ⦃fun _ s' => LocEq s' s₀ ∧ stP d s₀.mem [(0, a), (1, b)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_wr2")]
  simp only [callFn, erecWr2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP, UInt64.add_zero]

theorem erecWr3_spec (d a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_wr3" [d, a, b, c]
    ⦃fun _ s' => LocEq s' s₀ ∧ stP d s₀.mem [(0, a), (1, b), (2, c)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_wr3")]
  simp only [callFn, erecWr3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP, UInt64.add_zero]

theorem erecWr4_spec (d a b c e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_wr4" [d, a, b, c, e]
    ⦃fun _ s' => LocEq s' s₀ ∧ stP d s₀.mem [(0, a), (1, b), (2, c), (3, e)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_wr4")]
  simp only [callFn, erecWr4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP, UInt64.add_zero]

theorem erecWr5_spec (d a b c e g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_wr5" [d, a, b, c, e, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ stP d s₀.mem [(0, a), (1, b), (2, c), (3, e), (4, g)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_wr5")]
  simp only [callFn, erecWr5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP, UInt64.add_zero]

theorem capsWr_spec (d c a k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "caps_wr" [d, c, a, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ stP d s₀.mem [(1, c), (10, a), (13, k)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_wr")]
  simp only [callFn, capsWr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP]

theorem projWr_spec (d sn lp c ss bs gs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "proj_wr" [d, sn, lp, c, ss, bs, gs]
    ⦃fun _ s' => LocEq s' s₀ ∧
      stP d s₀.mem [(2, sn), (3, lp), (6, c), (8, ss), (9, bs), (11, gs)] = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "proj_wr")]
  simp only [callFn, projWr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [stP]

theorem erecCp_spec (d s l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erec_cp" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ cpW p n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erec_cp")]
  simp only [callFn, erecCp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "erec_cp"] <;>
    finish [cpW, memK_some]

/-! ## `promote_fire` -/

/-- The `i`-th result word (`setLocs` reads results as `headD`, `tail.headD`, …). -/
abbrev g0 (r : List Word) : Word := r.headD 0
abbrev g1 (r : List Word) : Word := r.tail.headD 0
abbrev g2 (r : List Word) : Word := r.tail.tail.headD 0
abbrev g3 (r : List Word) : Word := r.tail.tail.tail.headD 0
abbrev g4 (r : List Word) : Word := r.tail.tail.tail.tail.headD 0

/-- **The model of `promote_fire(f, s)`.** -/
def fireW (p : Prog) (n : Nat) (m : Mem) (f s : Word) : Option (List Word × Mem) :=
  (callW p n "erec_rd5" [s + 3] m).bind fun r₀ =>
  if g0 r₀.1 ≠ 1 then some ([g0 r₀.1, 0, 0, 0, 0], r₀.2)
  else
    (callW p n "promote_slice" [1, f, g1 r₀.1, g2 r₀.1] r₀.2).bind fun r₁ =>
    (callW p n "promote_slice" [2, f, g3 r₀.1, g4 r₀.1] r₁.2).bind fun r₂ =>
    some ([1, g0 r₁.1, g2 r₀.1, g0 r₂.1, g4 r₀.1], r₂.2)

theorem promoteFire_spec (f s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_fire" [f, s]
    ⦃fun r s' => LocEq s' s₀ ∧ fireW p n s₀.mem f s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_fire")]
  simp only [callFn, promoteFireL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd5", callW_spec p n "promote_slice"] <;>
    finish (gen := 20) [fireW, rd5W, Option.bind_some, Option.bind_none]

/-! ## `promote_rule`, `promote_rules` -/

/-- **The model of `pe_at(f, a)`.** -/
def peAtW (p : Prog) (n : Nat) (m : Mem) (f a : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd1" [a] m).bind fun r =>
  (callW p n "promote_e" [f, g0 r.1] r.2).bind fun x => some (g0 x.1, x.2)

theorem peAt_spec (f a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_at" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ peAtW p n s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pe_at")]
  simp only [callFn, peAt]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd1", callW_spec p n "promote_e"] <;>
    finish (gen := 20) [peAtW, Option.bind_some, Option.bind_none]

/-- **The model of `rule_wr(d, s, c, r)`.** -/
def ruleWrW (p : Prog) (n : Nat) (m : Mem) (d s c r : Word) : Option Mem :=
  (callW p n "erec_rd2" [s + 1] m).bind fun a =>
  (callW p n "erec_rd2" [s + 9] a.2).bind fun b =>
  (callW p n "erec_wr3" [d, c, g0 a.1, g1 a.1] b.2).bind fun w =>
  memK (callW p n "erec_wr3" [d + 8, r, g0 b.1, g1 b.1] w.2)

theorem ruleWr_spec (d s c r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rule_wr" [d, s, c, r]
    ⦃fun _ s' => LocEq s' s₀ ∧ ruleWrW p n s₀.mem d s c r = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rule_wr")]
  simp only [callFn, ruleWr]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd2", callW_spec p n "erec_wr3"] <;>
    finish (gen := 20) [ruleWrW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `promote_rule(f, s, d)`.** -/
def ruleW (p : Prog) (n : Nat) (m : Mem) (f s d : Word) : Option Mem :=
  (callW p n "pn_at" [f, s] m).bind fun c =>
  (callW p n "promote_fire" [f, s] c.2).bind fun u =>
  (callW p n "pe_at" [f, s + 8] u.2).bind fun r =>
  (callW p n "rule_wr" [d, s, g0 c.1, g0 r.1] r.2).bind fun w =>
  memK (callW p n "erec_wr5" [d + 3, g0 u.1, g1 u.1, g2 u.1, g3 u.1, g4 u.1] w.2)

theorem promoteRule_spec (f s d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_rule" [f, s, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ ruleW p n s₀.mem f s d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_rule")]
  simp only [callFn, promoteRuleL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pn_at", callW_spec p n "pe_at", callW_spec p n "rule_wr",
      callW_spec p n "erec_wr5", callW_spec p n "promote_fire"] <;>
    finish (gen := 20) [ruleW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `promote_rules(f, s, l, d)`.** -/
def rulesW (p : Prog) (n : Nat) (m : Mem) (f s l d : Word) : Option Mem :=
  if l = 0 then some m
  else (callW p n "promote_rule" [f, s, d] m).bind fun r =>
    memK (callW p n "promote_rules" [f, s + 11, l - 1, d + 11] r.2)

theorem promoteRules_spec (f s l d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_rules" [f, s, l, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ rulesW p n s₀.mem f s l d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_rules")]
  simp only [callFn, promoteRulesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "promote_rule", callW_spec p n "promote_rules"] <;>
    finish (gen := 20) [rulesW, memK_some, Option.bind_some, Option.bind_none]

/-! ## `promote_caps`, `promote_proj_table` -/

/-- **The model of `pn_at(f, a)`.** -/
def pnAtW (p : Prog) (n : Nat) (m : Mem) (f a : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd1" [a] m).bind fun r =>
  (callW p n "promote_n" [f, g0 r.1] r.2).bind fun x => some (g0 x.1, x.2)

theorem pnAt_spec (f a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pn_at" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ pnAtW p n s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pn_at")]
  simp only [callFn, pnAt]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd1", callW_spec p n "promote_n"] <;>
    finish (gen := 20) [pnAtW, Option.bind_some, Option.bind_none]

/-- **The model of `pl_at(f, a)`.** -/
def plAtW (p : Prog) (n : Nat) (m : Mem) (f a : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd1" [a] m).bind fun r =>
  (callW p n "promote_l" [f, g0 r.1] r.2).bind fun x => some (g0 x.1, x.2)

theorem plAt_spec (f a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pl_at" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ plAtW p n s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pl_at")]
  simp only [callFn, plAt]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd1", callW_spec p n "promote_l"] <;>
    finish (gen := 20) [plAtW, Option.bind_some, Option.bind_none]

/-- **The model of `ps_at(k, f, a)`.** -/
def psAtW (p : Prog) (n : Nat) (m : Mem) (k f a : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd2" [a] m).bind fun r =>
  (callW p n "promote_slice" [k, f, g0 r.1, g1 r.1] r.2).bind fun x => some (g0 x.1, x.2)

theorem psAt_spec (k f a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ps_at" [k, f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ psAtW p n s₀.mem k f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ps_at")]
  simp only [callFn, psAt]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd2", callW_spec p n "promote_slice"] <;>
    finish (gen := 20) [psAtW, Option.bind_some, Option.bind_none]

/-- **The model of `caps_parts(f, s)`**: the three handles. -/
def capsPW (p : Prog) (n : Nat) (m : Mem) (f s : Word) : Option (List Word × Mem) :=
  (callW p n "pn_at" [f, s + 1] m).bind fun c =>
  (callW p n "ps_at" [0, f, s + 10] c.2).bind fun x =>
  (callW p n "ps_at" [0, f, s + 13] x.2).bind fun y =>
  some ([g0 c.1, g0 x.1, g0 y.1], y.2)

theorem capsParts_spec (f s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "caps_parts" [f, s]
    ⦃fun r s' => LocEq s' s₀ ∧ capsPW p n s₀.mem f s = some ([g0 r, g1 r, g2 r], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "caps_parts")]
  simp only [callFn, capsParts]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pn_at", callW_spec p n "ps_at"] <;>
    finish (gen := 20) [capsPW, Option.bind_some, Option.bind_none]

/-- **The model of `promote_caps(f, s, d)`.** -/
def capsW (p : Prog) (n : Nat) (m : Mem) (f s d : Word) : Option Mem :=
  (callW p n "caps_parts" [f, s] m).bind fun r =>
  (callW p n "erec_cp" [d, s, 15] r.2).bind fun m₁ =>
  memK (callW p n "caps_wr" [d, g0 r.1, g1 r.1, g2 r.1] m₁.2)

theorem promoteCaps_spec (f s d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_caps" [f, s, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ capsW p n s₀.mem f s d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_caps")]
  simp only [callFn, promoteCapsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "caps_parts", callW_spec p n "caps_wr", callW_spec p n "erec_cp"] <;>
    finish (gen := 20) [capsW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `proj_a(f, q)`.** -/
def projAW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (List Word × Mem) :=
  (callW p n "pn_at" [f, q + 2] m).bind fun r6 =>
  (callW p n "ps_at" [0, f, q + 3] r6.2).bind fun r8 =>
  some ([g0 r6.1, g0 r8.1], r8.2)

theorem projA_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_a" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ projAW p n s₀.mem f q = some ([g0 r, g1 r], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "proj_a")]
  simp only [callFn, projA]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pn_at", callW_spec p n "ps_at"] <;>
    finish (gen := 20) [projAW, Option.bind_some, Option.bind_none]

/-- **The model of `proj_b(f, q)`.** -/
def projBW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (List Word × Mem) :=
  (callW p n "pn_at" [f, q + 6] m).bind fun r9 =>
  (callW p n "pl_at" [f, q + 8] r9.2).bind fun r10 =>
  (callW p n "ps_at" [2, f, q + 9] r10.2).bind fun r11 =>
  (callW p n "ps_at" [1, f, q + 11] r11.2).bind fun r12 =>
  some ([g0 r9.1, g0 r10.1, g0 r11.1, g0 r12.1], r12.2)

theorem projB_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_b" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧
      projBW p n s₀.mem f q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "proj_b")]
  simp only [callFn, projB]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pn_at", callW_spec p n "pl_at", callW_spec p n "ps_at"] <;>
    finish (gen := 20) [projBW, Option.bind_some, Option.bind_none]

/-- **The model of `promote_proj_table(f, p)`.** -/
def projW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "erec_alloc" [13] m).bind fun r5 =>
  (callW p n "proj_a" [f, q] r5.2).bind fun a =>
  (callW p n "proj_b" [f, q] a.2).bind fun b =>
  (callW p n "erec_cp" [g0 r5.1, q, 13] b.2).bind fun m₁ =>
  (callW p n "proj_wr" [g0 r5.1, g0 a.1, g1 a.1, g0 b.1, g1 b.1, g2 b.1, g3 b.1] m₁.2).bind fun w =>
  some (g0 r5.1, w.2)

theorem promoteProj_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_proj_table" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ projW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_proj_table")]
  simp only [callFn, promoteProjTableL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "proj_wr", callW_spec p n "proj_a", callW_spec p n "proj_b",
      callW_spec p n "erec_cp", callW_spec p n "erec_alloc"] <;>
    finish (gen := 20) [projW, memK_some, Option.bind_some, Option.bind_none]

/-! ## The `pci_*` arms -/

/-- **The model of `pci_mk(p, n, nm, q, l, t)`.** -/
def pciMkW (p : Prog) (n : Nat) (m : Mem) (q k nm qq l t : Word) : Option (Word × Mem) :=
  (callW p n "erec_alloc" [k] m).bind fun a =>
  (callW p n "erec_rd1" [q] a.2).bind fun r =>
  (callW p n "erec_wr1" [g0 a.1, g0 r.1] r.2).bind fun w =>
  (callW p n "cv_wr" [g0 a.1 + 1, nm, qq, l, t] w.2).bind fun z => some (g0 a.1, z.2)

theorem pciMk_spec (q k nm qq l t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pci_mk" [q, k, nm, qq, l, t]
    ⦃fun r s' => LocEq s' s₀ ∧ pciMkW p n s₀.mem q k nm qq l t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pci_mk")]
  simp only [callFn, pciMk]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_alloc", callW_spec p n "erec_rd1", callW_spec p n "erec_wr1",
      callW_spec p n "cv_wr"] <;>
    finish (gen := 20) [pciMkW, Option.bind_some, Option.bind_none]

/-- The `promote_cv` words as the arguments of `pci_mk`. -/
def pciMkC (p : Prog) (n : Nat) (m : Mem) (q k : Word) (c : List Word) : Option (Word × Mem) :=
  (callW p n "pci_mk" [q, k, g0 c, g1 c, g2 c, g3 c] m).bind fun d => some (g0 d.1, d.2)

/-- **The model of `pci_plain(f, q)`.** -/
def plainW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "promote_cv" [f, q + 1] m).bind fun c => pciMkC p n c.2 q 5 c.1

theorem pciPlain_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pci_plain" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ plainW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pci_plain")]
  simp only [callFn, pciPlain]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "promote_cv", callW_spec p n "pci_mk"] <;>
    finish (gen := 20) [plainW, pciMkC, Option.bind_some, Option.bind_none]

/-- **The model of `pci_defn(f, q)`.** -/
def defnW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd3" [q + 5] m).bind fun a =>
  (callW p n "promote_cv" [f, q + 1] a.2).bind fun c =>
  (callW p n "promote_e" [f, g0 a.1] c.2).bind fun x =>
  (pciMkC p n x.2 q 8 c.1).bind fun d =>
  (callW p n "erec_wr3" [d.1 + 5, g0 x.1, g1 a.1, g2 a.1] d.2).bind fun w => some (d.1, w.2)

theorem pciDefn_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pci_defn" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ defnW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pci_defn")]
  simp only [callFn, pciDefn]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd3", callW_spec p n "promote_cv", callW_spec p n "promote_e",
      callW_spec p n "pci_mk", callW_spec p n "erec_wr3"] <;>
    finish (gen := 20) [defnW, pciMkC, Option.bind_some, Option.bind_none]

/-- **The model of `pci_ind(f, q)`.** -/
def indW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "promote_cv" [f, q + 1] m).bind fun c =>
  (pciMkC p n c.2 q 20 c.1).bind fun d =>
  (callW p n "promote_caps" [f, q + 5, d.1 + 5] d.2).bind fun w => some (d.1, w.2)

theorem pciInd_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pci_ind" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ indW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pci_ind")]
  simp only [callFn, pciInd]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "promote_cv", callW_spec p n "pci_mk", callW_spec p n "promote_caps"] <;>
    finish (gen := 20) [indW, pciMkC, Option.bind_some, Option.bind_none]

/-- **The model of `pci_ctor(f, q)`.** -/
def ctorW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd2" [q + 5] m).bind fun a =>
  (callW p n "promote_cv" [f, q + 1] a.2).bind fun c =>
  (pciMkC p n c.2 q 7 c.1).bind fun d =>
  (callW p n "erec_wr2" [d.1 + 5, g0 a.1, g1 a.1] d.2).bind fun w => some (d.1, w.2)

theorem pciCtor_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pci_ctor" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ctorW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pci_ctor")]
  simp only [callFn, pciCtor]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd2", callW_spec p n "promote_cv", callW_spec p n "pci_mk",
      callW_spec p n "erec_wr2"] <;>
    finish (gen := 20) [ctorW, pciMkC, Option.bind_some, Option.bind_none]

/-- **The model of `rec_block(d5, w5, w6, l)`.** -/
def recBlockW (p : Prog) (n : Nat) (m : Mem) (d5 w5 w6 l : Word) : Option (Word × Mem) :=
  if 1152921504606846976 ≤ l then none else
  (callW p n "erec_alloc" [11 * l] m).bind fun r =>
  (callW p n "erec_wr4" [d5, w5, w6, g0 r.1, l] r.2).bind fun w => some (g0 r.1, w.2)

theorem recBlock_spec (d5 w5 w6 l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_block" [d5, w5, w6, l]
    ⦃fun r s' => LocEq s' s₀ ∧ recBlockW p n s₀.mem d5 w5 w6 l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "rec_block")]
  simp only [callFn, recBlock]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_alloc", callW_spec p n "erec_wr4"] <;>
    finish (gen := 20) [recBlockW, Option.bind_some, Option.bind_none]

/-- **The model of `pci_rec(f, q)`.** -/
def recW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd4" [q + 5] m).bind fun a =>
  (callW p n "promote_cv" [f, q + 1] a.2).bind fun c =>
  (pciMkC p n c.2 q 9 c.1).bind fun d =>
  (callW p n "rec_block" [d.1 + 5, g0 a.1, g1 a.1, g3 a.1] d.2).bind fun b =>
  (callW p n "promote_rules" [f, g2 a.1, g3 a.1, g0 b.1] b.2).bind fun w => some (d.1, w.2)

theorem pciRec_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pci_rec" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ recW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pci_rec")]
  simp only [callFn, pciRec]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd4", callW_spec p n "promote_cv", callW_spec p n "pci_mk",
      callW_spec p n "rec_block", callW_spec p n "promote_rules"] <;>
    finish (gen := 20) [recW, pciMkC, Option.bind_some, Option.bind_none]

/-! ## `promote_ci`, `promote_ci_list` -/

/-- The result of a `pci_*` arm as `promote_ci`'s answer. -/
def promoteArmK (p : Prog) (n : Nat) (f q : Word) (nm : FnName) (m : Mem) : Option (Word × Mem) :=
  (callW p n nm [f, q] m).bind fun d => some (g0 d.1, d.2)

/-- **The model of `promote_ci(f, q)`.** -/
def ciW (p : Prog) (n : Nat) (m : Mem) (f q : Word) : Option (Word × Mem) :=
  (callW p n "erec_rd1" [q] m).bind fun r =>
  if g0 r.1 = 0 ∨ g0 r.1 = 2 then promoteArmK p n f q "pci_plain" r.2
  else if g0 r.1 = 1 then promoteArmK p n f q "pci_defn" r.2
  else if g0 r.1 = 3 then promoteArmK p n f q "pci_ind" r.2
  else if g0 r.1 = 4 then promoteArmK p n f q "pci_ctor" r.2
  else if g0 r.1 = 5 then promoteArmK p n f q "pci_rec" r.2
  else none

theorem promoteCI_spec (f q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_ci" [f, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ciW p n s₀.mem f q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_ci")]
  simp only [callFn, promoteCIL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_rd1", callW_spec p n "pci_plain", callW_spec p n "pci_defn",
      callW_spec p n "pci_ind", callW_spec p n "pci_ctor", callW_spec p n "pci_rec"] <;>
    finish (gen := 20) [ciW, promoteArmK, Option.bind_some, Option.bind_none]

/-- **The model of `promote_ci_list(f, j, k)`.** -/
def ciListW (p : Prog) (n : Nat) (m : Mem) (f j k : Word) : Option Mem :=
  if k = 0 then some m
  else if (m.arr64 ECON).size ≤ j.toNat then none
  else (callW p n "promote_ci" [f, rdW (m.arr64 ECON) j] m).bind fun d =>
    if (d.2.arr64 ECON).size ≤ j.toNat then none
    else memK (callW p n "promote_ci_list" [f, j - 1, k - 1] (d.2.set64 ECON j (g0 d.1)))

theorem promoteCIList_spec (f j k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_ci_list" [f, j, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ ciListW p n s₀.mem f j k = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_ci_list")]
  simp only [callFn, promoteCIListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "promote_ci", callW_spec p n "promote_ci_list"] <;>
    finish (gen := 20) [ciListW, memK_some, Option.bind_some, Option.bind_none]

/-! ## `erase_installed`, `index_promoted`, `promote_new` -/

/-- **The model of `erase_installed(j, k)`.** -/
def eraseW (p : Prog) (n : Nat) (m : Mem) (j k : Word) : Option Mem :=
  if k = 0 then some m
  else if (m.arr64 ECON).size ≤ j.toNat then none
  else (callW p n "erec_rd1" [rdW (m.arr64 ECON) j + 1] m).bind fun w =>
    (callW p n "env_erase" [g0 w.1] w.2).bind fun z =>
    memK (callW p n "erase_installed" [j - 1, k - 1] z.2)

theorem eraseInstalled_spec (j k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erase_installed" [j, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ eraseW p n s₀.mem j k = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erase_installed")]
  simp only [callFn, eraseInstalledL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "erec_rd1", callW_spec p n "env_erase", callW_spec p n "erase_installed"] <;>
    finish (gen := 20) [eraseW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `index_promoted(c, j, k)`.** -/
def indexW (p : Prog) (n : Nat) (m : Mem) (c j k : Word) : Option Mem :=
  if k = 0 then some m
  else if (m.arr64 ECON).size ≤ j.toNat then none
  else (callW p n "erec_rd1" [rdW (m.arr64 ECON) j + 1] m).bind fun w =>
    (callW p n "env_row_set" [g0 w.1, c, rdW (m.arr64 ECON) j] w.2).bind fun z =>
    memK (callW p n "index_promoted" [c - 1, j - 1, k - 1] z.2)

theorem indexPromoted_spec (c j k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "index_promoted" [c, j, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ indexW p n s₀.mem c j k = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "index_promoted")]
  simp only [callFn, indexPromotedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "erec_rd1", callW_spec p n "env_row_set",
      callW_spec p n "index_promoted"] <;>
    finish (gen := 20) [indexW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `promote_new_consts(k, vis)`.** -/
def newCW (p : Prog) (n : Nat) (m₁ : Mem) (k vis : Word) : Option Mem :=
  if k = 0 then some m₁
  else if (m₁.arr64 CTL).size ≤ 128 then none
  else
  (callW p n "erase_installed" [rdW (m₁.arr64 CTL) 128 - 1,
      if rdW (m₁.arr64 CTL) 128 < k then rdW (m₁.arr64 CTL) 128 else k] m₁).bind fun r₁ =>
  (callW p n "promote_ci_list" [L.Ind.CWF, rdW (m₁.arr64 CTL) 128 - 1,
      if rdW (m₁.arr64 CTL) 128 < k then rdW (m₁.arr64 CTL) 128 else k] r₁.2).bind fun r₂ =>
  memK (callW p n "index_promoted" [vis, rdW (m₁.arr64 CTL) 128 - 1,
      if rdW (m₁.arr64 CTL) 128 < k then rdW (m₁.arr64 CTL) 128 else k] r₂.2)

theorem promoteNewConsts_spec (k vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_new_consts" [k, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ newCW p n s₀.mem k vis = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_new_consts")]
  simp only [callFn, promoteNewConstsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "erase_installed", callW_spec p n "promote_ci_list",
      callW_spec p n "index_promoted"] <;>
    finish (gen := 20) [newCW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `promote_proj_tables(f, j, k)`.** -/
def ptsW (p : Prog) (n : Nat) (m : Mem) (f j k : Word) : Option Mem :=
  if k = 0 then some m
  else (callW p n "tbl_at" [j] m).bind fun q =>
    (callW p n "promote_proj_table" [f, g0 q.1] q.2).bind fun d =>
    (callW p n "tbl_put" [j, g0 d.1] d.2).bind fun u =>
    memK (callW p n "promote_proj_tables" [f, j - 1, k - 1] u.2)

theorem promoteProjTables_spec (f j k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_proj_tables" [f, j, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ ptsW p n s₀.mem f j k = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_proj_tables")]
  simp only [callFn, promoteProjTablesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "tbl_at", callW_spec p n "promote_proj_table", callW_spec p n "tbl_put",
      callW_spec p n "promote_proj_tables"] <;>
    finish (gen := 20) [ptsW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `erase_installed_tables(j, k)`.** -/
def eraseTW (p : Prog) (n : Nat) (m : Mem) (j k : Word) : Option Mem :=
  if k = 0 then some m
  else (callW p n "tbl_at" [j] m).bind fun q =>
    (callW p n "erec_rd1" [g0 q.1 + 2] q.2).bind fun w =>
    (callW p n "tbl_row_set" [g0 w.1, 0] w.2).bind fun z =>
    memK (callW p n "erase_installed_tables" [j - 1, k - 1] z.2)

theorem eraseInstalledTables_spec (j k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erase_installed_tables" [j, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ eraseTW p n s₀.mem j k = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "erase_installed_tables")]
  simp only [callFn, eraseInstalledTablesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "tbl_at", callW_spec p n "erec_rd1", callW_spec p n "tbl_row_set",
      callW_spec p n "erase_installed_tables"] <;>
    finish (gen := 20) [eraseTW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `index_promoted_tables(j, k)`.** -/
def indexTW (p : Prog) (n : Nat) (m : Mem) (j k : Word) : Option Mem :=
  if k = 0 then some m
  else (callW p n "index_promoted_tables" [j - 1, k - 1] m).bind fun z₀ =>
    (callW p n "tbl_at" [j] z₀.2).bind fun q =>
    (callW p n "erec_rd1" [g0 q.1 + 2] q.2).bind fun w =>
    memK (callW p n "tbl_row_set" [g0 w.1, g0 q.1 + 1] w.2)

theorem indexPromotedTables_spec (j k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "index_promoted_tables" [j, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ indexTW p n s₀.mem j k = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "index_promoted_tables")]
  simp only [callFn, indexPromotedTablesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "tbl_at", callW_spec p n "erec_rd1", callW_spec p n "tbl_row_set",
      callW_spec p n "index_promoted_tables"] <;>
    finish (gen := 20) [indexTW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `promote_new_tables(kt)`.** -/
def newTW (p : Prog) (n : Nat) (m : Mem) (kt : Word) : Option Mem :=
  if kt = 0 then some m
  else (callW p n "tbl_cnt" [] m).bind fun c =>
    (callW p n "erase_installed_tables" [g0 c.1 - 1, if g0 c.1 < kt then g0 c.1 else kt] c.2).bind
      fun r₁ =>
    (callW p n "promote_proj_tables" [L.Ind.CWF, g0 c.1 - 1, if g0 c.1 < kt then g0 c.1 else kt]
      r₁.2).bind fun r₂ =>
    memK (callW p n "index_promoted_tables" [g0 c.1 - 1, if g0 c.1 < kt then g0 c.1 else kt] r₂.2)

theorem promoteNewTables_spec (kt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_new_tables" [kt]
    ⦃fun _ s' => LocEq s' s₀ ∧ newTW p n s₀.mem kt = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_new_tables")]
  simp only [callFn, promoteNewTablesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "tbl_cnt", callW_spec p n "erase_installed_tables",
      callW_spec p n "promote_proj_tables", callW_spec p n "index_promoted_tables"] <;>
    finish (gen := 20) [newTW, memK_some, Option.bind_some, Option.bind_none]

/-- **The model of `promote_new(k, kt, vis, fresh)`.** -/
def newW (p : Prog) (n : Nat) (m : Mem) (k kt vis fresh : Word) : Option Mem :=
  (if fresh ≠ 0 then (callW p n "promote_clear" [] m).bind fun r => some r.2 else some m).bind
    fun m₁ =>
  (callW p n "promote_new_consts" [k, vis] m₁).bind fun r₁ =>
  memK (callW p n "promote_new_tables" [kt] r₁.2)

theorem promoteNew_specW (k kt vis fresh : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_new" [k, kt, vis, fresh]
    ⦃fun _ s' => LocEq s' s₀ ∧ newW p n s₀.mem k kt vis fresh = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_new")]
  simp only [callFn, promoteNewL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "promote_clear", callW_spec p n "promote_new_consts",
      callW_spec p n "promote_new_tables"] <;>
    finish (gen := 20) [newW, memK_some, Option.bind_some, Option.bind_none]

end specs

end L.Arena
