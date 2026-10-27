module

meta import ConAgua.L.Semantics
public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.L.ByteClass
import ConAgua.Census.Attr
import ConAgua.L.Blocks
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# More `scan_fast.rs` leaf functions in L

Translations of further leaf functions of con-ron's `crates/con-ron-core/src/frontend/scan_fast.rs`
into `L`, each with a `Nat`-position model and a `vcgen` + `grind` spec proof in the style of
`ConAgua.L.Examples` (see DESIGN.md, "Proof recipe"). Order and citations follow the task list:
`is_ws`/`skip_ws` (`scan_fast.rs:96,107`), `skip_digits` (`:118`), `newline_from` (`:4072`),
`key_end` (`:149`), `num_end` (`:733`), `has_escape` (`:818`).

Unlike `str_close`/`skip_braced` (`L.Examples`), most of these loops never return from inside the
loop body (no early `return`): `is_ws`/`skip_digits` only ever fall through when the condition
goes false, so their loop spec states the POST-LOOP LOCAL directly (`s'.loc 0 = …`) rather than
`r.retOr d = …` — `retOr` is for propagating an early `return`, and there is none here.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Leaves

/-! ## `is_ws` / `skip_ws` (`scan_fast.rs:96,107`) -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:84-91 ConLeche.Frontend.skipWs -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:78-80 ConLeche.Frontend.isWs
@[l_impl ConLeche.Frontend.skipWs ConLeche.Frontend.isWs]
def skipWs : FunDecl := lfn (i) {
  if i < len(IN.u8) { i := scan!(IN.u8, i, len(IN.u8), notWsC) };
  return i
}

/-- The model: the first position `≥ i` whose byte is not JSON whitespace, or `b.size`. -/
def skipWsN (b : Array UInt8) (i : Nat) : Nat :=
  if h : i < b.size then
    if b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13 then skipWsN b (i + 1) else i
  else i
termination_by b.size - i

variable (b : Array UInt8) (i : Nat)

theorem skipWsN_ws (k : Nat) (hk : k = i + 1) (h : i < b.size)
    (hc : b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13) : skipWsN b i = skipWsN b k := by
  subst hk; rw [skipWsN]; simp [h, hc]
theorem skipWsN_other (h : i < b.size) (hc : ¬ (b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13)) :
    skipWsN b i = i := by rw [skipWsN]; simp [h, hc]
theorem skipWsN_end (h : b.size ≤ i) : skipWsN b i = i := by rw [skipWsN]; simp; omega

grind_pattern [lang_grind] skipWsN_ws => skipWsN b i, b[i], skipWsN b k
grind_pattern [lang_grind] skipWsN_other => skipWsN b i, b[i]
grind_pattern [lang_grind] skipWsN_end => skipWsN b i

/-- `skipWsN` is a `scan` to the first byte that is not whitespace. -/
theorem skipWsN_scan : ∀ k i, b.size - i = k → i ≤ b.size → skipWsN b i = scanN b notWsC i b.size := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    rw [skipWsN, scanN_end b _ _ _ (by omega)]; simp; omega
  | succ k ih =>
    intro i hk hi
    have h : i < b.size := by omega
    have hg : b[i]! = b[i] := getElem!_pos b i h
    by_cases hc : b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13
    · rw [skipWsN, dite_eq_left h, ite_eq_left hc, ih (i + 1) (by omega) (by omega), scanN_miss b _ _ _ h]
      rw [hg]; exact Classical.byContradiction fun hn => (notWsC_mem _).mp hn hc
    · rw [skipWsN, dite_eq_left h, ite_eq_right hc, scanN_hit b _ _ _ h]
      rw [hg]; exact (notWsC_mem _).mpr hc

section skipWs
variable (p : Prog) (hp : p.lookup "skip_ws" = some skipWs)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

include hp in
@[refines ConLeche.Frontend.skipWs]
theorem skipWs_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "skip_ws" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (skipWsN b i.toNat)]; ⊤⦄ := by
  rw [skipWsN_scan b _ i.toNat rfl hi, invoke_eq _ hp]
  simp only [callFn, skipWs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc]
    all_goals (simp_all [Mem.src8, Mem.len8, St.setLoc, Cmp.eval, Locals.init, Sig.retVal, Sig.retOr,
      Nat.mod_eq_of_lt hb])
    rename_i h
    have : b.size ≤ i.toNat := by
      have := UInt64.le_iff_toNat_le.mp h; simpa [UInt64.toNat_ofNat_of_lt' hb] using this
    rw [scanN_end _ _ _ _ (by omega)]; simp

end skipWs

/-! ## `skip_digits` (`scan_fast.rs:118`) -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:93-101 ConLeche.Frontend.skipDigits -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:82-82 ConLeche.Frontend.isDigit
@[l_impl ConLeche.Frontend.skipDigits ConLeche.Frontend.isDigit]
def skipDigits : FunDecl := lfn (i) {
  if i < len(IN.u8) { i := scan!(IN.u8, i, len(IN.u8), notDigitC) };
  return i
}

/-- The model: the position after the decimal digit run at `i`. -/
def skipDigitsN (b : Array UInt8) (i : Nat) : Nat :=
  if h : i < b.size then
    if 48 ≤ b[i] ∧ b[i] ≤ 57 then skipDigitsN b (i + 1) else i
  else i
termination_by b.size - i

variable (b : Array UInt8) (i : Nat)

theorem skipDigitsN_digit (k : Nat) (hk : k = i + 1) (h : i < b.size)
    (hc : 48 ≤ b[i] ∧ b[i] ≤ 57) : skipDigitsN b i = skipDigitsN b k := by
  subst hk; rw [skipDigitsN]; simp [h, hc]
theorem skipDigitsN_other (h : i < b.size) (hc : ¬ (48 ≤ b[i] ∧ b[i] ≤ 57)) :
    skipDigitsN b i = i := by rw [skipDigitsN]; simp [h, hc]
theorem skipDigitsN_end (h : b.size ≤ i) : skipDigitsN b i = i := by
  rw [skipDigitsN]; simp; omega

grind_pattern [lang_grind] skipDigitsN_digit => skipDigitsN b i, b[i], skipDigitsN b k
grind_pattern [lang_grind] skipDigitsN_other => skipDigitsN b i, b[i]
grind_pattern [lang_grind] skipDigitsN_end => skipDigitsN b i

/-- `skipDigitsN` is a `scan` to the first byte that is not a digit. -/
theorem skipDigitsN_scan : ∀ k i, b.size - i = k → i ≤ b.size →
    skipDigitsN b i = scanN b notDigitC i b.size := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    rw [skipDigitsN, scanN_end b _ _ _ (by omega)]; simp; omega
  | succ k ih =>
    intro i hk hi
    have h : i < b.size := by omega
    have hg : b[i]! = b[i] := getElem!_pos b i h
    by_cases hc : 48 ≤ b[i] ∧ b[i] ≤ 57
    · rw [skipDigitsN, dite_eq_left h, ite_eq_left hc, ih (i + 1) (by omega) (by omega), scanN_miss b _ _ _ h]
      rw [hg]; exact Classical.byContradiction fun hn => (notDigitC_mem _).mp hn hc
    · rw [skipDigitsN, dite_eq_left h, ite_eq_right hc, scanN_hit b _ _ _ h]
      rw [hg]; exact (notDigitC_mem _).mpr hc

/-- A nonzero advance means `i` was in bounds (used by `num_end`, which reads `b[i]` once it
knows `skipDigitsN b i ≠ i`). -/
theorem skipDigitsN_bounds (h : skipDigitsN b i ≠ i) : i < b.size ∧ i < skipDigitsN b i := by
  induction i using skipDigitsN.induct b with
  | case1 i h' hc ih => rw [skipDigitsN] at h ⊢; simp [h', hc] at h ⊢; grind
  | case2 i h' hc => rw [skipDigitsN] at h; simp [h', hc] at h
  | case3 i h' => rw [skipDigitsN] at h; simp [h'] at h

grind_pattern [lang_grind] skipDigitsN_bounds => skipDigitsN b i

/-- `skipDigitsN` never walks past the end of the array: needed (beyond `skipDigitsN_bounds`,
which only fires once the position moved) for the `e = i` branch of `num_end`, where the model's
answer is `i` itself, bounded by `hi`. -/
theorem skipDigitsN_le (h : i ≤ b.size) : skipDigitsN b i ≤ b.size := by
  induction i using skipDigitsN.induct b with
  | case1 i h' hc ih => rw [skipDigitsN]; simp [h', hc]; omega
  | case2 i h' hc => rw [skipDigitsN]; simp [h', hc]; omega
  | case3 i h' => rw [skipDigitsN]; simp [h']; omega

grind_pattern [lang_grind] skipDigitsN_le => skipDigitsN b i

section skipDigits
variable (p : Prog) (hp : p.lookup "skip_digits" = some skipDigits)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

include hp in
@[refines ConLeche.Frontend.skipDigits]
theorem skipDigits_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "skip_digits" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (skipDigitsN b i.toNat)]; ⊤⦄ := by
  rw [skipDigitsN_scan b _ i.toNat rfl hi, invoke_eq _ hp]
  simp only [callFn, skipDigits]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc]
    all_goals (simp_all [Mem.src8, Mem.len8, St.setLoc, Cmp.eval, Locals.init, Sig.retVal, Sig.retOr,
      Nat.mod_eq_of_lt hb])
    rename_i h
    have : b.size ≤ i.toNat := by
      have := UInt64.le_iff_toNat_le.mp h; simpa [UInt64.toNat_ofNat_of_lt' hb] using this
    rw [scanN_end _ _ _ _ (by omega)]; simp

end skipDigits

/-! ## `newline_from` (`scan_fast.rs:4072`) -/

def newlineFromLoop : Stmt := lblk (k) {
  while k < len(IN.u8) {
    if IN.u8[k] == 10 { return 1 };
    k += 1
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2601-2610 ConLeche.Frontend.newlineFrom -/
@[l_impl ConLeche.Frontend.newlineFrom]
def newlineFrom : FunDecl := lfn (k) { ⟪newlineFromLoop⟫; return 0 }

/-- The model: `1` if there is a newline at or after `i`, else `0`. -/
def newlineFromN (b : Array UInt8) (i : Nat) : Nat :=
  if h : i < b.size then (if b[i] = 10 then 1 else newlineFromN b (i + 1)) else 0
termination_by b.size - i

variable (b : Array UInt8) (i : Nat)

theorem newlineFromN_hit (h : i < b.size) (hc : b[i] = 10) : newlineFromN b i = 1 := by
  rw [newlineFromN]; simp [h, hc]
theorem newlineFromN_miss (k : Nat) (hk : k = i + 1) (h : i < b.size) (hc : b[i] ≠ 10) :
    newlineFromN b i = newlineFromN b k := by subst hk; rw [newlineFromN]; simp [h, hc]
theorem newlineFromN_end (h : b.size ≤ i) : newlineFromN b i = 0 := by
  rw [newlineFromN]; simp; omega

grind_pattern [lang_grind] newlineFromN_hit => newlineFromN b i, b[i]
grind_pattern [lang_grind] newlineFromN_miss => newlineFromN b i, b[i], newlineFromN b k
grind_pattern [lang_grind] newlineFromN_end => newlineFromN b i

section newlineFrom
variable (p : Prog) (hp : p.lookup "newline_from" = some newlineFrom)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem newlineFromLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n newlineFromLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (newlineFromN b (s₀.loc 0).toNat)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := newlineFromLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ih] <;> finish

include hp in
@[refines ConLeche.Frontend.newlineFrom]
theorem newlineFrom_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "newline_from" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (newlineFromN b i.toNat)]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, newlineFrom]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, fun s₀ hm hi => Triple.step_exec (newlineFromLoop_spec p b hb (n + 1) s₀ hm hi)] <;> finish

end newlineFrom

/-! ## `key_end` (`scan_fast.rs:149`) -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:133-146 ConLeche.Frontend.keyEnd -/
@[l_impl ConLeche.Frontend.keyEnd]
def keyEnd : FunDecl := lfn (j) locals (c) {
  if len(IN.u8) <= j { return 0 };
  j := scan!(IN.u8, j, len(IN.u8), strStopC);
  if j < len(IN.u8) { if IN.u8[j] == 34 { return j } };
  return 0
}

/-- The model: the closing quote of the key whose contents start at `j`, or `0`. -/
def keyEndN (b : Array UInt8) (j : Nat) : Nat :=
  if h : j < b.size then
    if b[j] = 34 then j
    else if b[j] < 32 ∨ b[j] = 92 then 0
    else keyEndN b (j + 1)
  else 0
termination_by b.size - j

variable (b : Array UInt8) (j : Nat)

theorem keyEndN_quote (h : j < b.size) (hc : b[j] = 34) : keyEndN b j = j := by
  rw [keyEndN]; simp [h, hc]
theorem keyEndN_ctrl (h : j < b.size) (h1 : b[j] ≠ 34) (h2 : b[j] < 32 ∨ b[j] = 92) :
    keyEndN b j = 0 := by rw [keyEndN]; simp [h, h1, h2]
theorem keyEndN_other (k : Nat) (hk : k = j + 1) (h : j < b.size) (h1 : b[j] ≠ 34)
    (h2 : ¬ (b[j] < 32 ∨ b[j] = 92)) : keyEndN b j = keyEndN b k := by
  subst hk; rw [keyEndN]; simp [h, h1, h2]
theorem keyEndN_end (h : b.size ≤ j) : keyEndN b j = 0 := by rw [keyEndN]; simp; omega

grind_pattern [lang_grind] keyEndN_quote => keyEndN b j, b[j]
grind_pattern [lang_grind] keyEndN_ctrl => keyEndN b j, b[j]
grind_pattern [lang_grind] keyEndN_other => keyEndN b j, b[j], keyEndN b k
grind_pattern [lang_grind] keyEndN_end => keyEndN b j

/-- `keyEndN` is a `scan` to the first quote, backslash or control byte. -/
theorem keyEndN_scan : ∀ k j, b.size - j = k → j ≤ b.size →
    keyEndN b j = if scanN b strStopC j b.size < b.size ∧ b[scanN b strStopC j b.size]! = 34 then
      scanN b strStopC j b.size else 0 := by
  intro k
  induction k with
  | zero =>
    intro j hk hj
    have h1 : ¬ j < b.size := by omega
    rw [keyEndN, scanN_end b _ _ _ (by omega), dite_eq_right h1, ite_eq_right (by omega)]
  | succ k ih =>
    intro j hk hj
    have h : j < b.size := by omega
    have hg : b[j]! = b[j] := getElem!_pos b j h
    have hcls : strStopC[(b[j]!).toNat]! ≠ 0 ↔ (b[j] = 34 ∨ b[j] = 92 ∨ b[j] < 32) := by
      rw [hg]; exact strStopC_mem _
    by_cases hq : b[j] = 34
    · rw [keyEndN, dite_eq_left h, ite_eq_left hq, scanN_hit b _ _ _ h (hcls.mpr (.inl hq))]
      simp [h, hq]
    · by_cases hc : b[j] < 32 ∨ b[j] = 92
      · rw [keyEndN, dite_eq_left h, ite_eq_right hq, ite_eq_left hc,
          scanN_hit b _ _ _ h (hcls.mpr (by rcases hc with hc | hc <;> simp [hc]))]
        simp [h, hq]
      · rw [keyEndN, dite_eq_left h, ite_eq_right hq, ite_eq_right hc, ih (j + 1) (by omega) (by omega),
          scanN_miss b _ _ _ h (by
            have : ¬ (b[j] = 34 ∨ b[j] = 92 ∨ b[j] < 32) := by
              simp only [not_or] at hc ⊢; exact ⟨hq, hc.2, hc.1⟩
            exact Classical.byContradiction fun hn => this (hcls.mp hn))]

section keyEnd
variable (p : Prog) (hp : p.lookup "key_end" = some keyEnd)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

include hp in
@[refines ConLeche.Frontend.keyEnd]
theorem keyEnd_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j : Word)
    (hj : j.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_end" [j]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (keyEndN b j.toNat)]; ⊤⦄ := by
  rw [keyEndN_scan b _ j.toNat rfl hj, invoke_eq _ hp]
  simp only [callFn, keyEnd]
  have hsc := scanN_le_end b strStopC j.toNat b.size hj
  have hs1 : scanN b strStopC j.toNat b.size < 2 ^ 64 := by omega
  have h34 : ∀ x : UInt8, x.toUInt64 = 34 ↔ x = 34 := by decide
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8]
    all_goals (simp_all [Mem.src8, Mem.len8, St.setLoc, Cmp.eval, Locals.init, Sig.retVal, Sig.retOr, Nat.mod_eq_of_lt hs1, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' hb])
    · rw [scanN_end _ _ _ _ (by omega), ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right (by omega)]; rfl

end keyEnd

/-! ## `has_escape` (`scan_fast.rs:818`) -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:522-531 ConLeche.Frontend.hasEscape -/
@[l_impl ConLeche.Frontend.hasEscape]
def hasEscape : FunDecl := lfn (j, e) {
  if len(IN.u8) < e { e := len(IN.u8) };
  if e <= j { return 0 };
  j := scan!(IN.u8, j, e, bslashC);
  if j < e { return 1 };
  return 0
}

/-- The model: `1` if the string body `[j, e)` contains a backslash, else `0`. -/
def hasEscapeN (b : Array UInt8) (j e : Nat) : Nat :=
  if h : j < b.size then
    if j < e then (if b[j] = 92 then 1 else hasEscapeN b (j + 1) e) else 0
  else 0
termination_by b.size - j

variable (b : Array UInt8) (j e : Nat)

theorem hasEscapeN_hit (h : j < b.size) (hlt : j < e) (hc : b[j] = 92) : hasEscapeN b j e = 1 := by
  rw [hasEscapeN]; simp [h, hlt, hc]
theorem hasEscapeN_miss (k : Nat) (hk : k = j + 1) (h : j < b.size) (hlt : j < e) (hc : b[j] ≠ 92) :
    hasEscapeN b j e = hasEscapeN b k e := by subst hk; rw [hasEscapeN]; simp [h, hlt, hc]
theorem hasEscapeN_past (h : j < b.size) (hge : e ≤ j) : hasEscapeN b j e = 0 := by
  rw [hasEscapeN]; simp [h]; omega
theorem hasEscapeN_end (h : b.size ≤ j) : hasEscapeN b j e = 0 := by rw [hasEscapeN]; simp; omega

grind_pattern [lang_grind] hasEscapeN_hit => hasEscapeN b j e, b[j]
grind_pattern [lang_grind] hasEscapeN_miss => hasEscapeN b j e, b[j], hasEscapeN b k e
grind_pattern [lang_grind] hasEscapeN_past => hasEscapeN b j e
grind_pattern [lang_grind] hasEscapeN_end => hasEscapeN b j e

/-- `hasEscapeN` is a `scan` to the first backslash before `min e b.size`. -/
theorem hasEscapeN_scan : ∀ k j, min e b.size - j = k → j ≤ min e b.size →
    hasEscapeN b j e = if scanN b bslashC j (min e b.size) < min e b.size then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro j hk hj
    rw [scanN_end b _ _ _ (by omega), ite_eq_right (by omega)]
    by_cases h1 : j < b.size
    · rw [hasEscapeN, dite_eq_left h1, ite_eq_right (by omega)]
    · rw [hasEscapeN, dite_eq_right h1]
  | succ k ih =>
    intro j hk hj
    have h : j < b.size := by omega
    have hje : j < e := by omega
    have hg : b[j]! = b[j] := getElem!_pos b j h
    have hcls : bslashC[(b[j]!).toNat]! ≠ 0 ↔ b[j] = 92 := by
      rw [hg]; exact bslashC_mem _
    by_cases hq : b[j] = 92
    · rw [hasEscapeN, dite_eq_left h, ite_eq_left hje, ite_eq_left hq, scanN_hit b _ _ _ (by omega) (hcls.mpr hq)]
      simp; omega
    · rw [hasEscapeN, dite_eq_left h, ite_eq_left hje, ite_eq_right hq, ih (j + 1) (by omega) (by omega),
        scanN_miss b _ _ _ (by omega) (Classical.byContradiction fun hn => hq (hcls.mp hn))]

/-- `hasEscapeN` for every `j`: nothing past `min e b.size`. -/
theorem hasEscapeN_eq (j e : Nat) : hasEscapeN b j e =
    if j < min e b.size then (if scanN b bslashC j (min e b.size) < min e b.size then 1 else 0) else 0 := by
  by_cases h : j ≤ min e b.size
  · rw [hasEscapeN_scan b e _ j rfl h]
    by_cases h' : j < min e b.size
    · rw [ite_eq_left h']
    · rw [ite_eq_right h', scanN_end _ _ _ _ h', ite_eq_right h']
  · rw [ite_eq_right (by omega), hasEscapeN]
    split
    · rw [ite_eq_right (by omega)]
    · rfl

section hasEscape
variable (p : Prog) (hp : p.lookup "has_escape" = some hasEscape)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

include hp in
@[refines ConLeche.Frontend.hasEscape]
theorem hasEscape_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e : Word)
    (hj : j.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "has_escape" [j, e]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (hasEscapeN b j.toNat e.toNat)]; ⊤⦄ := by
  rw [hasEscapeN_eq b j.toNat e.toNat, invoke_eq _ hp]
  simp only [callFn, hasEscape]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hs1 := scanN_le_end b bslashC j.toNat b.size
    have hs2 := scanN_le_end b bslashC j.toNat e.toNat
    have he := e.toNat_lt
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc]
    all_goals (simp_all [Mem.src8, Mem.len8, St.setLoc, Cmp.eval, Locals.init, Sig.retVal, Sig.retOr, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hb])
    all_goals (first
      | (have := hs1 (by omega); rw [Nat.mod_eq_of_lt (by omega)] at *; (try simp only [Nat.min_def] at *);
         split <;> (try split) <;> (try split) <;> (try simp_all) <;> omega)
      | (have := hs2 (by omega); rw [Nat.mod_eq_of_lt (by omega)] at *; (try simp only [Nat.min_def] at *);
         split <;> (try split) <;> (try split) <;> (try simp_all) <;> omega)
      | ((try simp only [Nat.min_def] at *); split <;> (try split) <;> (try split) <;> (try simp_all) <;> omega))

end hasEscape

/-! ## `num_end` (`scan_fast.rs:733`)

No loop: a call to `skip_digits` and two comparisons. -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:480-491 ConLeche.Frontend.numEnd -/
@[l_impl ConLeche.Frontend.numEnd]
def numEnd : FunDecl := lfn (i) locals (e) {
  e := call skip_digits(i);
  if e == i { return i }
  else if (IN.u8[i] == 48 && e != i + 1) { return i }
  else { return e }
}

/-- The model, following con-leche's `numEnd` (`byteAt`'s "0 past the end" via `Array.getD`,
since `e ≠ i` already proves `i` in bounds — `skipDigitsN_bounds` — so the L side's direct read
`IN.u8[i]` never actually needs it, but the model does not need the bound either way). -/
def numEndN (b : Array UInt8) (i : Nat) : Nat :=
  let e := skipDigitsN b i
  if e = i then i
  else if b.getD i 0 = 48 ∧ e ≠ i + 1 then i else e

attribute [local lang_grind] numEndN

section numEnd
variable (p : Prog) (hp1 : p.lookup "skip_digits" = some skipDigits)
    (hp2 : p.lookup "num_end" = some numEnd)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

include hp1 hp2 in
@[refines ConLeche.Frontend.numEnd]
theorem numEnd_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "num_end" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (numEndN b i.toNat)]; ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, numEnd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hgetD : ∀ (k : Nat) (hk : k < b.size), b.getD k 0 = b[k]'hk := by
      intro k hk; simp [Array.getD, hk]
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, skipDigits_spec p hp1 b hb n] <;> finish

end numEnd

end L.Scan.Leaves
