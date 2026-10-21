module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
meta import ConAgua.L.Semantics

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

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `is_ws` / `skip_ws` (`scan_fast.rs:96,107`) -/

/-- Rust's own loop, `while i < b.len() && is_ws(b[i]) { i += 1 }`, with `is_ws` inlined. -/
def skipWsLoop : Stmt := lblk (i) {
  while i < len(IN.u8) && (IN.u8[i] == 32 || IN.u8[i] == 9 || IN.u8[i] == 13) { i += 1 }
}

def skipWs : FunDecl := lfn (i) { ⟪skipWsLoop⟫; return i }

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

section skipWs
variable (p : Prog) (hp : p.lookup "skip_ws" = some skipWs)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem skipWsLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n skipWsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 0 = UInt64.ofNat (skipWsN b (s₀.loc 0).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := skipWsLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish

theorem skipWsLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) skipWsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 0 = UInt64.ofNat (skipWsN b (s₀.loc 0).toNat); ⊤⦄ :=
  Triple.step_exec (skipWsLoop_spec p b hb (n + 1) s₀ hm hi)

include hp in
theorem skipWs_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "skip_ws" [i]
    ⦃fun r s' => s' = s₀ ∧ r = UInt64.ofNat (skipWsN b i.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, skipWs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, skipWsLoop_step_spec p b hb n] <;> finish

end skipWs

/-! ## `skip_digits` (`scan_fast.rs:118`) -/

def skipDigitsLoop : Stmt := lblk (i) {
  while i < len(IN.u8) && 48 <= IN.u8[i] && IN.u8[i] <= 57 { i += 1 }
}

def skipDigits : FunDecl := lfn (i) { ⟪skipDigitsLoop⟫; return i }

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

theorem skipDigitsLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n skipDigitsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 0 = UInt64.ofNat (skipDigitsN b (s₀.loc 0).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := skipDigitsLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish

theorem skipDigitsLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) skipDigitsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 0 = UInt64.ofNat (skipDigitsN b (s₀.loc 0).toNat); ⊤⦄ :=
  Triple.step_exec (skipDigitsLoop_spec p b hb (n + 1) s₀ hm hi)

include hp in
theorem skipDigits_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "skip_digits" [i]
    ⦃fun r s' => s' = s₀ ∧ r = UInt64.ofNat (skipDigitsN b i.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, skipDigits]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, skipDigitsLoop_step_spec p b hb n] <;> finish

end skipDigits

/-! ## `newline_from` (`scan_fast.rs:4072`) -/

def newlineFromLoop : Stmt := lblk (k) {
  while k < len(IN.u8) {
    if IN.u8[k] == 10 { return 1 };
    k += 1
  }
}

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
      r.retOr 0 = UInt64.ofNat (newlineFromN b (s₀.loc 0).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := newlineFromLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish

theorem newlineFromLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) newlineFromLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr 0 = UInt64.ofNat (newlineFromN b (s₀.loc 0).toNat); ⊤⦄ :=
  Triple.step_exec (newlineFromLoop_spec p b hb (n + 1) s₀ hm hi)

include hp in
theorem newlineFrom_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "newline_from" [i]
    ⦃fun r s' => s' = s₀ ∧ r = UInt64.ofNat (newlineFromN b i.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, newlineFrom]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, newlineFromLoop_step_spec p b hb n] <;> finish

end newlineFrom

/-! ## `key_end` (`scan_fast.rs:149`) -/

def keyEndLoop : Stmt := lblk (j, c) {
  while j < len(IN.u8) {
    c := IN.u8[j];
    if c == '"' { return j }
    else if c < 32 || c == 92 { return 0 }
    else { j += 1 }
  }
}

def keyEnd : FunDecl := lfn (j) locals (c) { ⟪keyEndLoop⟫; return 0 }

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

section keyEnd
variable (p : Prog) (hp : p.lookup "key_end" = some keyEnd)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem keyEndLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n keyEndLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr 0 = UInt64.ofNat (keyEndN b (s₀.loc 0).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := keyEndLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish

theorem keyEndLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) keyEndLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr 0 = UInt64.ofNat (keyEndN b (s₀.loc 0).toNat); ⊤⦄ :=
  Triple.step_exec (keyEndLoop_spec p b hb (n + 1) s₀ hm hj)

include hp in
theorem keyEnd_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j : Word)
    (hj : j.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_end" [j]
    ⦃fun r s' => s' = s₀ ∧ r = UInt64.ofNat (keyEndN b j.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyEnd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, keyEndLoop_step_spec p b hb n] <;> finish

end keyEnd

/-! ## `has_escape` (`scan_fast.rs:818`) -/

def hasEscapeLoop : Stmt := lblk (j, e) {
  while j < len(IN.u8) && j < e {
    if IN.u8[j] == 92 { return 1 };
    j += 1
  }
}

def hasEscape : FunDecl := lfn (j, e) { ⟪hasEscapeLoop⟫; return 0 }

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

section hasEscape
variable (p : Prog) (hp : p.lookup "has_escape" = some hasEscape)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem hasEscapeLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n hasEscapeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr 0 = UInt64.ofNat (hasEscapeN b (s₀.loc 0).toNat (s₀.loc 1).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := hasEscapeLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish

theorem hasEscapeLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) hasEscapeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr 0 = UInt64.ofNat (hasEscapeN b (s₀.loc 0).toNat (s₀.loc 1).toNat); ⊤⦄ :=
  Triple.step_exec (hasEscapeLoop_spec p b hb (n + 1) s₀ hm hj)

include hp in
theorem hasEscape_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e : Word)
    (hj : j.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "has_escape" [j, e]
    ⦃fun r s' => s' = s₀ ∧ r = UInt64.ofNat (hasEscapeN b j.toNat e.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, hasEscape]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, hasEscapeLoop_step_spec p b hb n] <;> finish

end hasEscape

/-! ## `num_end` (`scan_fast.rs:733`)

No loop: a call to `skip_digits` and two comparisons. -/

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
theorem numEnd_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "num_end" [i]
    ⦃fun r s' => s' = s₀ ∧ r = UInt64.ofNat (numEndN b i.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, numEnd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hgetD : ∀ (k : Nat) (hk : k < b.size), b.getD k 0 = b[k]'hk := by
      intro k hk; simp [Array.getD, hk]
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, skipDigits_spec p hp1 b hb n] <;> finish

end numEnd

end L.Scan.Leaves

