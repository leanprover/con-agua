module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# L: worked examples

Two programs over the input buffer `IN`, each with a `vcgen` proof of its partial-correctness
spec against a pure Lean model, in the shape every translated function follows (see DESIGN.md,
"Proof recipe"):

* `find_byte(i, c)`: the first position `≥ i` holding byte `c`, or the length. A loop with an
  early `return`.
* `skip_braced(i, depth)` and `str_close(j)`: con-ron's `scan_fast.rs` functions of the same names
  (and con-leche's `skipBraced`/`strClose`), with a call from one to the other.
  The models `strCloseN`/`skipBracedN` are con-leche's functions with `Nat` positions in place of
  `USize`. `skipBraced_run` turns the triple into a statement about `run`.
* `histogram`: an executable smoke test of word-array loads and stores (no proof).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Examples

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `find_byte` -/

def findLoop : Stmt := lblk (i, c) {
  while i < len(IN.u8) {
    if IN.u8[i] == c { return i };
    i += 1
  }
}

/-- con-ron: none — an example program of L -/
def findByte : FunDecl := lfn (i, c) {
  ⟪findLoop⟫;
  return len(IN.u8)
}

/-- The model. -/
def findFrom (b : Array UInt8) (c : UInt8) (i : Nat) : Nat :=
  if h : i < b.size then if b[i] = c then i else findFrom b c (i + 1) else b.size
termination_by b.size - i

/-! One guarded equation per arm. The multi-pattern `findFrom b c i, b[i]` keeps `grind` from
unrolling the model further than the program has read. -/

theorem findFrom_hit (b : Array UInt8) (c : UInt8) (i : Nat) (h : i < b.size) (hc : b[i] = c) :
    findFrom b c i = i := by rw [findFrom]; simp [h, hc]

theorem findFrom_miss (b : Array UInt8) (c : UInt8) (i k : Nat) (hk : k = i + 1) (h : i < b.size)
    (hc : b[i] ≠ c) : findFrom b c i = findFrom b c k := by subst hk; rw [findFrom]; simp [h, hc]

theorem findFrom_end (b : Array UInt8) (c : UInt8) (i : Nat) (h : b.size ≤ i) :
    findFrom b c i = b.size := by rw [findFrom]; simp; omega

grind_pattern [lang_grind] findFrom_hit => findFrom b c i, b[i]
grind_pattern [lang_grind] findFrom_miss => findFrom b c i, b[i], findFrom b c k
grind_pattern [lang_grind] findFrom_end => findFrom b c i

section find
variable (p : Prog) (hp : p.lookup "find_byte" = some findByte)
    (b : Array UInt8) (hb : b.size < 2 ^ 64) (c : UInt8)
include hb

theorem findLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (h1 : s₀.loc 1 = c.toUInt64)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n findLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [(UInt64.ofNat b.size)] = [UInt64.ofNat (findFrom b c (s₀.loc 0).toNat)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := findLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ih] <;> finish

theorem findLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (h1 : s₀.loc 1 = c.toUInt64) (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) findLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [(UInt64.ofNat b.size)] = [UInt64.ofNat (findFrom b c (s₀.loc 0).toNat)]; ⊤⦄ :=
  Triple.step_exec (findLoop_spec p b hb c (n + 1) s₀ hm h1 hi)

include hp in
theorem findByte_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_byte" [i, c.toUInt64]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (findFrom b c i.toNat)]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, findByte]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalArgs, findLoop_step_spec p b hb c n] <;> finish

end find

/-- The program, as `#eval`-able code. -/
def findProg : Prog := [("find_byte", findByte)]

/- `"hello"` has its first `l` at 2; from 4 on there is none, so the answer is the length. -/
#guard (run findProg 100 "find_byte" [0, 'l'.toNat.toUInt64]
  { bytes := #["hello".toUTF8.data] }).toOption.map (·.1) == some [2]

#guard (run findProg 100 "find_byte" [4, 'l'.toNat.toUInt64]
  { bytes := #["hello".toUTF8.data] }).toOption.map (·.1) == some [5]

/-! ## `str_close` and `skip_braced`

Translated from con-ron `crates/con-ron-core/src/frontend/scan_fast.rs` (`str_close` :792,
`skip_braced` :1283); compare the Rust there line by line. -/

def strCloseLoop : Stmt := lblk (j, c) {
  while j < len(IN.u8) {
    c := IN.u8[j];
    if c == '"' {
      return j
    } else if c == '\\' {
      if j + 1 < len(IN.u8) {
        if IN.u8[j + 1] < 32 { return 0 };
        j += 2
      } else {
        return 0
      }
    } else if c < 32 {
      return 0
    } else {
      j += 1
    }
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:499-520 ConLeche.Frontend.strClose -/
@[l_impl ConLeche.Frontend.strClose]
def strClose : FunDecl := lfn (j) locals (c) {
  ⟪strCloseLoop⟫;
  return 0
}

def skipBracedLoop : Stmt := lblk (i, depth, c, e) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == '"' {
      e := call str_close(i + 1);
      if e == 0 { return 0 };
      i := e + 1
    } else if c == 10 {
      return 0
    } else if c == '{' || c == '[' {
      i += 1;
      depth += 1
    } else if c == '}' || c == ']' {
      if depth == 0 { return i + 1 };
      i += 1;
      depth -= 1
    } else {
      i += 1
    }
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:737-761 ConLeche.Frontend.skipBraced -/
@[l_impl ConLeche.Frontend.skipBraced]
def skipBraced : FunDecl := lfn (i, depth) locals (c, e) {
  ⟪skipBracedLoop⟫;
  return 0
}

def scanProg : Prog := [("str_close", strClose), ("skip_braced", skipBraced)]

#guard (run scanProg 1000 "skip_braced" [1, 0]
  { bytes := #["{\"a\":[1,{\"b\\\"\":2}]} x".toUTF8.data] }).toOption.map (·.1) == some [19]

/-! A word-array smoke test: `histogram` counts the bytes of `IN` into word array `HIST`. -/

/-- The histogram (a word array of length 256). -/
abbrev HIST : ArrId := 0

/-- con-ron: none — an example program of L -/
def histogram : FunDecl := lfn () locals (i, c) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    HIST.u64[c] := HIST.u64[c] + 1;
    i += 1
  };
  return HIST.u64['a']
}

#guard (run [("histogram", histogram)] 100 "histogram" []
  { bytes := #["banana".toUTF8.data], words := #[Array.replicate 256 0] }).toOption.map (·.1)
  == some [3]

/-- con-leche's `strClose` (`ConLeche/Frontend/Scan/Fast.lean`), with `Nat` positions. -/
def strCloseN (b : Array UInt8) (j : Nat) : Nat :=
  if h : j < b.size then
    if b[j] = 34 then j
    else if b[j] = 92 then
      if h2 : j + 1 < b.size then
        if b[j + 1] < 32 then 0 else strCloseN b (j + 2)
      else 0
    else if b[j] < 32 then 0
    else strCloseN b (j + 1)
  else 0
termination_by b.size - j

/-- con-leche's `skipBraced`, with `Nat` positions. -/
def skipBracedN (b : Array UInt8) (i : Nat) (depth : Nat) : Nat :=
  if h : i < b.size then
    if b[i] = 34 then
      let e := strCloseN b (i + 1)
      if e = 0 then 0
      else if i < e + 1 then skipBracedN b (e + 1) depth else 0
    else if b[i] = 10 then 0
    else if b[i] = 123 ∨ b[i] = 91 then skipBracedN b (i + 1) (depth + 1)
    else if b[i] = 125 ∨ b[i] = 93 then
      match depth with
      | 0 => i + 1
      | d + 1 => skipBracedN b (i + 1) d
    else skipBracedN b (i + 1) depth
  else 0
termination_by b.size - i

section strClose
variable (b : Array UInt8) (j : Nat)

theorem strCloseN_end (h : b.size ≤ j) : strCloseN b j = 0 := by
  rw [strCloseN]; simp; omega
theorem strCloseN_quote (h : j < b.size) (hc : b[j] = 34) : strCloseN b j = j := by
  rw [strCloseN]; simp [h, hc]
theorem strCloseN_esc_end (h : j < b.size) (hc : b[j] = 92) (h2 : b.size ≤ j + 1) :
    strCloseN b j = 0 := by
  rw [strCloseN]; simp [h, hc]; omega
theorem strCloseN_esc_ctrl (k : Nat) (hk : k = j + 1) (h : k < b.size) (hc : b[j] = 92)
    (hd : b[k] < 32) : strCloseN b j = 0 := by
  subst hk; rw [strCloseN]; simp [show j < b.size by omega, hc, h, hd]
theorem strCloseN_esc (k k' : Nat) (hk : k = j + 1) (hk' : k' = j + 2) (h : k < b.size)
    (hc : b[j] = 92) (hd : ¬b[k] < 32) : strCloseN b j = strCloseN b k' := by
  subst hk hk'; rw [strCloseN]; simp [show j < b.size by omega, hc, h, hd]
theorem strCloseN_ctrl (h : j < b.size) (h1 : b[j] ≠ 34) (h2 : b[j] ≠ 92) (h3 : b[j] < 32) :
    strCloseN b j = 0 := by
  rw [strCloseN]; simp [h, h1, h2, h3]
theorem strCloseN_other (k : Nat) (hk : k = j + 1) (h : j < b.size) (h1 : b[j] ≠ 34)
    (h2 : b[j] ≠ 92) (h3 : ¬b[j] < 32) : strCloseN b j = strCloseN b k := by
  subst hk; rw [strCloseN]; simp [h, h1, h2, h3]

grind_pattern [lang_grind] strCloseN_end => strCloseN b j
grind_pattern [lang_grind] strCloseN_quote => strCloseN b j, b[j]
grind_pattern [lang_grind] strCloseN_esc_end => strCloseN b j, b[j]
grind_pattern [lang_grind] strCloseN_esc_ctrl => strCloseN b j, b[j], b[k]
grind_pattern [lang_grind] strCloseN_esc => strCloseN b j, b[j], b[k], strCloseN b k'
grind_pattern [lang_grind] strCloseN_ctrl => strCloseN b j, b[j]
grind_pattern [lang_grind] strCloseN_other => strCloseN b j, b[j], strCloseN b k

/-- A nonzero answer is a position at or after `j`, inside the buffer. -/
theorem strCloseN_bounds (h : strCloseN b j ≠ 0) : j ≤ strCloseN b j ∧ strCloseN b j < b.size := by
  induction j using strCloseN.induct b <;> rw [strCloseN] at h ⊢ <;> grind

grind_pattern [lang_grind] strCloseN_bounds => strCloseN b j

end strClose

section skipBraced
variable (b : Array UInt8) (i d : Nat)

theorem skipBracedN_end (h : b.size ≤ i) : skipBracedN b i d = 0 := by
  rw [skipBracedN.eq_def]; simp; omega
theorem skipBracedN_str0 (k : Nat) (hk : k = i + 1) (h : i < b.size) (hc : b[i] = 34)
    (he : strCloseN b k = 0) : skipBracedN b i d = 0 := by
  subst hk; rw [skipBracedN.eq_def]; simp [h, hc, he]
theorem skipBracedN_str (k k' : Nat) (hk : k = i + 1) (hk' : k' = strCloseN b k + 1)
    (h : i < b.size) (hc : b[i] = 34) (he : strCloseN b k ≠ 0) :
    skipBracedN b i d = skipBracedN b k' d := by
  subst hk hk'
  have := strCloseN_bounds b (i + 1) he
  rw [skipBracedN.eq_def]; simp [h, hc, he]; omega
theorem skipBracedN_nl (h : i < b.size) (hc : b[i] = 10) : skipBracedN b i d = 0 := by
  rw [skipBracedN.eq_def]; simp [h, hc]
theorem skipBracedN_open (k d' : Nat) (hk : k = i + 1) (hd : d' = d + 1) (h : i < b.size)
    (hc : b[i] = 123 ∨ b[i] = 91) : skipBracedN b i d = skipBracedN b k d' := by
  subst hk hd; rw [skipBracedN.eq_def]; simp only [h, dite_true]; grind
theorem skipBracedN_close0 (h : i < b.size) (hc : b[i] = 125 ∨ b[i] = 93) :
    skipBracedN b i 0 = i + 1 := by
  rw [skipBracedN.eq_def]; simp only [h, dite_true]; grind
theorem skipBracedN_close (k d' : Nat) (hk : k = i + 1) (hd : d = d' + 1) (h : i < b.size)
    (hc : b[i] = 125 ∨ b[i] = 93) : skipBracedN b i d = skipBracedN b k d' := by
  subst hk hd; rw [skipBracedN.eq_def]; simp only [h, dite_true]; grind
theorem skipBracedN_other (k : Nat) (hk : k = i + 1) (h : i < b.size) (h1 : b[i] ≠ 34)
    (h2 : b[i] ≠ 10) (h3 : b[i] ≠ 123) (h4 : b[i] ≠ 91) (h5 : b[i] ≠ 125) (h6 : b[i] ≠ 93) :
    skipBracedN b i d = skipBracedN b k d := by
  subst hk; rw [skipBracedN.eq_def]; simp [h, h1, h2, h3, h4, h5, h6]

grind_pattern [lang_grind] skipBracedN_end => skipBracedN b i d
grind_pattern [lang_grind] skipBracedN_str0 => skipBracedN b i d, b[i], strCloseN b k
grind_pattern [lang_grind] skipBracedN_str => skipBracedN b i d, b[i], strCloseN b k, skipBracedN b k' d
grind_pattern [lang_grind] skipBracedN_nl => skipBracedN b i d, b[i]
grind_pattern [lang_grind] skipBracedN_open => skipBracedN b i d, b[i], skipBracedN b k d'
grind_pattern [lang_grind] skipBracedN_close0 => skipBracedN b i 0, b[i]
grind_pattern [lang_grind] skipBracedN_close => skipBracedN b i d, b[i], skipBracedN b k d'
grind_pattern [lang_grind] skipBracedN_other => skipBracedN b i d, b[i], skipBracedN b k d

end skipBraced

section scan
variable (p : Prog) (hp1 : p.lookup "str_close" = some strClose)
    (hp2 : p.lookup "skip_braced" = some skipBraced)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem strCloseLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n strCloseLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (strCloseN b (s₀.loc 0).toNat)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := strCloseLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ih] <;> finish

theorem strCloseLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) strCloseLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (strCloseN b (s₀.loc 0).toNat)]; ⊤⦄ :=
  Triple.step_exec (strCloseLoop_spec p b hb (n + 1) s₀ hm hj)

include hp1 in
@[refines ConLeche.Frontend.strClose]
theorem strClose_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j : Word)
    (hj : j.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_close" [j]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (strCloseN b j.toNat)]; ⊤⦄ := by
  rw [invoke_eq _ hp1]
  simp only [callFn, strClose]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, strCloseLoop_step_spec p b hb n] <;> finish

include hp1 in
theorem skipBracedLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) (hd : (s₀.loc 1).toNat + (b.size - (s₀.loc 0).toNat) < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    exec p n skipBracedLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (skipBracedN b (s₀.loc 0).toNat (s₀.loc 1).toNat)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := skipBracedLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih, strClose_spec p hp1 b hb n] <;> finish

include hp1 in
theorem skipBracedLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) (hd : (s₀.loc 1).toNat + (b.size - (s₀.loc 0).toNat) < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) skipBracedLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (skipBracedN b (s₀.loc 0).toNat (s₀.loc 1).toNat)]; ⊤⦄ :=
  Triple.step_exec (skipBracedLoop_spec p hp1 b hb (n + 1) s₀ hm hi hd)

include hp1 hp2 in
/-- The L `skip_braced` refines the model: if it returns, it returns `skipBracedN`. -/
@[refines ConLeche.Frontend.skipBraced]
theorem skipBraced_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i d : Word)
    (hi : i.toNat ≤ b.size) (hd : d.toNat + (b.size - i.toNat) < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "skip_braced" [i, d]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (skipBracedN b i.toNat d.toNat)]; ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, skipBraced]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, skipBracedLoop_step_spec p hp1 b hb n] <;> finish

end scan

/-- Partial correctness of the whole program: whenever `run` returns, it returns con-leche's
answer, and the memory is unchanged. -/
theorem skipBraced_run (b : Array UInt8) (hb : b.size < 2 ^ 64) (fuel : Nat) (i d : Word)
    (hi : i.toNat ≤ b.size) (hd : d.toNat + (b.size - i.toNat) < 2 ^ 64) (r : List Word) (m' : Mem)
    (h : run scanProg fuel "skip_braced" [i, d] { bytes := #[b] } = .ok (r, m')) :
    r = [UInt64.ofNat (skipBracedN b i.toNat d.toNat)] ∧ m' = { bytes := #[b] } := by
  simp only [run] at h
  cases hr : (invoke scanProg (exec scanProg fuel) "skip_braced" [i, d]).run
      { mem := { bytes := #[b] }, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok rs =>
    simp only [hr, Except.map] at h
    injection h with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have := M.of_run (P := fun s => s = { mem := { bytes := #[b] }, loc := Locals.init [] }) rfl hr
      (skipBraced_spec scanProg rfl rfl b hb fuel _ rfl i d hi hd)
    grind

/-! ## A callee that writes memory: the frame condition `LocEq`

`bump` stores into a word array, so its spec cannot post `s' = s₀`; it posts `LocEq s' s₀` (the
locals are the caller's), and the caller still reads its own `i` after the call. -/

abbrev W : ArrId := 0

/-- con-ron: none — an example program of L -/
def bump : FunDecl := lfn (i) { W.u64[0] := i; return 0 }
/-- con-ron: none — an example program of L -/
def bumpUser : FunDecl := lfn (i) locals (z) { z := call bump(i + 1); return i + z }

section bump
variable (p : Prog) (hp : p.lookup "bump" = some bump)
include hp

theorem bump_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "bump" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, bump]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n => sym only [lang_grind] => vcgen [exec, step, evalE, evalArgs, st64] <;> finish

theorem bumpUser_spec (hp2 : p.lookup "bump_user" = some bumpUser) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "bump_user" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [i]; ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, bumpUser]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalArgs, setLocs, setLoc, bump_spec p hp n] <;> finish

end bump

end L.Examples
