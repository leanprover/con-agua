module

meta import ConAgua.L.Semantics
meta import ConAgua.L.ByteClass
public import ConAgua.L.Notation
public import ConAgua.L.WriteSet
public import ConAgua.L.Records
public import ConAgua.L.ByteClass
import ConAgua.Census.Attr
import ConAgua.Front.Preserve
import ConAgua.L.Blocks
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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
    have hbang : ∀ x (h : x < b.size), b[x]! = b[x] := fun x h => getElem!_pos b x h
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
    j := scan!(IN.u8, j, len(IN.u8), strStopC);
    if j < len(IN.u8) {
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
    } else {
      return 0
    }
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

/-- A scan that stops before the end stops at a byte of the class. -/
theorem scanN_stop (b : Array UInt8) (c : List UInt8) (e : Nat) :
    ∀ i, scanN b c i e < e → c[(b[scanN b c i e]!).toNat]! ≠ 0 := by
  intro i
  induction i using scanN.induct b c e with
  | case1 i hi hc => intro _; rw [scanN_hit b c i e hi hc]; exact hc
  | case2 i hi hc ih => intro h; rw [scanN_miss b c i e hi (by simpa using hc)] at h ⊢; exact ih h
  | case3 i hi => intro h; rw [scanN_end b c i e hi] at h; omega

/-- `strCloseN` skips the plain bytes up to the next quote, backslash or control byte. -/
theorem strCloseN_scan (b : Array UInt8) : ∀ k j, b.size - j = k → j ≤ b.size →
    strCloseN b j = strCloseN b (scanN b strStopC j b.size) := by
  intro k
  induction k with
  | zero => intro j hk hj; rw [scanN_end b _ _ _ (by omega)]
  | succ k ih =>
    intro j hk hj
    have h : j < b.size := by omega
    have hg : b[j]! = b[j] := getElem!_pos b j h
    by_cases hc : b[j] = 34 ∨ b[j] = 92 ∨ b[j] < 32
    · rw [scanN_hit b _ _ _ h (by rw [hg]; exact (strStopC_mem _).mpr hc)]
    · rw [scanN_miss b _ _ _ h (by rw [hg]; exact Classical.byContradiction fun hn => hc ((strStopC_mem _).mp hn)),
        ← ih (j + 1) (by omega) (by omega)]
      simp only [not_or] at hc
      rw [strCloseN]; simp [h, hc.1, hc.2.1, show ¬ b[j] < 32 from hc.2.2]

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
    have hsrc : s₀.mem.src8 (.arr IN) = b := hm
    have hlen : s₀.mem.len8 IN = UInt64.ofNat b.size := by simp [Mem.len8, hm]
    have hlenN : (s₀.mem.len8 IN).toNat = b.size := by rw [hlen, UInt64.toNat_ofNat_of_lt' hb]
    have hbang : ∀ x (h : x < b.size), b[x]! = b[x] := fun x h => getElem!_pos b x h
    -- the scan, at this iteration's `j`
    have hscan : scanN (s₀.mem.src8 (.arr IN)) strStopC (s₀.loc 0).toNat (s₀.mem.len8 IN).toNat =
        scanN b strStopC (s₀.loc 0).toNat b.size := by rw [hsrc, hlenN]
    have hk_le : scanN b strStopC (s₀.loc 0).toNat b.size ≤ b.size :=
      scanN_le_end b strStopC _ _ hj
    have hk_eq : strCloseN b (s₀.loc 0).toNat = strCloseN b (scanN b strStopC (s₀.loc 0).toNat b.size) :=
      strCloseN_scan b _ _ rfl hj
    have hkN : (UInt64.ofNat (scanN b strStopC (s₀.loc 0).toNat b.size)).toNat =
        scanN b strStopC (s₀.loc 0).toNat b.size := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    have hk_st : ∀ h : scanN b strStopC (s₀.loc 0).toNat b.size < b.size,
        ¬ b[scanN b strStopC (s₀.loc 0).toNat b.size] = 34 →
        ¬ b[scanN b strStopC (s₀.loc 0).toNat b.size] = 92 →
        b[scanN b strStopC (s₀.loc 0).toNat b.size] < 32 := fun h h1 h2 => by
      have := (strStopC_mem _).mp (scanN_stop b strStopC _ _ h)
      rw [hbang _ h] at this; grind
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

/-! ## A callee that writes memory: the frame condition `LocEq`; global variables

`bump` writes memory (two global variables), so its spec cannot post `s' = s₀`; it posts
`LocEq s' s₀` (the locals are the caller's), and the caller still reads its own `i` after the
call. The caller also keeps a global of its own, `MARK`, across the call: that frame comes from
the program text (`closedG`, `Triple.gframe`), not from `bump`'s spec.

This was the first demonstration of global variables (lane `lfeat`): before, the three words were
`CTL.u64[0]`, `CTL.u64[1]`, `CTL.u64[2]` of a control array, and the specs needed a size
precondition, a hand-stated frame over `CTL` indices with `getElem` and `rdW` patterns, and array
lemmas in `finish` (DESIGN.md, "Global variables and records"). -/

/-- The last argument of `bump`. -/
abbrev LAST : GVar := ⟨0⟩
/-- The number of calls of `bump`. -/
abbrev CALLS : GVar := ⟨1⟩
/-- A global of `bump_user`'s. -/
abbrev MARK : GVar := ⟨2⟩

/-- con-ron: none — an example program of L -/
def bump : FunDecl := lfn (i) { LAST := i; CALLS += 1; return 0 }
/-- con-ron: none — an example program of L -/
def bumpUser : FunDecl := lfn (i) locals (z) {
  MARK := i;
  z := call bump(i + 1);
  return MARK + LAST + z
}

def bumpProg : Prog := [("bump", bump), ("bump_user", bumpUser)]

/-- `bump`'s global write set, from the text. -/
theorem bump_closed : closedG bumpProg [LAST, CALLS] ["bump"] = true := by decide

theorem bump_spec (p : Prog) (hp : p.lookup "bump" = some bump) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "bump" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [0] ∧ s'.mem.glob LAST = i ∧
      s'.mem.glob CALLS = s₀.mem.glob CALLS + 1; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, bump]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n => sym only [lang_grind] => vcgen [exec, step, evalE, evalArgs, setG] <;> finish

theorem bumpUser_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke bumpProg (exec bumpProg n) "bump_user" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [i + (i + 1)] ∧ s'.mem.glob CALLS = s₀.mem.glob CALLS + 1; ⊤⦄ := by
  rw [invoke_eq _ rfl]
  simp only [callFn, bumpUser]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalArgs, setLocs, setLoc, setG,
      Triple.gframe bump_closed (by decide) (bump_spec bumpProg rfl n _ _)] <;> finish

/-! ## Records

A node table of three-word records `[tag, a, b]` in word array 1. `node_mk(i, j, t, x)` writes
node `i`, reads field `a` of another node `j` and three fields of `i` back. The spec is about
`Mem.fld`, with no address arithmetic; `vcgen` gets `evalE_at` for the field addresses, and
`finish` decides the aliasing from `fld_set64` (different record, or different field: the old
value). Written with raw addresses (`NODES.u64[i * 3 + 1]`, the models over `rdW … (j * 3 + 1)`),
the same proof fails in `finish`: `grind` cannot refute `i * 3 + 1 = j * 3 + 1` in `UInt64`
without the injectivity lemma and bounds a store library proves by hand (`Schema.ad_inj`). -/

/-- The node table. -/
abbrev NODE : Record := ⟨1, 3⟩
abbrev NODE.tag : Field := ⟨0⟩
abbrev NODE.a : Field := ⟨1⟩
abbrev NODE.b : Field := ⟨2⟩

/-- con-ron: none — an example program of L -/
def nodeMk : FunDecl := lfn (i, j, t, x) locals (r) {
  NODE[i].tag := t;
  NODE[i].a := x;
  NODE[i].b := x + 1;
  r := NODE[j].a;
  return (NODE[i].tag, r, NODE[i].b)
}

theorem nodeMk_spec (p : Prog) (hp : p.lookup "node_mk" = some nodeMk) (n : Nat) (s₀ : St)
    (i j t x : Word) (hn : j ≠ i) (hi : i.toNat < 2 ^ 32) (hj : j.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "node_mk" [i, j, t, x]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [t, s₀.mem.fld NODE j NODE.a, x + 1] ∧
      s'.mem.fld NODE i NODE.a = x ∧ s'.mem.fld NODE j NODE.b = s₀.mem.fld NODE j NODE.b; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nodeMk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalE_at, evalArgs, setLoc, st64, ld64] <;> finish

def nodeProg : Prog := [("node_mk", nodeMk)]

end L.Examples
