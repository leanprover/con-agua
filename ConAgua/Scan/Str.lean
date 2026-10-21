module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.L.Examples
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Utf8
public import ConAgua.Scan.Common
meta import ConAgua.L.Semantics
meta import ConAgua.L.Examples
meta import ConAgua.Scan.Leaves
meta import ConAgua.Scan.Utf8

@[expose] public section

/-!
# `scan_string` (`scan_fast.rs:1087`), validating only

Rust's `scan_string(b, i)` returns the string's code points; the validator returns only the
position after the closing quote, or `0`. The parts:

* `utf8_valid(k, n)`: `1` if `[k, n)` is valid UTF-8, else `0`. It is Rust's `utf8_decode`
  without the output vector: the same loop over `utf8_char` (`ConAgua.Scan.Utf8`).
* `byte_in(k, e)`, `hex_val(c)`, `hex4(j, e)`, `hex3(j, e)`: Rust's `byte_at` (on the string
  body, which ends at `e`: con-leche hands `unescape` the body sliced out), `hex_val`, `hex4`,
  `hex3`; an `Option<u32>` is the two words `(ok, value)`.
* `unescape(j, e)`: `1` if the body `[j, e)` with escapes is a valid string, else `0`. Rust
  (and con-leche) collect the unescaped bytes and validate them with `utf8_decode`
  (`String.fromUTF8?`) at the end. The validator stores nothing: it checks each escape as Rust
  does, and validates each maximal run of raw bytes between escapes on its own
  (`utf8_valid(r, j)`, `r` the start of the run). An escape contributes the UTF-8 of one code
  point, which begins with a lead byte, so the collected bytes are valid exactly when every raw
  run is (`ConAgua.Scan.StrLink`).
* `scan_string(i)`.

The models compute with words, as the L code does.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Str

open L.Scan.Utf8 (byteW utf8CharN)
open L.Scan.Leaves (hasEscapeN)
open L.Examples (strCloseN)

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `utf8_valid` -/

def utf8ValidLoop : Stmt := lblk (k, n, cp, l) {
  while k < n {
    (cp, l) := call utf8_char(k, n);
    if l == 0 { return 0 };
    k += l
  }
}

def utf8Valid : FunDecl := lfn (k, n) locals (cp, l) {
  ⟪utf8ValidLoop⟫;
  return 1
}

/-- `1` if the bytes `[k, n)` are valid UTF-8, else `0`: `utf8LoopN` without the output. -/
def utf8ValidN (b : Array UInt8) (k n : Word) : Word :=
  if k < n then
    if (utf8CharN b k n).2 = 0 then 0
    else if k < k + (utf8CharN b k n).2 then utf8ValidN b (k + (utf8CharN b k n).2) n
    else 0
  else 1
termination_by n.toNat - k.toNat
decreasing_by
  rename_i h1 _ h2
  rw [UInt64.lt_iff_toNat_lt] at h1 h2
  omega

section
variable (b : Array UInt8) (k n : Word)

/-! One guarded equation per arm (DESIGN.md, "Proof recipe"), as for `utf8LoopN`. -/

theorem utf8ValidN_end (h : ¬ k < n) : utf8ValidN b k n = 1 := by rw [utf8ValidN]; simp [h]
theorem utf8ValidN_bad (h : k < n) (h0 : (utf8CharN b k n).2 = 0) : utf8ValidN b k n = 0 := by
  rw [utf8ValidN]; simp [h, h0]
theorem utf8ValidN_step (k' : Word) (h : k < n) (h0 : (utf8CharN b k n).2 ≠ 0)
    (hw : k < k + (utf8CharN b k n).2) (hk' : k' = k + (utf8CharN b k n).2) :
    utf8ValidN b k n = utf8ValidN b k' n := by
  subst hk'; rw [utf8ValidN]; simp [h, h0, hw]
theorem utf8ValidN_wrap (h : k < n) (h0 : (utf8CharN b k n).2 ≠ 0)
    (hw : ¬ k < k + (utf8CharN b k n).2) : utf8ValidN b k n = 0 := by
  rw [utf8ValidN]; simp [h, h0, hw]

grind_pattern [lang_grind] utf8ValidN_end => utf8ValidN b k n
grind_pattern [lang_grind] utf8ValidN_bad => utf8ValidN b k n, utf8CharN b k n
grind_pattern [lang_grind] utf8ValidN_step => utf8ValidN b k n, utf8CharN b k n, utf8ValidN b k' n
grind_pattern [lang_grind] utf8ValidN_wrap => utf8ValidN b k n, utf8CharN b k n

end

/-- `k + (utf8CharN b k n).2` never wraps when `k < n` and `b.size < 2 ^ 63`: either `k` is
inside `b` (`< 2 ^ 63`, and the length is at most `4`, `utf8CharN_snd_le`), or `k` is past the
end (`byteW` reads `0`, forcing the one-byte ASCII branch, length `1`), and then `k < n` (`n` a
`Word`, so `n.toNat < 2 ^ 64`) keeps `k` below the maximum. Discharges `utf8ValidN_step`'s `hw`
unconditionally, since `utf8Valid_spec` takes no bound on `k`, `n`. -/
theorem utf8CharN_no_wrap (b : Array UInt8) (hb : b.size < 2 ^ 63) (k n : Word) (h : k < n)
    (hl : (utf8CharN b k n).2 ≠ 0) : k < k + (utf8CharN b k n).2 := by
  rw [UInt64.lt_iff_toNat_lt] at h
  have hn : n.toNat < 2 ^ 64 := n.toNat_lt
  rcases Nat.lt_or_ge k.toNat b.size with hk | hk
  · have h4 := L.Scan.Utf8.utf8CharN_snd_le b k n
    rw [UInt64.le_iff_toNat_le] at h4
    have h4' : (4 : Word).toNat = 4 := by decide
    rw [h4'] at h4
    have hl' : (utf8CharN b k n).2.toNat ≠ 0 := by
      intro hc; apply hl
      have : (utf8CharN b k n).2.toNat = (0 : Word).toNat := by simpa using hc
      exact UInt64.toNat_inj.mp this
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  · have hc0 : byteW b k = 0 := by simp [byteW, Array.getD, Nat.not_lt.mpr hk]
    have heq : utf8CharN b k n = (0, 1) := by simp [utf8CharN, hc0]
    rw [heq] at hl ⊢
    simp only
    have h1' : (1 : Word).toNat = 1 := by decide
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, h1']
    omega

grind_pattern [lang_grind] utf8CharN_no_wrap => utf8CharN b k n

/-! ## Bytes of the body, hexadecimal digits -/

/-- Rust's `byte_at` on the string body `[_, e)`: the byte at `k`, `0` from `e` on. -/
def byteE (b : Array UInt8) (e k : Word) : Word := if k < e then byteW b k else 0

def byteIn : FunDecl := lfn (k, e) {
  if k < e { return IN.u8[k] };
  return 0
}

/-- Rust's `hex_val`: `(1, value)` for a hexadecimal digit, `(0, 0)` otherwise. -/
def hexValN (c : Word) : Word × Word :=
  if 48 ≤ c ∧ c ≤ 57 then (1, c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then (1, c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then (1, c - 55)
  else (0, 0)

def hexVal : FunDecl := lfn (c) {
  if 48 <= c && c <= 57 { return (1, c - 48) };
  if 97 <= c && c <= 102 { return (1, c - 87) };
  if 65 <= c && c <= 70 { return (1, c - 55) };
  return (0, 0)
}

/-- Rust's `hex4`: the value of the four hexadecimal digits at `j` (in the body `[_, e)`). -/
def hex4N (b : Array UInt8) (e j : Word) : Word × Word :=
  let a := hexValN (byteE b e j)
  let x := hexValN (byteE b e (j + 1))
  let y := hexValN (byteE b e (j + 2))
  let z := hexValN (byteE b e (j + 3))
  if a.1 = 0 ∨ x.1 = 0 ∨ y.1 = 0 ∨ z.1 = 0 then (0, 0)
  else (1, (a.2 <<< 12) ||| (x.2 <<< 8) ||| (y.2 <<< 4) ||| z.2)

def hex4 : FunDecl := lfn (j, e) locals (c, ok, a, x, y, z) {
  c := call byte_in(j, e);
  (ok, a) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  c := call byte_in(j + 1, e);
  (ok, x) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  c := call byte_in(j + 2, e);
  (ok, y) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  c := call byte_in(j + 3, e);
  (ok, z) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  return (1, (a << 12) | (x << 8) | (y << 4) | z)
}

/-- Rust's `hex3`: the value of the three hexadecimal digits at `j`. -/
def hex3N (b : Array UInt8) (e j : Word) : Word × Word :=
  let a := hexValN (byteE b e j)
  let x := hexValN (byteE b e (j + 1))
  let y := hexValN (byteE b e (j + 2))
  if a.1 = 0 ∨ x.1 = 0 ∨ y.1 = 0 then (0, 0)
  else (1, (a.2 <<< 8) ||| (x.2 <<< 4) ||| y.2)

def hex3 : FunDecl := lfn (j, e) locals (c, ok, a, x, y) {
  c := call byte_in(j, e);
  (ok, a) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  c := call byte_in(j + 1, e);
  (ok, x) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  c := call byte_in(j + 2, e);
  (ok, y) := call hex_val(c);
  if ok == 0 { return (0, 0) };
  return (1, (a << 8) | (x << 4) | y)
}

/-! ## `unescape` -/

def unescapeLoop : Stmt := lblk (j, e, r, c, d, ok, v, j6) {
  while j < len(IN.u8) && j < e {
    c := IN.u8[j];
    if c != 92 {
      j += 1
    } else {
      ok := call utf8_valid(r, j);
      if ok == 0 { return 0 };
      d := call byte_in(j + 1, e);
      if d == 34 || d == 92 || d == 47 || d == 98 || d == 102 || d == 110 || d == 114 || d == 116 {
        j += 2
      } else {
        if d != 117 { return 0 };
        (ok, v) := call hex4(j + 2, e);
        if ok == 0 { return 0 };
        j6 := j + 6;
        if v < 0xD800 || 0xE000 <= v {
          j := j6
        } else if 0xDC00 <= v {
          j := j6
        } else {
          -- a high surrogate: look for a `\uDxxx` continuation, else U+FFFD
          c := call byte_in(j6, e);
          d := call byte_in(j6 + 1, e);
          ok := call byte_in(j6 + 2, e);
          if c == 92 && d == 117 && (ok == 100 || ok == 68) {
            (ok, v) := call hex3(j6 + 3, e);
            if ok != 0 && 0xC00 <= v { j := j6 + 6 } else { j := j6 }
          } else {
            j := j6
          }
        }
      };
      r := j
    }
  }
}

def unescape : FunDecl := lfn (j, e) locals (r, c, d, ok, v, j6) {
  r := j;
  ⟪unescapeLoop⟫;
  ok := call utf8_valid(r, e);
  return ok
}

/-- Where an escape at `j` that is a `\u` escape with value `v` (`hex4N`) continues: after the
six bytes, or after twelve for a high surrogate followed by a `\uDxxx` low one. -/
def uNextN (b : Array UInt8) (e j v : Word) : Word :=
  if v < 0xD800 ∨ 0xE000 ≤ v then j + 6
  else if 0xDC00 ≤ v then j + 6
  else if byteE b e (j + 6) = 92 ∧ byteE b e (j + 6 + 1) = 117 ∧
      (byteE b e (j + 6 + 2) = 100 ∨ byteE b e (j + 6 + 2) = 68) ∧
      (hex3N b e (j + 6 + 3)).1 ≠ 0 ∧ 0xC00 ≤ (hex3N b e (j + 6 + 3)).2 then j + 6 + 6
  else j + 6

/-- `1` if the body `[j, e)` (the current raw run starting at `r`) is a valid string, else `0`:
every escape is one of JSON's, and every raw run between escapes is valid UTF-8. The guards
`j < j'` are con-leche's (`unescape`), there for termination. -/
def unescN (b : Array UInt8) (j e r : Word) : Word :=
  if h : j < UInt64.ofNat b.size ∧ j < e then
    if byteW b j ≠ 92 then
      if j < j + 1 then unescN b (j + 1) e r else 0
    else if utf8ValidN b r j = 0 then 0
    else
      let d := byteE b e (j + 1)
      if d = 34 ∨ d = 92 ∨ d = 47 ∨ d = 98 ∨ d = 102 ∨ d = 110 ∨ d = 114 ∨ d = 116 then
        if j < j + 2 then unescN b (j + 2) e (j + 2) else 0
      else if d ≠ 117 then 0
      else if (hex4N b e (j + 2)).1 = 0 then 0
      else if j < uNextN b e j (hex4N b e (j + 2)).2 then
        unescN b (uNextN b e j (hex4N b e (j + 2)).2) e (uNextN b e j (hex4N b e (j + 2)).2)
      else 0
  else utf8ValidN b r e
termination_by b.size - j.toNat
decreasing_by
  all_goals
    have := lt_of_lt_ofNat h.1
    rename_i hj
    rw [UInt64.lt_iff_toNat_lt] at hj
    omega

section
variable (b : Array UInt8) (j e r : Word)

/-! `j + 1`, `j + 2`, `j + 6`, `j + 6 + 6` do not wrap when `j` is inside `b` (`< 2 ^ 63`): the
small-offset analogue of `utf8CharN_no_wrap` above, needed for the termination guards `j < j + …`
inside `unescN` and `uNextN` (the loop reaches these only once it has read `b[j]`, so `j` is
always in bounds there). -/

theorem lt_add1_of_lt_size (hj : j.toNat < b.size) (hb : b.size < 2 ^ 63) : j < j + 1 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have : (1 : Word).toNat = 1 := by decide
  omega
theorem lt_add2_of_lt_size (hj : j.toNat < b.size) (hb : b.size < 2 ^ 63) : j < j + 2 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have : (2 : Word).toNat = 2 := by decide
  omega
theorem lt_add6_of_lt_size (hj : j.toNat < b.size) (hb : b.size < 2 ^ 63) : j < j + 6 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have : (6 : Word).toNat = 6 := by decide
  omega
theorem lt_add6add6_of_lt_size (hj : j.toNat < b.size) (hb : b.size < 2 ^ 63) :
    j < j + 6 + 6 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add]
  have : (6 : Word).toNat = 6 := by decide
  omega

grind_pattern [lang_grind] lt_add1_of_lt_size => j + (1 : Word), UInt64.ofNat b.size
grind_pattern [lang_grind] lt_add2_of_lt_size => j + (2 : Word), UInt64.ofNat b.size
grind_pattern [lang_grind] lt_add6_of_lt_size => j + (6 : Word), UInt64.ofNat b.size
grind_pattern [lang_grind] lt_add6add6_of_lt_size => j + (6 : Word) + 6, UInt64.ofNat b.size

/-- `uNextN`'s result is always `j + 6` or `j + 6 + 6`, so it is always `> j` when `j` is in
bounds: discharges `unescN_u_esc`'s own `j < uNextN …` guard. -/
theorem uNextN_lt (hj : j.toNat < b.size) (hb : b.size < 2 ^ 63) (v : Word) :
    j < uNextN b e j v := by
  simp only [uNextN]
  repeat' split
  all_goals first
    | exact lt_add6_of_lt_size b j hj hb
    | exact lt_add6add6_of_lt_size b j hj hb

grind_pattern [lang_grind] uNextN_lt => uNextN b e j v

/-! One guarded equation per reachable arm (DESIGN.md, "Proof recipe", item 5). The recursive
arms take the next position as a variable `j'` with an equation, with the read `byteW b j` (or
`b[j.toNat]` through `L.Scan.Utf8.byteW_lt`) in the pattern so `grind` does not unroll further
than the program has read. -/

theorem unescN_end (h : ¬ (j < UInt64.ofNat b.size ∧ j < e)) :
    unescN b j e r = utf8ValidN b r e := by
  rw [unescN]; simp [h]

/-- Split in two, matching the program's short-circuit `j < len(IN.u8) && j < e` (as
`hasEscapeN_past`/`hasEscapeN_end` do for the same shape in `Leaves.lean`): `grind` sees one of
these two separate facts, not a negated conjunction, when the loop guard evaluates to `false`. -/
theorem unescN_end1 (h : ¬ j < UInt64.ofNat b.size) : unescN b j e r = utf8ValidN b r e :=
  unescN_end b j e r (fun hc => h hc.1)
theorem unescN_end2 (h1 : j < UInt64.ofNat b.size) (h2 : ¬ j < e) :
    unescN b j e r = utf8ValidN b r e := unescN_end b j e r (fun hc => h2 hc.2)

theorem unescN_plain (j' : Word) (hj' : j' = j + 1) (h1 : j < UInt64.ofNat b.size) (h2 : j < e)
    (hc : byteW b j ≠ 92) (hw : j < j + 1) : unescN b j e r = unescN b j' e r := by
  subst hj'; rw [unescN]; simp [h1, h2, hc, hw]

theorem unescN_bad_run (h1 : j < UInt64.ofNat b.size) (h2 : j < e) (hc : byteW b j = 92)
    (hbad : utf8ValidN b r j = 0) : unescN b j e r = 0 := by
  rw [unescN]; simp [h1, h2, hc, hbad]

theorem unescN_simple_esc (j' : Word) (hj' : j' = j + 2) (h1 : j < UInt64.ofNat b.size)
    (h2 : j < e) (hc : byteW b j = 92) (hok : utf8ValidN b r j ≠ 0)
    (hd : byteE b e (j + 1) = 34 ∨ byteE b e (j + 1) = 92 ∨ byteE b e (j + 1) = 47 ∨
      byteE b e (j + 1) = 98 ∨ byteE b e (j + 1) = 102 ∨ byteE b e (j + 1) = 110 ∨
      byteE b e (j + 1) = 114 ∨ byteE b e (j + 1) = 116) (hw : j < j + 2) :
    unescN b j e r = unescN b j' e j' := by
  subst hj'; rw [unescN]; simp [h1, h2, hc, hok, hd, hw]

theorem unescN_bad_escchar (h1 : j < UInt64.ofNat b.size) (h2 : j < e) (hc : byteW b j = 92)
    (hok : utf8ValidN b r j ≠ 0)
    (hd1 : ¬ (byteE b e (j + 1) = 34 ∨ byteE b e (j + 1) = 92 ∨ byteE b e (j + 1) = 47 ∨
      byteE b e (j + 1) = 98 ∨ byteE b e (j + 1) = 102 ∨ byteE b e (j + 1) = 110 ∨
      byteE b e (j + 1) = 114 ∨ byteE b e (j + 1) = 116))
    (hd2 : byteE b e (j + 1) ≠ 117) : unescN b j e r = 0 := by
  rw [unescN]; simp [h1, h2, hc, hok, hd1, hd2]

theorem unescN_bad_hex4 (h1 : j < UInt64.ofNat b.size) (h2 : j < e) (hc : byteW b j = 92)
    (hok : utf8ValidN b r j ≠ 0)
    (hd1 : ¬ (byteE b e (j + 1) = 34 ∨ byteE b e (j + 1) = 92 ∨ byteE b e (j + 1) = 47 ∨
      byteE b e (j + 1) = 98 ∨ byteE b e (j + 1) = 102 ∨ byteE b e (j + 1) = 110 ∨
      byteE b e (j + 1) = 114 ∨ byteE b e (j + 1) = 116))
    (hd2 : byteE b e (j + 1) = 117) (hhex : (hex4N b e (j + 2)).1 = 0) :
    unescN b j e r = 0 := by
  rw [unescN]; simp [h1, h2, hc, hok, hd1, hd2, hhex]

theorem unescN_u_esc (j' : Word) (hj' : j' = uNextN b e j (hex4N b e (j + 2)).2)
    (h1 : j < UInt64.ofNat b.size) (h2 : j < e) (hc : byteW b j = 92)
    (hok : utf8ValidN b r j ≠ 0)
    (hd1 : ¬ (byteE b e (j + 1) = 34 ∨ byteE b e (j + 1) = 92 ∨ byteE b e (j + 1) = 47 ∨
      byteE b e (j + 1) = 98 ∨ byteE b e (j + 1) = 102 ∨ byteE b e (j + 1) = 110 ∨
      byteE b e (j + 1) = 114 ∨ byteE b e (j + 1) = 116))
    (hd2 : byteE b e (j + 1) = 117) (hhex : (hex4N b e (j + 2)).1 ≠ 0)
    (hw : j < uNextN b e j (hex4N b e (j + 2)).2) : unescN b j e r = unescN b j' e j' := by
  subst hj'; rw [unescN]; simp [h1, h2, hc, hok, hd1, hd2, hhex, hw]

grind_pattern [lang_grind] unescN_end => unescN b j e r
grind_pattern [lang_grind] unescN_end1 => unescN b j e r
grind_pattern [lang_grind] unescN_end2 => unescN b j e r
grind_pattern [lang_grind] unescN_plain => unescN b j e r, byteW b j, unescN b j' e r
grind_pattern [lang_grind] unescN_bad_run => unescN b j e r, byteW b j
grind_pattern [lang_grind] unescN_simple_esc => unescN b j e r, byteW b j, unescN b j' e j'
grind_pattern [lang_grind] unescN_bad_escchar => unescN b j e r, byteW b j
grind_pattern [lang_grind] unescN_bad_hex4 => unescN b j e r, byteW b j
grind_pattern [lang_grind] unescN_u_esc => unescN b j e r, byteW b j, unescN b j' e j'

end

/-! ## `scan_string` -/

def scanString : FunDecl := lfn (i) locals (e, h, ok) {
  if i < len(IN.u8) && IN.u8[i] == 34 {
    e := call str_close(i + 1);
    if e == 0 { return 0 };
    h := call has_escape(i + 1, e);
    if h != 0 { ok := call unescape(i + 1, e) } else { ok := call utf8_valid(i + 1, e) };
    if ok == 0 { return 0 };
    return e + 1
  };
  return 0
}

/-- con-leche's `scanString`, validating only: the position after the closing quote, or `0`. -/
def scanStringN (b : Array UInt8) (i : Word) : Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 34 then
    if UInt64.ofNat (strCloseN b (i + 1).toNat) = 0 then 0
    else if UInt64.ofNat (hasEscapeN b (i + 1).toNat (UInt64.ofNat (strCloseN b (i + 1).toNat)).toNat) ≠ 0 then
      if unescN b (i + 1) (UInt64.ofNat (strCloseN b (i + 1).toNat)) (i + 1) = 0 then 0
      else UInt64.ofNat (strCloseN b (i + 1).toNat) + 1
    else if utf8ValidN b (i + 1) (UInt64.ofNat (strCloseN b (i + 1).toNat)) = 0 then 0
    else UInt64.ofNat (strCloseN b (i + 1).toNat) + 1
  else 0

/-! ## Specs -/

section specs
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpc : p.lookup "utf8_char" = some L.Scan.Utf8.utf8Char)
    (hpv : p.lookup "utf8_valid" = some utf8Valid)
    (hpb : p.lookup "byte_in" = some byteIn)
    (hph : p.lookup "hex_val" = some hexVal)
    (hp4 : p.lookup "hex4" = some hex4)
    (hp3 : p.lookup "hex3" = some hex3)
    (hpu : p.lookup "unescape" = some unescape)
    (hps : p.lookup "str_close" = some L.Examples.strClose)
    (hpe : p.lookup "has_escape" = some L.Scan.Leaves.hasEscape)
    (hpt : p.lookup "scan_string" = some scanString)
include hb

include hpc in
theorem utf8ValidLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) :
    ⦃fun s => s = s₀⦄
    exec p n utf8ValidLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [utf8ValidN b (s₀.loc 0) (s₀.loc 1)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := utf8ValidLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, L.Scan.Utf8.utf8Char_spec p hpc b n,
        ih] <;> finish

include hpc in
theorem utf8ValidLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) utf8ValidLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [utf8ValidN b (s₀.loc 0) (s₀.loc 1)]; ⊤⦄ :=
  Triple.step_exec (utf8ValidLoop_spec p b hb hpc (n + 1) s₀ hm)

include hpc hpv in
theorem utf8Valid_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "utf8_valid" [k, e]
    ⦃fun r s' => s' = s₀ ∧ r = [utf8ValidN b k e]; ⊤⦄ := by
  rw [invoke_eq _ hpv]
  simp only [callFn, utf8Valid]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, utf8ValidLoop_step_spec p b hb hpc n] <;> finish

section hex4Hex3
attribute [local lang_grind] byteE hexValN hex4N hex3N

include hpb in
theorem byteIn_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "byte_in" [k, e]
    ⦃fun r s' => s' = s₀ ∧ r = [byteE b e k]; ⊤⦄ := by
  rw [invoke_eq _ hpb]
  simp only [callFn, byteIn]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalC, evalArgs, ld8] <;> finish

include hph in
theorem hexVal_spec (n : Nat) (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hex_val" [c]
    ⦃fun r s' => s' = s₀ ∧ r = [(hexValN c).1, (hexValN c).2]; ⊤⦄ := by
  rw [invoke_eq _ hph]
  simp only [callFn, hexVal]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalC, evalArgs] <;> finish

/- `hex4_spec`/`hex3_spec`: `vcgen` alone (replacing `<;> finish` with `<;> sorry` below the
`vcgen [...]` call) elaborates in ~1s, so the blow-up is entirely inside `finish`/`grind`'s own
search on the resulting verification conditions, not in `vcgen`. Four (resp. three) sequential
`byte_in`/`hex_val` calls, each a two-result destructuring call followed by an early-return
check, leave the state as a deeply right-nested `setLocs`/`loc` term (no call "returns" to a
freshly-named, re-collapsed state the way a loop's `ih` does), and `grind`'s matching search does
not converge on the resulting VCs (minutes, not a quick failure). Confirmed with a minimal
standalone reproducer (four chained two-result calls, no strings/UTF-8 involved at all) given in
the task report, along with what was tried (splitting the `local lang_grind` unfolding of
`byteE`/`hexValN` out of this proof did not help; `<;> grind` in place of `<;> finish` hit a
separate parse issue in this combinator). Left as `sorry`. -/

include hpb hph hp4 in
theorem hex4_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hex4" [j, e]
    ⦃fun r s' => s' = s₀ ∧ r = [(hex4N b e j).1, (hex4N b e j).2]; ⊤⦄ := by
  sorry

include hpb hph hp3 in
theorem hex3_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hex3" [j, e]
    ⦃fun r s' => s' = s₀ ∧ r = [(hex3N b e j).1, (hex3N b e j).2]; ⊤⦄ := by
  sorry

end hex4Hex3

/- `unescapeLoop_spec`: each iteration that hits the `\u` escape branch chains a `utf8_valid`
call, a `byte_in` call, and (for the surrogate-pair continuation) a `hex4` call plus up to three
more `byte_in` calls and a `hex3` call — a sequential-call chain at least as deep as `hex4_spec`'s
own (see the `sorry` note there), and `finish`/`grind` does not converge on it either (confirmed
directly, with `s.mem.arr8 IN = b` folded into the precondition instead of carried as a separate
`ih`/callee hypothesis — a fix that *did* work for an analogous loop in another lane's
`Records.lean`, `strNameLoop_spec` — and with `sym (gen := 16)`; neither changed the outcome
here). Left as `sorry`; see the task report. -/

include hpc hpv hpb hph hp4 hp3 in
theorem unescapeLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n unescapeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ s'.loc 1 = s₀.loc 1 ∧ r ≠ .brk ∧
      r.retOr [utf8ValidN b (s'.loc 2) (s₀.loc 1)] =
        [unescN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  sorry

include hpc hpv hpb hph hp4 hp3 in
theorem unescapeLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) unescapeLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ s'.loc 1 = s₀.loc 1 ∧ r ≠ .brk ∧
      r.retOr [utf8ValidN b (s'.loc 2) (s₀.loc 1)] =
        [unescN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (unescapeLoop_spec p b hb hpc hpv hpb hph hp4 hp3 (n + 1) s₀)

include hpc hpv hpb hph hp4 hp3 hpu in
theorem unescape_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "unescape" [j, e]
    ⦃fun r s' => s' = s₀ ∧ r = [unescN b j e j]; ⊤⦄ := by
  rw [invoke_eq _ hpu]
  simp only [callFn, unescape]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs,
        unescapeLoop_step_spec p b hb hpc hpv hpb hph hp4 hp3 n,
        utf8Valid_spec p b hb hpc hpv n] <;> finish

attribute [local lang_grind] scanStringN

include hpc hpv hpb hph hp4 hp3 hpu hps hpe hpt in
theorem scanString_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_string" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [scanStringN b i]; ⊤⦄ := by
  rw [invoke_eq _ hpt]
  simp only [callFn, scanString]
  have hb64 : b.size < 2 ^ 64 := by omega
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, L.Scan.lt_of_lt_ofNat, L.Scan.toNat_add_one_of_lt_ofNat] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Examples.strClose_spec p hps b hb64 n,
        L.Scan.Leaves.hasEscape_spec p hpe b hb64 n,
        unescape_spec p b hb hpc hpv hpb hph hp4 hp3 hpu n,
        utf8Valid_spec p b hb hpc hpv n] <;> finish

end specs

end L.Scan.Str

namespace L.Scan.Str

/-- The program, as `#eval`-able code. -/
def strProg : Prog := [("str_close", L.Examples.strClose), ("has_escape", L.Scan.Leaves.hasEscape),
  ("utf8_char", L.Scan.Utf8.utf8Char), ("utf8_valid", utf8Valid), ("byte_in", byteIn),
  ("hex_val", hexVal), ("hex4", hex4), ("hex3", hex3), ("unescape", unescape),
  ("scan_string", scanString)]

/-- `scan_string(0)` on `s` with the L program. -/
def runStr (s : String) : Option Word :=
  match run strProg 10000 "scan_string" [0] { bytes := #[s.toUTF8.data] } with
  | .ok ([e], _) => some e
  | _ => none

-- con-leche's `scanString`, on inputs with escapes, surrogates, and invalid syntax: the position
-- after the closing quote, or `0`.
#guard runStr "\"abc\"" == some 5
#guard runStr "\"a\\u0041\"" == some 9
#guard runStr "\"\\ud83d\\ude00x\"" == some 15
#guard runStr "\"\\u00\"" == some 0
#guard runStr "\"\\x\"" == some 0

end L.Scan.Str
