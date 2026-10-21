module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Scan.Common
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Lit
public import ConAgua.Scan.Utf8
public import ConAgua.Scan.Key
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The value scanners of the validator (`scan_fast.rs`)

Each returns the position after the value, or `0` for failure; the value itself is dropped.

* `slot_nat(ks, v)` (`:1419`): a JSON number at `v`, and the `noProgress` guard `ks < e`. Rust
  also reads the number (`read_nat_at`, which fails past `u64`); con-leche reads it as a `Nat`
  and never fails, so the validator does not read it.
* `scan_quoted_nat(i)` (`:1116`): `"digits"`.
* `scan_binder_info(i)` (`:1132`) and the string arms of `scan_hints(i)` (`:1219`) compare with
  `match_word(i, o, n)`, `match_lit` (`ConAgua.Scan.Lit`) over the constant `WORDS`.
* `scan_nat_list(i)` (`:1162,1208`): `[n, …]`; returns `(end, count)`, since `max`/`imax` need
  exactly two members.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Values

open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN keyEndN numEndN)
open L.Scan.Lit (matchLitN)
open L.Scan.Key (keyAtN valueAtN)

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `slot_nat` -/

def slotNat : FunDecl := lfn (ks, v) locals (e) {
  e := call num_end(v);
  if e == v { return 0 };
  if ks < e { return e };
  return 0
}

/-- `slot_nat(ks, v)`: the end of the number at `v`, `0` if there is none or `e ≤ ks`. -/
def slotNatN (b : Array UInt8) (ks v : Word) : Word :=
  if UInt64.ofNat (numEndN b v.toNat) = v then 0
  else if ks < UInt64.ofNat (numEndN b v.toNat) then UInt64.ofNat (numEndN b v.toNat)
  else 0

/-! ## `scan_quoted_nat` -/

def scanQuotedNat : FunDecl := lfn (i) locals (e) {
  if i < len(IN.u8) && IN.u8[i] == 34 {
    e := call skip_digits(i + 1);
    if e == i + 1 { return 0 };
    if e < len(IN.u8) && IN.u8[e] == 34 { return e + 1 };
    return 0
  };
  return 0
}

/-- con-leche's `scanQuotedNat`, validating only. -/
def quotedNatN (b : Array UInt8) (i : Word) : Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 34 then
    if UInt64.ofNat (L.Scan.Leaves.skipDigitsN b (i + 1).toNat) = i + 1 then 0
    else if UInt64.ofNat (L.Scan.Leaves.skipDigitsN b (i + 1).toNat) < UInt64.ofNat b.size ∧
        byteW b (UInt64.ofNat (L.Scan.Leaves.skipDigitsN b (i + 1).toNat)) = 34 then
      UInt64.ofNat (L.Scan.Leaves.skipDigitsN b (i + 1).toNat) + 1
    else 0
  else 0

/-! ## `match_word`, `scan_binder_info`, `scan_hints` -/

/-- The literals of `scan_binder_info` and `scan_hints`, each with its closing quote:
`default"` at `0`, `implicit"` at `8`, `strictImplicit"` at `17`, `instImplicit"` at `32`,
`abbrev"` at `45`, `opaque"` at `52`. -/
def WORDS : List UInt8 :=
  [100, 101, 102, 97, 117, 108, 116, 34, 105, 109, 112, 108, 105, 99, 105, 116, 34, 115, 116, 114, 105, 99, 116, 73, 109, 112, 108, 105, 99, 105,
   116, 34, 105, 110, 115, 116, 73, 109, 112, 108, 105, 99, 105, 116, 34, 97, 98, 98, 114, 101, 118, 34, 111, 112, 97, 113, 117, 101, 34]

theorem WORDS_length : WORDS.length = 59 := rfl

def matchWordLoop : Stmt := lblk (i, o, n, k, c) {
  while k < n {
    if i + k < len(IN.u8) { c := IN.u8[i + k] } else { c := 0 };
    if c != WORDS.c8[o + k] { return 0 };
    k += 1
  }
}

/-- `match_lit` against a slice `(o, n)` of `WORDS`. -/
def matchWord : FunDecl := lfn (i, o, n) locals (k, c) { ⟪matchWordLoop⟫; return 1 }

def scanBinderInfo : FunDecl := lfn (i) locals (m) {
  if i < len(IN.u8) && IN.u8[i] == 34 {
    m := call match_word(i + 1, 0, 8);
    if m != 0 { return i + 9 };
    m := call match_word(i + 1, 8, 9);
    if m != 0 { return i + 10 };
    m := call match_word(i + 1, 17, 15);
    if m != 0 { return i + 16 };
    m := call match_word(i + 1, 32, 13);
    if m != 0 { return i + 14 };
    return 0
  };
  return 0
}

/-- con-leche's `scanBinderInfo`. -/
def binderInfoN (b : Array UInt8) (i : Word) : Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 34 then
    if matchLitN b (i + 1).toNat WORDS 0 8 0 then i + 9
    else if matchLitN b (i + 1).toNat WORDS 8 9 0 then i + 10
    else if matchLitN b (i + 1).toNat WORDS 17 15 0 then i + 16
    else if matchLitN b (i + 1).toNat WORDS 32 13 0 then i + 14
    else 0
  else 0

def scanHints : FunDecl := lfn (i) locals (m, p, ke, k, v, e, q) {
  if i < len(IN.u8) && IN.u8[i] == 34 {
    m := call match_word(i + 1, 45, 7);
    if m != 0 { return i + 8 };
    m := call match_word(i + 1, 52, 7);
    if m != 0 { return i + 8 };
    return 0
  };
  if i < len(IN.u8) && IN.u8[i] == 123 {
    p := call skip_ws(i + 1);
    if !(p < len(IN.u8) && IN.u8[p] == 34) { return 0 };
    ke := call key_end(p + 1);
    if ke == 0 { return 0 };
    k := call key_at(p, ke - (p + 1));
    if k != 51 { return 0 };  -- `regular`
    v := call value_at(p, ke);
    if v == p { return 0 };
    e := call num_end(v);
    if e == v { return 0 };
    q := call skip_ws(e);
    if q < len(IN.u8) && IN.u8[q] == 125 { return q + 1 };
    return 0
  };
  return 0
}

/-- con-leche's `scanHints`, validating only. -/
def hintsN (b : Array UInt8) (i : Word) : Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 34 then
    if matchLitN b (i + 1).toNat WORDS 45 7 0 then i + 8
    else if matchLitN b (i + 1).toNat WORDS 52 7 0 then i + 8
    else 0
  else if i < UInt64.ofNat b.size ∧ byteW b i = 123 then
    hintsObjN b (UInt64.ofNat (skipWsN b (i + 1).toNat))
  else 0
where
  /-- `{"regular":n}` from the key's opening quote at `p`. -/
  hintsObjN (b : Array UInt8) (p : Word) : Word :=
    if ¬ (p < UInt64.ofNat b.size ∧ byteW b p = 34) then 0
    else if UInt64.ofNat (keyEndN b (p + 1).toNat) = 0 then 0
    else if keyAtN b p (UInt64.ofNat (keyEndN b (p + 1).toNat) - (p + 1)) ≠ 51 then 0
    else if valueAtN b p (UInt64.ofNat (keyEndN b (p + 1).toNat)) = p then 0
    else hintsNumN b (valueAtN b p (UInt64.ofNat (keyEndN b (p + 1).toNat)))
  /-- The number at `v` and the closing brace. -/
  hintsNumN (b : Array UInt8) (v : Word) : Word :=
    if UInt64.ofNat (numEndN b v.toNat) = v then 0
    else if UInt64.ofNat (skipWsN b (UInt64.ofNat (numEndN b v.toNat)).toNat) < UInt64.ofNat b.size ∧
        byteW b (UInt64.ofNat (skipWsN b (UInt64.ofNat (numEndN b v.toNat)).toNat)) = 125 then
      UInt64.ofNat (skipWsN b (UInt64.ofNat (numEndN b v.toNat)).toNat) + 1
    else 0

/-! ## `scan_nat_list` -/

def natListLoop : Stmt := lblk (i, cnt, w, c, e) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {
      i += 1
    } else if c == 93 {
      if w != 0 && cnt != 0 { return (0, 0) };
      return (i + 1, cnt)
    } else if c == 44 {
      if w != 0 { return (0, 0) };
      i += 1;
      w := 1
    } else if 48 <= c && c <= 57 {
      if w == 0 { return (0, 0) };
      e := call num_end(i);
      if e == i { return (0, 0) };
      cnt += 1;
      i := e;
      w := 0
    } else {
      return (0, 0)
    }
  }
}

def scanNatList : FunDecl := lfn (i) locals (cnt, w, c, e) {
  if i < len(IN.u8) && IN.u8[i] == 91 {
    i += 1;
    w := 1;
    ⟪natListLoop⟫
  };
  return (0, 0)
}

/-- con-leche's `scanNatListLoop`, validating only: `(end, count)`, `(0, 0)` for failure. The
guard `i < e` is con-leche's `noProgress` (always true: `num_end` advances). -/
def natListN (b : Array UInt8) (i cnt w : Word) : Word × Word :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13 then natListN b (i + 1) cnt w
    else if byteW b i = 93 then (if w ≠ 0 ∧ cnt ≠ 0 then (0, 0) else (i + 1, cnt))
    else if byteW b i = 44 then (if w ≠ 0 then (0, 0) else natListN b (i + 1) cnt 1)
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if w = 0 then (0, 0)
      else if UInt64.ofNat (numEndN b i.toNat) = i then (0, 0)
      else if i < UInt64.ofNat (numEndN b i.toNat) then
        natListN b (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1) 0
      else (0, 0)
    else (0, 0)
  else (0, 0)
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rename_i hj; rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

/-- `scan_nat_list(i)`. -/
def natListEntryN (b : Array UInt8) (i : Word) : Word × Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 91 then natListN b (i + 1) 0 1 else (0, 0)

/-! ## Facts about the leaf models -/

theorem keyEndN_lt (b : Array UInt8) (j : Nat) (h : keyEndN b j ≠ 0) : keyEndN b j < b.size := by
  fun_induction keyEndN b j with
  | case1 j hj hq => exact hj
  | case3 j hj hq hc ih => exact ih h
  | _ => simp_all

theorem numEndN_le (b : Array UInt8) (i : Nat) (h : i ≤ b.size) : numEndN b i ≤ b.size := by
  have hle := L.Scan.Leaves.skipDigitsN_le b i h
  simp only [numEndN]
  split
  · omega
  · split <;> omega

theorem numEndN_ge (b : Array UInt8) (i : Nat) : i ≤ numEndN b i := by
  have hge : i ≤ L.Scan.Leaves.skipDigitsN b i := by
    by_cases heq : L.Scan.Leaves.skipDigitsN b i = i
    · omega
    · have := (L.Scan.Leaves.skipDigitsN_bounds b i heq).2; omega
  simp only [numEndN]
  split
  · omega
  · split <;> omega

/-- A successful `slot_nat` is past the key. -/
theorem slotNatN_pos (b : Array UInt8) (ks v : Word) (h : slotNatN b ks v ≠ 0) :
    ks < slotNatN b ks v := by
  unfold slotNatN at h ⊢
  by_cases h1 : UInt64.ofNat (numEndN b v.toNat) = v
  · simp [h1] at h
  · by_cases h2 : ks < UInt64.ofNat (numEndN b v.toNat)
    · simp [h1, h2]
    · simp [h1, h2] at h

/-! ## Specs -/

section specs
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpw : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hpd : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits)
    (hpk : p.lookup "key_end" = some L.Scan.Leaves.keyEnd)
    (hpn : p.lookup "num_end" = some L.Scan.Leaves.numEnd)
    (hpa : p.lookup "key_at" = some L.Scan.Key.keyAt)
    (hpv : p.lookup "value_at" = some L.Scan.Key.valueAt)
    (hps : p.lookup "slot_nat" = some slotNat)
    (hpq : p.lookup "scan_quoted_nat" = some scanQuotedNat)
    (hpm : p.lookup "match_word" = some matchWord)
    (hpi : p.lookup "scan_binder_info" = some scanBinderInfo)
    (hph : p.lookup "scan_hints" = some scanHints)
    (hpl : p.lookup "scan_nat_list" = some scanNatList)
include hb

include hpd hpn hps in
attribute [local lang_grind] slotNatN in
theorem slotNat_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (ks v : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "slot_nat" [ks, v]
    ⦃fun r s' => s' = s₀ ∧ r = [slotNatN b ks v]; ⊤⦄ := by
  rw [invoke_eq _ hps]
  simp only [callFn, slotNat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Leaves.numEnd_spec p hpd hpn b hb64 n] <;> finish

include hpd hpq in
attribute [local lang_grind] quotedNatN in
theorem scanQuotedNat_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_quoted_nat" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [quotedNatN b i]; ⊤⦄ := by
  rw [invoke_eq _ hpq]
  simp only [callFn, scanQuotedNat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.skipDigits_spec p hpd b hb64 n] <;> finish

theorem matchWordLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat + (s₀.loc 2).toNat < 2 ^ 64)
    (ho : (s₀.loc 1).toNat + (s₀.loc 2).toNat ≤ WORDS.length) (hk : (s₀.loc 3).toNat ≤ (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    exec p n matchWordLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if matchLitN b (s₀.loc 0).toNat WORDS (s₀.loc 1).toNat (s₀.loc 2).toNat
        (s₀.loc 3).toNat then 1 else 0]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := matchWordLoop) rfl]
    sym only [lang_grind, WORDS_length] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ldc, ih] <;> finish

theorem matchWordLoop_step_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat + (s₀.loc 2).toNat < 2 ^ 64)
    (ho : (s₀.loc 1).toNat + (s₀.loc 2).toNat ≤ WORDS.length) (hk : (s₀.loc 3).toNat ≤ (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) matchWordLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if matchLitN b (s₀.loc 0).toNat WORDS (s₀.loc 1).toNat (s₀.loc 2).toNat
        (s₀.loc 3).toNat then 1 else 0]; ⊤⦄ :=
  Triple.step_exec (matchWordLoop_spec p b hb (n + 1) s₀ hm hi ho hk)

include hpm in
theorem matchWord_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i o l : Word)
    (hi : i.toNat + l.toNat < 2 ^ 64) (ho : o.toNat + l.toNat ≤ WORDS.length) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "match_word" [i, o, l]
    ⦃fun r s' => s' = s₀ ∧
      r = [if matchLitN b i.toNat WORDS o.toNat l.toNat 0 then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hpm]
  simp only [callFn, matchWord]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, matchWordLoop_step_spec p b hb n] <;> finish

include hpm hpi in
attribute [local lang_grind] binderInfoN in
theorem scanBinderInfo_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_binder_info" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [binderInfoN b i]; ⊤⦄ := by
  rw [invoke_eq _ hpi]
  simp only [callFn, scanBinderInfo]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, WORDS_length] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        matchWord_spec p b hb hpm n] <;> finish

include hpw hpd hpk hpn hpa hpv hpm hph in
theorem scanHints_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_hints" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [hintsN b i]; ⊤⦄ := by
  sorry

include hpd hpn hpl in
theorem scanNatList_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_nat_list" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [(natListEntryN b i).1, (natListEntryN b i).2]; ⊤⦄ := by
  sorry

end specs

end L.Scan.Values
