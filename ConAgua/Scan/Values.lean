module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Utf8
meta import ConAgua.L.Semantics
public import ConAgua.Scan.Lit
public import ConAgua.Scan.Key
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
public import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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

/-! ## `slot_nat` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:646-652 ConLeche.Frontend.scanQuotedNat -/
@[l_impl ConLeche.Frontend.scanQuotedNat]
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
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:121-131 ConLeche.Frontend.matchLit
def matchWord : FunDecl := lfn (i, o, n) locals (k, c) { ⟪matchWordLoop⟫; return 1 }

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:654-663 ConLeche.Frontend.scanBinderInfo -/
@[l_impl ConLeche.Frontend.scanBinderInfo]
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

/-- The number of `{"regular":n}` at `v`, and the closing brace. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:703-728 ConLeche.Frontend.scanHints
def hintsNum : FunDecl := lfn (v) locals (e, q) {
  e := call num_end(v);
  if e == v { return 0 };
  q := call skip_ws(e);
  if q < len(IN.u8) && IN.u8[q] == 125 { return q + 1 };
  return 0
}

/-- `{"regular":n}` from the key's opening quote at `p`. Rust's `scan_hints` has this inline; it is
a function of its own here so that each verification condition stays short. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:703-728 ConLeche.Frontend.scanHints
def hintsObj : FunDecl := lfn (p) locals (ke, k, v, e) {
  if !(p < len(IN.u8) && IN.u8[p] == 34) { return 0 };
  ke := call key_end(p + 1);
  if ke == 0 { return 0 };
  k := call key_at(p, ke - (p + 1));
  if k != 51 { return 0 };  -- `regular`
  v := call value_at(p, ke);
  if v == p { return 0 };
  e := call hints_num(v);
  return e
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:703-728 ConLeche.Frontend.scanHints -/
@[l_impl ConLeche.Frontend.scanHints]
def scanHints : FunDecl := lfn (i) locals (m, p, e) {
  if i < len(IN.u8) && IN.u8[i] == 34 {
    m := call match_word(i + 1, 45, 7);
    if m != 0 { return i + 8 };
    m := call match_word(i + 1, 52, 7);
    if m != 0 { return i + 8 };
    return 0
  };
  if i < len(IN.u8) && IN.u8[i] == 123 {
    p := call skip_ws(i + 1);
    e := call hints_obj(p);
    return e
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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:697-699 ConLeche.Frontend.scanNatList -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:667-695 ConLeche.Frontend.scanNatListLoop
@[l_impl ConLeche.Frontend.scanNatList ConLeche.Frontend.scanNatListLoop]
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

/-! One guarded equation per arm (DESIGN.md, "Proof recipe"), mirroring `natListN`'s own
nested-if chain, as `keyEndN`'s arms do. -/
section
variable (b : Array UInt8) (i cnt w : Word)

theorem natListN_ws (k : Word) (hk : k = i + 1) (h : i < UInt64.ofNat b.size)
    (hc : byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13) :
    natListN b i cnt w = natListN b k cnt w := by
  subst hk; rw [natListN]; simp [h, hc]

theorem natListN_close_ok (h : i < UInt64.ofNat b.size)
    (_h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (hc : byteW b i = 93)
    (hw : ¬ (w ≠ 0 ∧ cnt ≠ 0)) : natListN b i cnt w = (i + 1, cnt) := by
  rw [natListN]; simp [h, hc, hw]

theorem natListN_close_fail (h : i < UInt64.ofNat b.size)
    (_h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (hc : byteW b i = 93)
    (hw : w ≠ 0 ∧ cnt ≠ 0) : natListN b i cnt w = (0, 0) := by
  rw [natListN]; simp [h, hc, hw]

theorem natListN_comma (k : Word) (hk : k = i + 1)
    (h : i < UInt64.ofNat b.size) (_h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13))
    (_h2 : byteW b i ≠ 93) (hc : byteW b i = 44) (hw : w = 0) :
    natListN b i cnt w = natListN b k cnt 1 := by
  subst hk; rw [natListN]; simp [h, hc, hw]

theorem natListN_comma_fail (h : i < UInt64.ofNat b.size)
    (_h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (_h2 : byteW b i ≠ 93)
    (hc : byteW b i = 44) (hw : w ≠ 0) : natListN b i cnt w = (0, 0) := by
  rw [natListN]; simp [h, hc, hw]

theorem natListN_digit_w0 (h : i < UInt64.ofNat b.size)
    (h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h2 : byteW b i ≠ 93)
    (h3 : byteW b i ≠ 44) (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (hw : w = 0) :
    natListN b i cnt w = (0, 0) := by
  rw [natListN]; simp [h, h1, h2, h3, hd, hw]

theorem natListN_digit_noprog (h : i < UInt64.ofNat b.size)
    (h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h2 : byteW b i ≠ 93)
    (h3 : byteW b i ≠ 44) (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (hw : w ≠ 0)
    (he : UInt64.ofNat (numEndN b i.toNat) = i) : natListN b i cnt w = (0, 0) := by
  rw [natListN]; simp [h, h1, h2, h3, hd, hw, he]

theorem natListN_digit (k : Word) (hk : k = UInt64.ofNat (numEndN b i.toNat))
    (h : i < UInt64.ofNat b.size) (h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13))
    (h2 : byteW b i ≠ 93) (h3 : byteW b i ≠ 44) (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (hw : w ≠ 0)
    (he : UInt64.ofNat (numEndN b i.toNat) ≠ i) (hlt : i < UInt64.ofNat (numEndN b i.toNat)) :
    natListN b i cnt w = natListN b k (cnt + 1) 0 := by
  subst hk; rw [natListN]; simp [h, h1, h2, h3, hd, hw, he, hlt]

theorem natListN_other (h : i < UInt64.ofNat b.size)
    (h1 : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h2 : byteW b i ≠ 93)
    (h3 : byteW b i ≠ 44) (h4 : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) :
    natListN b i cnt w = (0, 0) := by
  rw [natListN]; simp [h, h1, h2, h3, h4]

theorem natListN_end (h : ¬ i < UInt64.ofNat b.size) : natListN b i cnt w = (0, 0) := by
  rw [natListN]; simp [h]

grind_pattern [lang_grind] natListN_ws => natListN b i cnt w, byteW b i, natListN b k cnt w
grind_pattern [lang_grind] natListN_close_ok => natListN b i cnt w, byteW b i
grind_pattern [lang_grind] natListN_close_fail => natListN b i cnt w, byteW b i
grind_pattern [lang_grind] natListN_comma => natListN b i cnt w, byteW b i, natListN b k cnt 1
grind_pattern [lang_grind] natListN_comma_fail => natListN b i cnt w, byteW b i
grind_pattern [lang_grind] natListN_digit_w0 => natListN b i cnt w, byteW b i
grind_pattern [lang_grind] natListN_digit_noprog => natListN b i cnt w, byteW b i, numEndN b i.toNat
grind_pattern [lang_grind] natListN_digit =>
  natListN b i cnt w, byteW b i, numEndN b i.toNat, natListN b k (cnt + 1) 0
grind_pattern [lang_grind] natListN_other => natListN b i cnt w, byteW b i
grind_pattern [lang_grind] natListN_end => natListN b i cnt w

end

/-! ## Facts about the leaf models -/

theorem keyEndN_lt (b : Array UInt8) (j : Nat) (h : keyEndN b j ≠ 0) : keyEndN b j < b.size := by
  fun_induction keyEndN b j with
  | case1 j hj hq => exact hj
  | case3 j hj hq hc ih => exact ih h
  | _ => simp_all

grind_pattern [lang_grind] keyEndN_lt => keyEndN b j

theorem numEndN_le (b : Array UInt8) (i : Nat) (h : i ≤ b.size) : numEndN b i ≤ b.size := by
  have hle := L.Scan.Leaves.skipDigitsN_le b i h
  simp only [numEndN]
  split
  · omega
  · split <;> omega

grind_pattern [lang_grind] numEndN_le => numEndN b i

theorem numEndN_ge (b : Array UInt8) (i : Nat) : i ≤ numEndN b i := by
  have hge : i ≤ L.Scan.Leaves.skipDigitsN b i := by
    by_cases heq : L.Scan.Leaves.skipDigitsN b i = i
    · omega
    · have := (L.Scan.Leaves.skipDigitsN_bounds b i heq).2; omega
  simp only [numEndN]
  split
  · omega
  · split <;> omega

grind_pattern [lang_grind] numEndN_ge => numEndN b i

/-- A successful `slot_nat` is past the key. -/
theorem slotNatN_pos (b : Array UInt8) (ks v : Word) (h : slotNatN b ks v ≠ 0) :
    ks < slotNatN b ks v := by
  unfold slotNatN at h ⊢
  by_cases h1 : UInt64.ofNat (numEndN b v.toNat) = v
  · simp [h1] at h
  · by_cases h2 : ks < UInt64.ofNat (numEndN b v.toNat)
    · simp [h1, h2]
    · simp [h1, h2] at h

grind_pattern [lang_grind] slotNatN_pos => slotNatN b ks v

section natListLoop
variable (p : Prog) (hpd : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits)
    (hpn : p.lookup "num_end" = some L.Scan.Leaves.numEnd)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb hpd hpn

theorem natListLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n natListLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0] = [(natListN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)).1,
        (natListN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)).2]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := natListLoop) rfl]
    have hbw : ∀ (k : Word) (hk : k.toNat < b.size), byteW b k = b[k.toNat].toUInt64 := fun k hk =>
      L.Scan.Utf8.byteW_lt b k hk
    have hge2 : ∀ k : Word, k.toNat ≤ b.size → k ≤ UInt64.ofNat (numEndN b k.toNat) := by
      intro k hk
      have h1 := numEndN_ge b k.toNat
      have h2 := numEndN_le b k.toNat hk
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat']
      omega
    have hgt2 : ∀ k : Word, k.toNat ≤ b.size → ¬ UInt64.ofNat (numEndN b k.toNat) = k →
        k < UInt64.ofNat (numEndN b k.toNat) := by
      intro k hk hne
      have h1 := numEndN_ge b k.toNat
      have h2 := numEndN_le b k.toNat hk
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
      have hne' : ¬ k.toNat = numEndN b k.toNat % 2 ^ 64 := by
        intro heq
        apply hne
        rw [← UInt64.toNat_inj, UInt64.toNat_ofNat']
        omega
      omega
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.numEnd_spec p hpd hpn b hb n, ih] <;> finish

end natListLoop

/-! ## Specs -/

section specs
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpw : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hpd : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits)
    (hpk : p.lookup "key_end" = some L.Scan.Leaves.keyEnd)
    (hpn : p.lookup "num_end" = some L.Scan.Leaves.numEnd)
    (hpa1 : p.lookup "key_at_g1" = some L.Scan.Key.keyAtG1)
    (hpa2 : p.lookup "key_at_g2" = some L.Scan.Key.keyAtG2)
    (hpa3 : p.lookup "key_at_g3" = some L.Scan.Key.keyAtG3)
    (hpa4 : p.lookup "key_at_g4" = some L.Scan.Key.keyAtG4)
    (hpa5 : p.lookup "key_at_g5" = some L.Scan.Key.keyAtG5)
    (hpa6 : p.lookup "key_at_g6" = some L.Scan.Key.keyAtG6)
    (hpa : p.lookup "key_at" = some L.Scan.Key.keyAt)
    (hpv : p.lookup "value_at" = some L.Scan.Key.valueAt)
    (hps : p.lookup "slot_nat" = some slotNat)
    (hpq : p.lookup "scan_quoted_nat" = some scanQuotedNat)
    (hpm : p.lookup "match_word" = some matchWord)
    (hpi : p.lookup "scan_binder_info" = some scanBinderInfo)
    (hphn : p.lookup "hints_num" = some hintsNum)
    (hpho : p.lookup "hints_obj" = some hintsObj)
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
@[refines_part ConLeche.Frontend.scanQuotedNat "validity"]
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
      vcgen [exec, step, evalE, evalArgs, fun s₀ hm hi ho hk => Triple.step_exec (matchWordLoop_spec p b hb (n + 1) s₀ hm hi ho hk)] <;> finish

include hpm hpi in
attribute [local lang_grind] binderInfoN in
@[refines_part ConLeche.Frontend.scanBinderInfo "validity"]
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

include hpw hpd hpn hphn in
attribute [local lang_grind] hintsN.hintsNumN in
theorem hintsNum_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hints_num" [v]
    ⦃fun r s' => s' = s₀ ∧ r = [hintsN.hintsNumN b v]; ⊤⦄ := by
  rw [invoke_eq _ hphn]
  simp only [callFn, hintsNum]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.numEnd_spec p hpd hpn b hb64 n, L.Scan.Leaves.skipWs_spec p hpw b hb64 n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hphn hpho in
attribute [local lang_grind] hintsN.hintsObjN in
theorem hintsObj_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (q : Word)
    (hq : q.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "hints_obj" [q]
    ⦃fun r s' => s' = s₀ ∧ r = [hintsN.hintsObjN b q]; ⊤⦄ := by
  rw [invoke_eq _ hpho]
  simp only [callFn, hintsObj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hval := L.Scan.Key.valueAtN_le b
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.keyEnd_spec p hpk b hb64 n,
        L.Scan.Key.keyAt_spec p hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa b hb n,
        L.Scan.Key.valueAt_spec p hpw hpv b hb n,
        hintsNum_spec p b hb hpw hpd hpn hphn n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hphn hpho hph in
attribute [local lang_grind] hintsN in
@[refines_part ConLeche.Frontend.scanHints "validity"]
theorem scanHints_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_hints" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [hintsN b i]; ⊤⦄ := by
  rw [invoke_eq _ hph]
  simp only [callFn, scanHints]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind, WORDS_length] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.skipWs_spec p hpw b hb64 n,
        matchWord_spec p b hb hpm n,
        hintsObj_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hphn hpho n] <;>
        finish

include hpd hpn hpl in
attribute [local lang_grind] natListEntryN in
@[refines_part ConLeche.Frontend.scanNatList "validity"]
theorem scanNatList_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_nat_list" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [(natListEntryN b i).1, (natListEntryN b i).2]; ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, scanNatList]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hstep : ∀ j : Word, (j + 1).toNat ≤ j.toNat + 1 := fun j => by
      simp [UInt64.toNat_add]; omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        fun s₀ hm hi => Triple.step_exec (natListLoop_spec p hpd hpn b hb64 (n + 1) s₀ hm hi)] <;> finish

end specs

/-- The program, as `#eval`-able code: every function `scan_hints` can reach. -/
-- Only the quoted-literal branch (`match_word`, `scan_hints`: both in this module) is testable
-- here with `#guard`/`run`: a cross-module program whose functions were never `#eval`'d/
-- `#guard`'d in their own defining file hits "(interpreter) IR of declaration … not available"
-- (tried with `skip_ws` from Leaves.lean and `value_at` from Key.lean, both of which have no
-- `#guard` of their own; `lake build`, not just `lake env lean`, has the same failure, so this
-- is not a staleness issue). The object branch (`{"regular":n}`, needing skip_ws/key_end/key_at/
-- value_at/num_end) would need those files to gain their own `#guard`/`#eval`, which are outside
-- Values.lean/Key.lean.
def hintsProg : Prog := [("match_word", matchWord), ("scan_hints", scanHints)]

-- `"abbrev"`: a quoted-literal hint (`scan_hints`' own two literals are `abbrev"`/`opaque"`,
-- not `scan_binder_info`'s four).
#guard (run hintsProg 100 "scan_hints" [0] { bytes := #["\"abbrev\"".toUTF8.data] }).toOption.map (·.1)
  == some [8]
-- `"opaque"`: the other quoted literal.
#guard (run hintsProg 100 "scan_hints" [0] { bytes := #["\"opaque\"".toUTF8.data] }).toOption.map (·.1)
  == some [8]
-- Neither literal: fails.
#guard (run hintsProg 100 "scan_hints" [0] { bytes := #["\"nope\"".toUTF8.data] }).toOption.map (·.1)
  == some [0]

end L.Scan.Values
