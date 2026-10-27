module

meta import ConAgua.L.Semantics
meta import ConAgua.L.Examples
meta import ConAgua.Scan.Leaves
meta import ConAgua.Scan.Utf8
meta import ConAgua.Scan.Str
public import ConAgua.Scan.Str
public import ConAgua.Arena.Pool
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.Blocks
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `str_put_esc`: a string body into the pool, escapes decoded

`str_put_esc(vs, ve)` copies the body `[vs, ve)` of a JSON string (between its quotes, validated
by Stage B's `scan_string`) to the pool top, one byte per word, decoding the escapes as con-leche's
`unescape` does (`vendor/con-leche/ConLeche/Frontend/Scan/Fast.lean`): `\" \\ \/ \b \f \n \r \t`,
`\uXXXX` (a lone or unpaired surrogate is U+FFFD, a high surrogate followed by `\uDxxx` with a low
one is the pair's code point), each code point written as its UTF-8 bytes. It moves the top past
them and returns the slice `(o, l)`. Without escapes it is `str_put` (`ConAgua/Front/Apply.lean`).

* `esc_one(j, e)`: the escape at the backslash `j` of the body `[_, e)`: `(1, code point, next)`,
  or `(0, 0, 0)` for a bad escape (the L code then aborts). `esc_sur(j, e, v)` is its high-surrogate
  tail (as Stage B's `u_next`, its own function to keep verification conditions short). Reads past
  the body's end are `0` (`byte_in`), as con-leche's on the sliced-out body.
* `utf8_put(top, k, cp)`: the UTF-8 bytes of `cp` at `POOL[top + k ‥]`, `k` advanced; aborts
  where the pool ends.
* the loop: a raw byte is copied, an escape decoded and encoded.

The models (`escOneN`, `u8PutW`, `escLoopW`, `strPutEscW`) compute with words, as the L code
does; `ConAgua.Front.UnescapeLink` relates them to con-leche.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.Unescape

open L.Arena (POOL CTL)
open L.Scan.Utf8 (byteW)
open L.Scan.Str (byteE hex4N hex3N)

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `esc_one`, `esc_sur` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:563-622 ConLeche.Frontend.unescape -/
def escSur : FunDecl := lfn (j, e, v) locals (c, d, f, ok, w) {
  c := call byte_in(j + 6, e);
  d := call byte_in(j + 7, e);
  f := call byte_in(j + 8, e);
  if c == 92 && d == 117 && (f == 100 || f == 68) {
    (ok, w) := call hex3(j + 9, e);
    if ok != 0 {
      if w < 3072 { return (65533, j + 6) };
      return (((v & 1023) << 10) + (w & 1023) + 65536, j + 12)
    }
  };
  return (65533, j + 6)
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:563-622 ConLeche.Frontend.unescape -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:559-561 ConLeche.Frontend.replacementChar
@[l_impl ConLeche.Frontend.replacementChar]
def escOne : FunDecl := lfn (j, e) locals (d, ok, v, cp, jn) {
  d := call byte_in(j + 1, e);
  if d == 34 || d == 92 || d == 47 { return (1, d, j + 2) };
  if d == 98 { return (1, 8, j + 2) };
  if d == 102 { return (1, 12, j + 2) };
  if d == 110 { return (1, 10, j + 2) };
  if d == 114 { return (1, 13, j + 2) };
  if d == 116 { return (1, 9, j + 2) };
  if d != 117 { return (0, 0, 0) };
  (ok, v) := call hex4(j + 2, e);
  if ok == 0 { return (0, 0, 0) };
  if v < 55296 || 57344 <= v { return (1, v, j + 6) };
  if 56320 <= v { return (1, 65533, j + 6) };
  (cp, jn) := call esc_sur(j, e, v);
  return (1, cp, jn)
}

/-- The surrogate pair's code point. -/
def pairCp (v w : Word) : Word := ((v &&& 1023) <<< 10) + (w &&& 1023) + 65536

/-- `esc_sur(j, e, v)`: after a high surrogate `v` at `j`, the code point and where the body
continues. -/
def escSurN (b : Array UInt8) (e j v : Word) : Word × Word :=
  if byteE b e (j + 6) = 92 ∧ byteE b e (j + 7) = 117 ∧
      (byteE b e (j + 8) = 100 ∨ byteE b e (j + 8) = 68) ∧ (hex3N b e (j + 9)).1 ≠ 0 then
    if (hex3N b e (j + 9)).2 < 3072 then (65533, j + 6)
    else (pairCp v (hex3N b e (j + 9)).2, j + 12)
  else (65533, j + 6)

/-- `esc_one(j, e)`: `(ok, code point, next)`. -/
def escOneN (b : Array UInt8) (e j : Word) : Word × Word × Word :=
  if byteE b e (j + 1) = 34 ∨ byteE b e (j + 1) = 92 ∨ byteE b e (j + 1) = 47 then
    (1, byteE b e (j + 1), j + 2)
  else if byteE b e (j + 1) = 98 then (1, 8, j + 2)
  else if byteE b e (j + 1) = 102 then (1, 12, j + 2)
  else if byteE b e (j + 1) = 110 then (1, 10, j + 2)
  else if byteE b e (j + 1) = 114 then (1, 13, j + 2)
  else if byteE b e (j + 1) = 116 then (1, 9, j + 2)
  else if byteE b e (j + 1) ≠ 117 then (0, 0, 0)
  else if (hex4N b e (j + 2)).1 = 0 then (0, 0, 0)
  else if (hex4N b e (j + 2)).2 < 55296 ∨ 57344 ≤ (hex4N b e (j + 2)).2 then
    (1, (hex4N b e (j + 2)).2, j + 6)
  else if 56320 ≤ (hex4N b e (j + 2)).2 then (1, 65533, j + 6)
  else (1, (escSurN b e j (hex4N b e (j + 2)).2).1, (escSurN b e j (hex4N b e (j + 2)).2).2)

/-! ## `utf8_put` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:563-622 ConLeche.Frontend.unescape -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:556-557 ConLeche.Frontend.utf8Of
@[l_impl ConLeche.Frontend.utf8Of]
def utf8Put : FunDecl := lfn (top, k, cp) locals (q, pt, pb) {
  q := top + k;
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.base;
  if cp < 128 {
    if len(POOL⟨pt⟩) <= q - pb { abort };
    POOL⟨pt⟩[q - pb] := cp;
    return k + 1
  };
  if cp < 2048 {
    if len(POOL⟨pt⟩) <= q + 1 - pb { abort };
    POOL⟨pt⟩[q - pb] := 192 + (cp >> 6);
    POOL⟨pt⟩[q + 1 - pb] := 128 + (cp & 63);
    return k + 2
  };
  if cp < 65536 {
    if len(POOL⟨pt⟩) <= q + 2 - pb { abort };
    POOL⟨pt⟩[q - pb] := 224 + (cp >> 12);
    POOL⟨pt⟩[q + 1 - pb] := 128 + ((cp >> 6) & 63);
    POOL⟨pt⟩[q + 2 - pb] := 128 + (cp & 63);
    return k + 3
  };
  if len(POOL⟨pt⟩) <= q + 3 - pb { abort };
  POOL⟨pt⟩[q - pb] := 240 + (cp >> 18);
  POOL⟨pt⟩[q + 1 - pb] := 128 + ((cp >> 12) & 63);
  POOL⟨pt⟩[q + 2 - pb] := 128 + ((cp >> 6) & 63);
  POOL⟨pt⟩[q + 3 - pb] := 128 + (cp & 63);
  return k + 4
}

/-- The UTF-8 bytes of the code point `cp`, as words (`utf8_put`'s). -/
def encW (cp : Word) : List Word :=
  if cp < 128 then [cp]
  else if cp < 2048 then [(192 : Word) + (cp >>> 6), (128 : Word) + (cp &&& 63)]
  else if cp < 65536 then
    [(224 : Word) + (cp >>> 12), (128 : Word) + ((cp >>> 6) &&& 63), (128 : Word) + (cp &&& 63)]
  else [(240 : Word) + (cp >>> 18), (128 : Word) + ((cp >>> 12) &&& 63),
    (128 : Word) + ((cp >>> 6) &&& 63), (128 : Word) + (cp &&& 63)]

/-- The words `xs` written to the pool's tier `t` from the address `q` on, relative to the tier's
base `b` (`utf8_put`'s stores `POOL⟨t⟩[q - b]`, `POOL⟨t⟩[q + 1 - b]`, …). -/
def wrs (m : Mem) (t q b : Word) : List Word → Mem
  | [] => m
  | x :: xs => wrs (m.set64 (tierA 0 t) (q - b) x) t (q + 1) b xs

@[lang_grind =] theorem wrs_nil (m : Mem) (t q b : Word) : wrs m t q b [] = m := rfl
@[lang_grind =] theorem wrs_cons (m : Mem) (t q b x : Word) (xs : List Word) :
    wrs m t q b (x :: xs) = wrs (m.set64 (tierA 0 t) (q - b) x) t (q + 1) b xs := rfl

/-- **The model of `utf8_put`**: the bytes written and `k` advanced, `none` where the pool's tier
ends. -/
def u8PutW (m : Mem) (top k cp : Word) : Option (Word × Mem) :=
  if cp < 128 then
    if m.len64 (tierA 0 (top >>> 40)) ≤ top + k - (top >>> 40) <<< 40 then none
    else some (k + 1, wrs m (top >>> 40) (top + k) ((top >>> 40) <<< 40) (encW cp))
  else if cp < 2048 then
    if m.len64 (tierA 0 (top >>> 40)) ≤ top + k + (1 : Word) - (top >>> 40) <<< 40 then none
    else some (k + 2, wrs m (top >>> 40) (top + k) ((top >>> 40) <<< 40) (encW cp))
  else if cp < 65536 then
    if m.len64 (tierA 0 (top >>> 40)) ≤ top + k + (2 : Word) - (top >>> 40) <<< 40 then none
    else some (k + 3, wrs m (top >>> 40) (top + k) ((top >>> 40) <<< 40) (encW cp))
  else if m.len64 (tierA 0 (top >>> 40)) ≤ top + k + (3 : Word) - (top >>> 40) <<< 40 then none
  else some (k + 4, wrs m (top >>> 40) (top + k) ((top >>> 40) <<< 40) (encW cp))

/-! ## The loop -/

/-- One run of plain bytes up to the next backslash (`scan!`), copied as one block (`copy!`; lane
blkcopy2). -/
def escRun : Stmt := lblk (vs, ve, top, k, j, c, ok, cp, jn, pt, pb, d, n) {
  jn := scan!(IN.u8, j, ve, bslashC);
  d := pb + k;
  n := jn - j;
  if len(POOL⟨pt⟩) < d { abort };
  if len(POOL⟨pt⟩) - d < n { abort };
  copy!(POOL.u64⟨pt⟩, d, IN.u8, j, n);
  k := k + n;
  j := jn
}

/-- The loop: each run of plain bytes up to the next backslash is one block copy (`escRun`),
then the escape is decoded. -/
def escLoop : Stmt := lblk (vs, ve, top, k, j, c, ok, cp, jn, pt, pb, d, n) {
  while j < ve {
    ⟪escRun⟫;
    if j < ve {
      (ok, cp, jn) := call esc_one(j, ve);
      if ok == 0 { abort };
      k := call utf8_put(top, k, cp);
      if jn <= j { abort };
      j := jn
    }
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:563-622 ConLeche.Frontend.unescape -/
@[l_impl ConLeche.Frontend.unescape]
def strPutEsc : FunDecl := lfn (vs, ve) locals (top, k, j, c, ok, cp, jn, pt, pb, d, n) {
  if ve < vs { abort };
  if len(IN.u8) < ve { abort };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  j := vs;
  ⟪escLoop⟫;
  CTL.u64[0] := top + k;
  return (top, k)
}

/-- **The model of the loop** from `j`, `k` words written so far: the final `k` and memory. -/
def escLoopW (b : Array UInt8) (m : Mem) (top e j k : Word) : Option (Word × Mem) :=
  if _h : j < e then
    if byteW b j ≠ 92 then
      if m.len64 (tierA 0 (top >>> 40)) ≤ (top &&& 1099511627775) + k then none
      else escLoopW b (m.set64 (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + k) (byteW b j))
        top e (j + 1) (k + 1)
    else if (escOneN b e j).1 = 0 then none
    else match u8PutW m top k (escOneN b e j).2.1 with
      | none => none
      | some (k', m') =>
        if _hj : (escOneN b e j).2.2 ≤ j then none
        else escLoopW b m' top e (escOneN b e j).2.2 k'
  else some (k, m)
termination_by e.toNat - j.toNat
decreasing_by
  · have := UInt64.lt_iff_toNat_lt.mp _h
    have : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := e.toNat_lt; omega
    omega
  · have := UInt64.lt_iff_toNat_lt.mp _h
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp _hj)
    omega

/-- The end of `str_put_esc`: the top moved past the `k` words written. -/
def finK (top : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (k, m') => some (k, m'.set64 CTL 0 (top + k))

@[lang_grind =] theorem finK_none (top : Word) : finK top none = none := rfl
@[lang_grind =] theorem finK_some (top k : Word) (m' : Mem) :
    finK top (some (k, m')) = some (k, m'.set64 CTL 0 (top + k)) := rfl

/-- **The model of `str_put_esc(vs, ve)`**: the slice's length and the memory after. -/
def strPutEscW (b : Array UInt8) (m : Mem) (vs ve : Word) : Option (Word × Mem) :=
  if ve < vs ∨ m.len8 IN < ve ∨
    m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775) then none
  else finK m.top (escLoopW b m m.top ve vs 0)

/-! ## Arms of the loop model -/

section arms
variable (b : Array UInt8) (m : Mem) (top e j k : Word)

theorem escLoopW_end (h : ¬ j < e) : escLoopW b m top e j k = some (k, m) := by
  rw [escLoopW, dite_eq_right h]

theorem escLoopW_raw (h : j < e) (hj : j.toNat < b.size) (hc : b[j.toNat].toUInt64 ≠ 92)
    (hl : ¬ m.len64 (tierA 0 (top >>> 40)) ≤ (top &&& 1099511627775) + k) :
    escLoopW b m top e j k =
      escLoopW b (m.set64 (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + k) b[j.toNat].toUInt64)
        top e (j + 1) (k + 1) := by
  have hb : byteW b j = b[j.toNat].toUInt64 := by simp [byteW, Array.getD, hj]
  rw [escLoopW, dite_eq_left h, hb, ite_eq_left hc, ite_eq_right hl]

theorem escLoopW_esc (k' : Word) (m' : Mem) (h : j < e) (hj : j.toNat < b.size)
    (hc : b[j.toNat].toUInt64 = 92) (ho : (escOneN b e j).1 ≠ 0)
    (hu : u8PutW m top k (escOneN b e j).2.1 = some (k', m')) (hn : j < (escOneN b e j).2.2) :
    escLoopW b m top e j k = escLoopW b m' top e (escOneN b e j).2.2 k' := by
  have hb : byteW b j = b[j.toNat].toUInt64 := by simp [byteW, Array.getD, hj]
  rw [escLoopW, dite_eq_left h, hb, ite_eq_right (by simp [hc]), ite_eq_right ho, hu]
  simp only [dite_eq_right (UInt64.not_le.mpr hn)]

end arms

grind_pattern [lang_grind] escLoopW_end => escLoopW b m top e j k
grind_pattern [lang_grind] escLoopW_raw => escLoopW b m top e j k, b[j.toNat]
grind_pattern [lang_grind] escLoopW_esc => escLoopW b m top e j k, b[j.toNat],
  escLoopW b m' top e (escOneN b e j).2.2 k'

/-! ## The block form of the loop (lane blkcopy2) -/

theorem escTN_add_one (x : Word) (h : x.toNat + 1 < 2 ^ 64) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-- A backslash-free run `[j, j')` of the body is one block copy (`copy!`). -/
theorem escLoopW_skip (b : Array UInt8) : ∀ d (m : Mem) (top e j j' k : Word),
    j'.toNat - j.toNat = d → j ≤ j' → j' ≤ e → j'.toNat ≤ b.size →
    (∀ x, j.toNat ≤ x → x < j'.toNat → b[x]! ≠ 92) →
    ((top &&& 1099511627775) + k).toNat + d ≤ (m.len64 (tierA 0 (top >>> 40))).toNat →
    escLoopW b m top e j k =
      escLoopW b (m.copy8w (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + k) b j d)
        top e j' (k + UInt64.ofNat d) := by
  intro d
  induction d with
  | zero =>
    intro m top e j j' k hd h1 _ _ _ _
    have : j = j' := by
      have := UInt64.le_iff_toNat_le.mp h1; apply UInt64.toNat_inj.mp; omega
    subst this; simp [Mem.copy8w_zero]
  | succ d ih =>
    intro m top e j j' k hd h1 h2 hb hx hl
    have hj1 := UInt64.le_iff_toNat_le.mp h1
    have hj2 := UInt64.le_iff_toNat_le.mp h2
    have hjb : j.toNat < b.size := by omega
    have hje : j < e := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have hn : b[j.toNat].toUInt64 ≠ 92 := by
      have := hx j.toNat (Nat.le_refl _) (by omega)
      rw [getElem!_pos b j.toNat hjb] at this
      intro h; apply this
      have := congrArg UInt64.toUInt8 h; simpa using this
    have hL := (m.len64 (tierA 0 (top >>> 40))).toNat_lt
    rw [escLoopW_raw b m top e j k hje hjb hn (by rw [UInt64.le_iff_toNat_le]; omega)]
    have hj1' : (j + 1).toNat = j.toNat + 1 := escTN_add_one j (by have := j'.toNat_lt; omega)
    have hk1 : ((top &&& 1099511627775) + (k + 1)).toNat =
        ((top &&& 1099511627775) + k).toNat + 1 := by
      rw [← UInt64.add_assoc]; exact escTN_add_one _ (by omega)
    have hlen : ∀ (i v : Word), (m.set64 (tierA 0 (top >>> 40)) i v).len64 (tierA 0 (top >>> 40)) =
        m.len64 (tierA 0 (top >>> 40)) := fun i v => by simp only [Mem.len64, Mem.size64_set64]
    rw [ih _ top e (j + 1) j' (k + 1) (by omega) (UInt64.le_iff_toNat_le.mpr (by omega)) h2 hb
      (fun x h1 h2 => hx x (by omega) h2) (by rw [hlen, hk1]; omega)]
    rw [Mem.copy8w_succ, getElem!_pos b j.toNat hjb, UInt64.add_assoc]
    congr 2
    rw [UInt64.add_assoc]; congr 1
    rw [Nat.add_comm d 1, UInt64.ofNat_add]; rfl


/-- One iteration's run: the plain bytes from `j` to the next backslash (`scan!`), copied as one
block (`copy!`). -/
theorem escLoopW_run (b : Array UInt8) (m : Mem) (top e j k : Word) (h : j < e)
    (he : e.toNat ≤ b.size)
    (hl : ((top &&& 1099511627775) + k).toNat +
      (UInt64.ofNat (scanN b bslashC j.toNat e.toNat) - j).toNat ≤
        (m.len64 (tierA 0 (top >>> 40))).toNat) :
    escLoopW b m top e j k =
      escLoopW b (m.copy8w (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + k) b j
          (UInt64.ofNat (scanN b bslashC j.toNat e.toNat) - j).toNat)
        top e (UInt64.ofNat (scanN b bslashC j.toNat e.toNat))
        (k + (UInt64.ofNat (scanN b bslashC j.toNat e.toNat) - j)) := by
  have hj := UInt64.lt_iff_toNat_lt.mp h
  have hs1 := scanN_ge b bslashC j.toNat e.toNat
  have hs2 := scanN_le_end b bslashC j.toNat e.toNat (by omega)
  have he' := e.toNat_lt
  have hS : (UInt64.ofNat (scanN b bslashC j.toNat e.toNat)).toNat = scanN b bslashC j.toNat e.toNat := by
    simp only [UInt64.toNat_ofNat']; omega
  have hD : (UInt64.ofNat (scanN b bslashC j.toNat e.toNat) - j).toNat =
      scanN b bslashC j.toNat e.toNat - j.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hS]
  rw [hD] at hl ⊢
  rw [escLoopW_skip b _ m top e j _ k (by rw [hS]) (UInt64.le_iff_toNat_le.mpr (by omega))
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by omega) (fun x h1 h2 => ?_) hl]
  · congr 1
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', hD]
    congr 1; omega
  · have := L.Scan.Str.scanN_before b bslashC e.toNat j.toNat x h1 (by omega)
    intro hx; rw [hx] at this; exact absurd this (by decide)

/-- After a run that stops before the end, the loop is at a backslash: the escape arm. -/
theorem escLoopW_hit (b : Array UInt8) (m : Mem) (top e k k' : Word) (m' : Mem) (i : Nat)
    (hi : i ≤ e.toNat) (he : e.toNat ≤ b.size)
    (h : UInt64.ofNat (scanN b bslashC i e.toNat) < e)
    (ho : (escOneN b e (UInt64.ofNat (scanN b bslashC i e.toNat))).1 ≠ 0)
    (hu : u8PutW m top k (escOneN b e (UInt64.ofNat (scanN b bslashC i e.toNat))).2.1 = some (k', m'))
    (hn : UInt64.ofNat (scanN b bslashC i e.toNat) <
      (escOneN b e (UInt64.ofNat (scanN b bslashC i e.toNat))).2.2) :
    escLoopW b m top e (UInt64.ofNat (scanN b bslashC i e.toNat)) k =
      escLoopW b m' top e (escOneN b e (UInt64.ofNat (scanN b bslashC i e.toNat))).2.2 k' := by
  have hs2 := scanN_le_end b bslashC i e.toNat hi
  have he' := e.toNat_lt
  have hS : (UInt64.ofNat (scanN b bslashC i e.toNat)).toNat = scanN b bslashC i e.toNat := by
    simp only [UInt64.toNat_ofNat']; omega
  have hlt : scanN b bslashC i e.toNat < e.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp h; rw [hS] at this; exact this
  have hb : (UInt64.ofNat (scanN b bslashC i e.toNat)).toNat < b.size := by omega
  apply escLoopW_esc b m top e _ k k' m' h hb _ ho hu hn
  have := L.Examples.scanN_stop b bslashC e.toNat i hlt
  rw [(bslashC_mem _)] at this
  rw [getElem!_pos b _ (by omega)] at this
  simp only [hS, this]; rfl

grind_pattern [lang_grind] escLoopW_run => escLoopW b m top e j k, scanN b bslashC j.toNat e.toNat
grind_pattern [lang_grind] escLoopW_hit =>
  escLoopW b m top e (UInt64.ofNat (scanN b bslashC i e.toNat)) k,
  escLoopW b m' top e (escOneN b e (UInt64.ofNat (scanN b bslashC i e.toNat))).2.2 k'

/-! ## Tests -/

/-- The program. -/
def escProg : Prog :=
  [("byte_in", L.Scan.Str.byteIn), ("hex_val", L.Scan.Str.hexVal), ("hex4", L.Scan.Str.hex4),
   ("hex3", L.Scan.Str.hex3), ("esc_sur", escSur), ("esc_one", escOne), ("utf8_put", utf8Put),
   ("str_put_esc", strPutEsc)]

/-- Run `str_put_esc` over the whole input `s` with a 16-word pool; the pool words written. -/
def runEsc (s : String) : Option (List Word) :=
  let m : Mem := { bytes := #[s.toUTF8.data], words := #[Array.replicate 16 0, Array.replicate 4 0] }
  match run escProg 400 "str_put_esc" [0, UInt64.ofNat s.toUTF8.size] m with
  | .ok ([o, l], m') => some (((m'.arr64 POOL).extract o.toNat (o + l).toNat).toList)
  | _ => none

#guard runEsc "ab" == some [97, 98]
#guard runEsc "a\\nb\\\"" == some [97, 10, 98, 34]
#guard runEsc "\\u00e9" == some [0xC3, 0xA9]
#guard runEsc "\\u20AC" == some [0xE2, 0x82, 0xAC]
#guard runEsc "\\ud83d\\ude00" == some [0xF0, 0x9F, 0x98, 0x80]
#guard runEsc "\\ud83dx" == some [0xEF, 0xBF, 0xBD, 120]
#guard runEsc "\\ude00" == some [0xEF, 0xBF, 0xBD]
#guard runEsc "\\q" == none
#guard runEsc "\\u12" == none

end L.Front.Unescape

namespace L.Front.Unescape

open L.Arena (POOL CTL)
open L.Scan.Utf8 (byteW)
open L.Scan.Str (byteE hex4N hex3N)

/-! ## Specs -/

section specs
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
  (hpb : p.lookup "byte_in" = some L.Scan.Str.byteIn)
  (hph : p.lookup "hex_val" = some L.Scan.Str.hexVal)
  (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4)
  (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
  (hps : p.lookup "esc_sur" = some escSur)
  (hpo : p.lookup "esc_one" = some escOne)
  (hpu : p.lookup "utf8_put" = some utf8Put)
  (hpe : p.lookup "str_put_esc" = some strPutEsc)
include hb

omit hb in
include hpb hph hp3 hps in
attribute [local lang_grind] escSurN pairCp in
theorem escSur_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "esc_sur" [j, e, v]
    ⦃fun r s' => s' = s₀ ∧ r = [(escSurN b e j v).1, (escSurN b e j v).2]; ⊤⦄ := by
  rw [invoke_eq _ hps]
  simp only [callFn, escSur]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 24) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Str.byteIn_spec p b hpb n, L.Scan.Str.hex3_spec p b hpb hph hp3 n] <;> finish

omit hb in
include hpb hph hp4 hp3 hps hpo in
attribute [local lang_grind] escOneN in
theorem escOne_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "esc_one" [j, e]
    ⦃fun r s' => s' = s₀ ∧
      r = [(escOneN b e j).1, (escOneN b e j).2.1, (escOneN b e j).2.2]; ⊤⦄ := by
  rw [invoke_eq _ hpo]
  simp only [callFn, escOne]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 24) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Str.byteIn_spec p b hpb n, L.Scan.Str.hex4_spec p b hpb hph hp4 n,
        escSur_spec p b hpb hph hp3 hps n] <;> finish

end specs

section put
variable (p : Prog) (hpu : p.lookup "utf8_put" = some utf8Put)

include hpu in
theorem utf8Put_spec (n : Nat) (s₀ : St) (top k cp : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "utf8_put" [top, k, cp]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem.arr8 IN = s₀.mem.arr8 IN ∧
      u8PutW s₀.mem top k cp = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpu]
  simp only [callFn, utf8Put]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [u8PutW, encW]

end put

/-! ## The loop and `str_put_esc` -/

section loop
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
  (hpb : p.lookup "byte_in" = some L.Scan.Str.byteIn)
  (hph : p.lookup "hex_val" = some L.Scan.Str.hexVal)
  (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4)
  (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
  (hps : p.lookup "esc_sur" = some escSur)
  (hpo : p.lookup "esc_one" = some escOne)
  (hpu : p.lookup "utf8_put" = some utf8Put)
include hb hpb hph hp4 hp3 hps hpo hpu

omit hb hpb hph hp4 hp3 hps hpo hpu in
theorem escRun_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 9 = s.loc 2 >>> 40 ∧
      s.loc 10 = s.loc 2 &&& 1099511627775 ∧ s.loc 4 < s.loc 1⦄
    step p (exec p n) escRun
    ⦃fun r s' => r = .normal ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 9 = s₀.loc 9 ∧
      s'.loc 10 = s₀.loc 10 ∧ s'.mem.arr8 IN = b ∧ (s₀.loc 1).toNat ≤ b.size ∧
      s'.loc 4 = UInt64.ofNat (scanN b bslashC (s₀.loc 4).toNat (s₀.loc 1).toNat) ∧
      escLoopW b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 4) (s₀.loc 3) =
        escLoopW b s'.mem (s₀.loc 2) (s₀.loc 1) (s'.loc 4) (s'.loc 3); ⊤⦄ := by
  unfold escRun
  vcgen [step, evalE, evalC, evalArgs, setLoc, warr]
  all_goals (simp_all [Mem.src8, St.setLoc, Cmp.eval, BinOp.eval, Mem.copy8w_arr8])
  rename_i hp h0 h1 h2 _
  have h1' := UInt64.le_iff_toNat_le.mp h1
  have h2' := UInt64.le_iff_toNat_le.mp h2
  rw [UInt64.toNat_sub_of_le _ _ h1] at h2'
  exact escLoopW_run b _ _ _ _ _ hp.2.2.2 h0.2 (by omega)

theorem escLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 9 = s.loc 2 >>> 40 ∧
      s.loc 10 = s.loc 2 &&& 1099511627775⦄
    exec p n escLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      escLoopW b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 4) (s₀.loc 3) = some (s'.loc 3, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := escLoop) rfl]
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, escRun_spec p b n,
        escOne_spec p b hpb hph hp4 hp3 hps hpo n, utf8Put_spec p hpu n] <;> finish [Mem.src8]

theorem escLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 9 = s.loc 2 >>> 40 ∧
      s.loc 10 = s.loc 2 &&& 1099511627775⦄
    step p (exec p n) escLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      escLoopW b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 4) (s₀.loc 3) = some (s'.loc 3, s'.mem); ⊤⦄ :=
  Triple.step_exec (escLoop_spec p b hb hpb hph hp4 hp3 hps hpo hpu (n + 1) s₀)

theorem strPutEsc_specW (hpe : p.lookup "str_put_esc" = some strPutEsc) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (vs ve : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_put_esc" [vs, ve]
    ⦃fun r s' => LocEq s' s₀ ∧ r.headD 0 = s₀.mem.top ∧
      strPutEscW b s₀.mem vs ve = some (r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpe]
  simp only [callFn, strPutEsc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64,
        escLoop_step_spec p b hb hpb hph hp4 hp3 hps hpo hpu n] <;>
      finish [strPutEscW]

end loop

end L.Front.Unescape
