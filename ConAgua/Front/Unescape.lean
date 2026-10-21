module

public import ConAgua.Scan.Str
public import ConAgua.Arena.Pool
meta import ConAgua.L.Semantics
meta import ConAgua.L.Examples
meta import ConAgua.Scan.Leaves
meta import ConAgua.Scan.Utf8
meta import ConAgua.Scan.Str

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

def utf8Put : FunDecl := lfn (top, k, cp) locals (q) {
  q := top + k;
  if cp < 128 {
    if len(POOL.u64) <= q { abort };
    POOL.u64[q] := cp;
    return k + 1
  };
  if cp < 2048 {
    if len(POOL.u64) <= q + 1 { abort };
    POOL.u64[q] := 192 + (cp >> 6);
    POOL.u64[q + 1] := 128 + (cp & 63);
    return k + 2
  };
  if cp < 65536 {
    if len(POOL.u64) <= q + 2 { abort };
    POOL.u64[q] := 224 + (cp >> 12);
    POOL.u64[q + 1] := 128 + ((cp >> 6) & 63);
    POOL.u64[q + 2] := 128 + (cp & 63);
    return k + 3
  };
  if len(POOL.u64) <= q + 3 { abort };
  POOL.u64[q] := 240 + (cp >> 18);
  POOL.u64[q + 1] := 128 + ((cp >> 12) & 63);
  POOL.u64[q + 2] := 128 + ((cp >> 6) & 63);
  POOL.u64[q + 3] := 128 + (cp & 63);
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

/-- The words `xs` written to the pool from `q` on. -/
def wrs (m : Mem) (q : Word) : List Word → Mem
  | [] => m
  | x :: xs => wrs (m.set64 POOL q x) (q + 1) xs

@[lang_grind =] theorem wrs_nil (m : Mem) (q : Word) : wrs m q [] = m := rfl
@[lang_grind =] theorem wrs_cons (m : Mem) (q x : Word) (xs : List Word) :
    wrs m q (x :: xs) = wrs (m.set64 POOL q x) (q + 1) xs := rfl

/-- **The model of `utf8_put`**: the bytes written and `k` advanced, `none` where the pool ends. -/
def u8PutW (m : Mem) (top k cp : Word) : Option (Word × Mem) :=
  if cp < 128 then
    if m.len64 POOL ≤ top + k then none else some (k + 1, wrs m (top + k) (encW cp))
  else if cp < 2048 then
    if m.len64 POOL ≤ top + k + 1 then none else some (k + 2, wrs m (top + k) (encW cp))
  else if cp < 65536 then
    if m.len64 POOL ≤ top + k + 2 then none else some (k + 3, wrs m (top + k) (encW cp))
  else if m.len64 POOL ≤ top + k + 3 then none else some (k + 4, wrs m (top + k) (encW cp))

/-! ## The loop -/

def escLoop : Stmt := lblk (vs, ve, top, k, j, c, ok, cp, jn) {
  while j < ve {
    c := IN.u8[j];
    if c != 92 {
      if len(POOL.u64) <= top + k { abort };
      POOL.u64[top + k] := c;
      k += 1;
      j += 1
    } else {
      (ok, cp, jn) := call esc_one(j, ve);
      if ok == 0 { abort };
      k := call utf8_put(top, k, cp);
      if jn <= j { abort };
      j := jn
    }
  }
}

def strPutEsc : FunDecl := lfn (vs, ve) locals (top, k, j, c, ok, cp, jn) {
  if ve < vs { abort };
  if len(IN.u8) < ve { abort };
  top := CTL.u64[0];
  if len(POOL.u64) < top { abort };
  j := vs;
  ⟪escLoop⟫;
  CTL.u64[0] := top + k;
  return (top, k)
}

/-- **The model of the loop** from `j`, `k` words written so far: the final `k` and memory. -/
def escLoopW (b : Array UInt8) (m : Mem) (top e j k : Word) : Option (Word × Mem) :=
  if h : j < e then
    if byteW b j ≠ 92 then
      if m.len64 POOL ≤ top + k then none
      else escLoopW b (m.set64 POOL (top + k) (byteW b j)) top e (j + 1) (k + 1)
    else if (escOneN b e j).1 = 0 then none
    else match u8PutW m top k (escOneN b e j).2.1 with
      | none => none
      | some (k', m') =>
        if hj : (escOneN b e j).2.2 ≤ j then none
        else escLoopW b m' top e (escOneN b e j).2.2 k'
  else some (k, m)
termination_by e.toNat - j.toNat
decreasing_by
  · have := UInt64.lt_iff_toNat_lt.mp h
    have : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := e.toNat_lt; omega
    omega
  · have := UInt64.lt_iff_toNat_lt.mp h
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hj)
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
  if ve < vs ∨ m.len8 IN < ve ∨ m.len64 POOL < m.top then none
  else finK m.top (escLoopW b m m.top ve vs 0)

/-! ## Arms of the loop model -/

section arms
variable (b : Array UInt8) (m : Mem) (top e j k : Word)

theorem escLoopW_end (h : ¬ j < e) : escLoopW b m top e j k = some (k, m) := by
  rw [escLoopW, dif_neg h]

theorem escLoopW_raw (h : j < e) (hj : j.toNat < b.size) (hc : b[j.toNat].toUInt64 ≠ 92)
    (hl : ¬ m.len64 POOL ≤ top + k) :
    escLoopW b m top e j k =
      escLoopW b (m.set64 POOL (top + k) b[j.toNat].toUInt64) top e (j + 1) (k + 1) := by
  have hb : byteW b j = b[j.toNat].toUInt64 := by simp [byteW, Array.getD, hj]
  rw [escLoopW, dif_pos h, hb, if_pos hc, if_neg hl]

theorem escLoopW_esc (k' : Word) (m' : Mem) (h : j < e) (hj : j.toNat < b.size)
    (hc : b[j.toNat].toUInt64 = 92) (ho : (escOneN b e j).1 ≠ 0)
    (hu : u8PutW m top k (escOneN b e j).2.1 = some (k', m')) (hn : j < (escOneN b e j).2.2) :
    escLoopW b m top e j k = escLoopW b m' top e (escOneN b e j).2.2 k' := by
  have hb : byteW b j = b[j.toNat].toUInt64 := by simp [byteW, Array.getD, hj]
  rw [escLoopW, dif_pos h, hb, if_neg (by simp [hc]), if_neg ho, hu]
  simp only [dif_neg (UInt64.not_le.mpr hn)]

end arms

grind_pattern [lang_grind] escLoopW_end => escLoopW b m top e j k
grind_pattern [lang_grind] escLoopW_raw => escLoopW b m top e j k, b[j.toNat]
grind_pattern [lang_grind] escLoopW_esc => escLoopW b m top e j k, b[j.toNat],
  escLoopW b m' top e (escOneN b e j).2.2 k'

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
        L.Scan.Str.byteIn_spec p b hb hpb n, L.Scan.Str.hex3_spec p b hb hpb hph hp3 n] <;> finish

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
        L.Scan.Str.byteIn_spec p b hb hpb n, L.Scan.Str.hex4_spec p b hb hpb hph hp4 n,
        escSur_spec p b hb hpb hph hp3 hps n] <;> finish

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

theorem escLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n escLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      escLoopW b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 4) (s₀.loc 3) = some (s'.loc 3, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := escLoop) rfl]
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, st64, ih,
        escOne_spec p b hb hpb hph hp4 hp3 hps hpo n, utf8Put_spec p hpu n] <;> finish

theorem escLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
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
