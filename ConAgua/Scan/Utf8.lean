module

meta import ConAgua.L.Semantics
public import ConAgua.L.Notation
public import ConAgua.L.Logic
import ConAgua.L.PureEval
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# `utf8_decode` (`scan_fast.rs:917`)

Rust's `utf8_decode(b, j, e) -> Option<Vec<u32>>` decodes the bytes `[j, min(e, len))`. In L the
code points go to the word array `OUT` and the function returns `(1, count)`, or `(0, 0)` for
invalid UTF-8 (a `Vec` that would outgrow `OUT` is an out-of-bounds error). The body of Rust's
loop, one code point, is the function `utf8_char(k, n) -> (code point, length)`, length `0` for
invalid bytes: a use of several results.

The models compute with words, as the L code does (`utf8CharN` is the Rust branch structure on
`UInt64`), so the verification conditions and the model agree term for term.
`ConAgua.Scan.Utf8Link` relates them to Lean's own decoder (`String.fromUTF8?`, which is what
con-leche calls).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Utf8

/-- The output: one code point per word. -/
abbrev OUT : ArrId := 0

/-! ## `utf8_char`: one code point -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:624-644 ConLeche.Frontend.scanString -/
def utf8Char : FunDecl := lfn (k, n) locals (c0, c1, c2, c3, v) {
  c0 := IN.u8[k];
  if c0 < 0x80 { return (c0, 1) };
  if c0 < 0xC2 { return (0, 0) };
  if c0 < 0xE0 {
    if n <= k + 1 { return (0, 0) };
    c1 := IN.u8[k + 1];
    if c1 < 0x80 || 0xC0 <= c1 { return (0, 0) };
    return (((c0 & 0x1F) << 6) | (c1 & 0x3F), 2)
  };
  if c0 < 0xF0 {
    if n <= k + 2 { return (0, 0) };
    c1 := IN.u8[k + 1];
    c2 := IN.u8[k + 2];
    if c1 < 0x80 || 0xC0 <= c1 || c2 < 0x80 || 0xC0 <= c2 { return (0, 0) };
    v := ((c0 & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
    if v < 0x800 || (0xD800 <= v && v < 0xE000) { return (0, 0) };
    return (v, 3)
  };
  if c0 < 0xF5 {
    if n <= k + 3 { return (0, 0) };
    c1 := IN.u8[k + 1];
    c2 := IN.u8[k + 2];
    c3 := IN.u8[k + 3];
    if c1 < 0x80 || 0xC0 <= c1 || c2 < 0x80 || 0xC0 <= c2 || c3 < 0x80 || 0xC0 <= c3 {
      return (0, 0)
    };
    v := ((c0 & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
    if v < 0x10000 || 0x10FFFF < v { return (0, 0) };
    return (v, 4)
  };
  return (0, 0)
}

/-- Byte `k` of `b` as a word (`0` past the end; the code reads only bytes below `n`). -/
def byteW (b : Array UInt8) (k : Word) : Word := (b.getD k.toNat 0).toUInt64

/-- The body of Rust's loop at `k`: the code point and its length, `(0, 0)` if invalid. -/
def utf8CharN (b : Array UInt8) (k n : Word) : Word × Word :=
  let c0 := byteW b k
  if c0 < 0x80 then (c0, 1)
  else if c0 < 0xC2 then (0, 0)
  else if c0 < 0xE0 then
    if n ≤ k + 1 then (0, 0) else
    let c1 := byteW b (k + 1)
    if c1 < 0x80 ∨ 0xC0 ≤ c1 then (0, 0) else (((c0 &&& 0x1F) <<< 6) ||| (c1 &&& 0x3F), 2)
  else if c0 < 0xF0 then
    if n ≤ k + 2 then (0, 0) else
    let c1 := byteW b (k + 1)
    let c2 := byteW b (k + 2)
    if c1 < 0x80 ∨ 0xC0 ≤ c1 ∨ c2 < 0x80 ∨ 0xC0 ≤ c2 then (0, 0) else
    let v := ((c0 &&& 0x0F) <<< 12) ||| ((c1 &&& 0x3F) <<< 6) ||| (c2 &&& 0x3F)
    if v < 0x800 ∨ (0xD800 ≤ v ∧ v < 0xE000) then (0, 0) else (v, 3)
  else if c0 < 0xF5 then
    if n ≤ k + 3 then (0, 0) else
    let c1 := byteW b (k + 1)
    let c2 := byteW b (k + 2)
    let c3 := byteW b (k + 3)
    if c1 < 0x80 ∨ 0xC0 ≤ c1 ∨ c2 < 0x80 ∨ 0xC0 ≤ c2 ∨ c3 < 0x80 ∨ 0xC0 ≤ c3 then (0, 0) else
    let v := ((c0 &&& 0x07) <<< 18) ||| ((c1 &&& 0x3F) <<< 12) ||| ((c2 &&& 0x3F) <<< 6) |||
      (c3 &&& 0x3F)
    if v < 0x10000 ∨ 0x10FFFF < v then (0, 0) else (v, 4)
  else (0, 0)

theorem byteW_lt (b : Array UInt8) (k : Word) (h : k.toNat < b.size) :
    byteW b k = b[k.toNat].toUInt64 := by simp [byteW, h]

grind_pattern [lang_grind] byteW_lt => byteW b k, b[k.toNat]

/-- The length is at most four (so `k + len` does not wrap below `n`). -/
theorem utf8CharN_snd_le (b : Array UInt8) (k n : Word) : (utf8CharN b k n).2 ≤ 4 := by
  simp only [utf8CharN]
  repeat' split
  all_goals simp

grind_pattern [lang_grind] utf8CharN_snd_le => utf8CharN b k n

section utf8Char
variable (p : Prog) (hp : p.lookup "utf8_char" = some utf8Char) (b : Array UInt8)
include hp

attribute [local lang_grind] utf8CharN in
theorem utf8Char_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "utf8_char" [k, e]
    ⦃fun r s' => s' = s₀ ∧ r = [(utf8CharN b k e).1, (utf8CharN b k e).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, utf8Char]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, show ∀ m a k, L.rd8 m a k = byteW (m.arr8 a) k from
      fun _ _ _ => rfl, hm, Locals.init, St.setLoc_loc, St.setLoc_mem, List.getD_cons_zero,
      List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true, Bool.or_eq_true] at *
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [utf8CharN, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, utf8CharN]

end utf8Char

/-! ## `utf8_decode` -/

def utf8DecodeLoop : Stmt := lblk (j, e, n, k, cnt, cp, l) {
  while k < n {
    (cp, l) := call utf8_char(k, n);
    if l == 0 { return (0, 0) };
    OUT.u64[cnt] := cp;
    cnt += 1;
    k += l
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:624-644 ConLeche.Frontend.scanString -/
def utf8Decode : FunDecl := lfn (j, e) locals (n, k, cnt, cp, l) {
  if e < len(IN.u8) { n := e } else { n := len(IN.u8) };
  k := j;
  ⟪utf8DecodeLoop⟫;
  return (1, cnt)
}

/-- Rust's loop from `k` (with `cnt` code points written so far, memory `m`): the count at the
end, or `none` for invalid UTF-8 or a full `OUT` (L's store fails there), and the memory with
the code points written to `OUT`. -/
def utf8LoopN (b : Array UInt8) (k n cnt : Word) (m : Mem) : Option Word × Mem :=
  if k < n then
    if (utf8CharN b k n).2 = 0 then (none, m)
    else if cnt.toNat < (m.arr64 OUT).size ∧ k < k + (utf8CharN b k n).2 then
      utf8LoopN b (k + (utf8CharN b k n).2) n (cnt + 1) (m.set64 OUT cnt (utf8CharN b k n).1)
    else (none, m) -- `OUT` is full, or `k + len` wraps (it does not, below `n`)
  else (some cnt, m)
termination_by n.toNat - k.toNat
decreasing_by
  rename_i h1 _ h2
  have h2 := h2.2
  rw [UInt64.lt_iff_toNat_lt] at h1 h2
  omega

/-- What `utf8_decode` returns. -/
def encDecode : Option Word → List Word
  | some c => [1, c]
  | none => [0, 0]

section
variable (b : Array UInt8) (k n cnt : Word) (m : Mem)

theorem utf8LoopN_end (h : ¬ k < n) : utf8LoopN b k n cnt m = (some cnt, m) := by
  rw [utf8LoopN]; simp [h]
theorem utf8LoopN_bad (h : k < n) (h0 : (utf8CharN b k n).2 = 0) :
    utf8LoopN b k n cnt m = (none, m) := by
  rw [utf8LoopN]; simp [h, h0]
theorem utf8LoopN_step (k' cnt' : Word) (m' : Mem) (h : k < n) (h0 : (utf8CharN b k n).2 ≠ 0)
    (hc0 : cnt.toNat < (m.arr64 OUT).size) (hw : k < k + (utf8CharN b k n).2)
    (hk' : k' = k + (utf8CharN b k n).2) (hc : cnt' = cnt + 1)
    (hm' : m' = m.set64 OUT cnt (utf8CharN b k n).1) :
    utf8LoopN b k n cnt m = utf8LoopN b k' n cnt' m' := by
  subst hk' hc hm'; rw [utf8LoopN]; simp [h, h0, hw, hc0]

grind_pattern [lang_grind] utf8LoopN_end => utf8LoopN b k n cnt m
grind_pattern [lang_grind] utf8LoopN_bad => utf8LoopN b k n cnt m, utf8CharN b k n
grind_pattern [lang_grind] utf8LoopN_step => utf8LoopN b k n cnt m, utf8CharN b k n, utf8LoopN b k' n cnt' m'

end

attribute [local lang_grind] encDecode

section utf8Decode
variable (p : Prog) (hp1 : p.lookup "utf8_char" = some utf8Char)
    (hp2 : p.lookup "utf8_decode" = some utf8Decode) (b : Array UInt8) (hb : b.size + 4 < 2 ^ 64)
include hb hp1

/-- Rust's `utf8_decode(b, j, e)`: the loop over `[j, min(e, len))`. -/
def utf8DecodeN (b : Array UInt8) (j e : Word) (m : Mem) : Option Word × Mem :=
  utf8LoopN b j (if e < UInt64.ofNat b.size then e else UInt64.ofNat b.size) 0 m

end utf8Decode

/-- The program, as `#eval`-able code. -/
def utf8Prog : Prog := [("utf8_char", utf8Char), ("utf8_decode", utf8Decode)]

/-- Decode `s` with the L program: `some` code points, or `none`. -/
def runDecode (bs : List UInt8) : Option (List Word) :=
  match run utf8Prog 1000 "utf8_decode" [0, UInt64.ofNat bs.length]
      { bytes := #[bs.toArray], words := #[Array.replicate 64 0] } with
  | .ok ([1, c], m) => some ((m.arr64 OUT).toList.take c.toNat)
  | _ => none

-- con-ron's test `utf8_decode_agrees_with_the_toolchain`, against `String.fromUTF8?`.
#guard [[], "plain ascii".toUTF8.toList, [0xC3, 0xA9], [0xE2, 0x86, 0x92], [0xF0, 0x9F, 0x98, 0x80],
    [0x80], [0xC0, 0x80], [0xC1, 0xBF], [0xE0, 0x80, 0x80], [0xED, 0xA0, 0x80],
    [0xF4, 0x90, 0x80, 0x80], [0xF5, 0x80, 0x80, 0x80], [0xC3], [0xE2, 0x86], [0xF0, 0x9F, 0x98],
    [0xE2, 0x28, 0xA1], [0x41, 0xC3, 0xA9, 0x42]].all fun bs =>
  runDecode bs == (String.fromUTF8? ⟨bs.toArray⟩).map fun t => t.toList.map (·.toNat.toUInt64)

end L.Scan.Utf8
