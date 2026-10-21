module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Utf8
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# `key_at` and `value_at` (`scan_fast.rs:183,704`)

`key_at(i, kl)` classifies the key whose opening quote is at `i` and whose contents are `kl`
bytes, and returns the key's code: the constructor index of con-leche's `Key`
(`ConLeche/Frontend/Scan/Types.lean`; `0` is `kUnknown`). The shape is con-leche's `keyAt`: a
switch on the first byte, then on the length, then an unrolled compare of the remaining bytes
against literals (`lit1`…`lit10`). Rust's `key_at` compares with `match_lit` against a `[u8; N]`
constant instead (its deviation 2); L has no slice type to pass a constant with, and the
unrolled compare needs none. The caller (`next_member`, `scan_hints`) has found the key's
closing quote at `i + 1 + kl`, so every byte the compare reads is in bounds: the spec has that
as a precondition, and the L code reads `IN.u8[…]` directly where con-leche's `byteAt` reads
`0` past the end.

The model `keyAtN` computes with words, as the L code does (`byteW` is the byte as a word, `0`
past the end); `ConAgua.Scan.KeyLink` relates it to con-leche's `keyAt`.

`value_at(i, ke)`: the position of a key's value, given the key's closing quote at `ke`, or `i`
when the colon is missing.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Key

open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN)

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `key_at` -/

/-- con-leche's `keyAt`, on words: the key's code (`Key.ctorIdx`), `0` for `kUnknown`.
Generated from `ConLeche/Frontend/Scan/Fast.lean`'s `keyAt`, branch for branch. -/
def keyAtN (b : Array UInt8) (i kl : Word) : Word :=
  let c := byteW b (i + 1)
  if c = 97 then  -- 'a'
    if kl = 3 then
      if byteW b (i + 2) = 112 ∧ byteW b (i + 3) = 112 then 2  -- "app"
      else if byteW b (i + 2) = 114 ∧ byteW b (i + 3) = 103 then 3  -- "arg"
      else if byteW b (i + 2) = 108 ∧ byteW b (i + 3) = 108 then 1  -- "all"
      else 0
    else if kl = 5 then
      if byteW b (i + 2) = 120 ∧ byteW b (i + 3) = 105 ∧ byteW b (i + 4) = 111 ∧ byteW b (i + 5) = 109 then 4  -- "axiom"
      else 0
    else 0
  else if c = 98 then  -- 'b'
    if kl = 4 then
      if byteW b (i + 2) = 111 ∧ byteW b (i + 3) = 100 ∧ byteW b (i + 4) = 121 then 6  -- "body"
      else if byteW b (i + 2) = 118 ∧ byteW b (i + 3) = 97 ∧ byteW b (i + 4) = 114 then 7  -- "bvar"
      else 0
    else if kl = 10 then
      if byteW b (i + 2) = 105 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 100 ∧ byteW b (i + 5) = 101 ∧ byteW b (i + 6) = 114 ∧ byteW b (i + 7) = 73 ∧ byteW b (i + 8) = 110 ∧ byteW b (i + 9) = 102 ∧ byteW b (i + 10) = 111 then 5  -- "binderInfo"
      else 0
    else 0
  else if c = 99 then  -- 'c'
    if kl = 5 then
      if byteW b (i + 2) = 111 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 115 ∧ byteW b (i + 5) = 116 then 9  -- "const"
      else if byteW b (i + 2) = 116 ∧ byteW b (i + 3) = 111 ∧ byteW b (i + 4) = 114 ∧ byteW b (i + 5) = 115 then 11  -- "ctors"
      else 0
    else if kl = 4 then
      if byteW b (i + 2) = 116 ∧ byteW b (i + 3) = 111 ∧ byteW b (i + 4) = 114 then 10  -- "ctor"
      else if byteW b (i + 2) = 105 ∧ byteW b (i + 3) = 100 ∧ byteW b (i + 4) = 120 then 8  -- "cidx"
      else 0
    else 0
  else if c = 100 then  -- 'd'
    if kl = 3 then
      if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 102 then 12  -- "def"
      else 0
    else 0
  else if c = 102 then  -- 'f'
    if kl = 2 then
      if byteW b (i + 2) = 110 then 13  -- "fn"
      else 0
    else if kl = 7 then
      if byteW b (i + 2) = 111 ∧ byteW b (i + 3) = 114 ∧ byteW b (i + 4) = 97 ∧ byteW b (i + 5) = 108 ∧ byteW b (i + 6) = 108 ∧ byteW b (i + 7) = 69 then 14  -- "forallE"
      else 0
    else 0
  else if c = 104 then  -- 'h'
    if kl = 5 then
      if byteW b (i + 2) = 105 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 116 ∧ byteW b (i + 5) = 115 then 15  -- "hints"
      else 0
    else 0
  else if c = 105 then  -- 'i'
    if kl = 2 then
      if byteW b (i + 2) = 101 then 18  -- "ie"
      else if byteW b (i + 2) = 110 then 21  -- "in"
      else if byteW b (i + 2) = 108 then 19  -- "il"
      else 0
    else if kl = 1 then
      16  -- kI
    else if kl = 3 then
      if byteW b (i + 2) = 100 ∧ byteW b (i + 3) = 120 then 17  -- "idx"
      else 0
    else if kl = 4 then
      if byteW b (i + 2) = 109 ∧ byteW b (i + 3) = 97 ∧ byteW b (i + 4) = 120 then 20  -- "imax"
      else 0
    else if kl = 9 then
      if byteW b (i + 2) = 110 ∧ byteW b (i + 3) = 100 ∧ byteW b (i + 4) = 117 ∧ byteW b (i + 5) = 99 ∧ byteW b (i + 6) = 116 ∧ byteW b (i + 7) = 105 ∧ byteW b (i + 8) = 118 ∧ byteW b (i + 9) = 101 then 23  -- "inductive"
      else 0
    else if kl = 5 then
      if byteW b (i + 2) = 115 ∧ byteW b (i + 3) = 82 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 99 then 24  -- "isRec"
      else 0
    else if kl = 11 then
      if byteW b (i + 2) = 115 ∧ byteW b (i + 3) = 82 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 102 ∧ byteW b (i + 6) = 108 ∧ byteW b (i + 7) = 101 ∧ byteW b (i + 8) = 120 ∧ byteW b (i + 9) = 105 ∧ byteW b (i + 10) = 118 ∧ byteW b (i + 11) = 101 then 25  -- "isReflexive"
      else 0
    else if kl = 8 then
      if byteW b (i + 2) = 115 ∧ byteW b (i + 3) = 85 ∧ byteW b (i + 4) = 110 ∧ byteW b (i + 5) = 115 ∧ byteW b (i + 6) = 97 ∧ byteW b (i + 7) = 102 ∧ byteW b (i + 8) = 101 then 26  -- "isUnsafe"
      else 0
    else if kl = 6 then
      if byteW b (i + 2) = 110 ∧ byteW b (i + 3) = 100 ∧ byteW b (i + 4) = 117 ∧ byteW b (i + 5) = 99 ∧ byteW b (i + 6) = 116 then 22  -- "induct"
      else 0
    else 0
  else if c = 107 then  -- 'k'
    if kl = 4 then
      if byteW b (i + 2) = 105 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 100 then 28  -- "kind"
      else 0
    else if kl = 1 then
      27  -- kK
    else 0
  else if c = 108 then  -- 'l'
    if kl = 3 then
      if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 109 then 29  -- "lam"
      else 0
    else if kl = 4 then
      if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 116 ∧ byteW b (i + 4) = 69 then 30  -- "letE"
      else 0
    else if kl = 11 then
      if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 118 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 108 ∧ byteW b (i + 6) = 80 ∧ byteW b (i + 7) = 97 ∧ byteW b (i + 8) = 114 ∧ byteW b (i + 9) = 97 ∧ byteW b (i + 10) = 109 ∧ byteW b (i + 11) = 115 then 31  -- "levelParams"
      else 0
    else 0
  else if c = 109 then  -- 'm'
    if kl = 3 then
      if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 120 then 32  -- "max"
      else 0
    else if kl = 4 then
      if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 116 ∧ byteW b (i + 4) = 97 then 33  -- "meta"
      else 0
    else 0
  else if c = 110 then  -- 'n'
    if kl = 4 then
      if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 101 then 34  -- "name"
      else 0
    else if kl = 3 then
      if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 then 38  -- "num"
      else 0
    else if kl = 6 then
      if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 116 ∧ byteW b (i + 4) = 86 ∧ byteW b (i + 5) = 97 ∧ byteW b (i + 6) = 108 then 35  -- "natVal"
      else if byteW b (i + 2) = 111 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 100 ∧ byteW b (i + 5) = 101 ∧ byteW b (i + 6) = 112 then 37  -- "nondep"
      else 0
    else if kl = 7 then
      if byteW b (i + 2) = 102 ∧ byteW b (i + 3) = 105 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 108 ∧ byteW b (i + 6) = 100 ∧ byteW b (i + 7) = 115 then 36  -- "nfields"
      else 0
    else if kl = 9 then
      if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 80 ∧ byteW b (i + 5) = 97 ∧ byteW b (i + 6) = 114 ∧ byteW b (i + 7) = 97 ∧ byteW b (i + 8) = 109 ∧ byteW b (i + 9) = 115 then 44  -- "numParams"
      else if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 70 ∧ byteW b (i + 5) = 105 ∧ byteW b (i + 6) = 101 ∧ byteW b (i + 7) = 108 ∧ byteW b (i + 8) = 100 ∧ byteW b (i + 9) = 115 then 39  -- "numFields"
      else if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 77 ∧ byteW b (i + 5) = 105 ∧ byteW b (i + 6) = 110 ∧ byteW b (i + 7) = 111 ∧ byteW b (i + 8) = 114 ∧ byteW b (i + 9) = 115 then 41  -- "numMinors"
      else if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 78 ∧ byteW b (i + 5) = 101 ∧ byteW b (i + 6) = 115 ∧ byteW b (i + 7) = 116 ∧ byteW b (i + 8) = 101 ∧ byteW b (i + 9) = 100 then 43  -- "numNested"
      else 0
    else if kl = 10 then
      if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 73 ∧ byteW b (i + 5) = 110 ∧ byteW b (i + 6) = 100 ∧ byteW b (i + 7) = 105 ∧ byteW b (i + 8) = 99 ∧ byteW b (i + 9) = 101 ∧ byteW b (i + 10) = 115 then 40  -- "numIndices"
      else if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 109 ∧ byteW b (i + 4) = 77 ∧ byteW b (i + 5) = 111 ∧ byteW b (i + 6) = 116 ∧ byteW b (i + 7) = 105 ∧ byteW b (i + 8) = 118 ∧ byteW b (i + 9) = 101 ∧ byteW b (i + 10) = 115 then 42  -- "numMotives"
      else 0
    else 0
  else if c = 111 then  -- 'o'
    if kl = 6 then
      if byteW b (i + 2) = 112 ∧ byteW b (i + 3) = 97 ∧ byteW b (i + 4) = 113 ∧ byteW b (i + 5) = 117 ∧ byteW b (i + 6) = 101 then 45  -- "opaque"
      else 0
    else 0
  else if c = 112 then  -- 'p'
    if kl = 3 then
      if byteW b (i + 2) = 114 ∧ byteW b (i + 3) = 101 then 47  -- "pre"
      else 0
    else if kl = 5 then
      if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 114 ∧ byteW b (i + 4) = 97 ∧ byteW b (i + 5) = 109 then 46  -- "param"
      else 0
    else if kl = 4 then
      if byteW b (i + 2) = 114 ∧ byteW b (i + 3) = 111 ∧ byteW b (i + 4) = 106 then 48  -- "proj"
      else 0
    else 0
  else if c = 113 then  -- 'q'
    if kl = 4 then
      if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 111 ∧ byteW b (i + 4) = 116 then 49  -- "quot"
      else 0
    else 0
  else if c = 114 then  -- 'r'
    if kl = 4 then
      if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 99 ∧ byteW b (i + 4) = 115 then 50  -- "recs"
      else 0
    else if kl = 5 then
      if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 108 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 115 then 53  -- "rules"
      else 0
    else if kl = 3 then
      if byteW b (i + 2) = 104 ∧ byteW b (i + 3) = 115 then 52  -- "rhs"
      else 0
    else if kl = 7 then
      if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 103 ∧ byteW b (i + 4) = 117 ∧ byteW b (i + 5) = 108 ∧ byteW b (i + 6) = 97 ∧ byteW b (i + 7) = 114 then 51  -- "regular"
      else 0
    else 0
  else if c = 115 then  -- 's'
    if kl = 3 then
      if byteW b (i + 2) = 116 ∧ byteW b (i + 3) = 114 then 56  -- "str"
      else 0
    else if kl = 4 then
      if byteW b (i + 2) = 111 ∧ byteW b (i + 3) = 114 ∧ byteW b (i + 4) = 116 then 55  -- "sort"
      else if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 99 ∧ byteW b (i + 4) = 99 then 59  -- "succ"
      else 0
    else if kl = 6 then
      if byteW b (i + 2) = 116 ∧ byteW b (i + 3) = 114 ∧ byteW b (i + 4) = 117 ∧ byteW b (i + 5) = 99 ∧ byteW b (i + 6) = 116 then 58  -- "struct"
      else if byteW b (i + 2) = 116 ∧ byteW b (i + 3) = 114 ∧ byteW b (i + 4) = 86 ∧ byteW b (i + 5) = 97 ∧ byteW b (i + 6) = 108 then 57  -- "strVal"
      else if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 102 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 116 ∧ byteW b (i + 6) = 121 then 54  -- "safety"
      else 0
    else 0
  else if c = 116 then  -- 't'
    if kl = 4 then
      if byteW b (i + 2) = 121 ∧ byteW b (i + 3) = 112 ∧ byteW b (i + 4) = 101 then 61  -- "type"
      else 0
    else if kl = 8 then
      if byteW b (i + 2) = 121 ∧ byteW b (i + 3) = 112 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 78 ∧ byteW b (i + 6) = 97 ∧ byteW b (i + 7) = 109 ∧ byteW b (i + 8) = 101 then 62  -- "typeName"
      else 0
    else if kl = 3 then
      if byteW b (i + 2) = 104 ∧ byteW b (i + 3) = 109 then 60  -- "thm"
      else 0
    else if kl = 5 then
      if byteW b (i + 2) = 121 ∧ byteW b (i + 3) = 112 ∧ byteW b (i + 4) = 101 ∧ byteW b (i + 5) = 115 then 63  -- "types"
      else 0
    else 0
  else if c = 117 then  -- 'u'
    if kl = 2 then
      if byteW b (i + 2) = 115 then 64  -- "us"
      else 0
    else 0
  else if c = 118 then  -- 'v'
    if kl = 5 then
      if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 108 ∧ byteW b (i + 4) = 117 ∧ byteW b (i + 5) = 101 then 65  -- "value"
      else 0
    else 0
  else 0


/-- `key_at(i, kl)`, generated from the same source as `keyAtN`. -/
def keyAt : FunDecl := lfn (i, kl) locals (c) {
  c := IN.u8[i + 1];
  if c == 97 {  -- 'a'
    if kl == 3 {
      if IN.u8[i + 2] == 112 && IN.u8[i + 3] == 112 { return 2 };  -- "app"
      if IN.u8[i + 2] == 114 && IN.u8[i + 3] == 103 { return 3 };  -- "arg"
      if IN.u8[i + 2] == 108 && IN.u8[i + 3] == 108 { return 1 };  -- "all"
      return 0
    };
    if kl == 5 {
      if IN.u8[i + 2] == 120 && IN.u8[i + 3] == 105 && IN.u8[i + 4] == 111 && IN.u8[i + 5] == 109 { return 4 };  -- "axiom"
      return 0
    };
    return 0
  };
  if c == 98 {  -- 'b'
    if kl == 4 {
      if IN.u8[i + 2] == 111 && IN.u8[i + 3] == 100 && IN.u8[i + 4] == 121 { return 6 };  -- "body"
      if IN.u8[i + 2] == 118 && IN.u8[i + 3] == 97 && IN.u8[i + 4] == 114 { return 7 };  -- "bvar"
      return 0
    };
    if kl == 10 {
      if IN.u8[i + 2] == 105 && IN.u8[i + 3] == 110 && IN.u8[i + 4] == 100 && IN.u8[i + 5] == 101 && IN.u8[i + 6] == 114 && IN.u8[i + 7] == 73 && IN.u8[i + 8] == 110 && IN.u8[i + 9] == 102 && IN.u8[i + 10] == 111 { return 5 };  -- "binderInfo"
      return 0
    };
    return 0
  };
  if c == 99 {  -- 'c'
    if kl == 5 {
      if IN.u8[i + 2] == 111 && IN.u8[i + 3] == 110 && IN.u8[i + 4] == 115 && IN.u8[i + 5] == 116 { return 9 };  -- "const"
      if IN.u8[i + 2] == 116 && IN.u8[i + 3] == 111 && IN.u8[i + 4] == 114 && IN.u8[i + 5] == 115 { return 11 };  -- "ctors"
      return 0
    };
    if kl == 4 {
      if IN.u8[i + 2] == 116 && IN.u8[i + 3] == 111 && IN.u8[i + 4] == 114 { return 10 };  -- "ctor"
      if IN.u8[i + 2] == 105 && IN.u8[i + 3] == 100 && IN.u8[i + 4] == 120 { return 8 };  -- "cidx"
      return 0
    };
    return 0
  };
  if c == 100 {  -- 'd'
    if kl == 3 {
      if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 102 { return 12 };  -- "def"
      return 0
    };
    return 0
  };
  if c == 102 {  -- 'f'
    if kl == 2 {
      if IN.u8[i + 2] == 110 { return 13 };  -- "fn"
      return 0
    };
    if kl == 7 {
      if IN.u8[i + 2] == 111 && IN.u8[i + 3] == 114 && IN.u8[i + 4] == 97 && IN.u8[i + 5] == 108 && IN.u8[i + 6] == 108 && IN.u8[i + 7] == 69 { return 14 };  -- "forallE"
      return 0
    };
    return 0
  };
  if c == 104 {  -- 'h'
    if kl == 5 {
      if IN.u8[i + 2] == 105 && IN.u8[i + 3] == 110 && IN.u8[i + 4] == 116 && IN.u8[i + 5] == 115 { return 15 };  -- "hints"
      return 0
    };
    return 0
  };
  if c == 105 {  -- 'i'
    if kl == 2 {
      if IN.u8[i + 2] == 101 { return 18 };  -- "ie"
      if IN.u8[i + 2] == 110 { return 21 };  -- "in"
      if IN.u8[i + 2] == 108 { return 19 };  -- "il"
      return 0
    };
    if kl == 1 {
      return 16  -- kI
    };
    if kl == 3 {
      if IN.u8[i + 2] == 100 && IN.u8[i + 3] == 120 { return 17 };  -- "idx"
      return 0
    };
    if kl == 4 {
      if IN.u8[i + 2] == 109 && IN.u8[i + 3] == 97 && IN.u8[i + 4] == 120 { return 20 };  -- "imax"
      return 0
    };
    if kl == 9 {
      if IN.u8[i + 2] == 110 && IN.u8[i + 3] == 100 && IN.u8[i + 4] == 117 && IN.u8[i + 5] == 99 && IN.u8[i + 6] == 116 && IN.u8[i + 7] == 105 && IN.u8[i + 8] == 118 && IN.u8[i + 9] == 101 { return 23 };  -- "inductive"
      return 0
    };
    if kl == 5 {
      if IN.u8[i + 2] == 115 && IN.u8[i + 3] == 82 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 99 { return 24 };  -- "isRec"
      return 0
    };
    if kl == 11 {
      if IN.u8[i + 2] == 115 && IN.u8[i + 3] == 82 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 102 && IN.u8[i + 6] == 108 && IN.u8[i + 7] == 101 && IN.u8[i + 8] == 120 && IN.u8[i + 9] == 105 && IN.u8[i + 10] == 118 && IN.u8[i + 11] == 101 { return 25 };  -- "isReflexive"
      return 0
    };
    if kl == 8 {
      if IN.u8[i + 2] == 115 && IN.u8[i + 3] == 85 && IN.u8[i + 4] == 110 && IN.u8[i + 5] == 115 && IN.u8[i + 6] == 97 && IN.u8[i + 7] == 102 && IN.u8[i + 8] == 101 { return 26 };  -- "isUnsafe"
      return 0
    };
    if kl == 6 {
      if IN.u8[i + 2] == 110 && IN.u8[i + 3] == 100 && IN.u8[i + 4] == 117 && IN.u8[i + 5] == 99 && IN.u8[i + 6] == 116 { return 22 };  -- "induct"
      return 0
    };
    return 0
  };
  if c == 107 {  -- 'k'
    if kl == 4 {
      if IN.u8[i + 2] == 105 && IN.u8[i + 3] == 110 && IN.u8[i + 4] == 100 { return 28 };  -- "kind"
      return 0
    };
    if kl == 1 {
      return 27  -- kK
    };
    return 0
  };
  if c == 108 {  -- 'l'
    if kl == 3 {
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 109 { return 29 };  -- "lam"
      return 0
    };
    if kl == 4 {
      if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 116 && IN.u8[i + 4] == 69 { return 30 };  -- "letE"
      return 0
    };
    if kl == 11 {
      if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 118 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 108 && IN.u8[i + 6] == 80 && IN.u8[i + 7] == 97 && IN.u8[i + 8] == 114 && IN.u8[i + 9] == 97 && IN.u8[i + 10] == 109 && IN.u8[i + 11] == 115 { return 31 };  -- "levelParams"
      return 0
    };
    return 0
  };
  if c == 109 {  -- 'm'
    if kl == 3 {
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 120 { return 32 };  -- "max"
      return 0
    };
    if kl == 4 {
      if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 116 && IN.u8[i + 4] == 97 { return 33 };  -- "meta"
      return 0
    };
    return 0
  };
  if c == 110 {  -- 'n'
    if kl == 4 {
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 101 { return 34 };  -- "name"
      return 0
    };
    if kl == 3 {
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 { return 38 };  -- "num"
      return 0
    };
    if kl == 6 {
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 116 && IN.u8[i + 4] == 86 && IN.u8[i + 5] == 97 && IN.u8[i + 6] == 108 { return 35 };  -- "natVal"
      if IN.u8[i + 2] == 111 && IN.u8[i + 3] == 110 && IN.u8[i + 4] == 100 && IN.u8[i + 5] == 101 && IN.u8[i + 6] == 112 { return 37 };  -- "nondep"
      return 0
    };
    if kl == 7 {
      if IN.u8[i + 2] == 102 && IN.u8[i + 3] == 105 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 108 && IN.u8[i + 6] == 100 && IN.u8[i + 7] == 115 { return 36 };  -- "nfields"
      return 0
    };
    if kl == 9 {
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 80 && IN.u8[i + 5] == 97 && IN.u8[i + 6] == 114 && IN.u8[i + 7] == 97 && IN.u8[i + 8] == 109 && IN.u8[i + 9] == 115 { return 44 };  -- "numParams"
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 70 && IN.u8[i + 5] == 105 && IN.u8[i + 6] == 101 && IN.u8[i + 7] == 108 && IN.u8[i + 8] == 100 && IN.u8[i + 9] == 115 { return 39 };  -- "numFields"
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 77 && IN.u8[i + 5] == 105 && IN.u8[i + 6] == 110 && IN.u8[i + 7] == 111 && IN.u8[i + 8] == 114 && IN.u8[i + 9] == 115 { return 41 };  -- "numMinors"
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 78 && IN.u8[i + 5] == 101 && IN.u8[i + 6] == 115 && IN.u8[i + 7] == 116 && IN.u8[i + 8] == 101 && IN.u8[i + 9] == 100 { return 43 };  -- "numNested"
      return 0
    };
    if kl == 10 {
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 73 && IN.u8[i + 5] == 110 && IN.u8[i + 6] == 100 && IN.u8[i + 7] == 105 && IN.u8[i + 8] == 99 && IN.u8[i + 9] == 101 && IN.u8[i + 10] == 115 { return 40 };  -- "numIndices"
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 109 && IN.u8[i + 4] == 77 && IN.u8[i + 5] == 111 && IN.u8[i + 6] == 116 && IN.u8[i + 7] == 105 && IN.u8[i + 8] == 118 && IN.u8[i + 9] == 101 && IN.u8[i + 10] == 115 { return 42 };  -- "numMotives"
      return 0
    };
    return 0
  };
  if c == 111 {  -- 'o'
    if kl == 6 {
      if IN.u8[i + 2] == 112 && IN.u8[i + 3] == 97 && IN.u8[i + 4] == 113 && IN.u8[i + 5] == 117 && IN.u8[i + 6] == 101 { return 45 };  -- "opaque"
      return 0
    };
    return 0
  };
  if c == 112 {  -- 'p'
    if kl == 3 {
      if IN.u8[i + 2] == 114 && IN.u8[i + 3] == 101 { return 47 };  -- "pre"
      return 0
    };
    if kl == 5 {
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 114 && IN.u8[i + 4] == 97 && IN.u8[i + 5] == 109 { return 46 };  -- "param"
      return 0
    };
    if kl == 4 {
      if IN.u8[i + 2] == 114 && IN.u8[i + 3] == 111 && IN.u8[i + 4] == 106 { return 48 };  -- "proj"
      return 0
    };
    return 0
  };
  if c == 113 {  -- 'q'
    if kl == 4 {
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 111 && IN.u8[i + 4] == 116 { return 49 };  -- "quot"
      return 0
    };
    return 0
  };
  if c == 114 {  -- 'r'
    if kl == 4 {
      if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 99 && IN.u8[i + 4] == 115 { return 50 };  -- "recs"
      return 0
    };
    if kl == 5 {
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 108 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 115 { return 53 };  -- "rules"
      return 0
    };
    if kl == 3 {
      if IN.u8[i + 2] == 104 && IN.u8[i + 3] == 115 { return 52 };  -- "rhs"
      return 0
    };
    if kl == 7 {
      if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 103 && IN.u8[i + 4] == 117 && IN.u8[i + 5] == 108 && IN.u8[i + 6] == 97 && IN.u8[i + 7] == 114 { return 51 };  -- "regular"
      return 0
    };
    return 0
  };
  if c == 115 {  -- 's'
    if kl == 3 {
      if IN.u8[i + 2] == 116 && IN.u8[i + 3] == 114 { return 56 };  -- "str"
      return 0
    };
    if kl == 4 {
      if IN.u8[i + 2] == 111 && IN.u8[i + 3] == 114 && IN.u8[i + 4] == 116 { return 55 };  -- "sort"
      if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 99 && IN.u8[i + 4] == 99 { return 59 };  -- "succ"
      return 0
    };
    if kl == 6 {
      if IN.u8[i + 2] == 116 && IN.u8[i + 3] == 114 && IN.u8[i + 4] == 117 && IN.u8[i + 5] == 99 && IN.u8[i + 6] == 116 { return 58 };  -- "struct"
      if IN.u8[i + 2] == 116 && IN.u8[i + 3] == 114 && IN.u8[i + 4] == 86 && IN.u8[i + 5] == 97 && IN.u8[i + 6] == 108 { return 57 };  -- "strVal"
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 102 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 116 && IN.u8[i + 6] == 121 { return 54 };  -- "safety"
      return 0
    };
    return 0
  };
  if c == 116 {  -- 't'
    if kl == 4 {
      if IN.u8[i + 2] == 121 && IN.u8[i + 3] == 112 && IN.u8[i + 4] == 101 { return 61 };  -- "type"
      return 0
    };
    if kl == 8 {
      if IN.u8[i + 2] == 121 && IN.u8[i + 3] == 112 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 78 && IN.u8[i + 6] == 97 && IN.u8[i + 7] == 109 && IN.u8[i + 8] == 101 { return 62 };  -- "typeName"
      return 0
    };
    if kl == 3 {
      if IN.u8[i + 2] == 104 && IN.u8[i + 3] == 109 { return 60 };  -- "thm"
      return 0
    };
    if kl == 5 {
      if IN.u8[i + 2] == 121 && IN.u8[i + 3] == 112 && IN.u8[i + 4] == 101 && IN.u8[i + 5] == 115 { return 63 };  -- "types"
      return 0
    };
    return 0
  };
  if c == 117 {  -- 'u'
    if kl == 2 {
      if IN.u8[i + 2] == 115 { return 64 };  -- "us"
      return 0
    };
    return 0
  };
  if c == 118 {  -- 'v'
    if kl == 5 {
      if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 108 && IN.u8[i + 4] == 117 && IN.u8[i + 5] == 101 { return 65 };  -- "value"
      return 0
    };
    return 0
  };
  return 0
}

/-! ## `value_at` -/

/-- con-leche's `valueAt` on words: past the colon, whitespace skipped on both sides; `i` when
the colon is missing. -/
def valueAtN (b : Array UInt8) (i ke : Word) : Word :=
  let p := UInt64.ofNat (skipWsN b (ke + 1).toNat)
  if p < UInt64.ofNat b.size ∧ byteW b p = 58 then UInt64.ofNat (skipWsN b (p + 1).toNat) else i

def valueAt : FunDecl := lfn (i, ke) locals (p, v) {
  p := call skip_ws(ke + 1);
  if p < len(IN.u8) && IN.u8[p] == 58 {
    v := call skip_ws(p + 1);
    return v
  };
  return i
}

/-! ## Specs -/

section keyAt
variable (p : Prog) (hp : p.lookup "key_at" = some keyAt) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hp hb

theorem keyAt_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at" [i, kl]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtN b i kl]; ⊤⦄ := by
  sorry

end keyAt

section valueAt
variable (p : Prog) (hp1 : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hp2 : p.lookup "value_at" = some valueAt) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hp1 hp2 hb

theorem valueAt_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i ke : Word)
    (hke : ke.toNat < b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "value_at" [i, ke]
    ⦃fun r s' => s' = s₀ ∧ r = [valueAtN b i ke]; ⊤⦄ := by
  sorry

end valueAt

/-- `value_at` returns `i` or a position inside the array or at its end. -/
theorem valueAtN_le (b : Array UInt8) (i ke : Word) (hi : i.toNat ≤ b.size) (hke : ke.toNat < b.size)
    (hb : b.size < 2 ^ 63) : (valueAtN b i ke).toNat ≤ b.size := by
  sorry

end L.Scan.Key
