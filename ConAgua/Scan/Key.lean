module

meta import ConAgua.L.Semantics
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Utf8
import ConAgua.Census.Attr
public import ConAgua.L.PureEval
import ConAgua.L.GrindAttr
public import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `key_at` and `value_at` (`scan_fast.rs:183,704`)

`key_at(i, kl)` classifies the key whose opening quote is at `i` and whose contents are `kl`
bytes, and returns the key's code: the constructor index of con-leche's `Key`
(`ConLeche/Frontend/Scan/Types.lean`; `0` is `kUnknown`). The shape is con-leche's `keyAt`: a
switch on the first byte, then on the length, then an unrolled compare of the remaining bytes
against literals (`lit1`…`lit10`). Rust's `key_at` compares with `match_lit` against a `[u8; N]`
constant instead (its deviation 2); L has no slice type to pass a constant with, and the
unrolled compare needs none. The L code reads `IN.u8[…]` directly (an out-of-bounds read throws,
and the exception post is `⊤`, so `keyAt_spec` needs no bounds precondition) where con-leche's
`byteAt` reads `0` past the end.

The model `keyAtN` computes with words, as the L code does (`byteW` is the byte as a word, `0`
past the end); `ConAgua.Scan.KeyLink` relates it to con-leche's `keyAt`.

**Proof-only split.** `keyAt`/`keyAtN` dispatch on the first byte into ~20 letter arms, each with
its own length/literal switch, ~133 `return`s in total (con-leche's `keyAt`, generated branch for
branch). A single `vcgen`/`grind` call over the whole function does not finish (`whnf`/`isDefEq`
heartbeat timeouts at up to 20× the default budget, and even a trivial postcondition not
mentioning the model times out the same way — so the cost is `vcgen`'s own traversal of a ~133-arm
L statement, not the model side). A 4-letter slice (24 `return`s, about the size of `utf8Char`)
proves in 13s with the plain recipe, so `keyAt`/`keyAtN` are split here into six groups
`keyAtG1`…`keyAtG6` (`keyAtG1N`…`keyAtG6N`), balanced to ~21–24 `return`s each by letter, called
from a small dispatcher that reads `c` once and passes it on. This changes the shape of
`keyAt`/`keyAtN` (no longer one flat function) but not their behavior on any input; each group is
a contiguous slice of the original branches, unchanged byte for byte.

`value_at(i, ke)`: the position of a key's value, given the key's closing quote at `ke`, or `i`
when the colon is missing.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Key

open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN)

/-! ## `key_at` -/

/-- con-leche's `keyAt`, on words: the key's code (`Key.ctorIdx`), `0` for `kUnknown`.
Generated from `ConLeche/Frontend/Scan/Fast.lean`'s `keyAt`, branch for branch, then split into
six groups (see the module doc); `c` is the first byte (`byteW b (i + 1)`), already read by the
caller. Group 1: `i`, `d`. -/
def keyAtG1N (b : Array UInt8) (i kl : Word) (c : Word) : Word :=
  if c = 105 then  -- 'i'
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
  else if c = 100 then  -- 'd'
      if kl = 3 then
        if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 102 then 12  -- "def"
        else 0
      else 0
  else 0

/-- Group 2: n, h, o. -/
def keyAtG2N (b : Array UInt8) (i kl : Word) (c : Word) : Word :=
  if c = 110 then  -- 'n'
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
  else if c = 104 then  -- 'h'
      if kl = 5 then
        if byteW b (i + 2) = 105 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 116 ∧ byteW b (i + 5) = 115 then 15  -- "hints"
        else 0
      else 0
  else if c = 111 then  -- 'o'
      if kl = 6 then
        if byteW b (i + 2) = 112 ∧ byteW b (i + 3) = 97 ∧ byteW b (i + 4) = 113 ∧ byteW b (i + 5) = 117 ∧ byteW b (i + 6) = 101 then 45  -- "opaque"
        else 0
      else 0
  else 0

/-- Group 3: s, t, q. -/
def keyAtG3N (b : Array UInt8) (i kl : Word) (c : Word) : Word :=
  if c = 115 then  -- 's'
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
  else if c = 113 then  -- 'q'
      if kl = 4 then
        if byteW b (i + 2) = 117 ∧ byteW b (i + 3) = 111 ∧ byteW b (i + 4) = 116 then 49  -- "quot"
        else 0
      else 0
  else 0

/-- Group 4: r, v, k, u. -/
def keyAtG4N (b : Array UInt8) (i kl : Word) (c : Word) : Word :=
  if c = 114 then  -- 'r'
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
  else if c = 118 then  -- 'v'
      if kl = 5 then
        if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 108 ∧ byteW b (i + 4) = 117 ∧ byteW b (i + 5) = 101 then 65  -- "value"
        else 0
      else 0
  else if c = 107 then  -- 'k'
      if kl = 4 then
        if byteW b (i + 2) = 105 ∧ byteW b (i + 3) = 110 ∧ byteW b (i + 4) = 100 then 28  -- "kind"
        else 0
      else if kl = 1 then
        27  -- kK
      else 0
  else if c = 117 then  -- 'u'
      if kl = 2 then
        if byteW b (i + 2) = 115 then 64  -- "us"
        else 0
      else 0
  else 0

/-- Group 5: p, l, c. -/
def keyAtG5N (b : Array UInt8) (i kl : Word) (c : Word) : Word :=
  if c = 112 then  -- 'p'
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
  else 0

/-- Group 6: a, b, m, f. -/
def keyAtG6N (b : Array UInt8) (i kl : Word) (c : Word) : Word :=
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
  else if c = 109 then  -- 'm'
      if kl = 3 then
        if byteW b (i + 2) = 97 ∧ byteW b (i + 3) = 120 then 32  -- "max"
        else 0
      else if kl = 4 then
        if byteW b (i + 2) = 101 ∧ byteW b (i + 3) = 116 ∧ byteW b (i + 4) = 97 then 33  -- "meta"
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
  else 0

/-- `keyAtN`: the dispatch on the first byte `c`, split (proof-only refactor, see below)
into six groups `keyAtG1N`…`keyAtG6N` above, roughly balanced by branch count. -/
def keyAtN (b : Array UInt8) (i kl : Word) : Word :=
  let c := byteW b (i + 1)
  if c = 105 ∨ c = 100 then keyAtG1N b i kl c
  else if c = 110 ∨ c = 104 ∨ c = 111 then keyAtG2N b i kl c
  else if c = 115 ∨ c = 116 ∨ c = 113 then keyAtG3N b i kl c
  else if c = 114 ∨ c = 118 ∨ c = 107 ∨ c = 117 then keyAtG4N b i kl c
  else if c = 112 ∨ c = 108 ∨ c = 99 then keyAtG5N b i kl c
  else if c = 97 ∨ c = 98 ∨ c = 109 ∨ c = 102 then keyAtG6N b i kl c
  else 0

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt -/
@[l_impl ConLeche.Frontend.keyAt]
def keyAtG1 : FunDecl := lfn (i, kl, c) {
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
  if c == 100 {  -- 'd'
      if kl == 3 {
        if IN.u8[i + 2] == 101 && IN.u8[i + 3] == 102 { return 12 };  -- "def"
        return 0
      };
      return 0
  };
  return 0
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt -/
@[l_impl ConLeche.Frontend.keyAt]
def keyAtG2 : FunDecl := lfn (i, kl, c) {
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
  if c == 104 {  -- 'h'
      if kl == 5 {
        if IN.u8[i + 2] == 105 && IN.u8[i + 3] == 110 && IN.u8[i + 4] == 116 && IN.u8[i + 5] == 115 { return 15 };  -- "hints"
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
  return 0
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt -/
@[l_impl ConLeche.Frontend.keyAt]
def keyAtG3 : FunDecl := lfn (i, kl, c) {
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
  if c == 113 {  -- 'q'
      if kl == 4 {
        if IN.u8[i + 2] == 117 && IN.u8[i + 3] == 111 && IN.u8[i + 4] == 116 { return 49 };  -- "quot"
        return 0
      };
      return 0
  };
  return 0
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt -/
@[l_impl ConLeche.Frontend.keyAt]
def keyAtG4 : FunDecl := lfn (i, kl, c) {
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
  if c == 118 {  -- 'v'
      if kl == 5 {
        if IN.u8[i + 2] == 97 && IN.u8[i + 3] == 108 && IN.u8[i + 4] == 117 && IN.u8[i + 5] == 101 { return 65 };  -- "value"
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
  if c == 117 {  -- 'u'
      if kl == 2 {
        if IN.u8[i + 2] == 115 { return 64 };  -- "us"
        return 0
      };
      return 0
  };
  return 0
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt -/
@[l_impl ConLeche.Frontend.keyAt]
def keyAtG5 : FunDecl := lfn (i, kl, c) {
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
  return 0
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt -/
@[l_impl ConLeche.Frontend.keyAt]
def keyAtG6 : FunDecl := lfn (i, kl, c) {
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
  return 0
}

/-- `key_at(i, kl)`, split into the six groups above (same reason as `keyAtN`). -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:224-443 ConLeche.Frontend.keyAt
@[l_impl ConLeche.Frontend.keyAt]
def keyAt : FunDecl := lfn (i, kl) locals (c, g) {
  c := IN.u8[i + 1];
  if c == 105 || c == 100 { g := call key_at_g1(i, kl, c); return g };
  if c == 110 || c == 104 || c == 111 { g := call key_at_g2(i, kl, c); return g };
  if c == 115 || c == 116 || c == 113 { g := call key_at_g3(i, kl, c); return g };
  if c == 114 || c == 118 || c == 107 || c == 117 { g := call key_at_g4(i, kl, c); return g };
  if c == 112 || c == 108 || c == 99 { g := call key_at_g5(i, kl, c); return g };
  if c == 97 || c == 98 || c == 109 || c == 102 { g := call key_at_g6(i, kl, c); return g };
  return 0
}

/-! ## `value_at` -/

/-- con-leche's `valueAt` on words: past the colon, whitespace skipped on both sides; `i` when
the colon is missing. -/
def valueAtN (b : Array UInt8) (i ke : Word) : Word :=
  let p := UInt64.ofNat (skipWsN b (ke + 1).toNat)
  if p < UInt64.ofNat b.size ∧ byteW b p = 58 then UInt64.ofNat (skipWsN b (p + 1).toNat) else i

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:445-450 ConLeche.Frontend.valueAt -/
@[l_impl ConLeche.Frontend.valueAt]
def valueAt : FunDecl := lfn (i, ke) locals (p, v) {
  p := call skip_ws(ke + 1);
  if p < len(IN.u8) && IN.u8[p] == 58 {
    v := call skip_ws(p + 1);
    return v
  };
  return i
}

/-- `skipWsN` never walks past the end of the array (mirrors `L.Scan.Leaves.skipDigitsN_le`,
which we cannot add a lemma next to since we only own `Key.lean`/`Values.lean`). -/
theorem skipWsN_le (b : Array UInt8) (i : Nat) (h : i ≤ b.size) : skipWsN b i ≤ b.size := by
  induction i using L.Scan.Leaves.skipWsN.induct b with
  | case1 i h' hc ih => rw [skipWsN]; simp [h', hc]; omega
  | case2 i h' hc => rw [skipWsN]; simp [h', hc]; omega
  | case3 i h' => rw [skipWsN]; simp [h']; omega

grind_pattern [lang_grind] skipWsN_le => skipWsN b i

/-! ## Specs -/

/-- `rd8` (`L.PureEval`) on the input is `byteW`. -/
theorem rd8_byteW (m : Mem) (a : ArrId) (k : Word) : L.rd8 m a k = byteW (m.arr8 a) k := rfl

section keyAtGroups
variable (p : Prog) (b : Array UInt8)

attribute [local lang_grind] keyAtG1N in
theorem keyAtG1_spec (hp : p.lookup "key_at_g1" = some keyAtG1) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at_g1" [i, kl, c]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtG1N b i kl c]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAtG1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, rd8_byteW, hm, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true,
      beq_iff_eq] at *
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [keyAtG1N, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, keyAtG1N]

attribute [local lang_grind] keyAtG2N in
theorem keyAtG2_spec (hp : p.lookup "key_at_g2" = some keyAtG2) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at_g2" [i, kl, c]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtG2N b i kl c]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAtG2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    -- `evalC_spec`: one path per `if`, not one per exit of the 8-byte `&&` chains, whose
    -- `return 0` tails multiplied (DESIGN.md, "Slow declarations").
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, rd8_byteW, hm, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true,
      beq_iff_eq] at *
    -- `subst_vars` drops the `Bool` copies of the conditions (`a = (x == k && …)`), on which
    -- `grind` split (12 s for the fall-through of the `kl = 9` names). With the path decided by
    -- the hypotheses, `simp` evaluates the model; `grind` only for what is left.
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [keyAtG2N, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, keyAtG2N]

attribute [local lang_grind] keyAtG3N in
theorem keyAtG3_spec (hp : p.lookup "key_at_g3" = some keyAtG3) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at_g3" [i, kl, c]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtG3N b i kl c]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAtG3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, rd8_byteW, hm, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true,
      beq_iff_eq] at *
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [keyAtG3N, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, keyAtG3N]

attribute [local lang_grind] keyAtG4N in
theorem keyAtG4_spec (hp : p.lookup "key_at_g4" = some keyAtG4) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at_g4" [i, kl, c]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtG4N b i kl c]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAtG4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, rd8_byteW, hm, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true,
      beq_iff_eq] at *
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [keyAtG4N, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, keyAtG4N]

attribute [local lang_grind] keyAtG5N in
theorem keyAtG5_spec (hp : p.lookup "key_at_g5" = some keyAtG5) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at_g5" [i, kl, c]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtG5N b i kl c]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAtG5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, rd8_byteW, hm, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true,
      beq_iff_eq] at *
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [keyAtG5N, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, keyAtG5N]

attribute [local lang_grind] keyAtG6N in
theorem keyAtG6_spec (hp : p.lookup "key_at_g6" = some keyAtG6) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at_g6" [i, kl, c]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtG6N b i kl c]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAtG6]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, rd8_byteW, hm, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true,
      beq_iff_eq] at *
    all_goals clear hp
    all_goals subst_vars
    all_goals first
      | (simp only [keyAtG6N, Sig.retVal, Sig.retOr, *, reduceIte]; done)
      | grind (splits := 40) [lang_grind, keyAtG6N]

end keyAtGroups

section keyAt
variable (p : Prog)
    (hp1 : p.lookup "key_at_g1" = some keyAtG1) (hp2 : p.lookup "key_at_g2" = some keyAtG2)
    (hp3 : p.lookup "key_at_g3" = some keyAtG3) (hp4 : p.lookup "key_at_g4" = some keyAtG4)
    (hp5 : p.lookup "key_at_g5" = some keyAtG5) (hp6 : p.lookup "key_at_g6" = some keyAtG6)
    (hp : p.lookup "key_at" = some keyAt) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hp hp1 hp2 hp3 hp4 hp5 hp6 hb

-- `key_at(i, kl)` against `keyAtN`, via the six group calls (see the module doc for why
-- `keyAt`/`keyAtN` are split this way): composed from `keyAtG1_spec`…`keyAtG6_spec` exactly as
-- `scan_bool` composes from two `match_lit` calls (`ConAgua.Scan.Lit`). No bounds precondition: an
-- out-of-bounds read throws, and the exception post is `⊤`.
omit hb in
attribute [local lang_grind] keyAtN in
@[refines ConLeche.Frontend.keyAt]
theorem keyAt_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i kl : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "key_at" [i, kl]
    ⦃fun r s' => s' = s₀ ∧ r = [keyAtN b i kl]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, keyAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        keyAtG1_spec p b hp1 n, keyAtG2_spec p b hp2 n, keyAtG3_spec p b hp3 n,
        keyAtG4_spec p b hp4 n, keyAtG5_spec p b hp5 n, keyAtG6_spec p b hp6 n] <;> finish

end keyAt

section valueAt
variable (p : Prog) (hp1 : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hp2 : p.lookup "value_at" = some valueAt) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hp1 hp2 hb

attribute [local lang_grind] valueAtN in
@[refines ConLeche.Frontend.valueAt]
theorem valueAt_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i ke : Word)
    (hke : ke.toNat < b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "value_at" [i, ke]
    ⦃fun r s' => s' = s₀ ∧ r = [valueAtN b i ke]; ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, valueAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hstep : ∀ j : Word, (j + 1).toNat ≤ j.toNat + 1 := fun j => by
      simp [UInt64.toNat_add]; omega
    have hofnat_le : ∀ j : Nat, (UInt64.ofNat j).toNat ≤ j := fun _ => UInt64.toNat_ofNat_le
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Scan.Leaves.skipWs_spec p hp1 b hb64 n] <;> finish

end valueAt

/-- `value_at` returns `i` or a position inside the array or at its end. -/
theorem valueAtN_le (b : Array UInt8) (i ke : Word) (hi : i.toNat ≤ b.size) (hke : ke.toNat < b.size)
    (hb : b.size < 2 ^ 63) : (valueAtN b i ke).toNat ≤ b.size := by
  have hke' : ke < UInt64.ofNat b.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']; omega
  have hke1 : (ke + 1).toNat = ke.toNat + 1 := L.Scan.toNat_add_one_of_lt_ofNat hke'
  have h1 : (ke + 1).toNat ≤ b.size := by omega
  have h2 : L.Scan.Leaves.skipWsN b (ke + 1).toNat ≤ b.size := skipWsN_le b _ h1
  simp only [valueAtN]
  split
  · next hcond =>
    have hplt := hcond.1
    have hp_le : (UInt64.ofNat (L.Scan.Leaves.skipWsN b (ke + 1).toNat)).toNat ≤ b.size := by
      have := @UInt64.toNat_ofNat_le (L.Scan.Leaves.skipWsN b (ke + 1).toNat); omega
    have hplt' := L.Scan.lt_of_lt_ofNat hplt
    have hp1 : (UInt64.ofNat (L.Scan.Leaves.skipWsN b (ke + 1).toNat) + 1).toNat
        = (UInt64.ofNat (L.Scan.Leaves.skipWsN b (ke + 1).toNat)).toNat + 1 :=
      L.Scan.toNat_add_one_of_lt_ofNat hplt
    have h3 : (UInt64.ofNat (L.Scan.Leaves.skipWsN b (ke + 1).toNat) + 1).toNat ≤ b.size := by omega
    have h4 := skipWsN_le b _ h3
    have := @UInt64.toNat_ofNat_le
      (L.Scan.Leaves.skipWsN b (UInt64.ofNat (L.Scan.Leaves.skipWsN b (ke + 1).toNat) + 1).toNat)
    omega
  · next => exact hi

grind_pattern [lang_grind] valueAtN_le => valueAtN b i ke

/-- The program, as `#eval`-able code. -/
def keyProg : Prog :=
  [("key_at_g1", keyAtG1), ("key_at_g2", keyAtG2), ("key_at_g3", keyAtG3),
   ("key_at_g4", keyAtG4), ("key_at_g5", keyAtG5), ("key_at_g6", keyAtG6), ("key_at", keyAt)]

#guard (run keyProg 100 "key_at" [0, 3] { bytes := #["\"app\"".toUTF8.data] }).toOption.map (·.1)
  == some [2]
#guard (run keyProg 100 "key_at" [0, 10] { bytes := #["\"binderInfo\"".toUTF8.data] }).toOption.map (·.1)
  == some [5]
#guard (run keyProg 100 "key_at" [0, 3] { bytes := #["\"xyz\"".toUTF8.data] }).toOption.map (·.1)
  == some [0]

end L.Scan.Key
