module

@[expose] public section

/-!
# The hash of a big `Nat` literal: the one native function

`natBigHash n` mixes all 64-bit words of `n` with Lean's `mixHash`
(`native/nat_hash.c`).  It is VENDORED FROM lean4#16146 (which fixes
lean4#15686): the C of that PR's `Literal.natHash`, under upstream's own
symbol `lean_nat_big_hash`.  The v4.36.0 runtime does not export it; a
toolchain that ships lean4#16146 does, and then the link fails on the
duplicate definition.

THE PLAN AT THAT BUMP (the first stable toolchain containing
lean4#16146).  That runtime's `lean.h` defines `lean_nat_hash`, the
whole hash (the number itself for a scalar, `lean_nat_big_hash` for a big
number), as an inline function.  Then `natHash` (`Kernel/Expr.lean`)
becomes our own declaration against that symbol,

    @[extern "lean_nat_hash"] opaque natHash (n : @& Nat) : UInt64

(not `Lean.Literal.natHash`: con-leche keeps its own `Expr` and does not
import `Lean`), and this module, `native/nat_hash.c`, `natHashWordBound`
and the native section of `lakefile.lean` are deleted; the lakefile can
go back to `lakefile.toml`.  The pinner whose toolchain already ships
the PR (`pinners/leanprover-lean4-nightly-nightly-2026-11-16/`) builds
this module without our C and links the runtime's function.

Why C (the maintainer's one deliberate exception to "no C"):
`Hashable Nat` is `n mod 2^64`, so literals that agree in their low 64
bits — all multiples of `2^64` (lean4#15686), the packed matrices of
CFSG's certificate computations (DESIGN #598) — shared one hash, and
every memo lookup among them walked one bucket.  A hash that reads every
word is one linear pass in C; Lean has no word access to a big `Nat`,
and reading the words with `% 2^64` and `>>> 64` costs a copy per word,
quadratic in the literal's size.

To the proofs `natBigHash` is an opaque function of the number: equal
literals have equal hashes whatever it computes, which is all a
`LawfulHashable` instance asks.  It is its own library (`ConLecheNative`
in `lakefile.lean`), compiled to native code, so that the interpreter
(elaboration-time code and the test library's `#eval`s) can call it too.
-/

namespace ConLeche

/-- **The hash of a `Nat` reading all its bits** (`native/nat_hash.c`,
vendored from lean4#16146; at the bump to a toolchain that ships it,
replaced by `@[extern "lean_nat_hash"] opaque natHash`, see the module
header): all 64-bit words of a big number mixed.  Only for `n ≥ 2^64`,
which is an mpz object, as upstream's `lean_nat_big_hash` (`natHash` in
`Kernel/Expr.lean` answers below). -/
-- con-agua patch: no `native/nat_hash.c` here (our `lakefile.toml` compiles no C, and the
-- nightly-2026-10-20 runtime does not export `lean_nat_big_hash`): the compiled code is this Lean
-- fold over the 64-bit words, low to high, split in halves so that it costs `O(n log n)` (a
-- word-by-word `>>> 64` would be quadratic). Only our tools' compiled code runs it. To the
-- proofs `natBigHash` stays an opaque function of the number.
def natBigHashImpl (n : @& Nat) : UInt64 :=
  go n (n.log2 / 64 + 1) 11
where
  /-- Mix the `k` words of `m` (`m < 2^(64 k)`) into `h`, the low half first. -/
  go (m : Nat) (k : Nat) (h : UInt64) : UInt64 :=
    if hk : k ≤ 1 then mixHash h (UInt64.ofNat m)
    else
      let lo := k / 2
      go (m >>> (64 * lo)) (k - lo) (go (m % 2 ^ (64 * lo)) lo h)
  termination_by k
  decreasing_by all_goals omega

@[implemented_by natBigHashImpl]
opaque natBigHash (n : @& Nat) : UInt64

end ConLeche
