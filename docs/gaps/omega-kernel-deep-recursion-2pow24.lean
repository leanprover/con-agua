/-!
`omega` proves a linear bound with the constants `2^24` and `2^64`, and the kernel rejects the
proof with "deep recursion detected" (the elaborator accepts it). Plain `Nat`, no `UInt64` needed.

Expected: both examples check. Observed: both fail in the kernel (nightly-2026-10-20; also Lean
4.35.0).

Met in `ConAgua/Arena/DefEqMidPeel.lean` (`defeqBinders_refines`: the depth leaves room for
`peelFuel = 2^24`). Workaround there: state the bound with the `@[noinline]` constant `peelFuel`,
which `omega` treats as an atom.
-/

/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
example (d : Nat) (h : d + 16777217 < 2 ^ 64) : d + 1 + 16777216 < 2 ^ 64 := by
  omega

-- with the constant opaque, it is fine:
def bigC : Nat := 16777216
example (d : Nat) (h : d + 1 + bigC < 2 ^ 64) : d + bigC < 2 ^ 64 := by
  omega
