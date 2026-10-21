/-
# grind: an equation derived by linear arithmetic does not reach the ring solver

Toolchain: leanprover/lean4:nightly-2026-10-20.

Expected: `grind` proves the first example. It proves the no-overflow equation
`(x + y + c).toNat = x.toNat + y.toNat + c.toNat` on its own (third example), and with that
equation as a hypothesis the goal is a ring consequence (second example).

Observed: the first example fails. The equation is derived inside the linear-arithmetic module
(from `toNat` bounds and `% 2^64`), and the goal needs it multiplied by the atom `w`, which only
the ring solver does; the derived equation is not handed to it.

Found in con-agua `ConAgua/Arena/NatAdd.lean` (the ripple-carry step of `nat_add`:
`V + c·wt i = …` with `w = wt i`). Workaround: state the digit equation as a lemma about a named
function (`adc_split : (x + y + c).toNat + adcHi x y c * 2^64 = …`, pattern `adcHi x y c`), so
that it enters `grind` as an asserted fact (`ConAgua/Arena/Pool.lean`).
-/

-- fails
example (x y c : UInt64) (V A w : Nat) (h : ¬ x + y < x) (h2 : ¬ x + y + c < x + y)
    (ih : V + c.toNat * w = A) :
    V + (x + y + c).toNat * w = A + (x.toNat + y.toNat) * w := by
  grind

-- works once the same equation is an asserted fact
example (x y c : UInt64) (V A w : Nat) (h : ¬ x + y < x) (h2 : ¬ x + y + c < x + y)
    (ih : V + c.toNat * w = A) (e : (x + y + c).toNat = x.toNat + y.toNat + c.toNat) :
    V + (x + y + c).toNat * w = A + (x.toNat + y.toNat) * w := by
  grind

-- and grind proves that equation on its own
example (x y c : UInt64) (h : ¬ x + y < x) (h2 : ¬ x + y + c < x + y) :
    (x + y + c).toNat = x.toNat + y.toNat + c.toNat := by
  grind
