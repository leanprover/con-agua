/-
# grind: record addresses with a variable stride are not decided

Toolchain: leanprover/lean4:nightly-2026-10-20.

Expected: `grind` proves the second example, as it proves the first. With `f, g < w`, `t, t' ≤ 1`
and small node indices, `(i * 2 + t) * w + f` determines `i`, `t` and `f`.

Observed: the first example (stride `8`, width `4`, numerals) succeeds; the second (stride
`2 * w`, width `w`, a variable) fails: the products `i * w`, `c * w` are nonlinear, so neither the
linear-arithmetic module nor the ring solver derives the disequalities.

Found in con-agua `ConAgua/Arena/StoreLib.lean` (the store library, a record schema with its
width as a parameter). Workaround: prove the injectivity once by hand (`Schema.ad_inj`, `Nat`
division by `w`) and give it to `grind` as a lemma; the generic read-after-write goals then close.
-/

-- succeeds
example (i c t t' f g : UInt64) (hi : i.toNat < 2 ^ 27) (hc : c.toNat < 2 ^ 27) (ht : t ≤ 1)
    (ht' : t' ≤ 1) (hf : f < 4) (hg : g < 4) (h : i * 8 + t * 4 + f = c * 8 + t' * 4 + g) :
    i = c ∧ t = t' ∧ f = g := by
  grind

-- fails
example (w i c t t' f g : UInt64) (hw : w ≤ 16) (hi : i.toNat < 2 ^ 27) (hc : c.toNat < 2 ^ 27)
    (ht : t ≤ 1) (ht' : t' ≤ 1) (hf : f < w) (hg : g < w)
    (h : i * (2 * w) + t * w + f = c * (2 * w) + t' * w + g) : i = c ∧ t = t' ∧ f = g := by
  grind
