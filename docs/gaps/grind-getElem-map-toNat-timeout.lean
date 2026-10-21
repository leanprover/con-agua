/-
# grind: timeout on an `Option`-valued read at index `(l + 1).toNat`

Toolchain: leanprover/lean4:nightly-2026-09-21 (Lean 4.36.0-nightly-2026-09-21, ca39d2bc).

Expected: each example is proved (or refuted) quickly; the last one, with the index abstracted
to a `Nat` variable, is proved in ~0.1 s.
Observed: the first two hit `(deterministic) timeout at isDefEq, maximum number of heartbeats
(200000)` after ~7 s each. Both have an `Option` built from `b[(l + 1).toNat]` (by `Option.map`
of `getElem?`, or by a `dite`) equated to `some x`, with `l : UInt64`.

Found in con-agua: L's byte read was `((m.arr8 a)[i.toNat]?).map UInt8.toUInt64`, then a `dite`
into `Option`, and a program reading `b[j + 1]` produced these hypotheses. Workaround there:
the read is a `dite` in the monad (`L.ld8`), so `vcgen` splits it and the verification
condition holds `h : i.toNat < size` and the element `arr[i.toNat]` directly, with no `Option`.
-/

example (b : Array UInt8) (l x : UInt64)
    (h5 : (l + 1).toNat < b.size)
    (h6 : b[(l + 1).toNat]?.map UInt8.toUInt64 = some x)
    (h7 : x < 32) :
    b[(l + 1).toNat] < 32 := by
  grind

example (b : Array UInt8) (l x : UInt64)
    (h5 : l + 1 < UInt64.ofNat b.size)
    (h6 : (if h : (l + 1).toNat < b.size then some b[(l + 1).toNat].toUInt64 else none) = some x)
    (h7 : x < 32) :
    b[(l + 1).toNat]! < 32 := by
  grind

example (b : Array UInt8) (k : Nat) (x : UInt64)
    (h5 : k < b.size)
    (h6 : b[k]?.map UInt8.toUInt64 = some x)
    (h7 : x < 32) :
    b[k] < 32 := by
  grind
