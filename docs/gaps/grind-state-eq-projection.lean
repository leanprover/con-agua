/-
# grind: a projection through a state-equality hypothesis is not found

Toolchain: leanprover/lean4:nightly-2026-09-21 (Lean 4.36.0-nightly-2026-09-21, ca39d2bc).

Expected: `grind`/`finish` closes the goal, the same way it closes every other `L` loop/function
proof in this project (`ConAgua/L/Examples.lean`, `ConAgua/Scan/Leaves.lean`).

Observed: `finish` (equivalently `grind [lang_grind]`) fails to derive `False`, even though the
hypotheses are directly contradictory. `subst ha` first (replacing `t` by its record literal
everywhere) makes the very same `finish` call succeed instantly, so the gap is specifically
"grind does not read a record field off a hypothesis `t = { field := v, ... }`, only off a
hypothesis whose LHS already *is* the record literal."

Found in con-agua (`ConAgua/Scan/Leaves.lean`, `numEndN_spec`): `num_end` calls `skip_digits`
and then tests the result `e` against the ORIGINAL parameter `i` (`if e == i { return i }`). The
callee's postcondition is `s' = s₀` (skip_digits changes no memory and no caller local), so
proving the comparison needs `s'.loc 0 = i`, i.e. a read of the `.loc` field through the
*hypothesis* `s' = s₀` — `s₀` itself being, after unfolding the call's own entry, a record
literal `{ mem := _, loc := Locals.init [i] }`. Nothing else in the verification condition ever
applies `.loc` to that literal, so `grind`'s congruence closure has no second node to merge
`t.loc 0` into, and the equality sits unused. Every other callee in this project either does not
need the "untouched" local back (`skip_braced`'s `i := e + 1` only reads the call's own result)
or needs it anyway through a loop induction hypothesis (which is stated, not derived through a
record literal), so this is the first function to hit it.

Workaround used in `numEndN_spec`'s proof (left as `sorry`, this is the reproducer instead):
none found that keeps the established `sym only [lang_grind] => vcgen [...] <;> finish` shape —
`subst` is not a hook `vcgen`'s per-VC `<;> finish` offers. A generic `St.loc_of_eq` congruence
lemma does not help either: `grind_pattern` refuses it, since its pattern (`s.loc x`) does not
mention the other two explicit parameters (`t`, `h`), so they "cannot be instantiated".
-/

import ConAgua.L.Logic

open L

-- Fails: the direct shape from `numEndN_spec`.
example (f B : Nat) (i r : UInt64) (s t : St)
    (ha : t = { mem := s.mem, loc := Locals.init [i] })
    (hb : B < 2 ^ 64) (hf : f ≤ B) (hf2 : r = UInt64.ofNat f)
    (heval : Cmp.eq.eval ((PUnit.unit, t.setLoc 1 r).snd.loc 1)
      ((PUnit.unit, t.setLoc 1 r).snd.loc 0) = true)
    (hne : f ≠ i.toNat) : False := by
  sym only [lang_grind] => finish

-- Succeeds: the exact same goal, `subst`ing the state equality first.
example (f B : Nat) (i r : UInt64) (s t : St)
    (ha : t = { mem := s.mem, loc := Locals.init [i] })
    (hb : B < 2 ^ 64) (hf : f ≤ B) (hf2 : r = UInt64.ofNat f)
    (heval : Cmp.eq.eval ((PUnit.unit, t.setLoc 1 r).snd.loc 1)
      ((PUnit.unit, t.setLoc 1 r).snd.loc 0) = true)
    (hne : f ≠ i.toNat) : False := by
  subst ha
  sym only [lang_grind] => finish

-- A registered congruence lemma does not help: `grind_pattern` rejects the pattern outright,
-- since `t` and `h` do not occur in it.
theorem St.loc_of_eq {s t : St} (h : s = t) (x : Var) : s.loc x = t.loc x := by rw [h]
-- grind_pattern [lang_grind] St.loc_of_eq => s.loc x
-- error: invalid pattern(s) for `St.loc_of_eq`
--   [St.loc #3 #0]
-- the following theorem parameters cannot be instantiated:
--   t : St
--   h : s = t
