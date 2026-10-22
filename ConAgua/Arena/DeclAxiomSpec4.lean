import ConAgua.Arena.DeclAxiomSpec3

/-!
# `std_axiom_ok(vis, q)` refines `stdAxiomOk` (lane `decls3`)

The model runs the three clauses of a family (`famK*`: pin, `find_pinned`, abort-free `0` on a
miss) for `propext` (after the pinned `Eq` test) or `Classical.choice`; the relational lemma runs
`stdAxiomOk_eq`'s flattened twin. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

section model
variable (p : Prog) (n : Nat) (vis q : Word)

/-- The family's end: the axiom's own pin. -/
def famK7 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => mpW m q (r.headD 0)

/-- After the third clause. -/
def famK6 (cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0], m) else famK7 q (stubM "rom_cv" m [cvid])

/-- After the third pin. -/
def famK5 (i3 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => famK6 q cvid (callW p n "find_pinned" [vis, r.headD 0, 5, c3, c3, i3] m)

/-- After the second clause. -/
def famK4 (s3 i3 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0], m) else famK5 p n vis q i3 c3 cvid (pinAtW m s3)

/-- After the second pin. -/
def famK3 (s3 i2 i3 c2 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    famK4 p n vis q s3 i3 c3 cvid (callW p n "find_pinned" [vis, r.headD 0, 4, c2, c2, i2] m)

/-- After the first clause. -/
def famK2 (s2 s3 i2 i3 c2 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0], m) else famK3 p n vis q s3 i2 i3 c2 c3 cvid (pinAtW m s2)

/-- After the first pin. -/
def famK1 (s2 s3 i1 i2 i3 c2 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid (callW p n "find_pinned" [vis, r.headD 0, 3, 0, 0, i1] m)

/-- After a family. -/
def stdRet : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- `propext`: after `find_is`. -/
def stdP3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0], m)
    else stdRet (callW p n "std_ax_family" [vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0] m)

/-- `propext`: after `rom_ci(0)`. -/
def stdP2 (en : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => stdP3 p n vis q (callW p n "find_is" [vis, en, r.headD 0] m)

/-- `propext`: after the `Eq` pin. -/
def stdP1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => stdP2 p n vis q (r.headD 0) (stubM "rom_ci" m [0])

/-- `choice`: after its pin. -/
def stdC1 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then stdRet (callW p n "std_ax_family" [vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1] m)
    else some ([0], m)

/-- After the `propext` pin. -/
def stdK1 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then stdP1 p n vis q (pinAtW m 0) else stdC1 p n vis q nm (pinAtW m 33)

end model

/-- **The model of `std_ax_family(vis, q, s1, …)`.** -/
def famW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid =>
    famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (pinAtW m s1)

/-- **The model of `std_axiom_ok(vis, q)`.** -/
def stdW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => stdK1 p n vis q (rdW (m.arr64 EREC) q) (pinAtW m 32)

section arms
variable (p : Prog) (n : Nat) (vis q nm en s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word) (r : List Word)
  (m : Mem)
theorem famW_step : famW p (n + 1) m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid =
    famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (pinAtW m s1) := rfl
theorem stdW_step : stdW p (n + 1) m vis q = stdK1 p n vis q (rdW (m.arr64 EREC) q) (pinAtW m 32) :=
  rfl
theorem stdK1_some : stdK1 p n vis q nm (some (r, m)) =
    if nm = r.headD 0 then stdP1 p n vis q (pinAtW m 0) else stdC1 p n vis q nm (pinAtW m 33) := rfl
theorem stdC1_some : stdC1 p n vis q nm (some (r, m)) =
    if nm = r.headD 0 then stdRet (callW p n "std_ax_family" [vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1] m)
    else some ([0], m) := rfl
theorem stdP1_some : stdP1 p n vis q (some (r, m)) =
    stdP2 p n vis q (r.headD 0) (stubM "rom_ci" m [0]) := rfl
theorem stdP2_some : stdP2 p n vis q en (some (r, m)) =
    stdP3 p n vis q (callW p n "find_is" [vis, en, r.headD 0] m) := rfl
theorem stdP3_some : stdP3 p n vis q (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m)
    else stdRet (callW p n "std_ax_family" [vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0] m) := rfl
theorem stdRet_some : stdRet (some (r, m)) = some ([r.headD 0], m) := rfl
theorem famK1_some : famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (some (r, m)) =
    famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid
      (callW p n "find_pinned" [vis, r.headD 0, 3, 0, 0, i1] m) := rfl
theorem famK2_some : famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m) else famK3 p n vis q s3 i2 i3 c2 c3 cvid (pinAtW m s2) :=
  rfl
theorem famK3_some : famK3 p n vis q s3 i2 i3 c2 c3 cvid (some (r, m)) =
    famK4 p n vis q s3 i3 c3 cvid (callW p n "find_pinned" [vis, r.headD 0, 4, c2, c2, i2] m) := rfl
theorem famK4_some : famK4 p n vis q s3 i3 c3 cvid (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m) else famK5 p n vis q i3 c3 cvid (pinAtW m s3) := rfl
theorem famK5_some : famK5 p n vis q i3 c3 cvid (some (r, m)) =
    famK6 q cvid (callW p n "find_pinned" [vis, r.headD 0, 5, c3, c3, i3] m) := rfl
theorem famK6_some : famK6 q cvid (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m) else famK7 q (stubM "rom_cv" m [cvid]) := rfl
theorem famK7_some : famK7 q (some (r, m)) = mpW m q (r.headD 0) := rfl
end arms

grind_pattern [ind_grind] famW_step => famW p (n + 1) m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid
grind_pattern [ind_grind] stdW_step => stdW p (n + 1) m vis q
grind_pattern [ind_grind] stdK1_some => stdK1 p n vis q nm (some (r, m))
grind_pattern [ind_grind] stdC1_some => stdC1 p n vis q nm (some (r, m))
grind_pattern [ind_grind] stdP1_some => stdP1 p n vis q (some (r, m))
grind_pattern [ind_grind] stdP2_some => stdP2 p n vis q en (some (r, m))
grind_pattern [ind_grind] stdP3_some => stdP3 p n vis q (some (r, m))
grind_pattern [ind_grind] stdRet_some => stdRet (some (r, m))
grind_pattern [ind_grind] famK1_some => famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK2_some => famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK3_some => famK3 p n vis q s3 i2 i3 c2 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK4_some => famK4 p n vis q s3 i3 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK5_some => famK5 p n vis q i3 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK6_some => famK6 q cvid (some (r, m))
grind_pattern [ind_grind] famK7_some => famK7 q (some (r, m))

/-- The lookups of `std_axiom_ok`. -/
structure StdProg2 (p : Prog) : Prop where
  std : StdProg p
  fam : p.lookup "std_ax_family" = some stdAxFamily

set_option maxHeartbeats 1600000 in
theorem fam_specW (p : Prog) (h : StdProg2 p) (n : Nat) (s₀ : St)
    (vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "std_ax_family" [vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid]
    ⦃fun r s' => LocEq s' s₀ ∧ famW p n s₀.mem vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid = some (r, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ h.fam]
  simp only [callFn, stdAxFamily]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p h.std.red.pa n,
        callW_spec p n "find_pinned", stubM_spec p "rom_cv" n,
        mp_specW p h.std.red.canon h.std.red.mp n] <;>
      finish (gen := 20) (instances := 5000) [mpW]

set_option maxHeartbeats 1600000 in
theorem std_specW (p : Prog) (h : StdProg2 p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "std_axiom_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ stdW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.std.std]
  simp only [callFn, stdAxiomOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pinAt_specW p h.std.red.pa n, stubM_spec p "rom_ci" n, callW_spec p n "find_is",
        callW_spec p n "std_ax_family"] <;>
      finish (gen := 20) [rdW_eq, pinAtW]

end L.Arena
