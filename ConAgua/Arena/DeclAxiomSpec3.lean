module

import ConAgua.Arena.DeclCanonSpec2
public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.Arena.DeclAxiomSpec2
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclValRef
import ConAgua.L.LocNF
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The standard axioms: `find_pinned`, `std_axiom_ok` (lane `decls3`)

`find_pinned(vis, n, k, a, b, id)` is one clause of `stdAxiomOk`: the stored constant `n` has the
pinned shape (`k = 3` an inductive, `4` a constructor with counts `a`, `b`, `5` a recursor with
counts `a`, `b`) and its constant value matches the pin `rom_ci(id)`'s (`ci_to_cv`, helper
`decls3-canon`). `std_axiom_ok(vis, q)` runs the pinned `Eq` test and three clauses for `propext`,
or three clauses for `Classical.choice`. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The pinned shape `(k, a, b)` of a stored constant: its constant value when it has the shape. -/
def fpShape (k a b : Word) : IConstantInfo → Option IConstantVal
  | .indInfo cv _ => if k = 3 then some cv else none
  | .ctorInfo cv nP nF => if k = 4 ∧ nP = a.toNat ∧ nF = b.toNat then some cv else none
  | .recInfo cv mI rP _ => if k = 5 ∧ mI = a.toNat ∧ rP = b.toNat then some cv else none
  | _ => none
-/

/-- The two counts of a stored constructor or recursor, as words against `a`, `b`. -/
theorem counts_words {arr : Array Word} {q a b : Word} {x y : Nat} (hsz : arr.size < 2 ^ 64)
    (hx : nat? (aread arr) (q.toNat + 5) = some x) (hy : nat? (aread arr) (q.toNat + 6) = some y) :
    ((rdW arr (q + 5) ≠ a ∨ rdW arr (q + 6) ≠ b) ↔ ¬ (x = a.toNat ∧ y = b.toNat)) := by
  sorry

/-- **The shape tests, failing**: the twin's shape does not match. -/
theorem fp_fail {arr : Array Word} {dn : NIdx → Option ConLeche.Name} {q k a b : Word}
    {ci : IConstantInfo} (hsz : arr.size < 2 ^ 64) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (h : decCI (aread arr) q.toNat = some ci)
    (hf : rdW arr q ≠ k ∨ (k ≠ 3 ∧ (rdW arr (q + 5) ≠ a ∨ rdW arr (q + 6) ≠ b))) :
    fpShape k a b ci = none := by
  sorry

/-- **The shape tests, passing**: the twin's shape matches. -/
theorem fp_pass {arr : Array Word} {dn : NIdx → Option ConLeche.Name} {q k a b : Word}
    {ci : IConstantInfo} (hsz : arr.size < 2 ^ 64) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (h : decCI (aread arr) q.toNat = some ci) (hkw : rdW arr q = k)
    (hc : ¬ (k ≠ 3 ∧ (rdW arr (q + 5) ≠ a ∨ rdW arr (q + 6) ≠ b))) :
    ∃ cv, fpShape k a b ci = some cv := by
  sorry

/-- A matching shape's constant value decodes where the record does. -/
theorem fpShape_cv {arr : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {k a b : Word}
    {ci : IConstantInfo} {cv : IConstantVal} (h : decCI (aread arr) q = some ci)
    (hs : fpShape k a b ci = some cv) : decCV (aread arr) (q + 1) = some cv := by
  sorry

/-- What one clause of `stdAxiomOk` does. -/
def FpT (fe : IFEnv) (nm : NIdx) (k a b : Word) (T : AM IConstantVal) (a0 : AState) (res : Bool)
    (a' : AState) : Prop :=
  ((fe.find? nm).bind (fpShape k a b)).elim (res = false ∧ a' = a0)
    (fun cvT => (do let pin ← T; pure (decide (cvT = pin)) : AM Bool).run a0 = .ok (res, a'))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The pin of a clause: the ROM constant's constant value. -/
def romPinT (id : Nat) : AM IConstantVal := do return (← romCiT id).toConstantVal
-/

section model
variable (p : Prog)

/-- After `ci_to_cv`: the comparison. -/
def fpK3 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => mpW m3 (q + 1) (r3.headD 0)

/-- After `rom_ci(id)`. -/
def fpK2 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => fpK3 q (callW p n "ci_to_cv" [r2.headD 0] m2)

/-- After the lookup: the shape tests. -/
def fpK1 (n : Nat) (k ca cb id : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k ≠ 3 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ ca ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ cb) then some ([0], m1)
    else fpK2 p n (r1.tail.headD 0) (callW p n "rom_ci" [id] m1)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `find_pinned(vis, n, k, a, b, id)`.** -/
def fpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nm, k, ca, cb, id => fpK1 p n k ca cb id (envFindW m nm vis)
-/

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis nm k ca cb id q : Word) (r1 r2 r3 : List Word)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem fpW_step : fpW p (n + 1) m vis nm k ca cb id = fpK1 p n k ca cb id (envFindW m nm vis) :=
  rfl
-/
theorem fpK1_some : fpK1 p n k ca cb id (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k ≠ 3 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ ca ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ cb) then some ([0], m1)
    else fpK2 p n (r1.tail.headD 0) (callW p n "rom_ci" [id] m1) := rfl
theorem fpK2_some : fpK2 p n q (some (r2, m2)) = fpK3 q (callW p n "ci_to_cv" [r2.headD 0] m2) :=
  rfl
theorem fpK3_some : fpK3 q (some (r3, m3)) = mpW m3 (q + 1) (r3.headD 0) := rfl
end arms

grind_pattern [ind_grind] fpW_step => fpW p (n + 1) m vis nm k ca cb id
grind_pattern [ind_grind] fpK1_some => fpK1 p n k ca cb id (some (r1, m1))
grind_pattern [ind_grind] fpK2_some => fpK2 p n q (some (r2, m2))
grind_pattern [ind_grind] fpK3_some => fpK3 q (some (r3, m3))

/-- The lookups of the standard axioms' test. -/
structure StdProg (p : Prog) : Prop where
  red : RedProg p
  fp : p.lookup "find_pinned" = some findPinned
  std : p.lookup "std_axiom_ok" = some stdAxiomOkL

set_option maxHeartbeats 1600000 in
theorem fp_specW (h : StdProg p) (n : Nat) (s₀ : St) (vis nm k ca cb id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "find_pinned" [vis, nm, k, ca, cb, id]
    ⦃fun r s' => LocEq s' s₀ ∧ fpW p n s₀.mem vis nm k ca cb id = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.fp]
  simp only [callFn, findPinned]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "env_find", callW_spec p n "rom_ci",
        callW_spec p n "ci_to_cv", mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end model

/-- **`find_pinned` against the twin's clause**, at the model level. -/
theorem fpW_ok {p : Prog} (h : StdProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k ca cb id : Word} {r : List Word}
    (hW : fpW p n m vis nm k ca cb id = some (r, m')) (hS : StageR vis fe m a)
    (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4 ∨ k = 5) (hid : id.toNat < 8) :
    ∃ b a', StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧
      FpT fe (decI nm) k ca cb (romPinT id.toNat) a b a' := by
  sorry

/-! ## `stdAxiomOk`, flattened -/

/-- A clause of `stdAxiomOk`: the stored constant has the pinned shape, its constant value matches
the pin. -/
def clausePT (fe : IFEnv) (nm : NIdx) (k a b : Word) (T : AM IConstantVal) : AM Bool :=
  match (fe.find? nm).bind (fpShape k a b) with
  | some cvT => do cvT.matchesPin (← T)
  | none => pure false

theorem clausePT_of_fp {fe : IFEnv} {nm : NIdx} {k ca cb : Word} {T : AM IConstantVal}
    {a a' : AState} {b : Bool} (h : FpT fe nm k ca cb T a b a') :
    (clausePT fe nm k ca cb T).run a = .ok (b, a') := by
  unfold FpT at h
  unfold clausePT
  cases hb : (fe.find? nm).bind (fpShape k ca cb) with
  | none => rw [hb] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | some cvT =>
    rw [hb] at h
    simp only [Option.elim] at h
    simp only [matchesPin_eq]
    exact h

end L.Arena
