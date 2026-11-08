module

public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclValRef
import ConAgua.L.LocNF
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `Lean.trustCompiler`: `find_pinned_cv`, `trust_compiler_ok` (lane `decls3`)

`find_pinned_cv(vis, n, k, id)` is one clause of `trustCompilerOk`: the stored constant `n` has the
pinned shape (`k = 3`: an inductive; `k = 4`: a constructor without parameters and fields), and its
constant value matches `rom_cv(id)`. Its relational lemma says what the twin's clause does
(`fpcShape`: the shape test as a partial function), and `trust_compiler_ok` chains two clauses and
the axiom's own pin. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The pinned shape `k` of a stored constant: its constant value when it has the shape. -/
def fpcShape (k : Word) : IConstantInfo → Option IConstantVal
  | .indInfo cv _ => if k = 3 then some cv else none
  | .ctorInfo cv nP nF => if k = 4 ∧ nP = 0 ∧ nF = 0 then some cv else none
  | _ => none

section model
variable (p : Prog)

/-- After `rom_cv(id)`: the comparison. -/
def fpcK2 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => mpW m2 (q + 1) (r2.headD 0)

/-- After the lookup: the shape tests. -/
def fpcK1 (n : Nat) (k id : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k = 4 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ 0 ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ 0) then some ([0], m1)
    else fpcK2 (r1.tail.headD 0) (callW p n "rom_cv" [id] m1)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `find_pinned_cv(vis, n, k, id)`.** -/
def fpcW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, nm, k, id => fpcK1 p n k id (envFindW m nm vis)
-/

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis nm k id q : Word) (r1 r2 : List Word)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem fpcW_step : fpcW p (n + 1) m vis nm k id = fpcK1 p n k id (envFindW m nm vis) := rfl
-/
theorem fpcK1_some : fpcK1 p n k id (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k = 4 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ 0 ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ 0) then some ([0], m1)
    else fpcK2 (r1.tail.headD 0) (callW p n "rom_cv" [id] m1) := rfl
theorem fpcK2_some : fpcK2 q (some (r2, m2)) = mpW m2 (q + 1) (r2.headD 0) := rfl
end arms

grind_pattern [ind_grind] fpcW_step => fpcW p (n + 1) m vis nm k id
grind_pattern [ind_grind] fpcK1_some => fpcK1 p n k id (some (r1, m1))
grind_pattern [ind_grind] fpcK2_some => fpcK2 q (some (r2, m2))

/-- The lookups of the compiler-trust family. -/
structure TcoProg (p : Prog) : Prop where
  red : RedProg p
  fpc : p.lookup "find_pinned_cv" = some findPinnedCv
  tco : p.lookup "trust_compiler_ok" = some trustCompilerOkL

set_option maxHeartbeats 1600000 in
theorem fpc_specW (h : TcoProg p) (n : Nat) (s₀ : St) (vis nm k id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "find_pinned_cv" [vis, nm, k, id]
    ⦃fun r s' => LocEq s' s₀ ∧ fpcW p n s₀.mem vis nm k id = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.fpc]
  simp only [callFn, findPinnedCv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "env_find", callW_spec p n "rom_cv",
        mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end model

/-- The counts of a stored constructor, as words. -/
theorem ctor_counts {a : Array Word} {q : Word} {np nf : Nat} (hsz : a.size < 2 ^ 64)
    (hnp : nat? (aread a) (q.toNat + 5) = some np) (hnf : nat? (aread a) (q.toNat + 6) = some nf) :
    ((rdW a (q + 5) ≠ 0 ∨ rdW a (q + 6) ≠ 0) ↔ ¬ (np = 0 ∧ nf = 0)) := by
  sorry

/-- **The shape tests on a stored record, failing**: the twin's shape does not match. -/
theorem fpc_fail {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q k : Word}
    {ci : IConstantInfo} (hsz : a.size < 2 ^ 64) (hk : k = 3 ∨ k = 4) (h : decCI (aread a) q.toNat = some ci)
    (hf : rdW a q ≠ k ∨ (k = 4 ∧ (rdW a (q + 5) ≠ 0 ∨ rdW a (q + 6) ≠ 0))) :
    fpcShape k ci = none := by
  sorry

/-- **The shape tests on a stored record, passing**: the twin's shape matches, with the constant
value at `q + 1`. -/
theorem fpc_pass {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q k : Word}
    {ci : IConstantInfo} (hsz : a.size < 2 ^ 64) (hk : k = 3 ∨ k = 4)
    (h : decCI (aread a) q.toNat = some ci) (hkw : rdW a q = k)
    (hc : ¬ (k = 4 ∧ (rdW a (q + 5) ≠ 0 ∨ rdW a (q + 6) ≠ 0))) :
    ∃ cv, fpcShape k ci = some cv ∧ decCV (aread a) (q.toNat + 1) = some cv := by
  sorry

/-- A matching shape's constant value decodes where the record does. -/
theorem fpcShape_cv {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {k : Word}
    {ci : IConstantInfo} {cv : IConstantVal} (h : decCI (aread a) q = some ci)
    (hs : fpcShape k ci = some cv) : decCV (aread a) (q + 1) = some cv := by
  sorry

/-- What one clause of `trustCompilerOk` does: with the pinned shape, the pin's intern and the
comparison; otherwise `false` and nothing. -/
def FpcT (fe : IFEnv) (nm : NIdx) (k : Word) (T : AM IConstantVal) (a : AState) (b : Bool)
    (a' : AState) : Prop :=
  ((fe.find? nm).bind (fpcShape k)).elim (b = false ∧ a' = a)
    (fun cvT => (do let pin ← T; pure (decide (cvT = pin)) : AM Bool).run a = .ok (b, a'))

/-- **`find_pinned_cv` against the twin's clause**, at the model level. -/
theorem fpcW_ok {p : Prog} (hR : L.Rom.RomRefs p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k id : Word} {r : List Word}
    (hW : fpcW p n m vis nm k id = some (r, m')) (hS : StageR vis fe m a)
    (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4) (hid : id.toNat < 10) :
    ∃ b a', StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧
      FpcT fe (decI nm) k (romCvT id.toNat) a b a' := by
  sorry

/-! ## `trust_compiler_ok(vis, q)` -/

section tco
variable (p : Prog)

/-- After `rom_cv(4)`: the axiom's own pin. -/
def tcoK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => mpW m5 q (r5.headD 0)

/-- After the `True.intro` clause. -/
def tcoK4 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then some ([0], m4) else tcoK5 q (callW p n "rom_cv" [4] m4)

/-- After the `True.intro` pin. -/
def tcoK3 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tcoK4 p n q (callW p n "find_pinned_cv" [vis, r3.headD 0, 4, 3] m3)

/-- After the `True` clause. -/
def tcoK2 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => if r2.headD 0 = 0 then some ([0], m2) else tcoK3 p n vis q (pinAtW m2 41)

/-- After the `True` pin. -/
def tcoK1 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => tcoK2 p n vis q (callW p n "find_pinned_cv" [vis, r1.headD 0, 3, 2] m1)

/-- **The model of `trust_compiler_ok(vis, q)`.** -/
def tcoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => tcoK1 p n vis q (pinAtW m 40)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis q : Word) (r1 r2 r3 r4 r5 : List Word)
theorem tcoW_step : tcoW p (n + 1) m vis q = tcoK1 p n vis q (pinAtW m 40) := rfl
theorem tcoK1_some : tcoK1 p n vis q (some (r1, m1)) =
    tcoK2 p n vis q (callW p n "find_pinned_cv" [vis, r1.headD 0, 3, 2] m1) := rfl
theorem tcoK2_some : tcoK2 p n vis q (some (r2, m2)) =
    if r2.headD 0 = 0 then some ([0], m2) else tcoK3 p n vis q (pinAtW m2 41) := rfl
theorem tcoK3_some : tcoK3 p n vis q (some (r3, m3)) =
    tcoK4 p n q (callW p n "find_pinned_cv" [vis, r3.headD 0, 4, 3] m3) := rfl
theorem tcoK4_some : tcoK4 p n q (some (r4, m4)) =
    if r4.headD 0 = 0 then some ([0], m4) else tcoK5 q (callW p n "rom_cv" [4] m4) := rfl
theorem tcoK5_some : tcoK5 q (some (r5, m5)) = mpW m5 q (r5.headD 0) := rfl
end arms

grind_pattern [ind_grind] tcoW_step => tcoW p (n + 1) m vis q
grind_pattern [ind_grind] tcoK1_some => tcoK1 p n vis q (some (r1, m1))
grind_pattern [ind_grind] tcoK2_some => tcoK2 p n vis q (some (r2, m2))
grind_pattern [ind_grind] tcoK3_some => tcoK3 p n vis q (some (r3, m3))
grind_pattern [ind_grind] tcoK4_some => tcoK4 p n q (some (r4, m4))
grind_pattern [ind_grind] tcoK5_some => tcoK5 q (some (r5, m5))

set_option maxHeartbeats 1600000 in
theorem tco_specW (h : TcoProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "trust_compiler_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ tcoW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tco]
  simp only [callFn, trustCompilerOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p h.red.pa n,
        callW_spec p n "find_pinned_cv", callW_spec p n "rom_cv",
        mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [mpW]

end tco

/-! ### The twin's clauses, flattened -/

/-- A clause of the twin's environment-shape tests: the stored constant has the pinned shape `k`,
and its constant value matches the pin `T`. -/
def clauseT (fe : IFEnv) (nm : NIdx) (k : Word) (T : AM IConstantVal) : AM Bool :=
  match (fe.find? nm).bind (fpcShape k) with
  | some cvT => do cvT.matchesPin (← T)
  | none => pure false

theorem clauseT_of_fpc {fe : IFEnv} {nm : NIdx} {k : Word} {T : AM IConstantVal} {a a' : AState}
    {b : Bool} (h : FpcT fe nm k T a b a') : (clauseT fe nm k T).run a = .ok (b, a') := by
  unfold FpcT at h
  unfold clauseT
  cases hb : (fe.find? nm).bind (fpcShape k) with
  | none => rw [hb] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | some cvT =>
    rw [hb] at h
    simp only [Option.elim] at h
    simp only [matchesPin_eq]
    exact h

/-- `trustCompilerOk` as two clauses and the axiom's pin. -/
theorem trustCompilerOk_eq (fe : IFEnv) (cv : IConstantVal) :
    trustCompilerOk fe cv = (do
      let t ← trueName
      let b ← clauseT fe t 3 trueCvA
      if !b then pure false else do
        let ti ← trueIntroName
        let b2 ← clauseT fe ti 4 trueIntroCvA
        if !b2 then pure false else cv.matchesPin (← trustCompilerA)) := by
  unfold trustCompilerOk
  congr 1; funext t
  unfold clauseT
  cases hf : fe.find? t with
  | none => simp
  | some ci =>
    cases ci with
    | indInfo cvT caps =>
      simp only [Option.bind_some, fpcShape, ite_true, bind_assoc]
      congr 1; funext pin
      simp only [matchesPin_eq, pure_bind]
      split <;> try rfl
      congr 1; funext ti
      cases hf2 : fe.find? ti with
      | none => simp
      | some ci2 =>
        cases ci2 with
        | ctorInfo cvTi nP nF =>
          simp only [Option.bind_some, fpcShape]
          by_cases e : nP = 0 ∧ nF = 0
          · obtain ⟨rfl, rfl⟩ := e
            simp only [and_self, ite_true, bind_assoc, pure_bind]
          · rcases Nat.eq_zero_or_pos nP with h0 | h0 <;> rcases Nat.eq_zero_or_pos nF with h1 | h1 <;>
              simp_all [Nat.pos_iff_ne_zero]
        | _ => simp [fpcShape]
    | _ => simp [fpcShape]

/-- A `find_pinned_cv` call's run, against its clause. -/
theorem fpc_call {p : Prog} (h : TcoProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k id : Word} {r : List Word}
    (hc : callW p n "find_pinned_cv" [vis, nm, k, id] m = some (r, m'))
    (hS : StageR vis fe m a) (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4)
    (hid : id.toNat < 10) :
    ∃ b a', (clauseT fe (decI nm) k (romCvT id.toNat)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  sorry

/-- **`trust_compiler_ok(vis, q)` refines `trustCompilerOk`** at the model level. -/
theorem tcoW_ok {p : Prog} (h : TcoProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : tcoW p n m vis q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (trustCompilerOk fe cv).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  sorry

/-- **`trust_compiler_ok(vis, q)` refines `trustCompilerOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.trustCompilerOk]
theorem trustCompilerOk_refines (p : Prog) (h : TcoProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "trust_compiler_ok" [vis, q]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (trustCompilerOk fe cv) (KeepPost vis fe decW0B) := by
  sorry

end L.Arena
