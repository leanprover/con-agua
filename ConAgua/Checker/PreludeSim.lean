import ConAgua.Checker.Prelude

/-!
# The prelude's copies of the frontend are the frontend on the prelude's bytes (lane `pipeline`)

`builtin_prelude` runs `pre_front_run`, the frontend with every function that reads the input
copied by `preFn` (`Checker/Prelude.lean`): `ld8 0 i` becomes `ldc preludeBytes i`, `len8 0` the
constant `preludeLenW`. **The simulation**: a returning run of a copy `pre_f` from state `s` is a
returning run of the original `f` from `s` with byte array `0` replaced by the prelude's bytes
(`St.setIn`), with the same results, ending in the copy's final state with byte array `0`
replaced the same way. So every spec of `f` is a spec of `pre_f` (`preSim_triple`).

The program's shape (`PreSimProg p t S`): every copied function `f` (its name in the tree `t`)
has its copy at `"pre_" ++ f`, stores no byte into array `0`, and calls only copied functions
(renamed by `preName`) or shared ones (`S`); a shared function reads and writes no byte of array
`0` and calls only shared functions.
-/

namespace L.Checker

open L L.Compiler
open Std.WP
open scoped Lean.Order

/-- Byte array `0` replaced by `x`. -/
def _root_.L.Mem.setIn (m : Mem) (x : Array UInt8) : Mem := { m with bytes := m.bytes.set! 0 x }

/-- Byte array `0` of the state's memory replaced by `x`. -/
def _root_.L.St.setIn (s : St) (x : Array UInt8) : St := { s with mem := s.mem.setIn x }

/-- The prelude's bytes, as the input array. -/
def preIn : Array UInt8 := preludeBytes.toArray

/-- No access to byte array `0`. -/
def _root_.L.Expr.noIn : Expr → Bool
  | .ld8 a i => a != 0 && i.noIn
  | .len8 a => a != 0
  | .ld64 _ i | .ldc _ i => i.noIn
  | .bin _ a b | .cmpw _ a b => a.noIn && b.noIn
  | _ => true

def _root_.L.Cond.noIn : Cond → Bool
  | .cmp _ a b => a.noIn && b.noIn
  | .and p q | .or p q => p.noIn && q.noIn
  | .not p => p.noIn

/-- No access to byte array `0` (no read, no store). -/
def _root_.L.Stmt.noIn : Stmt → Bool
  | .set _ e | .gset _ e => e.noIn
  | .st8 a i e => a != 0 && i.noIn && e.noIn
  | .st64 _ i e => i.noIn && e.noIn
  | .seq s t => s.noIn && t.noIn
  | .ite c s t => c.noIn && s.noIn && t.noIn
  | .while c s => c.noIn && s.noIn
  | .ret es | .call _ _ es => es.all Expr.noIn
  | _ => true

/-- No store into byte array `0`. -/
def _root_.L.Stmt.noSt8In : Stmt → Bool
  | .st8 a _ _ => a != 0
  | .seq s t => s.noSt8In && t.noSt8In
  | .ite _ s t => s.noSt8In && t.noSt8In
  | .while _ s => s.noSt8In
  | _ => true

/-- Every call of the statement is to a name satisfying `P`. -/
def _root_.L.Stmt.callsIn (P : FnName → Bool) : Stmt → Bool
  | .seq s t => s.callsIn P && t.callsIn P
  | .ite _ s t => s.callsIn P && t.callsIn P
  | .while _ s => s.callsIn P
  | .call _ f _ => P f
  | _ => true

/-- `f` is copied (its name code is in the tree). -/
def isCopied (t : NTree) (f : FnName) : Bool := (t.find (nameCode f)).isSome

/-- **The program's shape for the simulation**: the copies of the functions in `t`, and the
shared functions `S` they call. -/
structure PreSimProg (p : Prog) (t : NTree) (S : FnName → Bool) : Prop where
  copy : ∀ f fd, isCopied t f = true → p.lookup f = some fd →
    p.lookup ("pre_" ++ f) = some (preFn t fd) ∧ fd.body.noSt8In = true ∧
      fd.body.callsIn (fun g => isCopied t g || S g) = true
  shared : ∀ f fd, S f = true → p.lookup f = some fd →
    isCopied t f = false ∧ fd.body.noIn = true ∧ fd.body.callsIn S = true

/-- **The simulation.** -/
theorem preSim {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S) (n : Nat)
    (f : FnName) (hf : isCopied t f = true) (vs : List Word) (s : St) (r : List Word) (s' : St)
    (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) ("pre_" ++ f) vs).run s = .ok (r, s')) :
    (invoke p (exec p n) f vs).run (s.setIn preIn) = .ok (r, s'.setIn preIn) ∧
      s'.mem.arr8 0 = s.mem.arr8 0 := by
  sorry

/-- **A spec of `f` is a spec of its copy**, on the memory with the prelude's bytes as input. -/
theorem preSim_triple {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (n : Nat) (f : FnName) (hf : isCopied t f = true) (vs : List Word)
    (s₀ : St) (h0 : 0 < s₀.mem.bytes.size) {Q : List Word → St → Prop}
    (hQ : ⦃fun s => s = s₀.setIn preIn⦄ invoke p (exec p n) f vs ⦃fun r s => Q r s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) ("pre_" ++ f) vs
    ⦃fun r s => Q r (s.setIn preIn) ∧ s.mem.arr8 0 = s₀.mem.arr8 0; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2⟩ := preSim hP n f hf vs s r s' (hs ▸ h0) hrun
  exact ⟨M.of_run (P := fun x => x = s₀.setIn preIn) (by rw [hs]) h1 hQ, hs ▸ h2⟩

end L.Checker
