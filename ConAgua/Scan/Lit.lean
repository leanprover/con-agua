module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
import ConAgua.Census.Attr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `match_lit` and `scan_bool` (`scan_fast.rs:132,716`)

The literal is a slice `(o, n)` of the constant byte string `LITS` (`"truefalse"`), read with
`LITS.c8[…]` (constant data, DESIGN.md "L extensions"); Rust passes it as a `&[u8]`, which L
has no type for. `scan_bool` returns Rust's `ScanRes<bool>` as three words
`(ok, value, position)`; the error (always `ExpectedBool` at `i`) is `(0, 0, i)`.

Models: `matchLitN` is Rust's loop with `byte_at` (`0` past the end), `scanBoolN` the Rust
function. `ConAgua.Scan.LitLink` relates them to con-leche's `matchLit`/`scanBool`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Lit

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-- The literals of `scan_bool`: `true` at `0`, `false` at `4`. -/
def LITS : List UInt8 := [116, 114, 117, 101, 102, 97, 108, 115, 101]

theorem LITS_length : LITS.length = 9 := rfl

/-! ## `match_lit` -/

def matchLitLoop : Stmt := lblk (i, o, n, k, c) {
  while k < n {
    if i + k < len(IN.u8) { c := IN.u8[i + k] } else { c := 0 };
    if c != LITS.c8[o + k] { return 0 };
    k += 1
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:121-131 ConLeche.Frontend.matchLit -/
@[l_impl ConLeche.Frontend.matchLit]
def matchLit : FunDecl := lfn (i, o, n) locals (k, c) { ⟪matchLitLoop⟫; return 1 }

/-- Rust's `byte_at`: the byte at `i`, `0` past the end. -/
def byteAtN (b : Array UInt8) (i : Nat) : UInt8 := b.getD i 0

/-- `match_lit`'s loop from `k`: the literal `L[o..o+n)` matches `b` from `i` on, at the
positions from `k` on. -/
def matchLitN (b : Array UInt8) (i : Nat) (L : List UInt8) (o n k : Nat) : Bool :=
  if k < n then
    if byteAtN b (i + k) = L.getD (o + k) 0 then matchLitN b i L o n (k + 1) else false
  else true
termination_by n - k

section
variable (b : Array UInt8) (i : Nat) (L : List UInt8) (o n k : Nat)

/-! One guarded equation per arm (DESIGN.md, "Proof recipe"). The positions `i + k` and `o + k`
are variables `j`, `m` with an equation, so that a pattern matches the L side's reads
`b[(i + k).toNat]` and `L[(o + k).toNat]`. -/

theorem matchLitN_hit (k' j m : Nat) (hk' : k' = k + 1) (hj : j = i + k) (hm : m = o + k)
    (hk : k < n) (hb : j < b.size) (hmL : m < L.length) (h : b[j] = L[m]) :
    matchLitN b i L o n k = matchLitN b i L o n k' := by
  subst hk' hj hm; rw [matchLitN, ite_eq_left hk, ite_eq_left (by simp [byteAtN, hb, hmL, h])]
theorem matchLitN_miss (j m : Nat) (hj : j = i + k) (hm : m = o + k)
    (hk : k < n) (hb : j < b.size) (hmL : m < L.length) (h : b[j] ≠ L[m]) :
    matchLitN b i L o n k = false := by
  subst hj hm; rw [matchLitN, ite_eq_left hk, ite_eq_right (by simp [byteAtN, hb, hmL, h])]
theorem matchLitN_past0 (k' m : Nat) (hk' : k' = k + 1) (hm : m = o + k)
    (hk : k < n) (hb : b.size ≤ i + k) (hmL : m < L.length) (h : L[m] = 0) :
    matchLitN b i L o n k = matchLitN b i L o n k' := by
  subst hk' hm
  rw [matchLitN, ite_eq_left hk, ite_eq_left (by simp [byteAtN, Array.getD, show ¬ i + k < b.size by omega, hmL, h])]
theorem matchLitN_past (m : Nat) (hm : m = o + k)
    (hk : k < n) (hb : b.size ≤ i + k) (hmL : m < L.length) (h : L[m] ≠ 0) :
    matchLitN b i L o n k = false := by
  subst hm
  rw [matchLitN, ite_eq_left hk, ite_eq_right (by
    simp [byteAtN, Array.getD, show ¬ i + k < b.size by omega, hmL]; exact fun h' => h h'.symm)]
theorem matchLitN_end (hk : n ≤ k) : matchLitN b i L o n k = true := by
  rw [matchLitN, ite_eq_right (by omega)]

grind_pattern [lang_grind] matchLitN_hit => matchLitN b i L o n k, b[j], L[m], matchLitN b i L o n k'
grind_pattern [lang_grind] matchLitN_miss => matchLitN b i L o n k, b[j], L[m]
grind_pattern [lang_grind] matchLitN_past0 => matchLitN b i L o n k, L[m], matchLitN b i L o n k'
grind_pattern [lang_grind] matchLitN_past => matchLitN b i L o n k, L[m]
grind_pattern [lang_grind] matchLitN_end => matchLitN b i L o n k

end


section matchLit
variable (p : Prog) (hp : p.lookup "match_lit" = some matchLit)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem matchLitLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat + (s₀.loc 2).toNat < 2 ^ 64)
    (ho : (s₀.loc 1).toNat + (s₀.loc 2).toNat ≤ LITS.length) (hk : (s₀.loc 3).toNat ≤ (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    exec p n matchLitLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if matchLitN b (s₀.loc 0).toNat LITS (s₀.loc 1).toNat (s₀.loc 2).toNat
        (s₀.loc 3).toNat then 1 else 0]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := matchLitLoop) rfl]
    sym only [lang_grind, LITS_length] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ldc, ih] <;> finish


include hp in
@[refines ConLeche.Frontend.matchLit]
theorem matchLit_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i o l : Word)
    (hi : i.toNat + l.toNat < 2 ^ 64) (ho : o.toNat + l.toNat ≤ LITS.length) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "match_lit" [i, o, l]
    ⦃fun r s' => s' = s₀ ∧
      r = [if matchLitN b i.toNat LITS o.toNat l.toNat 0 then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, matchLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, fun s₀ hm hi ho hk => Triple.step_exec (matchLitLoop_spec p b hb (n + 1) s₀ hm hi ho hk)] <;> finish

end matchLit

/-! ## `scan_bool` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:460-464 ConLeche.Frontend.scanBool -/
@[l_impl ConLeche.Frontend.scanBool]
def scanBool : FunDecl := lfn (i) locals (m) {
  m := call match_lit(i, 0, 4);
  if m != 0 { return (1, 1, i + 4) };
  m := call match_lit(i, 4, 5);
  if m != 0 { return (1, 0, i + 5) };
  return (0, 0, i)
}

/-- Rust's `scan_bool`: the value and the position after it, or `none` (`ExpectedBool` at `i`). -/
def scanBoolN (b : Array UInt8) (i : Nat) : Option (Bool × Nat) :=
  if matchLitN b i LITS 0 4 0 then some (true, i + 4)
  else if matchLitN b i LITS 4 5 0 then some (false, i + 5)
  else none

/-- `ScanRes<bool>` as three words. -/
def encBool : Option (Bool × Nat) → Word → List Word
  | some (v, p), _ => [1, if v then 1 else 0, UInt64.ofNat p]
  | none, i => [0, 0, i]

attribute [local lang_grind] scanBoolN encBool

section scanBool
variable (p : Prog) (hp1 : p.lookup "match_lit" = some matchLit)
    (hp2 : p.lookup "scan_bool" = some scanBool) (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb hp1 hp2

theorem scanBool_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat + 5 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_bool" [i]
    ⦃fun r s' => s' = s₀ ∧ r = encBool (scanBoolN b i.toNat) i; ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, scanBool]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, LITS_length] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, matchLit_spec p hp1 b hb n] <;> finish

end scanBool

/-- The program, as `#eval`-able code. -/
def litProg : Prog := [("match_lit", matchLit), ("scan_bool", scanBool)]

#guard (run litProg 100 "scan_bool" [1] { bytes := #[" true".toUTF8.data] }).toOption.map (·.1)
  == some [1, 1, 5]
#guard (run litProg 100 "scan_bool" [0] { bytes := #["false".toUTF8.data] }).toOption.map (·.1)
  == some [1, 0, 5]
#guard (run litProg 100 "scan_bool" [0] { bytes := #["fals".toUTF8.data] }).toOption.map (·.1)
  == some [0, 0, 0]

end L.Scan.Lit
