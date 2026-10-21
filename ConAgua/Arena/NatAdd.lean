module

public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# `Nat.add` on the limb pool

`nat_trim` (con-ron's `norm`/`sig_len`, `ron/nat.rs:122,149`) and `nat_add` (`add`/`add_from`,
`ron/nat.rs:235,242`), with `vcgen` specs: the result slice denotes `a + b` and is normalised.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `nat_trim(o, n)`: the length of `(o, n)` without its trailing zero limbs -/

def trimLoop : Stmt := lblk (o, n) {
  while 0 < n {
    if POOL.u64[o + n - 1] != 0 { return n };
    n -= 1
  }
}

def natTrim : FunDecl := lfn (o, n) {
  ⟪trimLoop⟫;
  return 0
}

section trim
variable (p : Prog) (hp : p.lookup "nat_trim" = some natTrim)

theorem trimLoop_spec (n : Nat) (s₀ : St) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    exec p n trimLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ (r.retOr 0).toNat ≤ (s₀.loc 1).toNat ∧
      pv (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (r.retOr 0).toNat =
        pv (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
      Norm (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (r.retOr 0).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := trimLoop) rfl]
    sym only [lang_grind, arena_grind] => vcgen [step, evalE, evalC, setLoc, ld64, ih] <;> finish

theorem trimLoop_step_spec (n : Nat) (s₀ : St) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) trimLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ (r.retOr 0).toNat ≤ (s₀.loc 1).toNat ∧
      pv (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (r.retOr 0).toNat =
        pv (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
      Norm (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (r.retOr 0).toNat; ⊤⦄ :=
  Triple.step_exec (trimLoop_spec p (n + 1) s₀ hs hb)

include hp in
theorem natTrim_spec (n : Nat) (s₀ : St) (o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_trim" [o, l]
    ⦃fun r s' => s' = s₀ ∧ r.toNat ≤ l.toNat ∧
      pv (s₀.mem.arr64 POOL) o.toNat r.toNat = pv (s₀.mem.arr64 POOL) o.toNat l.toNat ∧
      Norm (s₀.mem.arr64 POOL) o.toNat r.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natTrim]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, trimLoop_step_spec p n] <;> finish

end trim

/-! ## `nat_add(oa, la, ob, lb)`: append `a + b` to the pool, return its length

The result slice starts at the old top `CTL[0]`. One pass of ripple carry over
`n = max la lb` limbs (a missing limb reads as `0`, con-ron's `limb`), the carry limb, then
`nat_trim`. Inputs need not be normalised; the output is. -/

/-- Limb `i` of the slice `(o, l)`, `0` past its end (con-ron's `limb`, `ron/nat.rs:112`). -/
def natLimb : FunDecl := lfn (o, l, i) {
  if i < l { return POOL.u64[o + i] };
  return 0
}

/-- The carry out of `x + y + c` for a carry-in `c ≤ 1` (the two `overflowing_add`s of
`add_from`, `ron/nat.rs:257-264`). -/
def addCarry : FunDecl := lfn (x, y, c) locals (s) {
  s := x + y;
  if s < x { return 1 };
  s := s + c;
  if s < c { return 1 };
  return 0
}

def addLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y) {
  while i < n {
    x := call nat_limb(oa, la, i);
    y := call nat_limb(ob, lb, i);
    POOL.u64[top + i] := x + y + c;
    c := call add_carry(x, y, c);
    i += 1
  }
}

def natAdd : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, c, x, y) {
  top := CTL.u64[0];
  n := la;
  if la < lb { n := lb };
  if len(POOL.u64) - top <= n { abort };
  ⟪addLoop⟫;
  POOL.u64[top + n] := c;
  n := call nat_trim(top, n + 1);
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions, as one `#eval`-able program. -/
def natProg : Prog :=
  [("nat_limb", natLimb), ("add_carry", addCarry), ("nat_trim", natTrim), ("nat_add", natAdd)]

/- `(2^128 - 1) + 1 = 2^128`: limbs `[max, max]` at 0 and `[1]` at 2, top 3; the sum is
`[0, 0, 1]` at 3 and the top moves to 6. -/
#guard (run natProg 100 "nat_add" [0, 2, 2, 1]
  { words := #[#[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 0, 0, 0], #[3]] }).toOption.map
  (fun (r, m) => (r, m.words)) ==
  some (3, #[#[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 1, 0, 0], #[6]])

/- Normalisation: `0 + 0` has length 0 (the carry limb `0` is trimmed); the top stays. -/
#guard (run natProg 100 "nat_add" [0, 0, 0, 0] { words := #[#[0, 0], #[0]] }).toOption.map (·.1)
  == some 0

/- No room: `abort`. -/
#guard (run natProg 100 "nat_add" [0, 1, 0, 1] { words := #[#[5, 0], #[1]] }).toOption.isNone

section add
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (Pg : Array Word)

include hpc in
theorem addCarry_spec (n : Nat) (s₀ : St) (x y c : Word) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "add_carry" [x, y, c]
    ⦃fun r s' => s' = s₀ ∧ r.toNat = adcHi x y c; ⊤⦄ := by
  rw [invoke_eq _ hpc]
  simp only [callFn, addCarry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, setLoc] <;> finish

include hpl in
theorem natLimb_spec (n : Nat) (s₀ : St) (o l i : Word)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_limb" [o, l, i]
    ⦃fun r s' => s' = s₀ ∧
      r.toNat = lv (s₀.mem.arr64 POOL) o.toNat l.toNat i.toNat; ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, natLimb]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, ld64] <;> finish

/-- The invariant of the add loop. Ghost `Pg`: the pool at entry; the pool agrees with it below
`top` (so the operands, which lie below `top`, read the same), and the first `i` limbs of the
result plus the carry denote the first `i` limbs of `a + b`. -/
def AddInv (Pg : Array Word) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ Pg.size < 2 ^ 64 ∧
  (s.mem.arr64 POOL).size = Pg.size ∧ Agree (s.mem.arr64 POOL) Pg (s.loc 4).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat < Pg.size ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 6).toNat ≤ (s.loc 5).toNat ∧ (s.loc 7).toNat ≤ 1 ∧
  pv (s.mem.arr64 POOL) (s.loc 4).toNat (s.loc 6).toNat + (s.loc 7).toNat * wt (s.loc 6).toNat =
    xv Pg (s.loc 0).toNat (s.loc 1).toNat (s.loc 6).toNat +
    xv Pg (s.loc 2).toNat (s.loc 3).toNat (s.loc 6).toNat

include hpl hpc in
/-- The add loop. -/
theorem addLoop_spec (n : Nat) (s₀ : St) (h : AddInv Pg s₀) :
    ⦃fun s => s = s₀⦄
    exec p n addLoop
    ⦃fun r s' => r = .normal ∧ Frame POOL s₀.mem s'.mem ∧
      (s'.mem.arr64 POOL).size = Pg.size ∧ Agree (s'.mem.arr64 POOL) Pg (s₀.loc 4).toNat ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ (s'.loc 7).toNat ≤ 1 ∧
      pv (s'.mem.arr64 POOL) (s₀.loc 4).toNat (s₀.loc 5).toNat + (s'.loc 7).toNat * wt (s₀.loc 5).toNat =
        xv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 5).toNat +
        xv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 5).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [AddInv] at h
    rw [exec, step_while (w := addLoop) rfl]
    -- `finish [AddInv]` unfolds the invariant of the next iteration into ten conjuncts, whose
    -- negation `grind` case-splits: more than the default nine splits
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, st64, ih, natLimb_spec p hpl n,
        addCarry_spec p hpc n] <;> finish (splits := 20) [AddInv]

include hpl hpc in
theorem addLoop_step_spec (n : Nat) (s₀ : St) (h : AddInv Pg s₀) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) addLoop
    ⦃fun r s' => r = .normal ∧ Frame POOL s₀.mem s'.mem ∧
      (s'.mem.arr64 POOL).size = Pg.size ∧ Agree (s'.mem.arr64 POOL) Pg (s₀.loc 4).toNat ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ (s'.loc 7).toNat ≤ 1 ∧
      pv (s'.mem.arr64 POOL) (s₀.loc 4).toNat (s₀.loc 5).toNat + (s'.loc 7).toNat * wt (s₀.loc 5).toNat =
        xv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 5).toNat +
        xv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 5).toNat; ⊤⦄ :=
  Triple.step_exec (addLoop_spec p hpl hpc Pg (n + 1) s₀ h)

end add

section addFn
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd)

include hpl hpc hpt hpa in
/-- `nat_add` appends `a + b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natAdd_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ Frame POOL (s₀.mem.set64 CTL 0 (s₀.mem.top + r)) s'.mem ∧
      (s'.mem.arr64 POOL).size = (s₀.mem.arr64 POOL).size ∧
      s₀.mem.top.toNat + r.toNat ≤ (s'.mem.arr64 POOL).size ∧
      Agree (s'.mem.arr64 POOL) (s₀.mem.arr64 POOL) s₀.mem.top.toNat ∧
      pv (s'.mem.arr64 POOL) s₀.mem.top.toNat r.toNat =
        pv (s₀.mem.arr64 POOL) oa.toNat la.toNat + pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat ∧
      Norm (s'.mem.arr64 POOL) s₀.mem.top.toNat r.toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  simp only [PoolOK, SliceOK] at hok ha hb
  rw [invoke_eq _ hpa]
  simp only [callFn, natAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64,
        addLoop_step_spec p hpl hpc (s₀.mem.arr64 POOL) n, natTrim_spec p hpt n] <;>
      -- depth, not search: the state after `top := …; n := …; if …` is many `setLoc`s deep
      finish (gen := 20) [AddInv, Grows]

end addFn

end L.Arena
