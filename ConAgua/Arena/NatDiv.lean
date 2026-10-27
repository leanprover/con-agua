module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatSub
meta import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
public import ConAgua.Arena.NatShl
public import ConAgua.Arena.NatSub
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmp
import ConAgua.Arena.NatGrindAttr
public import ConAgua.Arena.NatPow
public import ConAgua.Arena.NatShr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `Nat.div`/`Nat.mod` on the limb pool: `nat_divmod`

`nat_divmod(oa, la, ob, lb)` is `(a / b, a % b)` for a normalised `b` (con-ron's `div_mod`,
`dm_limbs`, `dm_bits`, `shl1_or`, `rev_copy_from`, `ron/nat.rs:570-640`): restoring shift-subtract
long division, one bit at a time from the top, as con-ron does (Knuth D would be faster; L has no
division instruction, and Knuth D's quotient estimate needs a 128-by-64 division). con-ron
allocates a new remainder per bit (`shl1_or`, `sub`); here the remainder lives in a scratch
region of `lb + 1` limbs above the quotient, and three in-place passes do the work per bit:

* `div_shl1(r, n, bit)`: `R := 2 R + bit`;
* `div_sub(r, n, ob, lb)`: `R := R - b`, returning the borrow;
* `div_add(r, n, ob, lb)`: `R := R + b` (the restore when the subtraction borrowed).

The quotient's limbs are written top down at `top + i`, each accumulated bit by bit in a word.
Lean's conventions: `a / 0 = 0`, `a % 0 = a` (the remainder is then `a`'s own slice, trimmed).

The in-place passes change only their region: `Off p q o n` (the pools agree off `[o, o + n)`)
is their frame, a named predicate with `grind` patterns, as `Agree` is for appending.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `Off`: the frame of an in-place pass -/

/-- `p` and `q` agree off the region `[o, o + n)`. -/
def Off (p q : Array Word) (o n : Nat) : Prop := ∀ j, (j < o ∨ o + n ≤ j) → p[j]? = q[j]?

theorem Off.refl (p : Array Word) (o n : Nat) : Off p p o n := fun _ _ => rfl
grind_pattern [arena_grind] Off.refl => Off p p o n

/-- Writing the limb just past the changed prefix extends it. -/
theorem Off.set (p q : Array Word) (o k k' j : Nat) (v : Word) (h : Off p q o k) (hj : j = o + k)
    (hk : k' = k + 1) : Off (p.set! j v) q o k' := by
  intro i hi
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  have : j ≠ i := by omega
  simp only [this, ite_false]
  exact h i (by omega)
grind_pattern [arena_grind] Off.set => Off (p.set! j v) q o k', Off p q o k

theorem Off.get (p q : Array Word) (o k j : Nat) (h : Off p q o k) (hj : o + k ≤ j)
    (hp : j < p.size) (hq : j < q.size) : p[j] = q[j] := by
  have := h j (Or.inr hj); simp [hp, hq] at this; exact this
grind_pattern [arena_grind] Off.get => Off p q o k, p[j]

theorem Off.pv_below (p q : Array Word) (o k o' l : Nat) (h : Off p q o k) (hl : o' + l ≤ o) :
    pv p o' l = pv q o' l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [pv, ih (by omega), h (o' + l) (Or.inl (by omega))]
grind_pattern [arena_grind] Off.pv_below => Off p q o k, pv p o' l

theorem Off.lv_below (p q : Array Word) (o k o' l i : Nat) (h : Off p q o k) (hl : o' + l ≤ o) :
    lv p o' l i = lv q o' l i := by
  simp only [lv]; split
  · rw [h (o' + i) (Or.inl (by omega))]
  · rfl
grind_pattern [arena_grind] Off.lv_below => Off p q o k, lv p o' l i

/-- An in-place pass over `[o, o + n)` inside a region `[t, t + m)` agrees with the pool off the
region. -/
theorem Off.widen (p q : Array Word) (o n t m : Nat) (h : Off p q o n) (h1 : t ≤ o)
    (h2 : o + n ≤ t + m) : Off p q t m := fun j hj => h j (by omega)

theorem Off.trans (p q r : Array Word) (o n : Nat) (h : Off p q o n) (h' : Off q r o n) :
    Off p r o n := fun j hj => (h j hj).trans (h' j hj)
grind_pattern [arena_grind] Off.trans => Off p q o n, Off q r o n

/-! ## Word facts -/

theorem shl1_split (x c : Word) (hc : c.toNat ≤ 1) :
    ((x <<< 1) ||| c).toNat + (x >>> 63).toNat * 2 ^ 64 = 2 * x.toNat + c.toNat := by
  have h := shl_split x c 1 (by decide) (by simpa using (by omega : c.toNat < 2))
  have e : (x >>> 1) >>> (63 - 1 : Word) = x >>> 63 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rfl
  rw [e] at h; simp only [show (1 : Word).toNat = 1 from rfl, Nat.pow_one] at h; omega
grind_pattern [arena_grind] shl1_split => (x <<< 1) ||| c

theorem shr63_le (x : Word) : (x >>> 63).toNat ≤ 1 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := x.toNat_lt
  show x.toNat / 2 ^ (63 % 64) ≤ 1
  rw [show 63 % 64 = 63 from rfl]
  exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
grind_pattern [arena_grind] shr63_le => x >>> 63

/-! ## The in-place passes -/

def shl1Loop : Stmt := lblk (r, n, bit, i, c, x, rt, rb) {
  while i < n {
    x := POOL⦃r + i⦄;
    POOL⟨rt⟩[rb + i] := (x << 1) | c;
    c := x >> 63;
    i += 1
  }
}

/-- `div_shl1(r, n, bit)`: `R := 2 R + bit` in place; returns the carry out. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def divShl1 : FunDecl := lfn (r, n, bit) locals (i, c, x, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  c := bit;
  ⟪shl1Loop⟫;
  return c
}

def dsubLoop : Stmt := lblk (r, n, ob, lb, i, c, x, y, rt, rb) {
  while i < n {
    x := POOL⦃r + i⦄;
    y := call nat_limb(ob, lb, i);
    POOL⟨rt⟩[rb + i] := x - y - c;
    c := call sub_borrow(x, y, c);
    i += 1
  }
}

/-- `div_sub(r, n, ob, lb)`: `R := R - b` in place (`b` zero-extended); returns the borrow. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def divSub : FunDecl := lfn (r, n, ob, lb) locals (i, c, x, y, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  ⟪dsubLoop⟫;
  return c
}

def daddLoop : Stmt := lblk (r, n, ob, lb, i, c, x, y, rt, rb) {
  while i < n {
    x := POOL⦃r + i⦄;
    y := call nat_limb(ob, lb, i);
    POOL⟨rt⟩[rb + i] := x + y + c;
    c := call add_carry(x, y, c);
    i += 1
  }
}

/-- `div_add(r, n, ob, lb)`: `R := R + b` in place (`b` zero-extended); returns the carry. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def divAdd : FunDecl := lfn (r, n, ob, lb) locals (i, c, x, y, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  ⟪daddLoop⟫;
  return c
}

section passes
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (P0 : Array Word) (C : Nat)

/-- The invariant of `div_shl1`'s pass, over the entry pool `P0`. -/
def Shl1Inv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 3).toNat ≤ (s.loc 1).toNat ∧
  s.loc 6 = s.loc 0 >>> 40 ∧ s.loc 7 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA 0 (s.loc 6))).size ≤ 2 ^ 40 ∧ (s.loc 6).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ 1 ∧ Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 3).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 3).toNat + (s.loc 4).toNat * wt (s.loc 3).toNat =
    2 * pv P0 (s.loc 0).toNat (s.loc 3).toNat + (s.loc 2).toNat

def Shl1Post (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  (s'.loc 4).toNat ≤ 1 ∧ Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 4).toNat * wt (s₀.loc 1).toNat =
    2 * pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + (s₀.loc 2).toNat

theorem shl1Loop_spec (n : Nat) (s₀ : St) (h : Shl1Inv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n shl1Loop ⦃fun r s' => Shl1Post P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [Shl1Inv, Shl1Post] at h ⊢
    rw [exec, step_while (w := shl1Loop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, Shl1Inv, Shl1Post]

/-- The invariant of `div_sub`'s pass. -/
def DSubInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∧
  s.loc 8 = s.loc 0 >>> 40 ∧ s.loc 9 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA 0 (s.loc 8))).size ≤ 2 ^ 40 ∧ (s.loc 8).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧ (s.loc 5).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat +
      xv P0 (s.loc 2).toNat (s.loc 3).toNat (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat

def DSubPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  (s'.loc 5).toNat ≤ 1 ∧ Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat +
      xv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 5).toNat * wt (s₀.loc 1).toNat

set_option maxHeartbeats 2000000 in
include hpl hps in
theorem dsubLoop_spec (n : Nat) (s₀ : St) (h : DSubInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n dsubLoop ⦃fun r s' => DSubPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DSubInv, DSubPost] at h ⊢
    rw [exec, step_while (w := dsubLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, natLimb_spec p hpl n,
      subBorrow_spec p hps n]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, DSubInv, DSubPost]

/-- The invariant of `div_add`'s pass. -/
def DAddInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∧
  s.loc 8 = s.loc 0 >>> 40 ∧ s.loc 9 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA 0 (s.loc 8))).size ≤ 2 ^ 40 ∧ (s.loc 8).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧ (s.loc 5).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + xv P0 (s.loc 2).toNat (s.loc 3).toNat (s.loc 4).toNat

def DAddPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  (s'.loc 5).toNat ≤ 1 ∧ Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 5).toNat * wt (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + xv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 1).toNat

-- the virtual pool's extra `P0.size` conjunct pushes the step past the default budget
set_option maxHeartbeats 2000000 in
include hpl hpc in
theorem daddLoop_spec (n : Nat) (s₀ : St) (h : DAddInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n daddLoop ⦃fun r s' => DAddPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DAddInv, DAddPost] at h ⊢
    rw [exec, step_while (w := daddLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, natLimb_spec p hpl n,
      addCarry_spec p hpc n]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, DAddInv, DAddPost]

theorem shl1Loop_step_spec (n : Nat) (s₀ : St) (h : Shl1Inv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) shl1Loop ⦃fun r s' => Shl1Post P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (shl1Loop_spec p P0 C (n + 1) s₀ h)

include hpl hps in
theorem dsubLoop_step_spec (n : Nat) (s₀ : St) (h : DSubInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) dsubLoop ⦃fun r s' => DSubPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (dsubLoop_spec p hpl hps P0 C (n + 1) s₀ h)

include hpl hpc in
theorem daddLoop_step_spec (n : Nat) (s₀ : St) (h : DAddInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) daddLoop ⦃fun r s' => DAddPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (daddLoop_spec p hpl hpc P0 C (n + 1) s₀ h)

end passes

section passFns
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)

theorem divShl1_spec (hp : p.lookup "div_shl1" = some divShl1) (n : Nat) (s₀ : St)
    (r k bit : Word) (hs : pcap s₀.mem < 2 ^ 64) (hw : POOL < s₀.mem.words.size)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : bit.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_shl1" [r, k, bit]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat + (res.headD 0).toNat * wt k.toNat =
        2 * pv (vpool s₀.mem) r.toNat k.toNat + bit.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divShl1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc,
        shl1Loop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n] <;>
      finish [Shl1Inv, Shl1Post]

include hpl hps in
theorem divSub_spec (hp : p.lookup "div_sub" = some divSub) (n : Nat) (s₀ : St)
    (r k ob lb : Word) (hs : pcap s₀.mem < 2 ^ 64) (hw : POOL < s₀.mem.words.size)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_sub" [r, k, ob, lb]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat + xv (vpool s₀.mem) ob.toNat lb.toNat k.toNat =
        pv (vpool s₀.mem) r.toNat k.toNat + (res.headD 0).toNat * wt k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divSub]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc,
        dsubLoop_step_spec p hpl hps (vpool s₀.mem) (pcap s₀.mem) n] <;>
      finish [DSubInv, DSubPost]

include hpl hpc in
theorem divAdd_spec (hp : p.lookup "div_add" = some divAdd) (n : Nat) (s₀ : St)
    (r k ob lb : Word) (hs : pcap s₀.mem < 2 ^ 64) (hw : POOL < s₀.mem.words.size)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_add" [r, k, ob, lb]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat + (res.headD 0).toNat * wt k.toNat =
        pv (vpool s₀.mem) r.toNat k.toNat + xv (vpool s₀.mem) ob.toNat lb.toNat k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc,
        daddLoop_step_spec p hpl hpc (vpool s₀.mem) (pcap s₀.mem) n] <;>
      finish [DAddInv, DAddPost]

end passFns

/-! ## Arithmetic of the long division -/

theorem Agree.of_off (p q r : Array Word) (o k t : Nat) (h : Off p q o k) (h' : Agree q r t)
    (ht : t ≤ o) : Agree p r t := fun j hj => (h j (Or.inl (by omega))).trans (h' j hj)
grind_pattern [arena_grind] Agree.of_off => Off p q o k, Agree q r t

/-- Prepending a limb: `pv p o (k + 1) = p[o] + 2^64 · pv p (o + 1) k`. -/
theorem pv_cons (p : Array Word) (o o' k k' : Nat) (ho : o' = o + 1) (hk : k' = k + 1)
    (h : o < p.size) : pv p o k' = p[o].toNat + 2 ^ 64 * pv p o' k := by
  subst ho hk
  have := pv_append p o 1 k
  rw [Nat.add_comm 1 k] at this
  rw [this, pv_one p o h]; rfl
grind_pattern [natop_grind] pv_cons => pv p o k', pv p o' k, p[o]

/-- Writing a limb just below a slice of an in-place region's other side (`Off`), and prepending
it: the slice is read in the pool before the pass. -/
theorem pv_set_cons_off (p q : Array Word) (o o' k k' j r n : Nat) (v : Word) (hoff : Off p q r n)
    (hj : j = o) (ho : o' = o + 1) (hk : k' = k + 1) (hd : o + k' ≤ r) (h : o < p.size) :
    pv (p.set! j v) o k' = v.toNat + 2 ^ 64 * pv q o' k := by
  subst j
  have hs : o < (p.set! o v).size := by simpa using h
  have hc := pv_cons (p.set! o v) o o' k k' ho hk hs
  rw [hc]
  have h1 : pv (p.set! o v) o' k = pv p o' k := by
    subst ho
    clear hk hc hd
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [pv, ih]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show o ≠ o + 1 + k by omega]
  rw [h1, Off.pv_below p q r n o' k hoff (by omega)]
  simp [Array.set!_eq_setIfInBounds]
grind_pattern [natop_grind] pv_set_cons_off => pv (p.set! j v) o k', Off p q r n, pv q o' k

theorem pv_pos_of_norm (p : Array Word) (o l : Nat) (hn : Norm p o l) (hl : 0 < l) :
    0 < pv p o l := Nat.lt_of_lt_of_le (wt_pos _) (pv_ge_wt p o l hl hn)
grind_pattern [arena_grind] pv_pos_of_norm => Norm p o l, pv p o l

theorem sh_step (a b : Nat) (h : a = b + 1) : sh a = 2 * sh b := by
  subst h; simp only [sh, Nat.pow_succ]; omega
grind_pattern [natop_grind] sh_step => sh a, sh b

theorem sh_of_zero (a : Nat) (h : a = 0) : sh a = 1 := by subst h; rfl
grind_pattern [natop_grind] sh_of_zero => sh a

theorem sh_of_64 (a : Nat) (h : a = 64) : sh a = 2 ^ 64 := by subst h; rfl
grind_pattern [natop_grind] sh_of_64 => sh a

theorem sh_le63 (a : Nat) (h : a ≤ 63) : sh a ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) h
grind_pattern [natop_grind] sh_le63 => sh a

theorem div_sh_64 (x : Word) (j : Nat) (h : j = 64) : x.toNat / sh j = 0 := by
  subst h; exact Nat.div_eq_of_lt x.toNat_lt
grind_pattern [natop_grind] div_sh_64 => x.toNat / sh j

theorem div_sh_0 (x : Word) (j : Nat) (h : j = 0) : x.toNat / sh j = x.toNat := by
  subst h; simp [sh]
grind_pattern [natop_grind] div_sh_0 => x.toNat / sh j

/-- The dividend's bits from the top: `x / 2^j' = 2 (x / 2^j) + bit j'`, for `j = j' + 1`. -/
theorem div_sh_step (x j' : Word) (j : Nat) (hj : j'.toNat + 1 = j) (h64 : j ≤ 64) :
    x.toNat / sh j'.toNat = 2 * (x.toNat / sh j) + ((x >>> j') &&& 1).toNat := by
  subst hj
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (by omega : j'.toNat < 64)]
  simp only [Nat.shiftRight_eq_div_pow, UInt64.toNat_one, sh]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.pow_succ,
    ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (x.toNat / 2 ^ j'.toNat) 2
  omega
grind_pattern [natop_grind] div_sh_step => x.toNat / sh j'.toNat, x.toNat / sh j

theorem shl1_or (q c : Word) (h : q.toNat < 2 ^ 63) (hc : c.toNat ≤ 1) :
    ((q <<< 1) ||| c).toNat = 2 * q.toNat + c.toNat := by
  have := shl1_split q c hc
  have h2 : (q >>> 63).toNat = 0 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by simpa using h)
  rw [h2] at this; simpa using this
grind_pattern [arena_grind] shl1_or => (q <<< 1) ||| c

/-- The quotient and the remainder from `A = Q · B + R`, `R < B` (bounds on `Q · B` only, so
that the pattern binds every variable). -/
theorem div_of_bounds (A B Q : Nat) (h1 : Q * B ≤ A) (h2 : A < Q * B + B) : A / B = Q := by
  apply Nat.div_eq_of_lt_le
  · exact h1
  · rw [Nat.succ_mul]; exact h2
grind_pattern [natcmp_grind] div_of_bounds => A / B, Q * B

theorem mod_of_bounds (A B Q : Nat) (h1 : Q * B ≤ A) (h2 : A < Q * B + B) :
    A % B = A - Q * B := by
  have := Nat.div_add_mod A B
  rw [div_of_bounds A B Q h1 h2] at this
  rw [Nat.mul_comm] at this; omega
grind_pattern [natcmp_grind] mod_of_bounds => A % B, Q * B

/-- Writing below a slice does not change it. -/
theorem pv_set_below (p : Array Word) (o k j : Nat) (v : Word) (h : j < o) :
    pv (p.set! j v) o k = pv p o k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pv, ih]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [show j ≠ o + k by omega]
grind_pattern [arena_grind] pv_set_below => pv (p.set! j v) o k

/-- The limb loop's exit: the pointer is back at the slice's start, all limbs done. -/
theorem pv_exit (p : Array Word) (pa oa : Nat) (i la : Word) (h : ¬ i < la)
    (hi : i.toNat ≤ la.toNat) (hpa : pa + i.toNat = oa + la.toNat) :
    pv p pa i.toNat = pv p oa la.toNat := by
  have : i.toNat = la.toNat := by
    have : ¬ i.toNat < la.toNat := fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')
    omega
  rw [this, show pa = oa by omega]
grind_pattern [natop_grind] pv_exit => pv p pa i.toNat, pv p oa la.toNat, i < la

theorem Grows.refl (m : Mem) (h : PoolOK m) : Grows m m := by
  have h2 := h.2.1
  have hf : PFrame (m.set64 CTL 0 m.top) m := by
    refine ⟨by rw [Mem.bytes_set64], by rw [Mem.words_size_set64], fun b _ _ => ?_,
      by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)],
      by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], rfl⟩
    by_cases hb : b = CTL
    · subst hb
      rw [Mem.arr64_set64_same, Mem.top_eq m h2]
      simp only [Array.set!_eq_setIfInBounds, show (0 : Word).toNat = 0 from rfl]
      grind
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hb]
  exact Grows.intro m m h hf (Agree.refl _ _) (Nat.le_refl _) (by have := h.2.2.2.2.2; omega)
grind_pattern [arena_grind] Grows.refl => Grows m m

/-- A shorter prefix of a slice in use is in use. -/
theorem SliceOK.shrink {m : Mem} {o l l' : Word} (h : SliceOK m o l) (hl : l'.toNat ≤ l.toNat) :
    SliceOK m o l' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩
grind_pattern [arena_grind] SliceOK.shrink => SliceOK m o l, SliceOK m o l'

/-- A slice of what a pool function appended, `[top, top')`, is in use. -/
theorem SliceOK.sub {m m' : Mem} {o l : Word} (hg : Grows m m') (ho : m.top.toNat ≤ o.toNat)
    (hl : o.toNat + l.toNat ≤ m'.top.toNat) : SliceOK m' o l := by
  have ht := hg.tier
  exact ⟨hl, by omega⟩
grind_pattern [arena_grind] SliceOK.sub => Grows m m', SliceOK m' o l

/-- `Grows.write` for a new top `v` not of the form `top + n` (`nat_divmod`'s `ro + n`); its
pattern puts the `Grows` fact into a goal about the final memory (`PoolOK`, `SliceOK`). -/
theorem Grows.write_at (m m₂ : Mem) (v : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (hv : m.top.toNat ≤ v.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (v.toNat - m.top.toNat) ≤
      (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    Grows m (m₂.set64 CTL 0 v) := by
  have hctl : 0 < (m₂.arr64 CTL).size := by rw [hf.ctl]; exact hok.2.1
  have htop : (m₂.set64 CTL 0 v).top = v := Mem.top_set64 _ _ hctl
  apply Grows.intro m _ hok
  · rw [htop]; exact PFrame.set64_both CTL 0 _ hf (by decide) (by decide)
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]; exact ha
  · rw [htop]; exact hv
  · rw [htop]; exact hk

/-- `Grows.write_at`'s pool invariant, keyed on the goal (a `Grows` pattern on `m₂.set64 CTL 0 v`
would fire on every frame `Grows.intro` builds). -/
theorem PoolOK.write_at (m m₂ : Mem) (v : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (hv : m.top.toNat ≤ v.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (v.toNat - m.top.toNat) ≤
      (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    PoolOK (m₂.set64 CTL 0 v) := hok.grows (Grows.write_at m m₂ v hok hf ha hv hk)
grind_pattern [arena_grind] PoolOK.write_at => PoolOK m, PoolOK (m₂.set64 CTL 0 v)

/-- `Grows.write_at`'s fresh slices, keyed on the goal. -/
theorem SliceOK.write_at (m m₂ : Mem) (v o l : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (hv : m.top.toNat ≤ v.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (v.toNat - m.top.toNat) ≤
      (m.arr64 (tierA 0 (m.top >>> 40))).size)
    (ho : m.top.toNat ≤ o.toNat) (hl : o.toNat + l.toNat ≤ v.toNat) :
    SliceOK (m₂.set64 CTL 0 v) o l := by
  have hg := Grows.write_at m m₂ v hok hf ha hv hk
  have hctl : 0 < (m₂.arr64 CTL).size := by rw [hf.ctl]; exact hok.2.1
  exact SliceOK.sub hg ho (by rw [Mem.top_set64 _ _ hctl]; exact hl)
grind_pattern [arena_grind] SliceOK.write_at => PoolOK m, SliceOK (m₂.set64 CTL 0 v) o l

/-- The slice of length `0` at the top is in use. -/
theorem SliceOK.top0 {m : Mem} {o : Word} (h : o = m.top) : SliceOK m o 0 := by
  subst h; exact ⟨by simp, by omega⟩
grind_pattern [arena_grind] SliceOK.top0 => SliceOK m o 0

/-! ## `nat_divmod(oa, la, ob, lb)` -/

/-- One bit of the dividend: `R := 2 R + bit`, then subtract `b`, restoring on a borrow; returns
the quotient bit (the body of con-ron's `dm_bits`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def divStep : FunDecl := lfn (r, n, ob, lb, bit) locals (c) {
  c := call div_shl1(r, n, bit);
  c := call div_sub(r, n, ob, lb);
  if c != 0 {
    c := call div_add(r, n, ob, lb);
    return 0
  };
  return 1
}

/-- The bits of limb `x` from the top, into the quotient word `q`. -/
def bitLoop : Stmt := lblk (oa, la, ob, lb, top, n, ro, i, x, q, j, c) {
  while 0 < j {
    j -= 1;
    c := call div_step(ro, n, ob, lb, (x >> j) & 1);
    q := (q << 1) | c
  }
}

/-- One limb of the dividend, from the top (con-ron's `dm_limbs`): `pa` and `pq` point at the
current limb of `a` and of the quotient, `i` counts the limbs done. -/
def limbLoop : Stmt := lblk (oa, la, ob, lb, top, n, ro, i, x, q, j, c, pa, pq, pt, pb) {
  while i < la {
    pa -= 1;
    pq -= 1;
    x := POOL⦃pa⦄;
    q := 0;
    j := 64;
    ⟪bitLoop⟫;
    POOL⟨pt⟩[pb + (pq - top)] := q;
    i += 1
  }
}

/-- The remainder starts at `0`. -/
def rzLoop : Stmt := lblk (oa, la, ob, lb, top, n, ro, i, x, q, j, c, pa, pq, pt, pb) {
  while j < n {
    POOL⟨pt⟩[pb + (la + j)] := 0;
    j += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natDivmod : FunDecl := lfn (oa, la, ob, lb) locals (top, n, ro, i, x, q, j, c, pa, pq, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if lb == 0 {
    c := call nat_trim(oa, la);
    return (top, 0, oa, c)
  };
  n := lb + 1;
  if len(POOL⟨pt⟩) - pb < la { abort };
  if len(POOL⟨pt⟩) - pb - la < n { abort };
  ro := top + la;
  ⟪rzLoop⟫;
  pa := oa + la;
  pq := ro;
  ⟪limbLoop⟫;
  x := call nat_trim(top, la);
  c := call nat_trim(ro, n);
  CTL.u64[0] := ro + n;
  return (top, x, ro, c)
}

/-- The pool functions with `nat_divmod`. -/
def natDivProg : Prog := natProg ++ [("sub_borrow", subBorrow), ("div_shl1", divShl1),
  ("div_sub", divSub), ("div_add", divAdd), ("div_step", divStep), ("nat_divmod", natDivmod)]

/- `(2^64 + 5) / 3 = 6148914691236517207, rem 0`; quotient `[0x5555555555555557]`. -/
#guard (run natDivProg 100000 "nat_divmod" [0, 2, 2, 1]
  { words := #[#[5, 1, 3, 0, 0, 0, 0, 0], #[3]] }).toOption.map
  (fun (r, m) => (r, m.words[0]![3]!, m.words[1]!)) ==
  some ([3, 1, 5, 0], 0x5555555555555557, #[7])
/- `7 / 2 = 3 rem 1`; `5 / 0 = 0 rem 5` (the remainder is `a`'s slice). -/
#guard (run natDivProg 100000 "nat_divmod" [0, 1, 1, 1]
  { words := #[#[7, 2, 0, 0, 0, 0], #[2]] }).toOption.map
  (fun (r, m) => (r, m.words[0]![2]!, m.words[0]![3]!)) == some ([2, 1, 3, 1], 3, 1)
#guard (run natDivProg 100000 "nat_divmod" [0, 1, 1, 0]
  { words := #[#[5, 0], #[1]] }).toOption.map (·.1) == some [1, 0, 0, 1]

section step
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (hp1 : p.lookup "div_shl1" = some divShl1) (hp2 : p.lookup "div_sub" = some divSub)
  (hp3 : p.lookup "div_add" = some divAdd)

include hpl hps hpc hp1 hp2 hp3 in
/-- One step of the long division: `R' + qbit · b = 2 R + bit`, `R' < b`, in place. -/
theorem divStep_spec (hp4 : p.lookup "div_step" = some divStep) (n : Nat) (s₀ : St)
    (r k ob lb bit : Word) (hs : pcap s₀.mem < 2 ^ 64) (hw : POOL < s₀.mem.words.size)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ r.toNat)
    (hk : k.toNat = lb.toNat + 1) (hbit : bit.toNat ≤ 1)
    (hR : pv (vpool s₀.mem) r.toNat k.toNat < pv (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_step" [r, k, ob, lb, bit]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat < pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat +
          (res.headD 0).toNat * pv (vpool s₀.mem) ob.toNat lb.toNat =
        2 * pv (vpool s₀.mem) r.toNat k.toNat + bit.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp4]
  simp only [callFn, divStep]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        divShl1_spec p hp1 n, divSub_spec p hpl hps hp2 n, divAdd_spec p hpl hpc hp3 n] <;>
      finish

end step

section div
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (hp1 : p.lookup "div_shl1" = some divShl1) (hp2 : p.lookup "div_sub" = some divSub)
  (hp3 : p.lookup "div_add" = some divAdd) (Pg : Array Word) (C : Nat)

/-- What every loop of `nat_divmod` keeps: the pool agrees with the entry pool below `top`; the
quotient's `la` limbs at `top` and the remainder's `n = lb + 1` limbs at `ro = top + la` fit;
`a` and `b` lie below `top`; `b > 0`. -/
def DivBase (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 63 ∧ Pg.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 6).toNat = (s.loc 4).toNat + (s.loc 1).toNat ∧ (s.loc 5).toNat = (s.loc 3).toNat + 1 ∧
  (s.loc 6).toNat + (s.loc 5).toNat ≤ C ∧
  s.loc 14 = s.loc 4 >>> 40 ∧ s.loc 15 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 15).toNat + (s.loc 1).toNat + (s.loc 5).toNat ≤ (s.mem.arr64 (tierA 0 (s.loc 14))).size ∧
  (s.mem.arr64 (tierA 0 (s.loc 14))).size ≤ 2 ^ 40 ∧ (s.loc 14).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  0 < pv Pg (s.loc 2).toNat (s.loc 3).toNat

/-- The bit loop: the quotient word so far is below `2^(64 - j)` and the remainder below `b`. -/
def DBitInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  DivBase Pg C s ∧ (s.loc 10).toNat ≤ 64 ∧ (s.loc 9).toNat < sh (64 - (s.loc 10).toNat) ∧
  pv (vpool s.mem) (s.loc 6).toNat (s.loc 5).toNat < pv Pg (s.loc 2).toNat (s.loc 3).toNat

/-- The bit loop's effect, relative to its entry (`R₀`, `q₀`, `j₀` bits of `x` left):
`R₀ · 2^j₀ + x + q₀ · 2^j₀ · b = q · b + R + (x / 2^j₀) · 2^j₀`. Stating it relative to the
entry keeps the dividend's and the quotient's other limbs out of the loop. -/
def DBitPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  Off (vpool s'.mem) (vpool s₀.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
  s'.loc 8 = s₀.loc 8 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
  s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧
  pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat < pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat ∧
  pv (vpool s₀.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat * sh (s₀.loc 10).toNat + (s₀.loc 8).toNat +
      (s₀.loc 9).toNat * sh (s₀.loc 10).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat =
    (s'.loc 9).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat +
      pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat +
      (s₀.loc 8).toNat / sh (s₀.loc 10).toNat * sh (s₀.loc 10).toNat

include hpl hps hpc hp1 hp2 hp3 in
theorem bitLoop_spec (hp4 : p.lookup "div_step" = some divStep) (n : Nat) (s₀ : St)
    (h : DBitInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n bitLoop ⦃fun r s' => DBitPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DBitInv, DivBase, DBitPost] at h ⊢
    rw [exec, step_while (w := bitLoop) rfl]
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        divStep_spec p hpl hps hpc hp1 hp2 hp3 hp4 n] <;>
      finish (splits := 20) [DBitInv, DivBase, DBitPost]

include hpl hps hpc hp1 hp2 hp3 in
theorem bitLoop_step_spec (hp4 : p.lookup "div_step" = some divStep) (n : Nat) (s₀ : St)
    (h : DBitInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) bitLoop ⦃fun r s' => DBitPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (bitLoop_spec p hpl hps hpc hp1 hp2 hp3 Pg C hp4 (n + 1) s₀ h)

/-- The limb loop: the top `i` limbs of `a` (at `pa`) are the top `i` limbs of the quotient
(at `pq`) times `b`, plus the remainder `R < b`. -/
def LimbInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  DivBase Pg C s ∧ (s.loc 7).toNat ≤ (s.loc 1).toNat ∧
  (s.loc 12).toNat + (s.loc 7).toNat = (s.loc 0).toNat + (s.loc 1).toNat ∧
  (s.loc 13).toNat + (s.loc 7).toNat = (s.loc 4).toNat + (s.loc 1).toNat ∧
  pv (vpool s.mem) (s.loc 6).toNat (s.loc 5).toNat < pv Pg (s.loc 2).toNat (s.loc 3).toNat ∧
  pv Pg (s.loc 12).toNat (s.loc 7).toNat =
    pv (vpool s.mem) (s.loc 13).toNat (s.loc 7).toNat * pv Pg (s.loc 2).toNat (s.loc 3).toNat +
    pv (vpool s.mem) (s.loc 6).toNat (s.loc 5).toNat

def LimbPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
  s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧
  pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat < pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat ∧
  pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat =
    pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 1).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat +
    pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat

include hpl hps hpc hp1 hp2 hp3 in
theorem limbLoop_spec (hp4 : p.lookup "div_step" = some divStep) (n : Nat) (s₀ : St)
    (h : LimbInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n limbLoop ⦃fun r s' => LimbPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [LimbInv, DivBase, LimbPost] at h ⊢
    rw [exec, step_while (w := limbLoop) rfl]
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        bitLoop_step_spec p hpl hps hpc hp1 hp2 hp3 Pg C hp4 n] <;>
      finish (splits := 20) [LimbInv, DivBase, LimbPost, DBitInv, DBitPost]

include hpl hps hpc hp1 hp2 hp3 in
theorem limbLoop_step_spec (hp4 : p.lookup "div_step" = some divStep) (n : Nat) (s₀ : St)
    (h : LimbInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) limbLoop ⦃fun r s' => LimbPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (limbLoop_spec p hpl hps hpc hp1 hp2 hp3 Pg C hp4 (n + 1) s₀ h)

/-- The zeroing of the remainder. -/
def RzInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  DivBase Pg C s ∧ (s.loc 10).toNat ≤ (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 6).toNat (s.loc 10).toNat = 0

def RzPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
  s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧
  pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 5).toNat = 0

theorem rzLoop_spec (n : Nat) (s₀ : St) (h : RzInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n rzLoop ⦃fun r s' => RzPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [RzInv, DivBase, RzPost] at h ⊢
    rw [exec, step_while (w := rzLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, setLoc, setLocs, st64, ih] <;>
      finish (splits := 20) [RzInv, DivBase, RzPost]

theorem rzLoop_step_spec (n : Nat) (s₀ : St) (h : RzInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) rzLoop ⦃fun r s' => RzPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (rzLoop_spec p Pg C (n + 1) s₀ h)

end div

section divFn
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (hp1 : p.lookup "div_shl1" = some divShl1) (hp2 : p.lookup "div_sub" = some divSub)
  (hp3 : p.lookup "div_add" = some divAdd) (hp4 : p.lookup "div_step" = some divStep)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_divmod" = some natDivmod)

set_option maxHeartbeats 4000000 in
include hpl hps hpc hp1 hp2 hp3 hp4 hpt hpn in
/-- `nat_divmod` returns two normalised slices in use, `(oq, lq)` denoting `a / b` and
`(or, lr)` denoting `a % b`; the memory grew. `b` must be normalised (its length decides). -/
theorem natDivmod_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_divmod" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat / pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      SliceOK s'.mem (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat % pv (vpool s₀.mem) ob.toNat lb.toNat; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  have ha1 := ha.1
  have hb1 := hb.1
  rw [invoke_eq _ hpn]
  simp only [callFn, natDivmod]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      rzLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n,
      limbLoop_step_spec p hpl hps hpc hp1 hp2 hp3 (vpool s₀.mem) (pcap s₀.mem) hp4 n,
      natTrim_spec p hpt n]
    all_goals (try simp only [RzInv, LimbInv, DivBase, RzPost, LimbPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte,
      Nat.reduceEqDiff, UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals grind (gen := 40) (ematch := 20) (splits := 30) (instances := 5000)
      [arena_grind, lang_grind, natcmp_grind, natop_grind]

end divFn

end L.Arena
