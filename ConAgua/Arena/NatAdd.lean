module

public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
import ConAgua.Census.Attr
public import ConAgua.L.Logic
import ConAgua.Arena.GrindAttr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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
    if POOL⦃o + n - 1⦄ != 0 { return n };
    n -= 1
  }
}

/-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat` -/
def natTrim : FunDecl := lfn (o, n) {
  ⟪trimLoop⟫;
  return 0
}

section trim
variable (p : Prog) (hp : p.lookup "nat_trim" = some natTrim)

theorem trimLoop_spec (n : Nat) (s₀ : St) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    exec p n trimLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ ((r.retOr [0]).headD 0).toNat ≤ (s₀.loc 1).toNat ∧
      pv (vpool s₀.mem) (s₀.loc 0).toNat ((r.retOr [0]).headD 0).toNat =
        pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
      Norm (vpool s₀.mem) (s₀.loc 0).toNat ((r.retOr [0]).headD 0).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := trimLoop) rfl]
    sym only [lang_grind, arena_grind] => vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish

theorem trimLoop_step_spec (n : Nat) (s₀ : St) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) trimLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ ((r.retOr [0]).headD 0).toNat ≤ (s₀.loc 1).toNat ∧
      pv (vpool s₀.mem) (s₀.loc 0).toNat ((r.retOr [0]).headD 0).toNat =
        pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
      Norm (vpool s₀.mem) (s₀.loc 0).toNat ((r.retOr [0]).headD 0).toNat; ⊤⦄ :=
  Triple.step_exec (trimLoop_spec p (n + 1) s₀ hs hb)

include hp in
theorem natTrim_spec (n : Nat) (s₀ : St) (o l : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_trim" [o, l]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat ≤ l.toNat ∧
      pv (vpool s₀.mem) o.toNat (r.headD 0).toNat = pv (vpool s₀.mem) o.toNat l.toNat ∧
      Norm (vpool s₀.mem) o.toNat (r.headD 0).toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natTrim]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, trimLoop_step_spec p n] <;> finish

end trim

/-! ## `nat_add(oa, la, ob, lb)`: append `a + b` to the pool, return its length

The result slice starts at the old top `CTL[0]`. One pass of ripple carry over
`n = max la lb` limbs (a missing limb reads as `0`, con-ron's `limb`), the carry limb, then
`nat_trim`. Inputs need not be normalised; the output is. -/

/-- Limb `i` of the slice `(o, l)`, `0` past its end (con-ron's `limb`, `ron/nat.rs:112`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def natLimb : FunDecl := lfn (o, l, i) {
  if i < l { return POOL⦃o + i⦄ };
  return 0
}

/-- The carry out of `x + y + c` for a carry-in `c ≤ 1` (the two `overflowing_add`s of
`add_from`, `ron/nat.rs:257-264`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def addCarry : FunDecl := lfn (x, y, c) locals (s) {
  s := x + y;
  if s < x { return 1 };
  s := s + c;
  if s < c { return 1 };
  return 0
}

def addLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, pt, pb) {
  while i < n {
    x := call nat_limb(oa, la, i);
    y := call nat_limb(ob, lb, i);
    POOL⟨pt⟩[pb + i] := x + y + c;
    c := call add_carry(x, y, c);
    i += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natAdd : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, c, x, y, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb <= n { abort };
  ⟪addLoop⟫;
  POOL⟨pt⟩[pb + n] := c;
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
  some ([3], #[#[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 1, 0, 0], #[6]])

/- Normalisation: `0 + 0` has length 0 (the carry limb `0` is trimmed); the top stays. -/
#guard (run natProg 100 "nat_add" [0, 0, 0, 0] { words := #[#[0, 0], #[0]] }).toOption.map (·.1)
  == some [0]

/- No room: `abort`. -/
#guard (run natProg 100 "nat_add" [0, 1, 0, 1] { words := #[#[5, 0], #[1]] }).toOption.isNone

section add
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (Pg : Array Word) (C : Nat)

include hpc in
theorem addCarry_spec (n : Nat) (s₀ : St) (x y c : Word) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "add_carry" [x, y, c]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat = adcHi x y c; ⊤⦄ := by
  rw [invoke_eq _ hpc]
  simp only [callFn, addCarry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, evalArgs, setLoc] <;> finish

include hpl in
theorem natLimb_spec (n : Nat) (s₀ : St) (o l i : Word)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) (hs : pcap s₀.mem < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_limb" [o, l, i]
    ⦃fun r s' => s' = s₀ ∧
      (r.headD 0).toNat = lv (vpool s₀.mem) o.toNat l.toNat i.toNat; ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, natLimb]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, evalArgs, ld64] <;> finish

/-- The invariant of the add loop. Ghost `Pg`: the pool at entry; the pool agrees with it below
`top` (so the operands, which lie below `top`, read the same), and the first `i` limbs of the
result plus the carry denote the first `i` limbs of `a + b`. -/
def AddInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 64 ∧
  pcap s.mem = C ∧ Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat < C ∧
  s.loc 10 = s.loc 4 >>> 40 ∧ s.loc 11 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 11).toNat + (s.loc 5).toNat < (s.mem.arr64 (tierA 0 (s.loc 10))).size ∧
  (s.mem.arr64 (tierA 0 (s.loc 10))).size ≤ 2 ^ 40 ∧ (s.loc 10).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 6).toNat ≤ (s.loc 5).toNat ∧ (s.loc 7).toNat ≤ 1 ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 6).toNat + (s.loc 7).toNat * wt (s.loc 6).toNat =
    xv Pg (s.loc 0).toNat (s.loc 1).toNat (s.loc 6).toNat +
    xv Pg (s.loc 2).toNat (s.loc 3).toNat (s.loc 6).toNat

set_option maxHeartbeats 2000000 in
include hpl hpc in
/-- The add loop. -/
theorem addLoop_spec (n : Nat) (s₀ : St) (h : AddInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    exec p n addLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧
      (s'.loc 7).toNat ≤ 1 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat + (s'.loc 7).toNat * wt (s₀.loc 5).toNat =
        xv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 5).toNat +
        xv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 5).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [AddInv] at h
    rw [exec, step_while (w := addLoop) rfl]
    -- plain `vcgen`, not `sym … => finish`: after `sym` the goals keep the tier-decoded loads in
    -- `setLoc` chains (PLAN.md, proof-style lessons); `grind` case-splits the next invariant's
    -- ten conjuncts, more than the default nine splits
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, natLimb_spec p hpl n,
      addCarry_spec p hpc n]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, AddInv]

include hpl hpc in
theorem addLoop_step_spec (n : Nat) (s₀ : St) (h : AddInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) addLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧
      (s'.loc 7).toNat ≤ 1 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat + (s'.loc 7).toNat * wt (s₀.loc 5).toNat =
        xv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 5).toNat +
        xv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 5).toNat; ⊤⦄ :=
  Triple.step_exec (addLoop_spec p hpl hpc Pg C (n + 1) s₀ h)

end add

section addFn
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd)

set_option maxHeartbeats 2000000 in
include hpl hpc hpt hpa in
/-- `nat_add` appends `a + b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natAdd_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat + pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpa]
  simp only [callFn, natAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      addLoop_step_spec p hpl hpc (vpool s₀.mem) (pcap s₀.mem) n, natTrim_spec p hpt n]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (ematch := 20) (splits := 30) (instances := 5000) [arena_grind, lang_grind, AddInv]

end addFn

end L.Arena
