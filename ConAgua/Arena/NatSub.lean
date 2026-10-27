module

public import ConAgua.Arena.NatCmp
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr

@[expose] public section

/-!
# Truncated subtraction on the limb pool: `nat_sub`

`nat_sub(oa, la, ob, lb)` is Lean's `a - b` (`0` when `a < b`), con-ron's `sub`/`sub_from`
(`ron/nat.rs:270-300`). con-ron compares first (`cmp`) and runs the ripple borrow only when
`a > b`; here the ripple borrow runs over `max la lb` limbs (`nat_add`'s loop shape, with
`nat_limb` for both operands) and the borrow out of the top limb decides: `1` means `a < b`,
and the result is `0`. This needs neither normalised inputs nor `nat_cmp`, and the loop is
`nat_add`'s with a borrow instead of a carry, so the proof is too.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The borrow -/

/-- The borrow out of the word subtraction `x - y - c`. -/
def sbbHi (x y c : Word) : Nat := if x.toNat < y.toNat + c.toNat then 1 else 0

/-- `x - y - c = low word - borrow · 2^64`, as an equation the ring solver sees. -/
theorem sbb_split (x y c : Word) (hc : c.toNat ≤ 1) :
    (x - y - c).toNat + y.toNat + c.toNat = x.toNat + sbbHi x y c * 2 ^ 64 := by
  simp only [sbbHi]
  have hx := x.toNat_lt; have hy := y.toNat_lt
  split
  · simp only [UInt64.toNat_sub, Nat.one_mul]; omega
  · simp only [UInt64.toNat_sub, Nat.zero_mul, Nat.add_zero]; omega
grind_pattern [arena_grind] sbb_split => sbbHi x y c

theorem sbbHi_le (x y c : Word) : sbbHi x y c ≤ 1 := by
  simp only [sbbHi]; split <;> omega
grind_pattern [arena_grind] sbbHi_le => sbbHi x y c

/-- The borrow out of `x - y - c` for a borrow-in `c ≤ 1` (the two `overflowing_sub`s of
`sub_from`, `ron/nat.rs:288-296`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def subBorrow : FunDecl := lfn (x, y, c) locals (d) {
  if x < y { return 1 };
  d := x - y;
  if d < c { return 1 };
  return 0
}

/-! ## `nat_sub(oa, la, ob, lb)` -/

def subLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, pt, pb) {
  while i < n {
    x := call nat_limb(oa, la, i);
    y := call nat_limb(ob, lb, i);
    POOL⟨pt⟩[pb + i] := x - y - c;
    c := call sub_borrow(x, y, c);
    i += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natSub : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, c, x, y, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪subLoop⟫;
  if c != 0 { n := 0 } else { n := call nat_trim(top, n) };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_sub`. -/
def natSubProg : Prog := natProg ++ [("sub_borrow", subBorrow), ("nat_sub", natSub)]

/- `2^64 - 1 = [max]`: operands `[0, 1]` at 0 and `[1]` at 2, top 3. -/
#guard (run natSubProg 100 "nat_sub" [0, 2, 2, 1]
  { words := #[#[0, 1, 1, 0, 0], #[3]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([1], #[#[0, 1, 1, 0xFFFFFFFFFFFFFFFF, 0], #[4]])
/- `1 - 2^64 = 0`, and `5 - 5 = 0`; the top stays. -/
#guard (run natSubProg 100 "nat_sub" [2, 1, 0, 2]
  { words := #[#[0, 1, 1, 0, 0], #[3]] }).toOption.map (fun (r, m) => (r, m.words.back!)) ==
  some ([0], #[3])
#guard (run natSubProg 100 "nat_sub" [0, 1, 1, 1]
  { words := #[#[5, 5, 0], #[2]] }).toOption.map (fun (r, m) => (r, m.words.back!)) ==
  some ([0], #[2])

section sub
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (Pg : Array Word) (C : Nat)

include hps in
theorem subBorrow_spec (n : Nat) (s₀ : St) (x y c : Word) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_borrow" [x, y, c]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat = sbbHi x y c; ⊤⦄ := by
  rw [invoke_eq _ hps]
  simp only [callFn, subBorrow]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, evalArgs, setLoc] <;>
      finish [sbbHi]

/-- The invariant of the subtract loop: `AddInv`'s, with the borrow on the other side. -/
def SubInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 64 ∧ Pg.size = 2 ^ 41 ∧
  pcap s.mem = C ∧ Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ C ∧
  s.loc 10 = s.loc 4 >>> 40 ∧ s.loc 11 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 11).toNat + (s.loc 5).toNat ≤ (s.mem.arr64 (tierA 0 (s.loc 10))).size ∧
  (s.mem.arr64 (tierA 0 (s.loc 10))).size ≤ 2 ^ 40 ∧ (s.loc 10).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 6).toNat ≤ (s.loc 5).toNat ∧ (s.loc 7).toNat ≤ 1 ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 6).toNat +
      xv Pg (s.loc 2).toNat (s.loc 3).toNat (s.loc 6).toNat =
    xv Pg (s.loc 0).toNat (s.loc 1).toNat (s.loc 6).toNat + (s.loc 7).toNat * wt (s.loc 6).toNat

/-- The post of the subtract loop. -/
def SubPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧
  (s'.loc 7).toNat ≤ 1 ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat +
      xv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 5).toNat =
    xv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 5).toNat + (s'.loc 7).toNat * wt (s₀.loc 5).toNat

set_option maxHeartbeats 2000000 in
include hpl hps in
theorem subLoop_spec (n : Nat) (s₀ : St) (h : SubInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n subLoop ⦃fun r s' => SubPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [SubInv, SubPost] at h ⊢
    rw [exec, step_while (w := subLoop) rfl]
    -- as `addLoop_spec`: the invariant unfolds into ten conjuncts
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, natLimb_spec p hpl n,
      subBorrow_spec p hps n]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, SubInv, SubPost]

include hpl hps in
theorem subLoop_step_spec (n : Nat) (s₀ : St) (h : SubInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) subLoop ⦃fun r s' => SubPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (subLoop_spec p hpl hps Pg C (n + 1) s₀ h)

end sub

/-- A set borrow (or carry) bit times a weight is the weight. -/
theorem bit_mul_wt (c : Word) (k : Nat) (h1 : c.toNat ≤ 1) (h2 : c ≠ 0) : c.toNat * wt k = wt k := by
  have : c.toNat ≠ 0 := fun h => h2 (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm))
  have : c.toNat = 1 := by omega
  rw [this, Nat.one_mul]
grind_pattern [arena_grind] bit_mul_wt => c.toNat * wt k

section subFn
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpn : p.lookup "nat_sub" = some natSub)

set_option maxHeartbeats 2000000 in
include hpl hps hpt hpn in
/-- `nat_sub` appends `a - b` (truncated), normalised, at the old top and moves the top past it;
nothing below the old top changes, and no other array but `CTL[0]`. -/
theorem natSub_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_sub" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat - pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpn]
  simp only [callFn, natSub]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      subLoop_step_spec p hpl hps (vpool s₀.mem) (pcap s₀.mem) n, natTrim_spec p hpt n]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals grind (ematch := 20) (splits := 30) (instances := 5000)
      [arena_grind, lang_grind, natcmp_grind, SubInv, SubPost]

end subFn

end L.Arena
