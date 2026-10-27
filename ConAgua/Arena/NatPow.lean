module

public import ConAgua.Arena.NatMul
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `Nat.pow` on the limb pool: `nat_pow`

`nat_pow(oa, la, e)` is `a ^ e` for a word exponent `e < 2^25` (con-ron's `pow`,
`ron/nat.rs:547-561`; the caller enforces con-leche's `ReducePowMaxExp`, `e ≤ 2^24`, as
`natOpResult` does). Square-and-multiply from the top bit down: start from a one-limb `1`, then
for `j = 24, …, 0` square, and multiply by `a` if bit `j` of `e` is set; each product is a call of
`nat_mul`, which appends it to the pool. The result is the last product, so `nat_pow` returns
its offset and its length, `(o, l)`. The intermediate products stay in the pool below the top
(garbage, as con-ron's dropped `Vec`s are, but never freed here).

The loop's invariant follows the accumulator slice `(o, l)`, which moves every iteration:
`pv o l = a ^ (e >> j)`, with `Grows` from the entry memory (`Grows.trans`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Frames and the exponent -/

theorem Agree.trans (p q r : Array Word) (t t' : Nat) (h : Agree p q t') (h' : Agree q r t)
    (ht : t ≤ t') : Agree p r t := fun j hj => (h j (by omega)).trans (h' j hj)


/-- A one-limb slice just written. -/
theorem pv_set_one (p : Array Word) (o j l : Nat) (v : Word) (hl : l = 1) (hj : j = o)
    (h : j < p.size) : pv (p.set! j v) o l = v.toNat := by
  subst hj hl; simp [pv, wt, h]
grind_pattern [natop_grind] pv_set_one => pv (p.set! j v) o l

theorem Norm.set_one (p : Array Word) (o j l : Nat) (v : Word) (hl : l = 1) (hj : j = o)
    (h : j < p.size) (hv : v ≠ 0) : Norm (p.set! j v) o l := by
  subst hj hl; simp [Norm, h, hv]
grind_pattern [natop_grind] Norm.set_one => Norm (p.set! j v) o l

/-- The exponent's bits from the top: `e >> j' = 2 (e >> j) + bit`, for `j = j' + 1`. -/
theorem shr_succ (e j j' : Word) (hj : j'.toNat + 1 = j.toNat) (h64 : j.toNat < 64) :
    (e >>> j').toNat = 2 * (e >>> j).toNat + ((e >>> j') &&& 1).toNat := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt (by omega : j'.toNat < 64), Nat.mod_eq_of_lt h64]
  simp only [Nat.shiftRight_eq_div_pow, UInt64.toNat_one]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, ← hj, Nat.pow_succ,
    ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (e.toNat / 2 ^ j'.toNat) 2
  omega

theorem pow_step1 (A : Nat) (e j j' : Word) (hj : j'.toNat + 1 = j.toNat) (h64 : j.toNat < 64)
    (hb : (e >>> j') &&& 1 ≠ 0) :
    A ^ (e >>> j').toNat = A ^ (e >>> j).toNat * A ^ (e >>> j).toNat * A := by
  have h1 : ((e >>> j') &&& 1).toNat = 1 := by
    have : ((e >>> j') &&& 1).toNat < 2 := by
      rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have : ((e >>> j') &&& 1).toNat ≠ 0 := fun h => hb (UInt64.toNat_inj.mp (by simpa using h))
    omega
  rw [shr_succ e j j' hj h64, h1, Nat.pow_succ, Nat.two_mul, Nat.pow_add]
grind_pattern [arena_grind] pow_step1 => A ^ (e >>> j').toNat, A ^ (e >>> j).toNat, (e >>> j') &&& 1

theorem pow_step0 (A : Nat) (e j j' : Word) (hj : j'.toNat + 1 = j.toNat) (h64 : j.toNat < 64)
    (hb : (e >>> j') &&& 1 = 0) :
    A ^ (e >>> j').toNat = A ^ (e >>> j).toNat * A ^ (e >>> j).toNat := by
  rw [shr_succ e j j' hj h64, hb, UInt64.toNat_zero, Nat.add_zero, Nat.two_mul, Nat.pow_add]
grind_pattern [arena_grind] pow_step0 => A ^ (e >>> j').toNat, A ^ (e >>> j).toNat, (e >>> j') &&& 1

theorem shr_of_zero (e j : Word) (h : ¬ 0 < j) : e >>> j = e := by
  have : j = 0 := by grind
  subst this; apply UInt64.toNat_inj.mp; simp
grind_pattern [arena_grind] shr_of_zero => e >>> j, (0 : Word) < j

theorem shr25 (e : Word) (h : e.toNat < 2 ^ 25) : (e >>> 25).toNat = 0 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (by simpa using h)

theorem pow_shr25 (A : Nat) (e : Word) (h : e.toNat < 2 ^ 25) : A ^ (e >>> 25).toNat = 1 := by
  rw [shr25 e h, Nat.pow_zero]
grind_pattern [arena_grind] pow_shr25 => A ^ (e >>> 25).toNat

/-! ## `nat_pow(oa, la, e)` -/

def powLoop : Stmt := lblk (oa, la, e, o, l, j, t) {
  while 0 < j {
    j -= 1;
    t := CTL.u64[0];
    l := call nat_mul(o, l, o, l);
    o := t;
    if (e >> j) & 1 != 0 {
      t := CTL.u64[0];
      l := call nat_mul(o, l, oa, la);
      o := t
    }
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natPow : FunDecl := lfn (oa, la, e) locals (o, l, j, t, pb) {
  o := CTL.u64[0];
  t := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  if len(POOL⟨t⟩) <= pb { abort };
  POOL⟨t⟩[pb] := 1;
  CTL.u64[0] := o + 1;
  l := 1;
  j := 25;
  ⟪powLoop⟫;
  return (o, l)
}

/-- The pool functions with `nat_pow`. -/
def natPowProg : Prog := natMulProg ++ [("nat_pow", natPow)]

/- `3 ^ 5 = 243`; `(2^64 - 1) ^ 2 = [1, 2^64 - 2]`; `a ^ 0 = 1`. -/
#guard (run natPowProg 10000 "nat_pow" [0, 1, 5]
  { words := #[(List.replicate 200 (3 : Word)).toArray, #[1]] }).toOption.map
  (fun (r, m) => (r, m.words[0]![r[0]!.toNat]!)) == some ([28, 1], 243)
#guard (run natPowProg 10000 "nat_pow" [0, 1, 2]
  { words := #[(List.replicate 200 (0xFFFFFFFFFFFFFFFF : Word)).toArray, #[1]] }).toOption.map
  (fun (r, m) => (r[1]!, m.words[0]![r[0]!.toNat]!, m.words[0]![r[0]!.toNat + 1]!)) ==
  some (2, 1, 0xFFFFFFFFFFFFFFFE)
#guard (run natPowProg 10000 "nat_pow" [0, 1, 0]
  { words := #[(List.replicate 200 (7 : Word)).toArray, #[1]] }).toOption.map
  (fun (r, m) => (r, m.words[0]![r[0]!.toNat]!, m.words[1]!)) == some ([26, 1], 1, #[27])

section pow
variable (p : Prog) (hph : p.lookup "mac_hi" = some macHi)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpm : p.lookup "nat_mul" = some natMul)

/-- The invariant of the square-and-multiply loop: the accumulator `(o, l)` is a normalised
slice in use and denotes `a ^ (e >> j)`; `a` lies below the entry top `m₀.top`, and the memory
grew from `m₀`. -/
def PowInv (A : Nat) (m₀ : Mem) (s : St) : Prop :=
  PoolOK s.mem ∧ Grows m₀ s.mem ∧ (s.loc 0).toNat + (s.loc 1).toNat ≤ m₀.top.toNat ∧
  SliceOK s.mem (s.loc 0) (s.loc 1) ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 1).toNat = A ∧
  SliceOK s.mem (s.loc 3) (s.loc 4) ∧
  Norm (vpool s.mem) (s.loc 3).toNat (s.loc 4).toNat ∧ (s.loc 5).toNat ≤ 25 ∧
  pv (vpool s.mem) (s.loc 3).toNat (s.loc 4).toNat = A ^ (s.loc 2 >>> s.loc 5).toNat

def PowPost (A : Nat) (m₀ : Mem) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PoolOK s'.mem ∧ Grows m₀ s'.mem ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
  SliceOK s'.mem (s'.loc 3) (s'.loc 4) ∧
  Norm (vpool s'.mem) (s'.loc 3).toNat (s'.loc 4).toNat ∧
  pv (vpool s'.mem) (s'.loc 3).toNat (s'.loc 4).toNat = A ^ (s₀.loc 2).toNat

include hph hpt hpm in
theorem powLoop_spec (A : Nat) (m₀ : Mem) (n : Nat) (s₀ : St) (h : PowInv A m₀ s₀) :
    ⦃fun s => s = s₀⦄ exec p n powLoop ⦃fun r s' => PowPost A m₀ s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [PowInv, PowPost] at h ⊢
    rw [exec, step_while (w := powLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        natMul_spec p hph hpt hpm n] <;>
      finish [PowInv, PowPost]

include hph hpt hpm in
theorem powLoop_step_spec (A : Nat) (m₀ : Mem) (n : Nat) (s₀ : St) (h : PowInv A m₀ s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) powLoop ⦃fun r s' => PowPost A m₀ s₀ r s'; ⊤⦄ :=
  Triple.step_exec (powLoop_spec p hph hpt hpm A m₀ (n + 1) s₀ h)

end pow

section powFn
variable (p : Prog) (hph : p.lookup "mac_hi" = some macHi)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpm : p.lookup "nat_mul" = some natMul)
  (hpn : p.lookup "nat_pow" = some natPow)

include hph hpt hpm hpn in
/-- `nat_pow` returns a normalised slice `(o, l)` in use that denotes `a ^ e`; the memory grew. -/
theorem natPow_spec (n : Nat) (s₀ : St) (oa la e : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (he : e.toNat < 2 ^ 25) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_pow" [oa, la, e]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat ^ e.toNat; ⊤⦄ := by
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hin := hok.2.2.2.2.2
  rw [invoke_eq _ hpn]
  simp only [callFn, natPow]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        powLoop_step_spec p hph hpt hpm (pv (vpool s₀.mem) oa.toNat la.toNat) s₀.mem n] <;>
      -- depth, not search: the initial state is several `setLoc`s and two stores deep
      finish (gen := 20) (splits := 20) [PowInv, PowPost]

end powFn

end L.Arena
