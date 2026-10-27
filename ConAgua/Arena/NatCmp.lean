module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Comparison on the limb pool: `nat_cmp`

`nat_cmp(oa, la, ob, lb)` (con-ron's `cmp`/`cmp_from`, `ron/nat.rs:174-200`): normalised operands,
so a length difference decides; otherwise the limbs from the top down. It returns a code word,
`0` (`Lt`), `1` (`Eq`) or `2` (`Gt`); `beq`/`ble`/`blt` are tests of the code.

**The model is not recursive.** The spec is `r = cmpW A B` with `cmpW` a plain function of two
`Nat`s (`if a < b then 0 else if a = b then 1 else 2`), and the loop invariant says that the
limbs above `k` agree, as one linear equation over the prefix values:
`pv a la + pv b k = pv b la + pv a k`. A recursive model of `cmp_from` with a `grind` pattern
diverged (DESIGN.md, lane `nat`): its conclusion makes a fresh `cmpFrom … (k - 1)` term, which
fires the pattern again. Here every lemma's conclusion only relates terms that are already
there, so instantiation stops.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The model -/

/-- The comparison code of con-ron's `Cmp`: `0` = `Lt`, `1` = `Eq`, `2` = `Gt`. -/
def cmpW (a b : Nat) : Word := if a < b then 0 else if a = b then 1 else 2

theorem cmpW_lt (a b : Nat) (h : a < b) : cmpW a b = 0 := by simp [cmpW, h]
theorem cmpW_eq (a b : Nat) (h : a = b) : cmpW a b = 1 := by simp [cmpW, h]
theorem cmpW_gt (a b : Nat) (h : b < a) : cmpW a b = 2 := by
  simp [cmpW, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
grind_pattern [natcmp_grind] cmpW_lt => cmpW a b
grind_pattern [natcmp_grind] cmpW_eq => cmpW a b
grind_pattern [natcmp_grind] cmpW_gt => cmpW a b

/-! ## Prefix values below a weight -/

/-- A prefix of `k` limbs is below `wt k`. (`LitRefine.lean` has the same fact as `pv_lt`; that
file is not a `module`, so it cannot be imported here.) -/
theorem pv_lt_wt (p : Array Word) (o k : Nat) : pv p o k < wt k := by
  induction k with
  | zero => simp [pv, wt]
  | succ k ih =>
    simp only [pv]
    have hw : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k (k + 1) rfl
    have hl := (p[o + k]?.getD 0).toNat_lt
    have : ((p[o + k]?.getD 0).toNat + 1) * wt k ≤ 2 ^ 64 * wt k :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hw]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ 64)] at this; omega
grind_pattern [natcmp_grind] pv_lt_wt => pv p o k

/-- The top limb decides: if limb `k - 1` of `a` is below limb `k - 1` of `b`, then the first `k`
limbs of `a` denote less than those of `b`. The pattern starts from the comparison the program
makes; its conclusion relates two terms already present, so it does not feed itself. -/
theorem pv_succ_lt (p : Array Word) (oa ob k ia ib : Nat) (ha : ia < p.size) (hb : ib < p.size)
    (hia : ia + 1 = oa + k) (hib : ib + 1 = ob + k) (hk : 0 < k) (hx : p[ia] < p[ib]) :
    pv p oa k < pv p ob k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 := pv_succ p oa j (j + 1) ia rfl (by omega) ha
  have h2 := pv_succ p ob j (j + 1) ib rfl (by omega) hb
  have h3 := pv_lt_wt p oa j
  have hx' : (p[ia]).toNat + 1 ≤ (p[ib]).toNat := hx
  have : ((p[ia]).toNat + 1) * wt j ≤ (p[ib]).toNat * wt j := Nat.mul_le_mul_right _ hx'
  rw [Nat.add_mul, Nat.one_mul] at this
  omega
grind_pattern [natcmp_grind] pv_succ_lt => p[ia] < p[ib], pv p oa k, pv p ob k

/-- A normalised slice with more limbs denotes more (the length test of `cmp`). -/
theorem pv_len_lt (p q : Array Word) (oa ob la lb : Nat) (hn : Norm q ob lb) (hl : la < lb) :
    pv p oa la < pv q ob lb := by
  have h1 := pv_lt_wt p oa la
  have h2 : wt (lb - 1) ≤ pv q ob lb := by
    obtain ⟨j, rfl⟩ : ∃ j, lb = j + 1 := ⟨lb - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pv]
    have : (q[ob + j]?.getD 0) ≠ 0 := hn (by omega)
    have : 1 ≤ (q[ob + j]?.getD 0).toNat := by
      rcases Nat.eq_zero_or_pos (q[ob + j]?.getD 0).toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)) this
      · exact h
    have := Nat.mul_le_mul_right (wt j) this
    omega
  have h3 : wt la ≤ wt (lb - 1) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
  omega

/-! ## `nat_cmp(oa, la, ob, lb)` -/

def cmpLoop : Stmt := lblk (oa, la, ob, lb, k, x, y) {
  while 0 < k {
    x := POOL⦃oa + k - 1⦄;
    y := POOL⦃ob + k - 1⦄;
    if x < y { return 0 };
    if y < x { return 2 };
    k -= 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natCmp : FunDecl := lfn (oa, la, ob, lb) locals (k, x, y) {
  if la < lb { return 0 };
  if lb < la { return 2 };
  k := la;
  ⟪cmpLoop⟫;
  return 1
}

/-- The comparison functions, as one program. -/
def natCmpProg : Prog := natProg ++ [("nat_cmp", natCmp)]

/- `[1, 2]` vs `[3, 1]`: the top limb decides (`Gt`); `[5]` vs `[5]` is `Eq`; `[]` vs `[1]`
is `Lt` by length. -/
#guard (run natCmpProg 100 "nat_cmp" [0, 2, 2, 2] { words := #[#[1, 2, 3, 1], #[4]] }).toOption.map
  (·.1) == some [2]
#guard (run natCmpProg 100 "nat_cmp" [0, 1, 1, 1] { words := #[#[5, 5], #[2]] }).toOption.map
  (·.1) == some [1]
#guard (run natCmpProg 100 "nat_cmp" [0, 0, 0, 1] { words := #[#[1], #[1]] }).toOption.map
  (·.1) == some [0]

/-- The invariant of the comparison loop over the pool `P` (unchanged): both slices have `la`
limbs and are in bounds, and their limbs at `k` and above agree. -/
def CmpInv (P : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P.size = 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 1).toNat ≤ C ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧
  pv P (s.loc 0).toNat (s.loc 1).toNat + pv P (s.loc 2).toNat (s.loc 4).toNat =
    pv P (s.loc 2).toNat (s.loc 1).toNat + pv P (s.loc 0).toNat (s.loc 4).toNat

section cmp
variable (p : Prog)

set_option maxHeartbeats 1000000 in
theorem cmpLoop_spec (n : Nat) (s₀ : St) (h : CmpInv (vpool s₀.mem) (pcap s₀.mem) s₀) :
    ⦃fun s => s = s₀⦄
    exec p n cmpLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r.retOr [1]).headD 0 = cmpW (pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat)
        (pv (vpool s₀.mem) (s₀.loc 2).toNat (s₀.loc 1).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [CmpInv] at h
    rw [exec, step_while (w := cmpLoop) rfl]
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      -- the `pv_succ`/`pv_succ_lt` instances' index side conditions are case splits
      finish (splits := 20) [CmpInv]

theorem cmpLoop_step_spec (n : Nat) (s₀ : St) (h : CmpInv (vpool s₀.mem) (pcap s₀.mem) s₀) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) cmpLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r.retOr [1]).headD 0 = cmpW (pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat)
        (pv (vpool s₀.mem) (s₀.loc 2).toNat (s₀.loc 1).toNat); ⊤⦄ :=
  Triple.step_exec (cmpLoop_spec p (n + 1) s₀ h)

variable (hpc : p.lookup "nat_cmp" = some natCmp)

include hpc in
/-- `nat_cmp` returns the comparison code of the two normalised slices; it changes nothing. -/
theorem natCmp_spec (n : Nat) (s₀ : St) (oa la ob lb : Word)
    (hs : pcap s₀.mem < 2 ^ 64)
    (ha : oa.toNat + la.toNat ≤ pcap s₀.mem)
    (hb : ob.toNat + lb.toNat ≤ pcap s₀.mem)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_cmp" [oa, la, ob, lb]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = cmpW (pv (vpool s₀.mem) oa.toNat la.toNat)
      (pv (vpool s₀.mem) ob.toNat lb.toNat); ⊤⦄ := by
  rw [invoke_eq _ hpc]
  simp only [callFn, natCmp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, cmpLoop_step_spec p n] <;>
      finish [CmpInv, pv_len_lt]

end cmp

end L.Arena
