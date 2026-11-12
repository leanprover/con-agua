module

public import ConAgua.Arena.NatPow
public import ConAgua.Arena.NatShl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.NatPow

@[expose] public section

/-!
# `pow_nat(oa, la, e)`: `a ^ e`, a one-limb power of two by a shift

`pow_nat` (`NatPow.lean`) is a hand spec with a `pv` post, as `nat_pow`: a one-limb base `2^k`
(`k < 64`, found by `powTwoLoop`) is `1 <<< k·e` (`nat_shl` of two pushed one-limb slices),
any other base `nat_pow`'s square-and-multiply.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- What the power-of-two loop leaves: the first four locals and the memory as they were, and
`1 <<< k = x` where `k < 64`. -/
def PtPost (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.mem = s₀.mem ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
  s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ (s'.loc 4 < 64 → (1 : Word) <<< s'.loc 4 = s'.loc 3)

theorem powTwoLoop_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p n powTwoLoop ⦃fun r s' => PtPost s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := powTwoLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, reduceIte,
      decide_eq_true_eq, PtPost] at *)
    all_goals grind [PtPost]

theorem powTwoLoop_step_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ step p (exec p n) powTwoLoop ⦃fun r s' => PtPost s₀ r s'; ⊤⦄ :=
  Triple.step_exec (powTwoLoop_spec p (n + 1) s₀)

/-- A one-limb `2^k`, `k < 64`, to the `e`-th power is `2^(k·e)` (the word `k * e` does not wrap). -/
theorem pow_two_shift (x k e : Word) (hx : (1 : Word) <<< k = x) (hk : k < 64) (he : e.toNat < 2 ^ 32) :
    x.toNat ^ e.toNat = 2 ^ (k * e).toNat := by
  have hk' : k.toNat < 64 := hk
  have hxv : x.toNat = 2 ^ k.toNat := by
    rw [← hx, UInt64.toNat_shiftLeft, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega : k.toNat < 64),
      Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk')]
  have hke : (k * e).toNat = k.toNat * e.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt]
    calc k.toNat * e.toNat < 64 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt hk' he
      _ < 2 ^ 64 := by decide
  rw [hxv, hke, ← Nat.pow_mul]

/-- Pushing one limb at the top is growing the pool. -/
theorem Grows.push1 (m : Mem) (t v : Word) (ht : t = m.top) (h : PoolOK m)
    (hs : (t &&& 1099511627775).toNat < (m.arr64 (tierA POOL (t >>> 40))).size) :
    Grows m ((m.set64 (tierA POOL (t >>> 40)) (t &&& 1099511627775) v).set64 CTL 0 (t + 1)) := by
  subst ht
  have h41 := h.top41
  have hsz := h.small.tier (m.top >>> 40)
  apply Grows.write m _ 1 h (PFrame.set64 _ _ _ (PFrame.refl m))
  · rw [vpool_stidx0 m m.top v h41 hs (by omega)]
    exact Agree.set _ _ _ _ _ (Agree.refl _ _) (Nat.le_refl _)
  · simp only [show (1 : Word).toNat = 1 from rfl]; omega
grind_pattern [arena_grind] Grows.push1 =>
  (m.set64 (tierA POOL (t >>> 40)) (t &&& 1099511627775) v).set64 CTL 0 (t + 1)

/-- **`limb_push(v)`** appends the limb `v` at the top: the slice `(top, 1)` denotes `v`. -/
theorem limbPush_spec (p : Prog) (hp : p.lookup "limb_push" = some limbPushL) (n : Nat) (s₀ : St)
    (v : Word) (hok : PoolOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "limb_push" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧ r.headD 0 = s₀.mem.top ∧
      s'.mem.top = s₀.mem.top + 1 ∧ SliceOK s'.mem (r.headD 0) 1 ∧
      pv (vpool s'.mem) (r.headD 0).toNat 1 = v.toNat ∧
      (v ≠ 0 → Norm (vpool s'.mem) (r.headD 0).toNat 1); ⊤⦄ := by
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hin := hok.inTier
  rw [invoke_eq _ hp]
  simp only [callFn, limbPushL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (first | grind (gen := 20) [lang_grind, arena_grind, natop_grind, Grows.push1, PoolOK.grows] | (trace_state; sorry))

section powNat
variable (p : Prog) (hph : p.lookup "mac_hi" = some macHi)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpm : p.lookup "nat_mul" = some natMul)
  (hpn : p.lookup "nat_pow" = some natPow) (hps : p.lookup "nat_shl" = some natShl)
  (hpp : p.lookup "pow_nat" = some powNatL) (hlp : p.lookup "limb_push" = some limbPushL)

include hph hpt hpm hpn hps hpp hlp in
/-- **`pow_nat` returns a normalised slice `(o, l)` in use that denotes `a ^ e`** (`e < 2^32`); the
memory grew. -/
theorem powNat_spec (n : Nat) (s₀ : St) (oa la e : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pow_nat" [oa, la, e]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat ^ e.toNat; ⊤⦄ := by
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hin := hok.inTier
  rw [invoke_eq _ hpp]
  simp only [callFn, powNatL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        powTwoLoop_step_spec p n, natPow_spec p hph hpt hpm hpn n, natShl_spec p hpt hps n,
        limbPush_spec p hlp n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq, PtPost] at *)
    all_goals (first | grind (gen := 20) (splits := 20) [lang_grind, arena_grind, natop_grind, pow_two_shift] | (trace_state; sorry))

end powNat

end L.Arena
