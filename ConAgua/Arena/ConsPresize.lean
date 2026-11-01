module

public import ConAgua.Arena.ConsLibRel
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# A cons table sized up front: `X_presize(n)` (lane presize)

`consPresizeG C` (part of the cons library, `ConsLib.lean`; con-ron's `HashMap2::with_capacity`) sets tier 0's count word of table `C` to `n - SN0` when the
table is the fresh one and `n` is a layout (`psOK`); `psMem C n m` is its memory. On a memory
whose `CTL` and slot arrays are zero (the loaded memory at the start of `check`), the result is
an empty table of `n` slots: `consR_presized` (from `consR_initN`). The table's internals stay
behind `ConsR`: a caller sees only `psMem` and the relation.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `X_presize(n)`: the persistent table at `n` slots before the first intern

con-ron's `HashMap2::with_capacity` (`ron/hashmap2.rs`): an empty map sized up front, so that
the first inserts do not grow it. The caller picks `n` (the checker sizes the parse's large
tables from the input length, `Checker/Presize.lean`). The template writes only the count word:
if tier 0's table is still the fresh one (count word `0`), `n` is a multiple of `8`, at least
`SN0` and leaves room for `n` slots at offset `0` (`2 n + 2` words), the count word becomes
`n - SN0`; otherwise nothing changes. On an all-zero slot array the result is an empty table of
`n` slots (`consR_initN`): its slots are the array's zeros, so nothing is
zeroed and no page is touched up front. -/

-- con-ron: none — `HashMap2::with_capacity` (`ron/hashmap2.rs`); con-ron's tables start empty (D42)
def consPresizeG (C : ConsSch) : FunDecl := lfn (n) {
  if n & 7 == 0 && 8 <= n && n <= 1152921504606846976 && n * 2 + 2 <= len(C.sa⟨0⟩) &&
      C.sa⟨0⟩[0] == 0 {
    C.sa⟨0⟩[0] := n - ⟪SN0⟫
  };
  return 0
}

/-- The template's test: `n` a multiple of `8`, at least `SN0`, at most `2^60`, room for `n`
slots at offset `0`, and tier 0's count word still `0`. -/
def psOK (C : ConsSch) (n : Word) (m : Mem) : Bool :=
  n &&& 7 == 0 && 8 ≤ n && n ≤ 1152921504606846976 &&
    n * 2 + 2 ≤ UInt64.ofNat (m.arr64 (tierA C.sa 0)).size && rdW (m.arr64 (tierA C.sa 0)) 0 == 0

/-- **The memory after `X_presize(n)`**. -/
def psMem (C : ConsSch) (n : Word) (m : Mem) : Mem :=
  if psOK C n m then m.set64 (tierA C.sa 0) 0 (n - SN0) else m

theorem psMem_arr_ne (C : ConsSch) (n : Word) (m : Mem) {b : TieredArray} (hb : b ≠ tierA C.sa 0) :
    (psMem C n m).arr64 b = m.arr64 b := by
  unfold psMem; split
  · exact Mem.arr64_set64_ne _ _ _ _ _ hb
  · rfl

theorem psMem_size (C : ConsSch) (n : Word) (m : Mem) (b : TieredArray) :
    ((psMem C n m).arr64 b).size = (m.arr64 b).size := by
  unfold psMem; split
  · by_cases hb : b = tierA C.sa 0
    · subst hb; simp [Mem.arr64, Mem.set64]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hb]
  · rfl

theorem psMem_rd_ne0 (C : ConsSch) (n : Word) (m : Mem) (b : TieredArray) {x : Word} (hx : x ≠ 0) :
    rdW ((psMem C n m).arr64 b) x = rdW (m.arr64 b) x := by
  unfold psMem; split
  · by_cases hb : b = tierA C.sa 0
    · subst hb
      have hx' : x.toNat ≠ 0 := fun h => hx (UInt64.toNat_inj.mp (by simpa using h))
      simp only [rdW, Mem.arr64, Mem.set64, ↓reduceIte, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne (Ne.symm hx'), UInt64.toNat_zero]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hb]
  · rfl

@[simp] theorem psMem_bytes (C : ConsSch) (n : Word) (m : Mem) : (psMem C n m).bytes = m.bytes := by
  unfold psMem; split <;> rfl

@[simp] theorem psMem_glob (C : ConsSch) (n : Word) (m : Mem) : (psMem C n m).glob = m.glob := by
  unfold psMem; split <;> rfl

theorem psMem_arr8 (C : ConsSch) (n : Word) (m : Mem) (a : ArrId) : (psMem C n m).arr8 a = m.arr8 a := by
  simp [Mem.arr8]

theorem psMem_len8 (C : ConsSch) (n : Word) (m : Mem) (a : ArrId) : (psMem C n m).len8 a = m.len8 a := by
  simp [Mem.len8, psMem_arr8]

/-- The global write commutes with the presize. -/
theorem psMem_setG (C : ConsSch) (n : Word) (m : Mem) (g : GVar) (w : Word) :
    psMem C n (m.setG g w) = (psMem C n m).setG g w := by
  have e : psOK C n (m.setG g w) = psOK C n m := rfl
  unfold psMem; rw [e]; split <;> rfl

/-- **The layout after the presize** of a table whose count word was `0` (the fresh `SN0` slots
in an array of at least `consMinWords` words): `n` slots if the test passed, else `SN0`. -/
theorem psMem_lay (C : ConsSch) (n : Word) (m : Mem) (hz : rdW (m.arr64 (tierA C.sa 0)) 0 = 0)
    (hs : consMinWords ≤ (m.arr64 (tierA C.sa 0)).size) (hs' : (m.arr64 (tierA C.sa 0)).size < 2 ^ 61) :
    8 ≤ (knW C.sa (psMem C n m) 0).toNat ∧ (knW C.sa (psMem C n m) 0).toNat % 8 = 0 ∧
      2 + 2 * (knW C.sa (psMem C n m) 0).toNat ≤ ((psMem C n m).arr64 (tierA C.sa 0)).size := by
  rw [psMem_size]
  simp only [consMinWords] at hs
  unfold knW psMem
  split
  · rename_i h
    simp only [psOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h7, h8⟩, h60⟩, hr⟩, -⟩ := h
    have hlt : 0 < (m.arr64 (tierA C.sa 0)).size := by omega
    have e : rdW ((m.set64 (tierA C.sa 0) 0 (n - SN0)).arr64 (tierA C.sa 0)) 0 = n - SN0 := by
      rw [rdW_set64]
      split
      · rfl
      · rename_i hc; exact absurd ⟨rfl, rfl, by simpa using hlt⟩ hc
    rw [e]
    have h8' : (8 : Nat) ≤ n.toNat := h8
    have h60' : n.toNat ≤ 1152921504606846976 := h60
    have e2 : (n - SN0 + SN0) = n := by simp
    rw [e2]
    have h7' : n.toNat % 8 = 0 := by
      have := congrArg UInt64.toNat h7
      simp only [UInt64.toNat_and, UInt64.reduceToNat, UInt64.toNat_zero] at this
      have e3 : n.toNat &&& 7 = n.toNat % 8 := Nat.and_two_pow_sub_one_eq_mod _ 3
      omega
    have hr' := UInt64.le_iff_toNat_le.mp hr
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega), UInt64.toNat_add,
      UInt64.toNat_mul] at hr'
    simp only [UInt64.reduceToNat] at hr'
    refine ⟨h8', h7', ?_⟩
    omega
  · rw [hz]
    refine ⟨by decide, by decide, ?_⟩
    show 2 + 2 * 8 ≤ _
    omega

/-- `X_presize(0)` changes nothing. -/
theorem psMem_zero (C : ConsSch) (m : Mem) : psMem C 0 m = m := by
  unfold psMem psOK; simp

/-! ## The relation after the presize -/

section rel
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {C : ConsSch}
  {R : Mem → Word → Word → α → Prop}

/-- **The relation holds on a fresh table of `n` slots** (`consPresizeG`, con-ron's
`HashMap2::with_capacity`): `CTL` and the slot arrays all zero but tier 0's count word, whose
slot count `knW` is a layout of `n` slots at offset `0` (`n = SN0`: the fresh table, count word
`0`). The record arrays are not read: both tables are empty. -/
theorem consR_initN {m : Mem} (hzc : ∀ x, rdW (m.arr64 CTL) x = 0)
    (hz1 : ∀ x, rdW (m.arr64 (tierA C.sa 1)) x = 0)
    (hz0 : ∀ x, x ≠ 0 → rdW (m.arr64 (tierA C.sa 0)) x = 0)
    (hn : 8 ≤ (knW C.sa m 0).toNat ∧ (knW C.sa m 0).toNat % 8 = 0 ∧
      2 + 2 * (knW C.sa m 0).toNat ≤ (m.arr64 (tierA C.sa 0)).size)
    (hctl : C.ca.toNat + 2 ≤ (m.arr64 CTL).size)
    (hsa : ∀ t, consMinWords ≤ (m.arr64 (tierA C.sa t)).size ∧ (m.arr64 (tierA C.sa t)).size < 2 ^ 61) :
    ConsR C R m false (Tbl.empty : Tbl α (Idx k) δ) Tbl.empty := by
  have hT : ∀ t, (∀ j : Word, j < nSl C.sch m t → slotW C.sch m t j = 0) →
      TierR C.sch R C.hsM C.KP m t (Tbl.empty : Tbl α (Idx k) δ) := by
    intro t hs
    refine ⟨by simp [cntW, hzc, Tbl.empty], by simp [Tbl.empty], by simp [Tbl.empty],
      fun i a h => by simp [Tbl.empty] at h, fun i a h => by simp [Tbl.empty] at h,
      fun a x h => by simp [Tbl.empty] at h, fun j hj => by simp [hs j hj],
      fun j hj h => absurd (hs j hj) h, fun i hi => by simp [Tbl.empty] at hi⟩
  have hz1' : ∀ x, rdW (m.arr64 (tier1 C.sch.sa)) x = 0 := hz1
  have hz0' : ∀ x, x ≠ 0 → rdW (m.arr64 (C.sch.sa : TieredArray)) x = 0 := hz0
  have ho0 : koW C.sch.sa m 0 = 0 := hz0 1 (by decide)
  have ho1 : koW C.sch.sa m 1 = 0 := hz1 1
  have hn1 : (knW C.sch.sa m 1).toNat = 8 := by
    simp only [knW]; rw [show rdW (m.arr64 (tierA C.sch.sa 1)) 0 = 0 from hz1 0]; decide
  obtain ⟨hn8, hnm, hnr⟩ := hn
  have hn8' : 8 ≤ (knW C.sch.sa m 0).toNat := hn8
  have hnm' : (knW C.sch.sa m 0).toNat % 8 = 0 := hnm
  have hnr' : 2 + 2 * (knW C.sch.sa m 0).toNat ≤ (m.arr64 (tierA C.sch.sa 0)).size := hnr
  have h0 : 18 ≤ (m.arr64 (tierA C.sch.sa 0)).size ∧ (m.arr64 (tierA C.sch.sa 0)).size < 2 ^ 61 :=
    hsa 0
  have h1 : 18 ≤ (m.arr64 (tierA C.sch.sa 1)).size ∧ (m.arr64 (tierA C.sch.sa 1)).size < 2 ^ 61 :=
    hsa 1
  have hs0 : ∀ j : Word, j < nSl C.sch m 0 → slotW C.sch m 0 j = 0 := fun j hj => by
    have hj' : j.toNat < (knW C.sa m 0).toNat := hj
    have hne : krW C.sch.sa m 0 + j * 2 ≠ 0 := by
      intro h
      have e := congrArg UInt64.toNat h
      simp only [krW, ho0, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_zero,
        UInt64.reduceToNat] at e
      have : j.toNat < (knW C.sch.sa m 0).toNat := hj'
      omega
    simp only [slotW, slotV, slotRd]
    rw [show rdW (m.arr64 (tierA C.sch.sa 0)) (krW C.sch.sa m 0 + j * 2) = 0 from hz0 _ hne]; simp
  have hs1 : ∀ j : Word, j < nSl C.sch m 1 → slotW C.sch m 1 j = 0 := fun j _ => by
    simp only [slotW, slotV, slotRd]
    rw [show rdW (m.arr64 (tierA C.sch.sa 1)) (krW C.sch.sa m 1 + j * 2) = 0 from hz1 _]; simp
  have hG : GrowR C.sch m := by
    refine ⟨⟨h0.2, ?_, ?_, ?_, fun _ => ho0⟩, ⟨h1.2, ?_, ?_, ?_, fun _ => ho1⟩⟩
    all_goals (try rw [hn1]); all_goals (try rw [ho0]); all_goals (try rw [ho1])
    all_goals (try simp only [UInt64.toNat_zero])
    all_goals omega
  exact consR_iff.mpr ⟨⟨hctl, by simp [hzc]⟩, by simp [hzc], hT 0 hs0, hT 1 hs1, hG⟩


/-- **A presized zero table is an empty table**: in a memory `M` whose `CTL` and tier-1 slot
array are zero and whose tier-0 slot array is that of `X_presize(n)` from an all-zero one, the
table relates to two empty tables. (`n = 0`, `m = M`: the fresh table of `SN0` slots,
`psMem_zero`.) -/
theorem consR_initM {M m : Mem} (n : Word)
    (hsa0 : M.arr64 (tierA C.sa 0) = (psMem C n m).arr64 (tierA C.sa 0))
    (hzc : ∀ x, rdW (M.arr64 CTL) x = 0) (hz1 : ∀ x, rdW (M.arr64 (tierA C.sa 1)) x = 0)
    (hz0 : ∀ x, rdW (m.arr64 (tierA C.sa 0)) x = 0)
    (hctl : C.ca.toNat + 2 ≤ (M.arr64 CTL).size)
    (hsa : ∀ t, consMinWords ≤ (M.arr64 (tierA C.sa t)).size ∧ (M.arr64 (tierA C.sa t)).size < 2 ^ 61) :
    ConsR C R M false (Tbl.empty : Tbl α (Idx k) δ) Tbl.empty := by
  have hs0 : (m.arr64 (tierA C.sa 0)).size = (M.arr64 (tierA C.sa 0)).size := by
    rw [hsa0, psMem_size]
  have hk : knW C.sa M 0 = knW C.sa (psMem C n m) 0 := by simp only [knW, hsa0]
  have hl := psMem_lay C n m (hz0 0) (hs0 ▸ (hsa 0).1) (hs0 ▸ (hsa 0).2)
  rw [← hk, ← hsa0] at hl
  refine consR_initN hzc hz1 (fun x hx => ?_) hl hctl hsa
  rw [hsa0, psMem_rd_ne0 C n m _ hx]; exact hz0 x

end rel

/-! ## The template's spec -/

/-- **`X_presize(n)`**: a returning call keeps the caller's locals and leaves `psMem C n`. -/
theorem consPresize_spec (p : Prog) (C : ConsSch) (f : FnName) (hp : p.lookup f = some (consPresizeG C))
    (k : Nat) (s₀ : St) (n : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) f [n]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = psMem C n s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, consPresizeG]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64]
    all_goals (try simp only [Cmp.eval, BinOp.eval, LocEq] at *)
    all_goals (try simp only [Locals.init_cons_zero, UInt64.toNat_zero, Mem.len64, beq_iff_eq,
      Bool.not_eq_true, Bool.false_eq_true] at *)
    all_goals (unfold psMem psOK rdW; grind)

end L.Arena
