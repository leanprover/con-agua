module

public import ConAgua.Front.NatDecBig
public import ConAgua.Front.NatDecLink
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.Blocks
import all ConAgua.Front.NatDec

@[expose] public section

/-!
# What `nat_dec` does on a long literal

`nat_dec_split` and `nat_dec_big` (`NatDec.lean`) through their word models over `callW`
(`NatDecBig.lean`), in the program `natDecProg`; `nat_mul` and `nat_add` enter only through their
specs (`natMul_spec`, `natAdd_spec`), so a change of their code leaves these proofs alone.
-/

open Std.WP
open scoped Lean.Order

namespace L.Front

open L.Arena

/-! ## Pool facts -/

/-- A pool word below the old top reads the same after growth. -/
theorem prd_grows {m m' : Mem} (hok : PoolOK m) (hg : Grows m m') {x : Word}
    (hx : x.toNat < m.top.toNat) : prd m' x = prd m x := by
  have h41 := hok.top41
  rw [← vpool_getD m' x (by omega), ← vpool_getD m x (by omega), hg.agree _ hx]

/-- **A pool rewritten above the old top, then the top set back**: writes `m₁ ↝ m₂` of the
pool's tiers only (`PFrame`) that keep the pool below `m`'s top, then `CTL[0] := v` for a `v`
between `m`'s top and `m₁`'s: the pool grew from `m`. -/
theorem Grows.reset {m m₁ m₂ : Mem} (hok : PoolOK m) (hg : Grows m m₁) (hf : PFrame m₁ m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (v : Word) (hv1 : m.top.toNat ≤ v.toNat)
    (hv2 : v.toNat ≤ m₁.top.toNat) : Grows m (m₂.set64 CTL 0 v) := by
  have hsm := hok.small
  have h41 := hok.top41
  have hctl1 : (m₁.arr64 CTL).size = (m.arr64 CTL).size := by
    rw [hg.frame.ctl, Mem.size_arr64_set64]
  have hctl2 : 0 < (m₂.arr64 CTL).size := by rw [hf.ctl, hctl1]; exact hok.ctl
  have htop : (m₂.set64 CTL 0 v).top = v := Mem.top_set64 _ _ hctl2
  have ht1 := hg.tier
  have hle1 := hg.le
  have hin1 := hg.inn
  have hcap1 := hg.cap
  have hp1 : pcap m₁ = 2 ^ 41 - 1 := by rw [hg.pcapEq]; exact pcap_of_small m hsm
  -- `m₁`'s top is in `m`'s tier
  have hT : m₁.top >>> 40 = m.top >>> 40 := tag_tier_eq (by omega)
  have hsz : (m₁.arr64 (tierA POOL (m.top >>> 40))).size = (m.arr64 (tierA POOL (m.top >>> 40))).size := by
    have := PFrame.tsize (m.top >>> 40) hg.frame
    rw [this]
    rcases tierA_pool (m.top >>> 40) with e | e <;> rw [e]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  rw [hT, tag_idx_toNat, hsz] at hin1
  apply Grows.intro m _ hok
  · rw [htop]
    refine ⟨?_, fun b h0 h1 => ?_, ?_, ?_, ?_⟩
    · rw [Mem.bytes_set64, hf.bytes, hg.frame.bytes, Mem.bytes_set64, Mem.bytes_set64]
    · by_cases hbc : b = CTL
      · subst hbc
        rw [Mem.arr64_set64_same, Mem.arr64_set64_same, hf.arr _ h0 h1, hg.frame.ctl, Mem.arr64_set64_same]
        simp
      · rw [Mem.arr64_set64_ne _ _ _ _ _ hbc, Mem.arr64_set64_ne _ _ _ _ _ hbc, hf.arr b h0 h1,
          hg.frame.arr b h0 h1, Mem.arr64_set64_ne _ _ _ _ _ hbc]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), hf.size0,
        hg.frame.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), hf.size1,
        hg.frame.size1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · funext g
      rw [Mem.set64_glob, Mem.set64_glob, hf.glob, hg.frame.glob, Mem.set64_glob]
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]; exact ha
  · rw [htop]; exact hv1
  · rw [htop, tag_idx_toNat]
    omega

/-! ## The block copy down -/

theorem PFrame.copy64 {m : Mem} (t : Word) :
    ∀ (n : Nat) (m' : Mem) (di si : Word), PFrame m m' →
      PFrame m (m'.copy64 (tierA POOL t) di (tierA POOL t) si n) := by
  intro n
  induction n with
  | zero => intro m' _ _ h'; exact h'
  | succ n ih =>
    intro m' di si h'
    rw [Mem.copy64_succ]
    exact ih _ _ _ (PFrame.set64 t di _ h')

/-- **A copy down inside one tier** (`di ≤ si`, ascending): the words `[di, di + n)` of the tier
read the old words `[si, si + n)`, every other word of the virtual pool is unchanged. -/
theorem vpool_copy64 (t : Word) (ht : t.toNat ≤ 1) :
    ∀ (n : Nat) (m : Mem) (di si : Word), (m.arr64 (tierA POOL t)).size ≤ 2 ^ 40 →
      di.toNat ≤ si.toNat → si.toNat + n ≤ (m.arr64 (tierA POOL t)).size → ∀ j : Nat,
      (vpool (m.copy64 (tierA POOL t) di (tierA POOL t) si n))[j]? =
        if t.toNat * 2 ^ 40 + di.toNat ≤ j ∧ j < t.toNat * 2 ^ 40 + di.toNat + n then
          (vpool m)[j + (si.toNat - di.toNat)]?
        else (vpool m)[j]? := by
  intro n
  induction n with
  | zero =>
    intro m di si _ _ _ j
    rw [Mem.copy64_zero]
    split
    · omega
    · rfl
  | succ n ih =>
    intro m di si hs hds hb j
    rw [Mem.copy64_succ]
    have hsi : si.toNat < (m.arr64 (tierA POOL t)).size := by omega
    have hdi : di.toNat < (m.arr64 (tierA POOL t)).size := by omega
    have hv : (m.arr64 (tierA POOL t))[si.toNat]! = (vpool m)[t.toNat * 2 ^ 40 + si.toNat]?.getD 0 := by
      rw [getElem!_pos (m.arr64 (tierA POOL t)) si.toNat hsi, vpool_ldt m t si ht hsi hs (by rw [vpool_size]; omega)]
      rw [Array.getElem?_eq_getElem (xs := vpool m) (by rw [vpool_size]; omega)]; rfl
    have e := vpool_set64t m t di ((m.arr64 (tierA POOL t))[si.toNat]!) ht hdi hs
    have hs' : ((m.set64 (tierA POOL t) di ((m.arr64 (tierA POOL t))[si.toNat]!)).arr64 (tierA POOL t)).size =
        (m.arr64 (tierA POOL t)).size := Mem.size_arr64_set64 _ _ _ _
    have hd1 : (di + 1).toNat = di.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    have hs1 : (si + 1).toNat = si.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    have hvs : t.toNat * 2 ^ 40 + di.toNat < (vpool m).size := by rw [vpool_size]; omega
    have hss : t.toNat * 2 ^ 40 + si.toNat < (vpool m).size := by rw [vpool_size]; omega
    rw [ih _ (di + 1) (si + 1) (by rw [hs']; exact hs) (by omega) (by rw [hs']; omega) j, e, hd1, hs1, hv,
      Array.getElem?_eq_getElem hss]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Option.getD_some]
    by_cases hj : t.toNat * 2 ^ 40 + di.toNat = j
    · subst hj
      have c1 : ¬ (t.toNat * 2 ^ 40 + (di.toNat + 1) ≤ t.toNat * 2 ^ 40 + di.toNat ∧
          t.toNat * 2 ^ 40 + di.toNat < t.toNat * 2 ^ 40 + (di.toNat + 1) + n) := by omega
      have c2 : t.toNat * 2 ^ 40 + di.toNat ≤ t.toNat * 2 ^ 40 + di.toNat ∧
          t.toNat * 2 ^ 40 + di.toNat < t.toNat * 2 ^ 40 + di.toNat + (n + 1) := by omega
      have e3 : t.toNat * 2 ^ 40 + di.toNat + (si.toNat - di.toNat) = t.toNat * 2 ^ 40 + si.toNat := by omega
      simp only [c1, c2, e3, hvs, ↓reduceIte, and_self, Array.getElem?_eq_getElem hss]
    · by_cases hr : t.toNat * 2 ^ 40 + (di.toNat + 1) ≤ j ∧ j < t.toNat * 2 ^ 40 + (di.toNat + 1) + n
      · have c2 : t.toNat * 2 ^ 40 + di.toNat ≤ j ∧ j < t.toNat * 2 ^ 40 + di.toNat + (n + 1) := by omega
        have c3 : t.toNat * 2 ^ 40 + di.toNat ≠ j + (si.toNat - di.toNat) := by omega
        have e3 : si.toNat + 1 - (di.toNat + 1) = si.toNat - di.toNat := by omega
        simp only [hr, c2, e3, and_self, ↓reduceIte, c3]
      · have c2 : ¬ (t.toNat * 2 ^ 40 + di.toNat ≤ j ∧ j < t.toNat * 2 ^ 40 + di.toNat + (n + 1)) := by omega
        simp only [hr, c2, hj, ↓reduceIte]

end L.Front
