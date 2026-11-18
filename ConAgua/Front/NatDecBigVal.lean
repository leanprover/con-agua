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

/-! ## The callees in `natDecProg` -/

/-- The result of a pool operation that appends one slice: the pool grew, the top moved past
the slice, which is normalised and denotes `v`. -/
structure Appended (m m' : Mem) (l : Word) (v : Nat) : Prop where
  grows : Grows m m'
  top : m'.top = m.top + l
  fits : m.top.toNat + l.toNat ≤ pcap m'
  norm : Norm (vpool m') m.top.toNat l.toNat
  val : pv (vpool m') m.top.toNat l.toNat = v

theorem pframe_top {m m' : Mem} {v : Word} (hc : 0 < (m.arr64 CTL).size)
    (h : PFrame (m.set64 CTL 0 v) m') : m'.top = v := by
  rw [h.top, Mem.top_set64 _ _ hc]

/-- **`nat_mul` in `natDecProg`**, from its spec. -/
theorem mul_callW {n : Nat} {m m' : Mem} {oa la ob lb : Word} {r : List Word} (hok : PoolOK m)
    (ha : SliceOK m oa la) (hb : SliceOK m ob lb)
    (h : callW natDecProg n "nat_mul" [oa, la, ob, lb] m = some (r, m')) :
    Appended m m' (r.headD 0) (pv (vpool m) oa.toNat la.toNat * pv (vpool m) ob.toNat lb.toNat) := by
  obtain ⟨s', rfl, -, hf, -, hfit, -, hv, hN, hg⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natMul_spec natDecProg rfl rfl rfl n ⟨m, Locals.init []⟩ oa la ob lb hok ha hb) h
  exact ⟨hg, pframe_top hok.ctl hf, hfit, hN, hv⟩

/-- **`nat_add` in `natDecProg`**, from its spec. -/
theorem add_callW {n : Nat} {m m' : Mem} {oa la ob lb : Word} {r : List Word} (hok : PoolOK m)
    (ha : SliceOK m oa la) (hb : SliceOK m ob lb)
    (h : callW natDecProg n "nat_add" [oa, la, ob, lb] m = some (r, m')) :
    Appended m m' (r.headD 0) (pv (vpool m) oa.toNat la.toNat + pv (vpool m) ob.toNat lb.toNat) := by
  obtain ⟨s', rfl, -, hf, -, hfit, -, hv, hN, hg⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natAdd_spec natDecProg rfl rfl rfl rfl n ⟨m, Locals.init []⟩
      oa la ob lb hok ha hb) h
  exact ⟨hg, pframe_top hok.ctl hf, hfit, hN, hv⟩

/-- **`nat_dec_chunks` in `natDecProg`**: the chunk loop's value. -/
theorem chunks_callW {n : Nat} {b : Array UInt8} {m m' : Mem} {c d : Word} {r : List Word}
    (hok : PoolOK m) (hb : m.arr8 IN = b) (hcd : c ≤ d) (hdig : Digits b c.toNat (d.toNat - c.toNat))
    (h : callW natDecProg n "nat_dec_chunks" [c, d] m = some (r, m')) :
    ∃ l, r = [m.top, l] ∧ Grows m m' ∧ SliceOK m' m.top l ∧ Norm (vpool m') m.top.toNat l.toNat ∧
      pv (vpool m') m.top.toNat l.toNat = decN b c.toNat (d.toNat - c.toNat) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natDecChunks_specW natDecProg b rfl rfl rfl n ⟨m, Locals.init []⟩ hb c d) h
  exact natChunksW_val b m s'.mem c d r hok hcd hdig hW

/-! ## The split level -/

/-- The split loop's invariant: `dd = 19 · 2^t`, at most half of `n`. -/
structure LevelInv (n t dd : Word) : Prop where
  pow : dd.toNat = 19 * 2 ^ t.toNat
  half : 2 * dd.toNat ≤ n.toNat

theorem sub2_toNat {n dd : Word} (h : 2 * dd.toNat ≤ n.toNat) :
    (n - dd - dd).toNat = n.toNat - 2 * dd.toNat := by
  have hd1 : dd ≤ n := UInt64.le_iff_toNat_le.mpr (by omega)
  have e0 : (n - dd).toNat = n.toNat - dd.toNat := UInt64.toNat_sub_of_le _ _ hd1
  have hd2 : dd ≤ n - dd := UInt64.le_iff_toNat_le.mpr (by rw [e0]; omega)
  rw [UInt64.toNat_sub_of_le _ _ hd2, e0]; omega

theorem LevelInv.step {n t dd : Word} (h : LevelInv n t dd) (hc : dd + dd ≤ n - dd - dd) :
    LevelInv n (t + 1) (dd + dd) ∧ 4 * dd.toNat ≤ n.toNat := by
  have h1 := h.pow; have h2 := h.half
  have hn := n.toNat_lt
  have e1 : (dd + dd).toNat = 2 * dd.toNat := by rw [UInt64.toNat_add]; omega
  have e2 : (n - dd - dd).toNat = n.toNat - 2 * dd.toNat := sub2_toNat h2
  have hc' := UInt64.le_iff_toNat_le.mp hc
  rw [e1, e2] at hc'
  have ht : t.toNat < 64 := by
    rcases Nat.lt_or_ge t.toNat 64 with hh | hh
    · exact hh
    · have : 2 ^ 64 ≤ 2 ^ t.toNat := Nat.pow_le_pow_right (by decide) hh
      omega
  have e3 : (t + 1).toNat = t.toNat + 1 := by rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  refine ⟨⟨by rw [e1, e3, Nat.pow_succ]; omega, by rw [e1]; omega⟩, by omega⟩

theorem LevelInv.stop {n t dd : Word} (h : LevelInv n t dd) (hc : ¬ dd + dd ≤ n - dd - dd) :
    n.toNat < 4 * dd.toNat := by
  have h1 := h.pow; have h2 := h.half
  have hn := n.toNat_lt
  have e1 : (dd + dd).toNat = 2 * dd.toNat := by rw [UInt64.toNat_add]; omega
  have e2 : (n - dd - dd).toNat = n.toNat - 2 * dd.toNat := sub2_toNat h2
  rw [UInt64.le_iff_toNat_le, e1, e2] at hc
  omega

theorem splitLoop_val {p : Prog} {n' : Word} : ∀ (f : Nat) (m : Mem) (t dd t' dd' : Word) (m' : Mem),
    LevelInv n' t dd → splitW.loop1 p f m n' t dd = some (t', dd', m') →
    m' = m ∧ LevelInv n' t' dd' := by
  intro f
  induction f with
  | zero => intro m t dd t' dd' m' _ h; rw [splitW.loop1.eq_1] at h; cases h
  | succ f ih =>
    intro m t dd t' dd' m' hI h
    by_cases hc : dd + dd ≤ n' - dd - dd
    · rw [splitW.loop1.arm1 p f m n' t dd hc] at h
      exact ih m _ _ t' dd' m' (hI.step hc).1 h
    · rw [splitW.loop1.arm2 p f m n' t dd hc] at h
      cases h
      exact ⟨rfl, hI⟩

/-! ## The copy down to the old top -/

private theorem pv_congr' (p q : Array Word) (a b l : Nat)
    (h : ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0) : pv p a l = pv q b l := by
  induction l with
  | zero => rfl
  | succ k ih => simp only [pv, ih (fun i hi => h i (by omega)), h k (by omega)]

/-- A grown pool's top is in the old top's tier, inside its tier array. -/
theorem Grows.same_tier {m m' : Mem} (hok : PoolOK m) (hg : Grows m m') :
    m'.top >>> 40 = m.top >>> 40 ∧ m'.top.toNat < 2 ^ 41 ∧
      m'.top.toNat % 2 ^ 40 ≤ (m'.arr64 (tierA POOL (m.top >>> 40))).size := by
  have h41 := hok.top41
  have hsm := hok.small
  have ht := hg.tier; have hle := hg.le; have hc := hg.cap
  have hp : pcap m' = 2 ^ 41 - 1 := by rw [hg.pcapEq]; exact pcap_of_small m hsm
  have hT : m'.top >>> 40 = m.top >>> 40 := tag_tier_eq (by omega)
  have hin := hg.inn
  rw [hT, tag_idx_toNat] at hin
  exact ⟨hT, by omega, hin⟩

/-- **The result copied down to the old top**: a slice `(os, ls)` that ends at the top of a pool
grown from `m`, copied to `m`'s top `T` (same tier, `T ≤ os`), and the top set to `T + ls`: the
pool grew from `m`, and the new slice at `T` is the old one. -/
theorem copy_down {m m₄ : Mem} {os ls : Word} (hok : PoolOK m) (hg : Grows m m₄)
    (hos : m.top.toNat ≤ os.toNat) (hend : os.toNat + ls.toNat ≤ m₄.top.toNat) :
    Grows m ((m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (tierA POOL (m.top >>> 40))
        (os &&& 1099511627775) ls.toNat).set64 CTL 0 (m.top + ls)) ∧
    SliceOK ((m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (tierA POOL (m.top >>> 40))
        (os &&& 1099511627775) ls.toNat).set64 CTL 0 (m.top + ls)) m.top ls ∧
    (Norm (vpool m₄) os.toNat ls.toNat →
      Norm (vpool ((m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775)
        (tierA POOL (m.top >>> 40)) (os &&& 1099511627775) ls.toNat).set64 CTL 0 (m.top + ls)))
        m.top.toNat ls.toNat) ∧
    pv (vpool ((m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (tierA POOL (m.top >>> 40))
        (os &&& 1099511627775) ls.toNat).set64 CTL 0 (m.top + ls))) m.top.toNat ls.toNat =
      pv (vpool m₄) os.toNat ls.toNat := by
  have h41 := hok.top41
  have hsm := hok.small
  obtain ⟨hT4, h41', hin4⟩ := Grows.same_tier hok hg
  have e4 := tag_tier_toNat m₄.top
  have eT := tag_tier_toNat m.top
  rw [hT4] at e4
  have hok4 := hok.grows hg
  have hsz4 : (m₄.arr64 (tierA POOL (m.top >>> 40))).size ≤ 2 ^ 40 :=
    Nat.le_of_lt (hok4.small.tier _)
  have ht : (m.top >>> 40).toNat ≤ 1 := tag_tier_le _ h41
  have hdi := tag_idx_toNat m.top
  have hsi := tag_idx_toNat os
  have hsplit := tag_split m.top
  have hq : os.toNat / 2 ^ 40 = m.top.toNat / 2 ^ 40 := by omega
  have hrange : (m.top &&& 1099511627775).toNat ≤ (os &&& 1099511627775).toNat := by omega
  have hbound : (os &&& 1099511627775).toNat + ls.toNat ≤ (m₄.arr64 (tierA POOL (m.top >>> 40))).size := by
    omega
  have hcopy := vpool_copy64 (m.top >>> 40) ht ls.toNat m₄ (m.top &&& 1099511627775) (os &&& 1099511627775)
    hsz4 hrange hbound
  have hTl : (m.top + ls).toNat = m.top.toNat + ls.toNat := by
    rw [UInt64.toNat_add]; omega
  have hpf : PFrame m₄ (m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775)
      (tierA POOL (m.top >>> 40)) (os &&& 1099511627775) ls.toNat) :=
    PFrame.copy64 (m := m₄) (m.top >>> 40) ls.toNat m₄ _ _ (PFrame.refl m₄)
  have hag : Agree (vpool (m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775)
      (tierA POOL (m.top >>> 40)) (os &&& 1099511627775) ls.toNat)) (vpool m) m.top.toNat := by
    intro j hj
    rw [hcopy j, if_neg (by omega)]
    exact hg.agree j hj
  have hgr := Grows.reset hok hg hpf hag (m.top + ls) (by omega) (by omega)
  have hctl : 0 < ((m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775)
      (tierA POOL (m.top >>> 40)) (os &&& 1099511627775) ls.toNat).arr64 CTL).size := by
    rw [hpf.ctl]; exact hok4.ctl
  have hget : ∀ i, i < ls.toNat →
      (vpool (m₄.copy64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775)
        (tierA POOL (m.top >>> 40)) (os &&& 1099511627775) ls.toNat))[m.top.toNat + i]? =
        (vpool m₄)[os.toNat + i]? := by
    intro i hi
    rw [hcopy, if_pos (by omega)]
    congr 1
    omega
  refine ⟨hgr, SliceOK.fresh hgr (Mem.top_set64 _ _ hctl), ?_, ?_⟩
  · intro hN hl
    rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, hget _ (by omega)]
    exact hN hl
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]
    exact pv_congr' _ _ _ _ _ (fun i hi => by rw [hget i hi])

/-! ## The power table -/

/-- Entry `t` of the power table at `tbl`: the slice's address and length. -/
def tblA (m : Mem) (tbl t : Word) : Word := prd m (tbl + t + t)
def tblL (m : Mem) (tbl t : Word) : Word := prd m (tbl + t + t + 1)

/-- **The power table** at `tbl`, room for `K` entries below the top, the first `i` filled:
entry `t` a normalised slice in use, above the table, denoting `10^(19 · 2^t)`. -/
structure TblOK (m : Mem) (tbl K i : Word) : Prop where
  room : tbl.toNat + 2 * K.toNat ≤ m.top.toNat
  le : i.toNat ≤ K.toNat
  above : ∀ t : Word, t < i → tbl.toNat + 2 * K.toNat ≤ (tblA m tbl t).toNat
  slice : ∀ t : Word, t < i → SliceOK m (tblA m tbl t) (tblL m tbl t)
  norm : ∀ t : Word, t < i → Norm (vpool m) (tblA m tbl t).toNat (tblL m tbl t).toNat
  val : ∀ t : Word, t < i →
    pv (vpool m) (tblA m tbl t).toNat (tblL m tbl t).toNat = 10 ^ (19 * 2 ^ t.toNat)

theorem tbl_idx {tbl K t : Word} (h : tbl.toNat + 2 * K.toNat < 2 ^ 64) (ht : t.toNat < K.toNat) :
    (tbl + t + t).toNat = tbl.toNat + 2 * t.toNat ∧ (tbl + t + t + 1).toNat = tbl.toNat + 2 * t.toNat + 1 := by
  have e1 : (tbl + t).toNat = tbl.toNat + t.toNat := by rw [UInt64.toNat_add]; omega
  have e2 : (tbl + t + t).toNat = tbl.toNat + 2 * t.toNat := by rw [UInt64.toNat_add, e1]; omega
  refine ⟨e2, ?_⟩
  rw [UInt64.toNat_add, e2]; simp only [UInt64.reduceToNat]; omega

theorem TblOK.grows {m m' : Mem} {tbl K i : Word} (hok : PoolOK m) (hg : Grows m m')
    (h : TblOK m tbl K i) : TblOK m' tbl K i := by
  have h41 := hok.top41
  have hroom := h.room
  have hle := h.le
  have eA : ∀ t : Word, t < i → tblA m' tbl t = tblA m tbl t ∧ tblL m' tbl t = tblL m tbl t := by
    intro t ht
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    obtain ⟨e1, e2⟩ := tbl_idx (tbl := tbl) (K := K) (t := t) (by omega) (by omega)
    exact ⟨prd_grows hok hg (by rw [e1]; omega), prd_grows hok hg (by rw [e2]; omega)⟩
  refine ⟨by have := hg.le; omega, hle, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [(eA t ht).1]; exact h.above t ht
  · rw [(eA t ht).1, (eA t ht).2]; exact (h.slice t ht).grows hg
  · rw [(eA t ht).1, (eA t ht).2]
    exact (Grows.norm hg (h.slice t ht).le).mpr (h.norm t ht)
  · rw [(eA t ht).1, (eA t ht).2, Grows.pv hg (h.slice t ht).le]; exact h.val t ht

/-! ## `nat_dec_split` -/

theorem _root_.L.Arena.Grows.arr8 {m m' : Mem} (hg : Grows m m') (a : ArrId) : m'.arr8 a = m.arr8 a := by
  simp only [Mem.arr8, hg.frame.bytes, Mem.bytes_set64]

/-- What `nat_dec_split` (and `nat_dec`) post: the decimal value of `[c, d)` appended at the old
top, normalised. -/
def DecPost (b : Array UInt8) (m m' : Mem) (c d : Word) (r : List Word) : Prop :=
  r = [m.top, r.tail.headD 0] ∧ Grows m m' ∧ SliceOK m' m.top (r.tail.headD 0) ∧
    Norm (vpool m') m.top.toNat (r.tail.headD 0).toNat ∧
    pv (vpool m') m.top.toNat (r.tail.headD 0).toNat = decN b c.toNat (d.toNat - c.toNat)

theorem split_run {n : Nat} {m m' : Mem} {c d tbl k : Word} {r : List Word}
    (h : callW natDecProg n "nat_dec_split" [c, d, tbl, k] m = some (r, m')) :
    splitW natDecProg n m c d tbl k = some (r, m') := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natDecSplit_spec natDecProg rfl n ⟨m, Locals.init []⟩ c d tbl k) h
  exact hW

/-- **`nat_dec_split(c, d, tbl, k)`**: on digits `[c, d)` and a full power table of `k` entries,
the value of the digits appended at the old top. -/
theorem split_val (b : Array UInt8) : ∀ (n : Nat) (m m' : Mem) (c d tbl k : Word) (r : List Word),
    PoolOK m → m.arr8 IN = b → c ≤ d → Digits b c.toNat (d.toNat - c.toNat) → TblOK m tbl k k →
    callW natDecProg n "nat_dec_split" [c, d, tbl, k] m = some (r, m') → DecPost b m m' c d r := by
  intro n
  induction n with
  | zero => intro m m' c d tbl k r _ _ _ _ _ h; rw [callW_zero] at h; cases h
  | succ n ih =>
  intro m m' c d tbl k r hok hb hcd hdig hT h
  have hW := split_run h
  rw [splitW.eq_2] at hW
  have h41 := hok.top41
  have hcd' := UInt64.le_iff_toNat_le.mp hcd
  have hdc : (d - c).toNat = d.toNat - c.toNat := UInt64.toNat_sub_of_le _ _ hcd
  split at hW
  · -- the chunk loop
    rcases hC : callW natDecProg n "nat_dec_chunks" [c, d] m with _ | ⟨r₁, m₁⟩
    · rw [hC, splitW.k_nat_dec_chunks.eq_1] at hW; cases hW
    rw [hC, splitW.k_nat_dec_chunks.eq_2] at hW
    cases hW
    obtain ⟨l, rfl, hg, hs, hN, hv⟩ := chunks_callW hok hb hcd hdig hC
    exact ⟨rfl, hg, hs, hN, hv⟩
  · rename_i hbig
    have hbig' : decBase.toNat < d.toNat - c.toNat := by
      rw [← hdc]; exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hbig)
    have hb38 : 38 ≤ decBase.toNat := by decide
    rcases hL : splitW.loop1 natDecProg (n + 1) m (d - c) 0 19 with _ | ⟨t, dd, m₀⟩
    · rw [hL, splitW.k_loop1.eq_1] at hW; cases hW
    obtain ⟨hm0, hI⟩ := splitLoop_val (n + 1) m 0 19 t dd m₀ ⟨by simp, by rw [hdc]; simp; omega⟩ hL
    rw [hL, hm0] at hW
    by_cases hkt : k ≤ t
    · rw [splitW.k_loop1.abort1 _ _ _ _ _ _ _ _ _ hkt] at hW; cases hW
    rw [splitW.k_loop1.arm1 _ _ _ _ _ _ _ _ _ hkt] at hW
    have hpow := hI.pow
    have hhalf := hI.half
    rw [hdc] at hhalf
    have hmd : (d - dd).toNat = d.toNat - dd.toNat := UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by omega))
    -- the high part
    rcases hH : callW natDecProg n "nat_dec_split" [c, d - dd, tbl, k] m with _ | ⟨r₁, m₁⟩
    · rw [hH, splitW.k_nat_dec_split.eq_1] at hW; cases hW
    rw [hH, splitW.k_nat_dec_split.eq_2] at hW
    obtain ⟨hr₁, hg₁, hs₁, hN₁, hv₁⟩ := ih m m₁ c (d - dd) tbl k r₁ hok hb
      (UInt64.le_iff_toNat_le.mpr (by omega))
      (digits_mono _ _ _ _ hdig (by omega)) hT hH
    have hok₁ := hok.grows hg₁
    -- the low part
    rcases hLo : callW natDecProg n "nat_dec_split" [d - dd, d, tbl, k] m₁ with _ | ⟨r₂, m₂⟩
    · rw [hLo, splitW.k_nat_dec_split_2.eq_1] at hW; cases hW
    rw [hLo, splitW.k_nat_dec_split_2.eq_2] at hW
    have hdig₂ : Digits b (d - dd).toNat (d.toNat - (d - dd).toNat) := by
      have := digits_shift b c.toNat (d.toNat - c.toNat - dd.toNat) dd.toNat
        (by rw [show d.toNat - c.toNat - dd.toNat + dd.toNat = d.toNat - c.toNat by omega]; exact hdig)
      rw [show c.toNat + (d.toNat - c.toNat - dd.toNat) = d.toNat - dd.toNat by omega] at this
      rw [hmd, show d.toNat - (d.toNat - dd.toNat) = dd.toNat by omega]
      exact this
    obtain ⟨hr₂, hg₂, hs₂, hN₂, hv₂⟩ := ih m₁ m₂ (d - dd) d tbl k r₂ hok₁ (by rw [hg₁.arr8]; exact hb)
      (UInt64.le_iff_toNat_le.mpr (by omega)) hdig₂ (hT.grows hok hg₁) hLo
    have hok₂ := hok₁.grows hg₂
    have hT₂ := (hT.grows hok hg₁).grows hok₁ hg₂
    have hkt' : t < k := UInt64.lt_iff_toNat_lt.mpr (by have := UInt64.not_le.mp hkt; exact UInt64.lt_iff_toNat_lt.mp this)
    -- the product with the table's entry `t`
    rcases hM : callW natDecProg n "nat_mul" [r₁.headD 0, r₁.tail.headD 0,
        rdW (m₂.arr64 (tierA POOL ((tbl + t + t) >>> 40))) (tbl + t + t &&& 1099511627775),
        rdW (m₂.arr64 (tierA POOL ((tbl + t + t + 1) >>> 40))) (tbl + t + t + 1 &&& 1099511627775)] m₂
      with _ | ⟨r₃, m₃⟩
    · rw [hM, splitW.k_nat_mul.eq_1] at hW; cases hW
    rw [hM, splitW.k_nat_mul.eq_2] at hW
    replace hM : callW natDecProg n "nat_mul" [r₁.headD 0, r₁.tail.headD 0, tblA m₂ tbl t, tblL m₂ tbl t] m₂ =
      some (r₃, m₃) := hM
    have hs₁' : SliceOK m₂ (r₁.headD 0) (r₁.tail.headD 0) := by
      rw [hr₁]; exact hs₁.grows hg₂
    have hA₃ := mul_callW hok₂ hs₁' (hT₂.slice t hkt') hM
    have hok₃ := hok₂.grows hA₃.grows
    -- the sum with the low part
    have hop : rdW (m₂.arr64 CTL) 0 = m₂.top := by simp [rdW, Mem.top]
    rw [hop] at hW
    rcases hS : callW natDecProg n "nat_add" [m₂.top, r₃.headD 0, r₂.headD 0, r₂.tail.headD 0] m₃
      with _ | ⟨r₄, m₄⟩
    · rw [hS, splitW.k_nat_add.eq_1] at hW; cases hW
    have hos : rdW (m₃.arr64 CTL) 0 = m₃.top := by simp [rdW, Mem.top]
    rw [hS, hos, splitW.k_nat_add.eq_2] at hW
    have hs₂' : SliceOK m₃ (r₂.headD 0) (r₂.tail.headD 0) := by rw [hr₂]; exact hs₂.grows hA₃.grows
    have hA₄ := add_callW hok₃ (SliceOK.fresh hA₃.grows hA₃.top) hs₂' hS
    have htop0 : rdW (m.arr64 CTL) 0 = m.top := by simp [rdW, Mem.top]
    rw [htop0] at hW
    cases hW
    have hok₄ := hok₃.grows hA₄.grows
    have hg₄ : Grows m m₄ := Grows.trans _ _ _ (Grows.trans _ _ _ (Grows.trans _ _ _ hg₁ hg₂) hA₃.grows) hA₄.grows
    have h41₄ := hok₄.top41
    have hl₃ := hA₃.grows.le
    have hl₂ := hg₂.le
    have hl₁ := hg₁.le
    have hend : m₃.top.toNat + (r₄.headD 0).toNat = m₄.top.toNat := by
      have hfit := hA₄.fits
      have hp4 : pcap m₄ = 2 ^ 41 - 1 := pcap_of_small m₄ hok₄.small
      rw [hA₄.top, UInt64.toNat_add]
      rw [Nat.mod_eq_of_lt (by omega)]
    obtain ⟨hgF, hsF, hNF, hvF⟩ := copy_down (os := m₃.top) (ls := r₄.headD 0) hok hg₄ (by omega) (by omega)
    refine ⟨by simp, hgF, by simpa using hsF, by simpa using hNF hA₄.norm, ?_⟩
    simp only [List.tail_cons, List.headD_cons]
    rw [hvF, hA₄.val, hA₃.val]
    -- the operands' values
    have e1 : pv (vpool m₂) (r₁.headD 0).toNat (r₁.tail.headD 0).toNat =
        decN b c.toNat ((d - dd).toNat - c.toNat) := by
      rw [hr₁]; simp only [List.headD_cons, List.tail_cons]
      rw [Grows.pv hg₂ hs₁.le, hv₁]
    have e2 : pv (vpool m₂) (tblA m₂ tbl t).toNat (tblL m₂ tbl t).toNat = 10 ^ dd.toNat := by
      rw [hT₂.val t hkt', hpow]
    have e3 : pv (vpool m₃) (r₂.headD 0).toNat (r₂.tail.headD 0).toNat =
        decN b (d - dd).toNat (d.toNat - (d - dd).toNat) := by
      rw [hr₂]; simp only [List.headD_cons, List.tail_cons]
      rw [Grows.pv hA₃.grows hs₂.le, hv₂]
    rw [e1, e2, e3, hmd, show d.toNat - (d.toNat - dd.toNat) = dd.toNat by omega]
    have := decN_append b c.toNat (d.toNat - dd.toNat - c.toNat) dd.toNat
    rw [show d.toNat - dd.toNat - c.toNat + dd.toNat = d.toNat - c.toNat by omega,
      show c.toNat + (d.toNat - dd.toNat - c.toNat) = d.toNat - dd.toNat by omega] at this
    rw [this]

/-! ## Writes into the table -/

/-- A read of the top's tier at index `i`, in bounds, is the virtual pool at `top's tier base + i`. -/
theorem rdW_tier (m : Mem) (T i : Word) (hT : T.toNat < 2 ^ 41)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hi : i.toNat < (m.arr64 (tierA POOL (T >>> 40))).size) :
    rdW (m.arr64 (tierA POOL (T >>> 40))) i =
      (vpool m)[(T >>> 40).toNat * 2 ^ 40 + i.toNat]?.getD 0 := by
  have ht : (T >>> 40).toNat ≤ 1 := tag_tier_le _ hT
  have hv : (T >>> 40).toNat * 2 ^ 40 + i.toNat < (vpool m).size := by rw [vpool_size]; omega
  rw [Array.getElem?_eq_getElem hv, ← vpool_ldt m _ i ht hi hs hv]
  simp [rdW, hi]

/-- **A pool word written above the old top** (index `i` of the top's tier, the address
`T + j`): the pool still grew, and the virtual pool has the word. -/
theorem Grows.poke {m m₁ : Mem} (hok : PoolOK m) (hg : Grows m m₁) (i v : Word) (j : Nat)
    (hi : i.toNat = m.top.toNat % 2 ^ 40 + j)
    (hb : i.toNat < (m₁.arr64 (tierA POOL (m.top >>> 40))).size) :
    Grows m (m₁.set64 (tierA POOL (m.top >>> 40)) i v) ∧
      vpool (m₁.set64 (tierA POOL (m.top >>> 40)) i v) = (vpool m₁).set! (m.top.toNat + j) v := by
  have h41 := hok.top41
  have ok1 := hok.grows hg
  have ht : (m.top >>> 40).toNat ≤ 1 := tag_tier_le _ h41
  have hs : (m₁.arr64 (tierA POOL (m.top >>> 40))).size ≤ 2 ^ 40 := Nat.le_of_lt (ok1.small.tier _)
  have hsplit := tag_split m.top
  have hidx := tag_idx_toNat m.top
  have hv : vpool (m₁.set64 (tierA POOL (m.top >>> 40)) i v) = (vpool m₁).set! (m.top.toNat + j) v := by
    rw [vpool_set64t m₁ _ i v ht hb hs]; congr 1; omega
  have hpf : PFrame m₁ (m₁.set64 (tierA POOL (m.top >>> 40)) i v) := PFrame.set64 _ _ _ (PFrame.refl m₁)
  have htop : (m₁.set64 (tierA POOL (m.top >>> 40)) i v).top = m₁.top := hpf.top
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hv⟩
  · rw [htop]; exact hg.frame.trans hpf
  · rw [hv]; exact Agree.set _ _ _ _ _ hg.agree (by omega)
  · rw [htop]; exact hg.le
  · rw [htop, hpf.pcap]; exact hg.cap
  · rw [hpf.pcap]; exact hg.pcapEq
  · rw [htop]; exact hg.tier
  · rw [htop, hpf.tsize]; exact hg.inn

/-- `SliceOK` reads only the top and `PT0`. -/
theorem SliceOK.congr {m m' : Mem} {o l : Word} (h : SliceOK m o l) (ht : m'.top = m.top)
    (hp : m'.ptop0 = m.ptop0) : SliceOK m' o l := by
  unfold SliceOK at h ⊢; rw [ht, hp]; exact h

theorem pv_set_out (p : Array Word) (x : Nat) (v : Word) (o l : Nat) (h : x < o ∨ o + l ≤ x) :
    pv (p.set! x v) o l = pv p o l := by
  apply pv_congr'
  intro i hi
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  rw [if_neg (by omega)]

theorem norm_set_out (p : Array Word) (x : Nat) (v : Word) (o l : Nat) (h : x < o ∨ o + l ≤ x) :
    Norm (p.set! x v) o l ↔ Norm p o l := by
  unfold Norm
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  constructor <;> intro hn hl <;> have := hn hl
  · rwa [if_neg (by omega)] at this
  · rwa [if_neg (by omega)]

/-- `tblA`/`tblL` as reads of the virtual pool. -/
theorem tbl_vpool (m : Mem) (tbl t : Word) (h : tbl.toNat + 2 * t.toNat + 1 < 2 ^ 41) :
    tblA m tbl t = (vpool m)[tbl.toNat + 2 * t.toNat]?.getD 0 ∧
      tblL m tbl t = (vpool m)[tbl.toNat + 2 * t.toNat + 1]?.getD 0 := by
  have e0 : (tbl + t).toNat = tbl.toNat + t.toNat := by rw [UInt64.toNat_add]; omega
  have e1 : (tbl + t + t).toNat = tbl.toNat + 2 * t.toNat := by rw [UInt64.toNat_add, e0]; omega
  have e2 : (tbl + t + t + 1).toNat = tbl.toNat + 2 * t.toNat + 1 := by
    rw [UInt64.toNat_add, e1]; simp only [UInt64.reduceToNat]; omega
  unfold tblA tblL
  rw [← vpool_getD m _ (by omega), ← vpool_getD m _ (by omega), e1, e2]
  exact ⟨rfl, rfl⟩

/-- **The table grows by one entry**: after `nat_mul` appended the square `(s, l)` at `s`, the
top of `mi`, the entry `i` written at `T + 2i`, `T + 2i + 1`. -/
theorem TblOK.push {mi m₁ m₂ : Mem} {T K i s l : Word} (hok : PoolOK mi) (h : TblOK mi T K i)
    (hiK : i < K) (hA : Appended mi m₁ l (10 ^ (19 * 2 ^ i.toNat))) (hs : s = mi.top)
    (h2 : vpool m₂ = ((vpool m₁).set! (T.toNat + 2 * i.toNat) s).set! (T.toNat + 2 * i.toNat + 1) l)
    (htop : m₂.top = m₁.top) (hp0 : m₂.ptop0 = m₁.ptop0) : TblOK m₂ T K (i + 1) := by
  have h41 := hok.top41
  have hroom := h.room
  have hle := h.le
  have hiK' := UInt64.lt_iff_toNat_lt.mp hiK
  have hok₁ := hok.grows hA.grows
  have h41₁ := hok₁.top41
  have hT₁ := h.grows hok hA.grows
  have hle1 := hA.grows.le
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  -- reads of the new table
  have rd2 : ∀ x, x < 2 ^ 41 → (vpool m₂)[x]?.getD 0 =
      if x = T.toNat + 2 * i.toNat + 1 then l
      else if x = T.toNat + 2 * i.toNat then s else (vpool m₁)[x]?.getD 0 := by
    intro x hx
    rw [h2]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds, vpool_size]
    by_cases e1 : x = T.toNat + 2 * i.toNat + 1
    · subst e1; simp [show T.toNat + 2 * i.toNat + 1 < 2 ^ 41 by omega]
    · by_cases e2 : x = T.toNat + 2 * i.toNat
      · subst e2; simp [show T.toNat + 2 * i.toNat < 2 ^ 41 by omega]
      · simp [Ne.symm e1, Ne.symm e2, e1, e2]
  have eOld : ∀ t : Word, t < i → tblA m₂ T t = tblA m₁ T t ∧ tblL m₂ T t = tblL m₁ T t := by
    intro t ht
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    obtain ⟨a2, l2⟩ := tbl_vpool m₂ T t (by omega)
    obtain ⟨a1, l1⟩ := tbl_vpool m₁ T t (by omega)
    rw [a2, l2, a1, l1, rd2 _ (by omega), rd2 _ (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    exact ⟨rfl, rfl⟩
  have eNew : tblA m₂ T i = s ∧ tblL m₂ T i = l := by
    obtain ⟨a2, l2⟩ := tbl_vpool m₂ T i (by omega)
    rw [a2, l2, rd2 _ (by omega), rd2 _ (by omega), if_neg (by omega), if_pos rfl, if_pos rfl]
    exact ⟨rfl, rfl⟩
  -- a slice above the table reads the same
  have hout : ∀ o ln : Nat, T.toNat + 2 * K.toNat ≤ o →
      (T.toNat + 2 * i.toNat + 1 < o ∨ o + ln ≤ T.toNat + 2 * i.toNat + 1) ∧
      (T.toNat + 2 * i.toNat < o ∨ o + ln ≤ T.toNat + 2 * i.toNat) := by
    intro o ln ho; omega
  have hpv : ∀ o ln : Nat, T.toNat + 2 * K.toNat ≤ o → pv (vpool m₂) o ln = pv (vpool m₁) o ln := by
    intro o ln ho
    rw [h2, pv_set_out _ _ _ _ _ (hout o ln ho).1, pv_set_out _ _ _ _ _ (hout o ln ho).2]
  have hnm : ∀ o ln : Nat, T.toNat + 2 * K.toNat ≤ o → (Norm (vpool m₂) o ln ↔ Norm (vpool m₁) o ln) := by
    intro o ln ho
    rw [h2, norm_set_out _ _ _ _ _ (hout o ln ho).1, norm_set_out _ _ _ _ _ (hout o ln ho).2]
  have hsT : T.toNat + 2 * K.toNat ≤ s.toNat := by rw [hs]; exact hroom
  have hcase : ∀ t : Word, t < i + 1 → t < i ∨ t = i := by
    intro t ht
    have := UInt64.lt_iff_toNat_lt.mp ht
    rcases Nat.lt_or_ge t.toNat i.toNat with h1 | h1
    · exact .inl (UInt64.lt_iff_toNat_lt.mpr h1)
    · exact .inr (UInt64.toNat_inj.mp (by omega))
  refine ⟨by rw [htop]; omega, by omega, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rcases hcase t ht with ht | rfl
    · rw [(eOld t ht).1]; exact hT₁.above t ht
    · rw [eNew.1]; exact hsT
  · rcases hcase t ht with ht | rfl
    · rw [(eOld t ht).1, (eOld t ht).2]; exact SliceOK.congr (hT₁.slice t ht) htop hp0
    · rw [eNew.1, eNew.2, hs]; exact SliceOK.congr (SliceOK.fresh hA.grows hA.top) htop hp0
  · rcases hcase t ht with ht | rfl
    · rw [(eOld t ht).1, (eOld t ht).2, hnm _ _ (hT₁.above t ht)]; exact hT₁.norm t ht
    · rw [eNew.1, eNew.2, hnm _ _ hsT, hs]; exact hA.norm
  · rcases hcase t ht with ht | rfl
    · rw [(eOld t ht).1, (eOld t ht).2, hpv _ _ (hT₁.above t ht)]; exact hT₁.val t ht
    · rw [eNew.1, eNew.2, hpv _ _ hsT, hs, hA.val]

/-! ## `nat_dec_big`: the power table -/

/-- The table loop's invariant: from `m` (the table at `m`'s top, room for `k` entries in the
tier array), the pool grew to `mi` and the first `i` entries are filled. -/
structure BigInv (m mi : Mem) (k i : Word) : Prop where
  ok : PoolOK mi
  grows : Grows m mi
  tbl : TblOK mi m.top k i
  one : 1 ≤ i.toNat
  k64 : k.toNat ≤ 64
  room : m.top.toNat % 2 ^ 40 + 2 * k.toNat + 1 ≤ (mi.arr64 (tierA POOL (m.top >>> 40))).size

theorem ptop0_poke (m : Mem) (t i v : Word) : (m.set64 (tierA POOL t) i v).ptop0 = m.ptop0 :=
  Mem.ptop0_set64_ne _ _ _ _ (by rcases tierA_pool t with e | e <;> rw [e] <;> decide)

theorem pow_sq (i : Nat) (hi : 1 ≤ i) :
    10 ^ (19 * 2 ^ (i - 1)) * 10 ^ (19 * 2 ^ (i - 1)) = 10 ^ (19 * 2 ^ i) := by
  rw [← Nat.pow_add]
  congr 1
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.pow_succ]
  omega

theorem loop2_val {m : Mem} (hok : PoolOK m) {k : Word} : ∀ (f : Nat) (mi : Mem) (i : Word) (m' : Mem),
    BigInv m mi k i →
    bigW.loop2 natDecProg f mi (m.top >>> 40) (m.top &&& 1099511627775) k i = some m' →
    BigInv m m' k k := by
  intro f
  induction f with
  | zero => intro mi i m' _ h; rw [bigW.loop2.eq_1] at h; cases h
  | succ f ih =>
  intro mi i m' hI h
  have hle := hI.tbl.le
  by_cases hik : i < k
  · rw [bigW.loop2.arm1 _ _ _ _ _ _ _ hik] at h
    have hik' := UInt64.lt_iff_toNat_lt.mp hik
    have h41 := hok.top41
    have hoki := hI.ok
    have hsplit := tag_split m.top
    have hidx := tag_idx_toNat m.top
    have hroom := hI.room
    have hk64 := hI.k64
    have hone := hI.one
    have hs : (mi.arr64 (tierA POOL (m.top >>> 40))).size ≤ 2 ^ 40 := Nat.le_of_lt (hoki.small.tier _)
    -- the reads of entry `i - 1`
    have hi1 : (i - 1).toNat = i.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hone))]; simp
    have e0 : ((m.top &&& 1099511627775) + i).toNat = m.top.toNat % 2 ^ 40 + i.toNat := by
      rw [UInt64.toNat_add, hidx]; omega
    have ixA : ((m.top &&& 1099511627775) + i + i).toNat = m.top.toNat % 2 ^ 40 + 2 * i.toNat := by
      rw [UInt64.toNat_add, e0]; omega
    have ix2 : ((m.top &&& 1099511627775) + i + i - 2).toNat = m.top.toNat % 2 ^ 40 + 2 * i.toNat - 2 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [ixA]; simp; omega)), ixA]; simp
    have ix1 : ((m.top &&& 1099511627775) + i + i - 1).toNat = m.top.toNat % 2 ^ 40 + 2 * i.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [ixA]; simp; omega)), ixA]; simp
    obtain ⟨ta, tl⟩ := tbl_vpool mi m.top (i - 1) (by omega)
    have rA : rdW (mi.arr64 (tierA POOL (m.top >>> 40))) ((m.top &&& 1099511627775) + i + i - 2) =
        tblA mi m.top (i - 1) := by
      rw [rdW_tier mi m.top _ h41 hs (by rw [ix2]; omega), ix2, ta, hi1]
      congr 2; omega
    have rL : rdW (mi.arr64 (tierA POOL (m.top >>> 40))) ((m.top &&& 1099511627775) + i + i - 1) =
        tblL mi m.top (i - 1) := by
      rw [rdW_tier mi m.top _ h41 hs (by rw [ix1]; omega), ix1, tl, hi1]
      congr 2; omega
    rw [rA, rL] at h
    have hlt : i - 1 < i := UInt64.lt_iff_toNat_lt.mpr (by omega)
    rcases hM : callW natDecProg f "nat_mul" [tblA mi m.top (i - 1), tblL mi m.top (i - 1),
        tblA mi m.top (i - 1), tblL mi m.top (i - 1)] mi with _ | ⟨r, m₁⟩
    · rw [hM, bigW.k_nat_mul.eq_1] at h; cases h
    rw [hM, bigW.k_nat_mul.eq_2] at h
    have hA := mul_callW hoki (hI.tbl.slice _ hlt) (hI.tbl.slice _ hlt) hM
    rw [hI.tbl.val _ hlt, hi1, pow_sq _ hone] at hA
    have hg₁ : Grows m m₁ := Grows.trans _ _ _ hI.grows hA.grows
    have hsz₁ : (m₁.arr64 (tierA POOL (m.top >>> 40))).size = (mi.arr64 (tierA POOL (m.top >>> 40))).size := by
      have e := PFrame.tsize (m.top >>> 40) hA.grows.frame
      rw [e]
      rcases tierA_pool (m.top >>> 40) with e' | e' <;> rw [e', Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    have ixL : ((m.top &&& 1099511627775) + i + i + 1).toNat = m.top.toNat % 2 ^ 40 + (2 * i.toNat + 1) := by
      rw [UInt64.toNat_add, ixA]; simp only [UInt64.reduceToNat]; omega
    obtain ⟨hgP1, hvP1⟩ := Grows.poke hok hg₁ ((m.top &&& 1099511627775) + i + i) (rdW (mi.arr64 CTL) 0)
      (2 * i.toNat) ixA (by rw [ixA, hsz₁]; omega)
    obtain ⟨hgP2, hvP2⟩ := Grows.poke hok hgP1 ((m.top &&& 1099511627775) + i + i + 1) (r.headD 0)
      (2 * i.toNat + 1) ixL (by rw [ixL, Mem.size_arr64_set64, hsz₁]; omega)
    have hi1' : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    have hpfP : PFrame m₁ (((m₁.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + i + i)
        (rdW (mi.arr64 CTL) 0)).set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + i + i + 1)
        (r.headD 0))) := PFrame.set64 _ _ _ (PFrame.set64 _ _ _ (PFrame.refl m₁))
    refine ih _ (i + 1) m' ⟨hok.grows hgP2, hgP2, ?_, by omega, hk64, ?_⟩ h
    · refine TblOK.push (s := rdW (mi.arr64 CTL) 0) hoki hI.tbl hik hA (by simp [rdW, Mem.top]) ?_ hpfP.top
        (by rw [ptop0_poke, ptop0_poke])
      rw [hvP2, hvP1]
      congr 1
    · rw [hpfP.tsize, hsz₁]; exact hroom
  · rw [bigW.loop2.arm2 _ _ _ _ _ _ _ hik] at h
    cases h
    have : i = k := UInt64.toNat_inj.mp (by have := UInt64.not_lt.mp hik; have := UInt64.le_iff_toNat_le.mp this; omega)
    subst this
    exact hI

theorem bigLoop_val {p : Prog} {n' : Word} : ∀ (f : Nat) (m : Mem) (k dd k' : Word) (m' : Mem),
    1 ≤ k.toNat → LevelInv n' (k - 1) dd → bigW.loop1 p f m n' k dd = some (k', m') →
    m' = m ∧ 1 ≤ k'.toNat ∧ k'.toNat ≤ 64 := by
  intro f
  induction f with
  | zero => intro m k dd k' m' _ _ h; rw [bigW.loop1.eq_1] at h; cases h
  | succ f ih =>
    intro m k dd k' m' h1 hI h
    have hk : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using h1))]; simp
    by_cases hc : dd + dd ≤ n' - dd - dd
    · rw [bigW.loop1.arm1 p f m n' k dd hc] at h
      obtain ⟨hI', -⟩ := hI.step hc
      have hpow := hI'.pow
      have ht : (k - 1 + 1).toNat < 64 := by
        have := hI'.half; have := n'.toNat_lt
        rcases Nat.lt_or_ge (k - 1 + 1).toNat 64 with hh | hh
        · exact hh
        · have : 2 ^ 64 ≤ 2 ^ (k - 1 + 1).toNat := Nat.pow_le_pow_right (by decide) hh
          omega
      have hkl := k.toNat_lt
      have e1 : (k - 1 + 1).toNat = k.toNat := by
        rw [UInt64.toNat_add, hk]; simp only [UInt64.reduceToNat]; omega
      have e2 : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
      have e3 : k + 1 - 1 = k - 1 + 1 := UInt64.toNat_inj.mp (by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [e2]; simp)), e2, e1]; simp)
      exact ih m (k + 1) (dd + dd) k' m' (by omega) (by rw [e3]; exact hI') h
    · rw [bigW.loop1.arm2 p f m n' k dd hc] at h
      cases h
      have hpow := hI.pow; have hhalf := hI.half; have := n'.toNat_lt
      refine ⟨rfl, h1, ?_⟩
      rcases Nat.lt_or_ge (k - 1).toNat 63 with hh | hh
      · omega
      · have : 2 ^ 63 ≤ 2 ^ (k - 1).toNat := Nat.pow_le_pow_right (by decide) hh
        omega

/-- A word written into the top's tier at index `i` (the address `T + j`). -/
theorem vpool_poke (m : Mem) (T i v : Word) (j : Nat) (hT : T.toNat < 2 ^ 41)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hi : i.toNat = T.toNat % 2 ^ 40 + j) (hb : i.toNat < (m.arr64 (tierA POOL (T >>> 40))).size) :
    vpool (m.set64 (tierA POOL (T >>> 40)) i v) = (vpool m).set! (T.toNat + j) v := by
  have ht : (T >>> 40).toNat ≤ 1 := tag_tier_le _ hT
  have hsplit := tag_split T
  have hidx := tag_idx_toNat T
  rw [vpool_set64t m _ i v ht hb hs]; congr 1; omega

theorem get_set3 (V : Array Word) (a b c x : Nat) (va vb vc : Word) (hx : x < V.size) :
    (((V.set! a va).set! b vb).set! c vc)[x]?.getD 0 =
      if x = c then vc else if x = b then vb else if x = a then va else V[x]?.getD 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases e1 : c = x
  · subst e1; simp [hx]
  · by_cases e2 : b = x
    · subst e2; simp [hx, e1, Ne.symm e1]
    · by_cases e3 : a = x
      · subst e3; simp [hx, e1, e2, Ne.symm e1, Ne.symm e2]
      · simp [Ne.symm e1, Ne.symm e2, Ne.symm e3, e1, e2, e3]

/-- **`nat_dec_big`'s first entry**: `10^19` at `T + 2k`, the entry `(T + 2k, 1)` at `T`, the top
past it. -/
theorem big_init {m : Mem} {k : Word} (hok : PoolOK m) (hk1 : 1 ≤ k.toNat) (hk64 : k.toNat ≤ 64)
    (hlen : ¬ m.len64 (tierA POOL (m.top >>> 40)) < (m.top &&& 1099511627775) + k + k + 1) :
    BigInv m ((((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k) 10000000000000000000).set64
      (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64 (tierA POOL (m.top >>> 40))
      ((m.top &&& 1099511627775) + 1) 1).set64 CTL 0 (m.top + k + k + 1)) k 1 := by
  have h41 := hok.top41
  have hsm := hok.small
  have hidx := tag_idx_toNat m.top
  have hs : (m.arr64 (tierA POOL (m.top >>> 40))).size ≤ 2 ^ 40 := Nat.le_of_lt (hsm.tier _)
  have e0 : ((m.top &&& 1099511627775) + k).toNat = m.top.toNat % 2 ^ 40 + k.toNat := by
    rw [UInt64.toNat_add, hidx]; omega
  have eA : ((m.top &&& 1099511627775) + k + k).toNat = m.top.toNat % 2 ^ 40 + 2 * k.toNat := by
    rw [UInt64.toNat_add, e0]; omega
  have eL : ((m.top &&& 1099511627775) + k + k + 1).toNat = m.top.toNat % 2 ^ 40 + 2 * k.toNat + 1 := by
    rw [UInt64.toNat_add, eA]; simp only [UInt64.reduceToNat]; omega
  have e1 : ((m.top &&& 1099511627775) + 1).toNat = m.top.toNat % 2 ^ 40 + 1 := by
    rw [UInt64.toNat_add, hidx]; simp only [UInt64.reduceToNat]; omega
  have hroom : m.top.toNat % 2 ^ 40 + 2 * k.toNat + 1 ≤ (m.arr64 (tierA POOL (m.top >>> 40))).size := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hlen)
    have hl : (m.len64 (tierA POOL (m.top >>> 40))).toNat = (m.arr64 (tierA POOL (m.top >>> 40))).size :=
      UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
    rw [eL, hl] at this
    exact this
  -- the three writes
  have v1 := vpool_poke m m.top ((m.top &&& 1099511627775) + k + k) 10000000000000000000 (2 * k.toNat) h41 hs
    eA (by omega)
  have v2 := vpool_poke (m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k) 10000000000000000000)
    m.top (m.top &&& 1099511627775) (m.top + k + k) 0 h41 (by rw [Mem.size_arr64_set64]; exact hs) (by omega)
    (by rw [Mem.size_arr64_set64]; omega)
  have v3 := vpool_poke ((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k))
    m.top ((m.top &&& 1099511627775) + 1) 1 1 h41 (by rw [Mem.size_arr64_set64, Mem.size_arr64_set64]; exact hs)
    e1 (by rw [Mem.size_arr64_set64, Mem.size_arr64_set64]; omega)
  rw [v2, v1] at v3
  have hpf : PFrame m (((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64
      (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + 1) 1) :=
    PFrame.set64 _ _ _ (PFrame.set64 _ _ _ (PFrame.set64 _ _ _ (PFrame.refl m)))
  have hag : Agree (vpool (((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64
      (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + 1) 1)) (vpool m) m.top.toNat := by
    rw [v3]
    exact Agree.set _ _ _ _ _ (Agree.set _ _ _ _ _ (Agree.set _ _ _ _ _ (Agree.refl _ _) (by omega))
      (by omega)) (by omega)
  have htk : m.top + k + k + 1 = m.top + (k + k + 1) := by
    simp only [UInt64.add_assoc]
  have hkk : (k + k + 1).toNat = 2 * k.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  have hg := Grows.write m _ (k + k + 1) hok hpf hag (by rw [hkk, hidx]; omega)
  rw [← htk] at hg
  have hok' := hok.grows hg
  have hctl : 0 < ((((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64
      (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + 1) 1).arr64 CTL).size := by
    rw [hpf.ctl]; exact hok.ctl
  have htop := Mem.top_set64 _ (m.top + k + k + 1) hctl
  have hT2 : (m.top + k + k).toNat = m.top.toNat + 2 * k.toNat := by
    have : (m.top + k).toNat = m.top.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
    rw [UInt64.toNat_add, this]; omega
  have hT3 : (m.top + k + k + 1).toNat = m.top.toNat + 2 * k.toNat + 1 := by
    rw [UInt64.toNat_add, hT2]; simp only [UInt64.reduceToNat]; omega
  have hV : vpool ((((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64
      (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + 1) 1).set64 CTL 0 (m.top + k + k + 1)) =
      (((vpool m).set! (m.top.toNat + 2 * k.toNat) 10000000000000000000).set! (m.top.toNat + 0)
        (m.top + k + k)).set! (m.top.toNat + 1) 1 := by
    rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, v3]
  have hvs : ∀ x, x < 2 ^ 41 → x < (vpool m).size := fun x hx => by rw [vpool_size]; exact hx
  obtain ⟨ta, tl⟩ := tbl_vpool ((((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64
      (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + 1) 1).set64 CTL 0 (m.top + k + k + 1)) m.top 0
      (by simp; omega)
  simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at ta tl
  rw [hV, get_set3 _ _ _ _ _ _ _ _ (hvs _ (by omega))] at ta
  rw [hV, get_set3 _ _ _ _ _ _ _ _ (hvs _ (by omega))] at tl
  rw [if_neg (by omega), if_pos (by omega)] at ta
  rw [if_pos (by omega)] at tl
  have h0 : ∀ t : Word, t < 1 → t = 0 := fun t ht => UInt64.toNat_inj.mp (by
    have := UInt64.lt_iff_toNat_lt.mp ht; simp at this ⊢; omega)
  have hTt := hg.tier
  rw [htop] at hTt
  have hgetA : (vpool ((((m.set64 (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + k + k)
      10000000000000000000).set64 (tierA POOL (m.top >>> 40)) (m.top &&& 1099511627775) (m.top + k + k)).set64
      (tierA POOL (m.top >>> 40)) ((m.top &&& 1099511627775) + 1) 1).set64 CTL 0 (m.top + k + k + 1)))[
        m.top.toNat + 2 * k.toNat]?.getD 0 = 10000000000000000000 := by
    rw [hV, get_set3 _ _ _ _ _ _ _ _ (hvs _ (by omega)), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  refine ⟨hok', hg, ⟨?_, by simpa using hk1, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩,
    by simp, hk64, ?_⟩
  · rw [htop, hT3]; omega
  · rw [h0 t ht, ta, hT2]; exact Nat.le_refl _
  · rw [h0 t ht, ta, tl]
    unfold SliceOK
    rw [htop, hT2, hT3]
    simp only [UInt64.reduceToNat]
    omega
  · rw [h0 t ht, ta, tl, hT2]
    intro _
    simp only [UInt64.reduceToNat, Nat.sub_self, Nat.add_zero]
    rw [hgetA]; decide
  · rw [h0 t ht, ta, tl, hT2]
    simp only [UInt64.reduceToNat, pv, wt, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add,
      UInt64.toNat_zero]
    rw [hgetA]; rfl
  · have hne : tierA POOL (m.top >>> 40) ≠ CTL := by
      rcases tierA_pool (m.top >>> 40) with e | e <;> rw [e] <;> decide
    rw [Mem.arr64_set64_ne _ _ _ _ _ hne, Mem.size_arr64_set64, Mem.size_arr64_set64, Mem.size_arr64_set64]
    exact hroom

end L.Front
