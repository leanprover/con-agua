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
  obtain ⟨s', rfl, -, hf, -, -, -, hv, hN, hg⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natMul_spec natDecProg rfl rfl rfl n ⟨m, Locals.init []⟩ oa la ob lb hok ha hb) h
  exact ⟨hg, pframe_top hok.ctl hf, hN, hv⟩

/-- **`nat_add` in `natDecProg`**, from its spec. -/
theorem add_callW {n : Nat} {m m' : Mem} {oa la ob lb : Word} {r : List Word} (hok : PoolOK m)
    (ha : SliceOK m oa la) (hb : SliceOK m ob lb)
    (h : callW natDecProg n "nat_add" [oa, la, ob, lb] m = some (r, m')) :
    Appended m m' (r.headD 0) (pv (vpool m) oa.toNat la.toNat + pv (vpool m) ob.toNat lb.toNat) := by
  obtain ⟨s', rfl, -, hf, -, -, -, hv, hN, hg⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natAdd_spec natDecProg rfl rfl rfl rfl n ⟨m, Locals.init []⟩
      oa la ob lb hok ha hb) h
  exact ⟨hg, pframe_top hok.ctl hf, hN, hv⟩

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
    (hos : m.top.toNat ≤ os.toNat) (hend : os.toNat + ls.toNat = m₄.top.toNat) :
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

end L.Front
