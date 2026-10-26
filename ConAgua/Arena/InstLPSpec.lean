import ConAgua.Arena.InstLP
import ConAgua.Arena.LsRefine
import ConAgua.Census.Attr

/-!
# The level-list functions of `InstLP.lean`: models and specs

Word-level models (`…W`) of `sle_go`, `slp_go`, `sls_go`, `spn_pool`, `spn_ls`,
`rec_fire_levels`, each proved by `vcgen` + `finish` from its callees' models.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `sle_go` / `sls_go`: substitute and intern each element of a slice -/

/-- The element read of `sle_go` (`EREC.u64[o]`) and `sls_go` (the tagged `POOL⦃o⦄`). -/
def elemRd (A : ArrId) (m : Mem) (o : Word) : Word := if A = POOL then prd m o else rdW (m.arr64 A) o

@[arena_grind =] theorem elemRd_pool (m : Mem) (o : Word) : elemRd POOL m o = prd m o := rfl
@[arena_grind =] theorem elemRd_erec (m : Mem) (o : Word) : elemRd EREC m o = rdW (m.arr64 EREC) o := rfl

section elems
variable (A : ArrId)

mutual
/-- **The model of `sle_go`** (`A = EREC`) and `sls_go` (`A = POOL`). -/
def slElemW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, o, l, b, ko, kc, vo, vc =>
    if l = 0 then some m
    else slElemK n o l b ko kc vo vc (lvSubIntW n m (elemRd A m o) ko kc vo vc)

/-- After the element: check, store, the rest. -/
def slElemK (n : Nat) (o l b ko kc vo vc : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (h, m₁) =>
    if 4294967296 ≤ h then none else slElemW n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc
end

theorem slElemW_nil (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l = 0) :
    slElemW A (n + 1) m o l b ko kc vo vc = some m := by rw [slElemW]; simp [h]
theorem slElemW_cons (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l ≠ 0) :
    slElemW A (n + 1) m o l b ko kc vo vc =
      slElemK A n o l b ko kc vo vc (lvSubIntW n m (elemRd A m o) ko kc vo vc) := by
  rw [slElemW]; simp [h]
theorem slElemK_some (n : Nat) (o l b ko kc vo vc h : Word) (m₁ : Mem) :
    slElemK A n o l b ko kc vo vc (some (h, m₁)) =
      if 4294967296 ≤ h then none else slElemW A n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc := by
  rw [slElemK]

end elems

grind_pattern [arena_grind] slElemW_nil => slElemW A (n + 1) m o l b ko kc vo vc
grind_pattern [arena_grind] slElemW_cons => slElemW A (n + 1) m o l b ko kc vo vc
attribute [arena_grind =] slElemK_some

/-! ## `slp_go`: the parameters' substitutes -/

/-- The level of a parameter `w`: its value interned, or the parameter node. -/
def slpOne (n : Nat) (m : Mem) (w : Word) : Option (Word × Word) → Option (Word × Mem)
  | none => none
  | some (f, v) => if f ≠ 0 then lvInternW n m v else pinternW m w

mutual
/-- **The model of `slp_go`.** -/
def slpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, o, l, b, ko, kc, vo, vc =>
    if l = 0 then some m
    else slpK n o l b ko kc vo vc
      (slpOne n m (rdW (m.arr64 EREC) o) (lookupW SPN POOL n m ko kc vo vc (rdW (m.arr64 EREC) o)))

/-- After the parameter: check, store, the rest. -/
def slpK (n : Nat) (o l b ko kc vo vc : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (h, m₁) =>
    if 4294967296 ≤ h then none else slpW n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc
end

theorem slpW_nil (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l = 0) :
    slpW (n + 1) m o l b ko kc vo vc = some m := by rw [slpW]; simp [h]
theorem slpW_cons (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l ≠ 0) :
    slpW (n + 1) m o l b ko kc vo vc = slpK n o l b ko kc vo vc
      (slpOne n m (rdW (m.arr64 EREC) o) (lookupW SPN POOL n m ko kc vo vc (rdW (m.arr64 EREC) o))) := by
  rw [slpW]; simp [h]
theorem slpK_some (n : Nat) (o l b ko kc vo vc h : Word) (m₁ : Mem) :
    slpK n o l b ko kc vo vc (some (h, m₁)) =
      if 4294967296 ≤ h then none else slpW n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc := by
  rw [slpK]
theorem slpOne_hit (n : Nat) (m : Mem) (w f v : Word) (hf : f ≠ 0) :
    slpOne n m w (some (f, v)) = lvInternW n m v := by simp [slpOne, hf]
theorem slpOne_miss (n : Nat) (m : Mem) (w v : Word) : slpOne n m w (some (0, v)) = pinternW m w := by
  simp [slpOne]

grind_pattern [arena_grind] slpW_nil => slpW (n + 1) m o l b ko kc vo vc
grind_pattern [arena_grind] slpW_cons => slpW (n + 1) m o l b ko kc vo vc
attribute [arena_grind =] slpK_some
grind_pattern [arena_grind] slpOne_hit => slpOne n m w (some (f, v))
attribute [arena_grind =] slpOne_miss

/-! ## `spn_pool`, `spn_ls`: the stack slice to the pool, interned -/

/-- **The model of `spn_pool`.** -/
def spnPoolW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, b, d, l =>
    if l = 0 then some m
    else spnPoolW n (m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) (rdW (m.arr64 SPN) b))
      (b + 1) (d + 1) (l - 1)

theorem spnPoolW_nil (n : Nat) (m : Mem) (b d l : Word) (h : l = 0) :
    spnPoolW (n + 1) m b d l = some m := by simp [spnPoolW, h]
theorem spnPoolW_cons (n : Nat) (m : Mem) (b d l : Word) (h : l ≠ 0) :
    spnPoolW (n + 1) m b d l =
      spnPoolW n (m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) (rdW (m.arr64 SPN) b))
        (b + 1) (d + 1) (l - 1) := by
  simp [spnPoolW, h]
grind_pattern [arena_grind] spnPoolW_nil => spnPoolW (n + 1) m b d l
grind_pattern [arena_grind] spnPoolW_cons => spnPoolW (n + 1) m b d l

theorem spnPoolW_size (n : Nat) : ∀ (m m' : Mem) (b d l : Word), spnPoolW n m b d l = some m' →
    ∀ A, (m'.arr64 A).size = (m.arr64 A).size := by
  induction n with
  | zero => intro m m' b d l h; simp [spnPoolW] at h
  | succ n ih =>
    intro m m' b d l h A
    by_cases hl : l = 0
    · rw [spnPoolW_nil n m b d l hl] at h; cases h; rfl
    · rw [spnPoolW_cons n m b d l hl] at h
      rw [ih _ _ _ _ _ h A]
      by_cases hA : A = tierA 0 (d >>> 40)
      · subst hA; exact Mem.size_arr64_set64 _ _ _ _
      · rw [Mem.arr64_set64_ne _ _ _ _ _ hA]
grind_pattern [arena_grind] spnPoolW_size => spnPoolW n m b d l, (m'.arr64 A).size

theorem spnPoolW_pcap (n : Nat) (m m' : Mem) (b d l : Word) (h : spnPoolW n m b d l = some m') :
    pcap m' = pcap m :=
  pcap_congr (spnPoolW_size n m m' b d l h POOL) (spnPoolW_size n m m' b d l h POOL1)
grind_pattern [arena_grind] spnPoolW_pcap => spnPoolW n m b d l, pcap m'

/-- `spn_pool` writes only the pool's tiers. -/
theorem spnPoolW_arr (n : Nat) : ∀ (m m' : Mem) (b d l : Word), spnPoolW n m b d l = some m' →
    ∀ A, A ≠ POOL → A ≠ POOL1 → m'.arr64 A = m.arr64 A := by
  induction n with
  | zero => intro m m' b d l h; simp [spnPoolW] at h
  | succ n ih =>
    intro m m' b d l h A h0 h1
    by_cases hl : l = 0
    · rw [spnPoolW_nil n m b d l hl] at h; cases h; rfl
    · rw [spnPoolW_cons n m b d l hl] at h
      rw [ih _ _ _ _ _ h A h0 h1, Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne _ A h0 h1)]

theorem spnPoolW_top (n : Nat) (m m' : Mem) (b d l : Word) (h : spnPoolW n m b d l = some m') :
    m'.top = m.top := by
  simp only [Mem.top, spnPoolW_arr n m m' b d l h CTL (by decide) (by decide)]
grind_pattern [arena_grind] spnPoolW_top => spnPoolW n m b d l, m'.top

/-- **`spn_pool` copies the stack slice to the pool** at the tagged address `d` (inside `d`'s
tier array): it writes only the pool's tiers, nothing below `d`, and the slice at `d` is the
stack's. -/
theorem spnPoolW_ok : ∀ (n : Nat) (m m' : Mem) (b d l : Word), spnPoolW n m b d l = some m' →
    d.toNat < 2 ^ 41 →
    (d &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (d >>> 40))).size →
    (m.arr64 (tierA 0 (d >>> 40))).size < 2 ^ 40 →
    b.toNat + l.toNat < 2 ^ 64 →
    PFrame m m' ∧ MemFrame [POOL, POOL1] [] m m' ∧ Agree (vpool m') (vpool m) d.toNat ∧
      sliceL (vpool m') d.toNat l.toNat = sliceL (m.arr64 SPN) b.toNat l.toNat := by
  intro n
  induction n with
  | zero => intro m m' b d l h; simp [spnPoolW] at h
  | succ n ih =>
    intro m m' b d l h hd hk hsz hb
    by_cases hl : l = 0
    · rw [spnPoolW_nil n m b d l hl] at h; cases h; subst hl
      exact ⟨PFrame.refl _, MemFrame.refl _ _ _, Agree.refl _ _, by simp [sliceL]⟩
    rw [spnPoolW_cons n m b d l hl] at h
    have hl1 : 1 ≤ l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hl
      · omega
    have hi := tag_idx_toNat d
    have ht := tag_tier_toNat d
    have hd1 : (d + 1).toNat = d.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hb1 : (b + 1).toNat = b.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have htd : (d + 1) >>> 40 = d >>> 40 := tag_tier_eq (by rw [hd1]; omega)
    have hid : ((d + 1) &&& 1099511627775).toNat = (d &&& 1099511627775).toNat + 1 := by
      rw [tag_idx_toNat, hd1]; omega
    generalize hv : rdW (m.arr64 SPN) b = v at h
    generalize hm₁ : m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) v = m₁ at h
    have hsz₁ : (m₁.arr64 (tierA 0 (d >>> 40))).size = (m.arr64 (tierA 0 (d >>> 40))).size := by
      rw [← hm₁, Mem.size_arr64_set64]
    have hvp : vpool m₁ = (vpool m).set! d.toNat v := by
      rw [← hm₁]; exact vpool_stidx0 m d v hd (by omega) (by omega)
    have hspn : m₁.arr64 SPN = m.arr64 SPN := by
      rw [← hm₁]; exact Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne _ SPN (by decide) (by decide))
    obtain ⟨hf, hmf, hag, hsl⟩ := ih _ _ _ _ _ h (by omega) (by rw [htd, hid, hsz₁, hlm]; omega)
      (by rw [htd, hsz₁]; exact hsz) (by rw [hb1, hlm]; omega)
    have hpf : PFrame m m₁ := by rw [← hm₁]; exact PFrame.set64 _ _ _ (PFrame.refl m)
    have hmf₁ : MemFrame [POOL, POOL1] [] m m₁ := by
      rw [← hm₁]
      refine (MemFrame.set64 m _ (tierA_pool_ne _ CTL (by decide) (by decide)).symm _ _).mono ?_ (by simp)
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      rcases tierA_pool (d >>> 40) with e | e <;> rw [e] <;> simp
    have hdlt : d.toNat < (vpool m).size := by rw [vpool_size]; exact hd
    refine ⟨hpf.trans hf, hmf₁.trans hmf, fun j hj => ?_, ?_⟩
    · rw [hag j (by rw [hd1]; omega), hvp, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show d.toNat ≠ j by omega]
    · obtain ⟨k, hk'⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
      rw [hk', sliceL_succ, sliceL_succ]
      rw [hd1, hb1, hlm, hk', hspn] at hsl
      simp only [Nat.add_sub_cancel] at hsl
      rw [hsl, hag d.toNat (by rw [hd1]; omega), hvp, ← hv]
      simp [Array.set!_eq_setIfInBounds, hdlt, rdW]

/-- `spn_pool` writes the pool's tiers only above the old top, so the pool grew (the top kept). -/
theorem spnPoolW_grows (n : Nat) (m m' : Mem) (b l : Word) (h : spnPoolW n m b m.top l = some m')
    (hp : PoolOK m)
    (hk : (m.top &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size)
    (hb : b.toNat + l.toNat < 2 ^ 64) :
    PFrame m m' ∧ MemFrame [POOL, POOL1] [] m m' ∧ Agree (vpool m') (vpool m) m.top.toNat ∧
      sliceL (vpool m') m.top.toNat l.toNat = sliceL (m.arr64 SPN) b.toNat l.toNat :=
  spnPoolW_ok n m m' b m.top l h hp.top41 hk (hp.small.tier _) hb

/-- After the copy: the top raised, the list interned, the handle checked. -/
def spnLsK (l : Word) (top : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m₁ =>
    match lsinternW (m₁.set64 CTL 0 (top + l)) top l with
    | none => none
    | some (h, m₂) => if 4294967296 ≤ h then none else some (h, m₂)

@[arena_grind =] theorem spnLsK_some (l top : Word) (m₁ : Mem) :
    spnLsK l top (some m₁) = match lsinternW (m₁.set64 CTL 0 (top + l)) top l with
      | none => none
      | some (h, m₂) => if 4294967296 ≤ h then none else some (h, m₂) := rfl

/-- **The model of `spn_ls`.** -/
def spnLsW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, b, l =>
    if m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775) then none
    else if m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775) < l then none
    else spnLsK l m.top (spnPoolW n m b m.top l)

/-- **The pool stage of `spn_ls`**: the copy at the top and the raised top grow the pool, the new
slice at the old top is the stack's, and the list is interned from the grown memory. -/
theorem spnLsW_pool (n : Nat) (m m' : Mem) (b l r : Word) (hp : PoolOK m)
    (hb : b.toNat + l.toNat < 2 ^ 64) (hW : spnLsW n m b l = some (r, m')) :
    ∃ m₂, Grows m m₂ ∧ m₂.top = m.top + l ∧ (m.top + l).toNat = m.top.toNat + l.toNat ∧
      sliceL (vpool m₂) m.top.toNat l.toNat = sliceL (m.arr64 SPN) b.toNat l.toNat ∧
      MemFrame [POOL, POOL1] [0] m m₂ ∧ m₂.arr64 SPN = m.arr64 SPN ∧
      lsinternW m₂ m.top l = some (r, m') ∧ r.toNat < 2 ^ 32 := by
  cases n with
  | zero => simp [spnLsW] at hW
  | succ n =>
  simp only [spnLsW] at hW
  have hsz := hp.small.tier (m.top >>> 40)
  have h41 := hp.top41
  have hin := hp.2.2.2.2.2
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have t1 : ¬ m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775) := fun t1 => by
    simp [t1] at hW
  have t2 : ¬ m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775) < l := fun t2 => by
    simp [t1, t2] at hW
  simp only [t1, t2, ↓reduceIte] at hW
  have t2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp t1), hlen] at t2'
  have hk : (m.top &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    omega
  cases hc : spnPoolW n m b m.top l with
  | none => rw [hc] at hW; simp [spnLsK] at hW
  | some m₁ =>
  rw [hc, spnLsK_some] at hW
  obtain ⟨hf₁, hmf₁, hag₁, hsl₁⟩ := spnPoolW_ok n m m₁ b m.top l hc h41 hk hsz hb
  have hg := Grows.write m m₁ l hp hf₁ hag₁ hk
  have hi := tag_idx_toNat m.top
  have htl : (m.top + l).toNat = m.top.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hc₁ : 0 < (m₁.arr64 CTL).size := by rw [hf₁.ctl]; exact hp.2.1
  have hspn₁ : m₁.arr64 SPN = m.arr64 SPN := hf₁.arr SPN (by decide) (by decide)
  rcases hI : lsinternW (m₁.set64 CTL 0 (m.top + l)) m.top l with _ | ⟨r', m₃⟩ <;> rw [hI] at hW
  · cases hW
  have hr : ¬ 4294967296 ≤ r' := fun hr => by simp [hr] at hW
  simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  refine ⟨_, hg, Mem.top_set64 _ _ hc₁, htl, ?_, ?_, ?_, hI, UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hr)⟩
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]; exact hsl₁
  · exact (hmf₁.mono (by simp) (by simp)).trans ((MemFrame.setCtl _ _ _).mono (by simp) (by simp))
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hspn₁

/-! ## `rec_fire_levels` (a model over its callees' runs, `callW`) -/

/-- After the keys: the branch of the fire kind, the list interned, the stack top put back. -/
def rflK (p : Prog) (n : Nat) (fk fvo fvc qo qc pc vo vc : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (bs, m₁) =>
    if fk ≠ 0 then
      if m₁.len64 SPN < spTop m₁ then none
      else if m₁.len64 SPN - spTop m₁ < fvc then none
      else match callW p n "sle_go" [fvo, fvc, spTop m₁, bs.headD 0, pc, vo, vc] m₁ with
        | none => none
        | some (_, m₂) => match callW p n "spn_ls" [spTop m₁, fvc] m₂ with
          | none => none
          | some (rs, m₃) => some (rs.headD 0, m₃.set64 CTL 136 (bs.headD 0))
    else
      if m₁.len64 SPN < spTop m₁ then none
      else if m₁.len64 SPN - spTop m₁ < qc then none
      else match callW p n "slp_go" [qo, qc, spTop m₁, bs.headD 0, pc, vo, vc] m₁ with
        | none => none
        | some (_, m₂) => match callW p n "spn_ls" [spTop m₁, qc] m₂ with
          | none => none
          | some (rs, m₃) => some (rs.headD 0, m₃.set64 CTL 136 (bs.headD 0))

/-- **The model of `rec_fire_levels`** at L fuel `n + 1` (its callees at `n`). -/
def recFireLevelsW (p : Prog) (n : Nat) (m : Mem) (fk fvo fvc po pc us qo qc : Word) :
    Option (Word × Mem) :=
  match callW p n "ls_node" [us] m with
  | none => none
  | some (vs, m₀) => rflK p n fk fvo fvc qo qc pc (vs.headD 0) (vs.tail.headD 0)
      (callW p n "keys_push" [po, pc] m₀)

/-! ## The specs -/

/-- A memory read as `rdW` (as `InferBodyIntern.lean`'s `ld64_rdW_spec`, not imported here). -/
theorem lp_ld64_spec (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, by simp [rdW, h], h⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

/-- What the list functions need of the program. -/
structure LsProg (p : Prog) : Prop extends LvSubProg p where
  sle_go : p.lookup "sle_go" = some sleGo
  sls_go : p.lookup "sls_go" = some slsGo
  slp_go : p.lookup "slp_go" = some slpGo
  spn_pool : p.lookup "spn_pool" = some spnPool
  spn_ls : p.lookup "spn_ls" = some spnLs
  rec_fire_levels : p.lookup "rec_fire_levels" = some recFireLevelsL
  lit_hash : p.lookup "lit_hash" = some litHash
  limbs_eq : p.lookup "limbs_eq" = some limbsEq
  ls_match : p.lookup "ls_match" = some lsMatch
  ls_find : p.lookup "ls_find" = some lsFind
  ls_push : p.lookup "ls_push" = some lsPush
  intern_ls : p.lookup "intern_ls" = some internLs

section spec
variable (p : Prog) (hL : LsProg p)
include hL

theorem sleGo_spec (n : Nat) : ∀ (s₀ : St) (o l b ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sle_go" [o, l, b, ko, kc, vo, vc]
    ⦃fun _ s' => LocEq s' s₀ ∧ slElemW EREC n s₀.mem o l b ko kc vo vc = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l b ko kc vo vc; rw [invoke_eq _ hL.sle_go]; simp only [callFn, sleGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l b ko kc vo vc
    rw [invoke_eq _ hL.sle_go]
    simp only [callFn, sleGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lvSubInt_spec p hL.toLvSubProg n, ih] <;>
      finish

theorem slsGo_spec (n : Nat) : ∀ (s₀ : St) (o l b ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sls_go" [o, l, b, ko, kc, vo, vc]
    ⦃fun _ s' => LocEq s' s₀ ∧ slElemW POOL n s₀.mem o l b ko kc vo vc = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l b ko kc vo vc; rw [invoke_eq _ hL.sls_go]; simp only [callFn, slsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l b ko kc vo vc
    rw [invoke_eq _ hL.sls_go]
    simp only [callFn, slsGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lvSubInt_spec p hL.toLvSubProg n, ih] <;>
      finish

theorem slpGo_spec (n : Nat) : ∀ (s₀ : St) (o l b ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "slp_go" [o, l, b, ko, kc, vo, vc]
    ⦃fun _ s' => LocEq s' s₀ ∧ slpW n s₀.mem o l b ko kc vo vc = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l b ko kc vo vc; rw [invoke_eq _ hL.slp_go]; simp only [callFn, slpGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l b ko kc vo vc
    rw [invoke_eq _ hL.slp_go]
    simp only [callFn, slpGo]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lpLookup_spec p hL.lp_lookup n, lvIntern_spec p hL.toLvInternProg n,
        internParam_spec p hL.param_find hL.param_push hL.intern_param n, ih] <;>
      finish

theorem spnPool_spec (n : Nat) : ∀ (s₀ : St) (b d l : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "spn_pool" [b, d, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ spnPoolW n s₀.mem b d l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ b d l; rw [invoke_eq _ hL.spn_pool]; simp only [callFn, spnPool]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ b d l
    rw [invoke_eq _ hL.spn_pool]
    simp only [callFn, spnPool]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish

theorem spnLs_spec (n : Nat) (s₀ : St) (b l : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (ht : s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "spn_ls" [b, l]
    ⦃fun r s' => LocEq s' s₀ ∧ spnLsW n s₀.mem b l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.spn_ls]
  simp only [callFn, spnLs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        spnPool_spec p hL n,
        internLs_spec p hL.lit_hash hL.limbs_eq hL.ls_match hL.ls_find hL.ls_push hL.intern_ls n] <;>
      finish [spnLsW]

theorem recFireLevels_spec (n : Nat) (s₀ : St) (fk fvo fvc po pc us qo qc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "rec_fire_levels" [fk, fvo, fvc, po, pc, us, qo, qc]
    ⦃fun r s' => LocEq s' s₀ ∧
      recFireLevelsW p n s₀.mem fk fvo fvc po pc us qo qc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.rec_fire_levels]
  simp only [callFn, recFireLevelsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lp_ld64_spec, st64,
      callW_spec p n "ls_node", callW_spec p n "keys_push", callW_spec p n "sle_go",
      callW_spec p n "slp_go", callW_spec p n "spn_ls"] <;>
  simp_all [recFireLevelsW, rflK, spTop, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

end spec

end L.Arena
