module

public import ConAgua.Arena.Tiers
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.ErecGrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The two-tier record pool: its vocabulary

One file for the facts about the record pool `EREC` (both tiers) that proofs use: the decoder
reader `erecP`, L's tagged read `EREC⦃a⦄` (`erRd`) and the tops `erTop`, `erecTop1` (all three
defined in `Tiers.lean`), the decoders' `erA`, the store `erec_put` (`erecPutMem`), and the
tagged-load spec. A proof outside this file and the definitions' own files
(`EnvRec`, `Tiers`, `Env`, `ErecRd`) states its facts over these names and does not unfold them.

**Attribute sets.**
* `arena_grind` holds the equations over the named reads: `erRd_get`, `aread_apply`,
  `erecPutMem_ctl`. A `sym only [lang_grind, arena_grind, …] => vcgen … <;> finish` proof finds
  them without naming them.
* `erec_grind` holds `erRd`'s definition (a `finish` that compares a model's `erRd` with the
  loads `vcgen` leaves): `finish [erec_grind]`. Not in `arena_grind`, and `erRd_foldN` (the
  reverse equation) in no set: either one in `arena_grind` cost 8–92 % of the instructions of
  modules with many tagged reads (DeclCanonSpec, ClassNPcOf; docs/design/syncvocab.md).
* `L.Arena.ErecSpec` is the spec set of a tagged load for `vcgen` (`vcgen` reads one global
  `@[spec]` set; a scoped one is a named set): `open scoped L.Arena.ErecSpec in vcgen [...]`,
  or `open scoped L.Arena.ErecSpec in sym only [...] => vcgen ...`, adds `ld64_rdT_spec`,
  `evalE_tld`, `tld`, `evalE_tagE`, `evalE_idxAE`, `evalE_idxGE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

/-! ## Reads: the decoders' reader, the tops, the tagged read -/

/-- The constant records (both tiers of `EREC`, `erecP`). -/
def erA (m : Mem) : Nat → Option Word := erecP m

/-- A word the record pool decodes is the word `EREC⦃a⦄` reads, in bounds. -/
theorem erRd_of_erecP {m : Mem} {a v : Word} (h : erecP m a.toNat = some v) :
    erRd m a = v ∧ (a &&& 0xFFFFFFFFFF).toNat < (m.arr64 (tierA EREC (a >>> 40))).size := by
  obtain ⟨hlt, hget⟩ := erecP_tagRead h
  exact ⟨by simp only [erRd, rdW, hget, Option.getD_some], hlt⟩

theorem erRd_of_erA {m : Mem} {a v : Word} (h : erA m a.toNat = some v) : erRd m a = v :=
  (erRd_of_erecP h).1


/-- An in-bounds `EREC⦃a⦄` read, as the model's `erRd`. -/
theorem erRd_get (m : Mem) (a : Word) (h : (a &&& 1099511627775).toNat < (m.arr64 (tierA EREC (a >>> 40))).size) :
    (m.arr64 (tierA EREC (a >>> 40)))[(a &&& 1099511627775).toNat] = erRd m a := by
  unfold erRd; rw [rdW_eq _ _ _ rfl h]


/-- `EREC⦃a⦄` as the generated models spell it. -/
theorem erRd_foldN (m : Mem) (a : Word) :
    rdW (m.arr64 (tierA EREC (a >>> 40))) (a &&& 1099511627775) = erRd m a := rfl


/-- A word the record pool reads at `cq + j` (as a number) is `EREC⦃cq + j⦄`. -/
theorem erRd_add {m : Mem} {cq : Word} {j : Nat} {w : Word} (h : erecP m (cq.toNat + j) = some w)
    (_hj : j < 2 ^ 64) : erRd m (cq + UInt64.ofNat j) = w ∧ (cq + UInt64.ofNat j).toNat = cq.toNat + j := by
  have hlt : cq.toNat + j < 2 ^ 64 := by
    rcases Nat.lt_or_ge (cq.toNat + j) (2 ^ 64) with h' | h'
    · exact h'
    · unfold erecP at h; rw [ite_eq_right (by omega)] at h; cases h
  have e : (cq + UInt64.ofNat j).toNat = cq.toNat + j := by
    rw [UInt64.toNat_add]; simp; omega
  exact ⟨(erRd_of_erecP (by rw [e]; exact h)).1, e⟩

/-- A word the record pool decodes as a number. -/
theorem erRd_natA {m : Mem} {a : Word} {k : Nat} (h : nat? (erA m) a.toNat = some k) :
    (erRd m a).toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  rw [erRd_of_erA hw]


theorem erTop_lt (m : Mem) : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt


/-! ## The tagged address and `erec_put` -/

/-- The memory after `erec_put(a, v)`. -/
def erecPutMem (m : Mem) (a v : Word) : Mem :=
  m.set64 (tierA EREC (a >>> 40)) (a &&& 0xFFFFFFFFFF) v

theorem mask40_toNat (a : Word) : (a &&& 0xFFFFFFFFFF).toNat = a.toNat % 2 ^ 40 := by
  rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 40

theorem tierA_EREC (a : Word) : tierA EREC (a >>> 40) =
    if a.toNat / 2 ^ 40 % 2 = 0 then (EREC : TieredArray) else tier1 EREC := by
  have hbit : ((a >>> 40) &&& 1).toNat = a.toNat / 2 ^ 40 % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat]
    exact Nat.and_one_is_mod _
  unfold tierA
  by_cases e : a.toNat / 2 ^ 40 % 2 = 0
  · have : (a >>> 40) &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [hbit, e]; rfl)
    simp [e, this]
  · have : (a >>> 40) &&& 1 ≠ 0 := fun h' => e (by rw [← hbit, h']; rfl)
    simp [e, this]

/-- The offset of a tagged address within its tier. -/
def erOff (a : Word) : Nat := a.toNat % 2 ^ 40

/-- The tier array of a tagged address. -/
def erTier (a : Word) : TieredArray := if a.toNat / 2 ^ 40 % 2 = 0 then (EREC : TieredArray) else tier1 EREC

/-- The top of the tier of a tagged address. -/
def erTopOf (m : Mem) (a : Word) : Nat := if a.toNat / 2 ^ 40 % 2 = 0 then erTop m else erecTop1 m

theorem nat_and40 (n : Nat) : n &&& 1099511627775 = n % 1099511627776 :=
  Nat.and_two_pow_sub_one_eq_mod n 40

theorem erecPutMem_arr (m : Mem) (a v : Word) (b : TieredArray) :
    (erecPutMem m a v).arr64 b = if b = erTier a then (m.arr64 b).setIfInBounds (erOff a) v else m.arr64 b := by
  unfold erecPutMem
  rw [tierA_EREC, ← erTier]
  by_cases e : b = erTier a
  · subst e; simp [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, mask40_toNat, erOff, nat_and40]
  · simp [Mem.arr64_set64_ne _ _ _ _ _ e, e]

theorem ctl_ne_erTier (a : Word) : (CTL : TieredArray) ≠ erTier a := by
  unfold erTier; split <;> decide

theorem erecPutMem_ctl (m : Mem) (a v : Word) : (erecPutMem m a v).arr64 CTL = m.arr64 CTL := by
  rw [erecPutMem_arr, ite_eq_right (ctl_ne_erTier a)]

/-- **A write at or above the top of its tier keeps the record pool.** -/
theorem erecPutMem_grow {m : Mem} {a v : Word} (h : erTopOf m a ≤ erOff a) :
    ErecGrow m (erecPutMem m a v) := by
  have hc := erecPutMem_ctl m a v
  simp only [erTopOf, erOff] at h
  refine ⟨by simp [erTop, hc], fun i hi => ?_, by simp [erecTop1, hc], fun i hi => ?_⟩
  · rw [erecPutMem_arr]; unfold erTier; split
    · rename_i e; simp only [e, ite_true] at h
      have : ¬ (a.toNat % 2 ^ 40 = i) := by omega
      simp [Array.getElem?_setIfInBounds, erOff, this]
    · simp
  · rw [erecPutMem_arr]; unfold erTier; split
    · simp
    · rename_i e; simp only [e, ite_false] at h
      have : ¬ (a.toNat % 2 ^ 40 = i) := by omega
      simp [Array.getElem?_setIfInBounds, erOff, this]

/-- A written word below its tier's top reads back. -/
theorem erecP_putMem_self {m : Mem} {a v : Word} (ht : erOff a < erTopOf m a)
    (hb : erOff a < (m.arr64 (erTier a)).size) :
    erecP (erecPutMem m a v) a.toNat = some v := by
  have hc := erecPutMem_ctl m a v
  simp only [erecP, a.toNat_lt, ite_true, erTop, erecTop1, hc, erecPutMem_arr]
  simp only [erTopOf, erOff, erTier] at ht hb ⊢
  split
  · rename_i e; simp only [e, ite_true] at ht hb
    simp [erTop] at ht; simp [ht, Array.getElem?_setIfInBounds, hb]
  · rename_i e; simp only [e, ite_false] at ht hb
    simp [erecTop1] at ht; simp [ht, Array.getElem?_setIfInBounds, hb]

/-- A write leaves every other address (modulo `2^41`, the tier bit and the offset). -/
theorem erecP_putMem_other {m : Mem} {a v : Word} {i : Nat} (hi : i % 2 ^ 41 ≠ a.toNat % 2 ^ 41) :
    erecP (erecPutMem m a v) i = erecP m i := by
  have hc := erecPutMem_ctl m a v
  have hne : ¬ (i / 2 ^ 40 % 2 = a.toNat / 2 ^ 40 % 2 ∧ i % 2 ^ 40 = a.toNat % 2 ^ 40) := by
    intro ⟨h1, h2⟩; apply hi; omega
  simp only [erecP, erTop, erecTop1, hc, erecPutMem_arr, erTier, erOff]
  by_cases t : a.toNat / 2 ^ 40 % 2 = 0 <;> by_cases ti : i / 2 ^ 40 % 2 = 0 <;>
    simp only [t, ti, ite_true, ite_false] <;> simp [Array.getElem?_setIfInBounds] <;>
    first | rfl | (have : a.toNat % 1099511627776 ≠ i % 1099511627776 := by omega
                   simp [this]; rfl)


theorem erecPutMem_frame (m : Mem) (a v : Word) : MemFrame [EREC, tier1 EREC] [] m (erecPutMem m a v) := by
  refine ⟨fun b hb _ => ?_, fun x _ => by rw [erecPutMem_ctl], fun b => ?_⟩
  · rw [erecPutMem_arr, ite_eq_right]
    unfold erTier; split <;> (intro e; subst e; simp at hb)
  · rw [erecPutMem_arr]; split <;> simp

/-- `EREC⦃x⦄` across an `erec_put` at another place. -/
theorem erRd_erecPutMem_ne {m : Mem} {a v x : Word} (h : erTier x ≠ erTier a ∨ erOff x ≠ erOff a) :
    erRd (erecPutMem m a v) x = erRd m x := by
  have ht : tierA EREC (x >>> 40) = erTier x := by rw [tierA_EREC]; rfl
  unfold erRd
  rw [ht, erecPutMem_arr]
  split
  · rename_i e
    have ho : erOff x ≠ erOff a := by
      rcases h with h | h
      · exact absurd e h
      · exact h
    simp only [rdW, Array.getElem?_setIfInBounds, mask40_toNat]
    rw [ite_eq_right (fun h' => ho (by unfold erOff at h' ⊢; omega))]
  · rfl

end L.Ind

open L L.Arena L.Ind in
/-- A number decoded off the record pool is the word `EREC⦃·⦄` reads there. -/
theorem erRd_nat {m : Mem} {q : Word} {i v : Nat} (h : nat? (erA m) i = some v) (hi : q.toNat = i) :
    erRd m q = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨by rw [erRd_of_erA (by rw [hi]; exact hw), UInt64.ofNat_toNat], w.toNat_lt⟩


namespace L.Arena

open L.Ind

/-- Below the tier-0 top (and below `2^40`, the tier bit clear), the record pool is `EREC`. -/
theorem erecP_getE {m : Mem} {j : Nat} (h : j < erTop m) (h40 : j < 2 ^ 40) :
    erecP m j = (m.arr64 EREC)[j]? := by
  have h64 : j < 2 ^ 64 := by omega
  have hd : j / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h40]
  have hm : j % 2 ^ 40 = j := Nat.mod_eq_of_lt h40
  simp only [erecP, h64, hd, hm, ite_true]
  rw [ite_eq_left (by simpa [erTop] using h)]

/-- A tier-0 address the record pool decodes is below the tier-0 top. -/
theorem erecP_lt {m : Mem} {j : Nat} {v : Word} (h : erecP m j = some v) (h40 : j < 2 ^ 40) :
    j < erTop m := by
  have hd : j / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h40]
  have hm : j % 2 ^ 40 = j := Nat.mod_eq_of_lt h40
  unfold erecP at h
  simp only [hd, hm, ite_true] at h
  split at h
  · split at h
    · rename_i hlt; simpa [erTop] using hlt
    · cases h
  · cases h


open Std.WP in
open scoped Lean.Order in
set_option experimental.vcgen true in
/-- **A read of any tiered array as a value** (`ld64_rdW_spec` at a computed tier, e.g. the
tagged read `EREC⦃a⦄` = `ld64 (tierA EREC (a >>> 40)) (a &&& 0xFFFFFFFFFF)`). -/
theorem ld64_rdT_spec (a : TieredArray) (i : Word) (s₀ : St) :
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


end L.Arena

namespace L.Rom

open L.Arena L.Ind

/-- `erec_put` at an untagged address below `2^40` is a tier-0 store. -/
theorem erecPutMem_lo (m : Mem) (x v : Word) (h : x.toNat < 2 ^ 40) :
    erecPutMem m x v = m.set64 EREC x v := by
  have hb : x.toNat / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h]
  have hm : x &&& 0xFFFFFFFFFF = x := UInt64.toNat_inj.mp (by rw [mask40_toNat]; exact Nat.mod_eq_of_lt h)
  unfold erecPutMem; rw [tierA_EREC, ite_eq_left hb, hm]


end L.Rom

/-! ## The attribute sets -/

namespace L.Ind
attribute [arena_grind =] erRd_get erecPutMem_ctl
attribute [erec_grind] erRd
end L.Ind

attribute [arena_grind =] L.Arena.aread_apply

-- The tagged-load specs, as a named `vcgen` set: `open scoped L.Arena.ErecSpec in vcgen [...]`.
namespace L.Arena.ErecSpec
attribute [scoped spec] L.Arena.ld64_rdT_spec L.Arena.evalE_tld L.Arena.tld L.Arena.evalE_tagE
  L.Arena.evalE_idxAE L.Arena.evalE_idxGE
end L.Arena.ErecSpec
