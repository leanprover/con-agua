import ConAgua.Arena.TwinStep
import ConAgua.Arena.CapsNeverZeroCore

/-!
# `lv_zero_caps` under `StageT` (lane `indproofs4`, helper `lvl`)

`lzcF_simT`: a run of `lv_zero_caps(l)` (its model `lzcF`, `IndRealLvlZ.lean`) from a memory in
`StageT`, the handle `l` reading back to `lv`, is the twin's `readLevelM l` (which returns `lv` and
caches it), `StageT` after, the pools grown, and the three result words the zero-ness of `lv`
(`decZC`). Through lane `levels`' `zeroW_ok` (`lv_zero` is `zeronessOf` on the heap), the heap
frame (`StageT.of_heap`) and the record-pool writer `StageR.erec`.

The names of the `ifAllZero` datum decode by the **name store** (`denoteN`), not by the record
decoder `dn` of the stage relation: `dn` is only known to agree with the store where it is defined
(`StoreDen.dnN`), so `decZC dn` follows for a `dn` that decodes every stored name (`decZC_mono`).
This is why the stub contract `IndStubs.lvZeroCaps_spec` (`StageR` only, `decZC dn`) is not proved
from it: `StageR` lacks the twin's invariants (`TwinOK`: the readback cache holds readbacks) and
the handle's readback, and the decoder is `dn`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A name slice on an array, copied word by word, decodes as a handle slice** reading back to
the names (the converse of `nmsR_of_hslice`). -/
theorem hslice_of_nmsR (ns : NStore) {m : Mem} {A : ArrId} {o k : Word} {ps : List ConLeche.Name}
    (h : NmsR (nameN ns) m A o k ps) :
    o.toNat + k.toNat < 2 ^ 64 → ∀ (arr : Array Word) (q : Nat),
      (∀ j < k.toNat, arr[q + j]? = some ((m.arr64 A)[o.toNat + j]?.getD 0)) →
      ∃ lps : List NIdx, hslice? arr q k.toNat = some lps ∧ lps.mapM (denoteN ns) = some ps := by
  induction h with
  | nil => intro _ arr q _; exact ⟨[], by simp [hslice?], rfl⟩
  | @cons o k x xs hk hx _ ih =>
    intro hb arr q hget
    have hk1 : 1 ≤ k.toNat := Nat.pos_of_ne_zero fun h0 => hk (UInt64.toNat_inj.mp (by simpa using h0))
    have ho : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hk' : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    obtain ⟨lps, hs, hm⟩ := ih (by rw [ho, hk']; omega) arr (q + 1) (fun j hj => by
      have := hget (j + 1) (by rw [hk'] at hj; omega)
      rw [ho, show q + 1 + j = q + (j + 1) by omega, show o.toNat + 1 + j = o.toNat + (j + 1) by omega]
      exact this)
    have h0 := hget 0 (by omega)
    simp only [Nat.add_zero] at h0
    obtain ⟨hw, hd⟩ := hx
    refine ⟨decI (rdW (m.arr64 A) o) :: lps, ?_, ?_⟩
    · rw [show k.toNat = (k - 1).toNat + 1 by rw [hk']; omega, hslice?_succ]
      simp only [hd?, h0, Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_left (by simpa [rdW] using hw)]
      simp [hs]; rfl
    · simp only [List.mapM_cons, hd, hm]; rfl

/-- `erec_alloc(k)` unpacked: the old top, the new top `k` further within the array. -/
theorem lzc_alloc {m m2 : Mem} {k q : Word} (h : erAllocW m k = some (q, m2))
    (hEs : (m.arr64 EREC).size < 2 ^ 64) (hc : 129 < (m.arr64 CTL).size) :
    q = rdW (m.arr64 CTL) 129 ∧ m2 = erAllocMem m k ∧ q.toNat + k.toNat ≤ (m.arr64 EREC).size ∧
      erTop m2 = q.toNat + k.toNat := by
  simp only [erAllocW] at h
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at h
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < k
  · simp [h1, h2] at h
  simp only [h1, h2, ite_false, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + k.toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < k.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  refine ⟨rfl, rfl, hroom, ?_⟩
  have h129 : (129 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  simp only [erTop, erAllocMem, rdW_set64]
  rw [ite_eq_left ⟨trivial, trivial, h129⟩, UInt64.toNat_add]
  omega

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

end

end L.Ind
