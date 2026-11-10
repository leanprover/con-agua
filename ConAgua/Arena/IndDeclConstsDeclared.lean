module

public import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import all ConAgua.Arena.IndParts
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen
import ConAgua.Arena.ErecRd
import ConRon.Bridge.Grind
import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

@[expose] public section

/-!
# A declaration's constants: the block's members as declared (lane `ronsync2`, stage 3)

`block_shape_declared(p)` (`BlockShape.members.map (·.declared)`, through `member_field_copy` at
word `4`): its model `declW` and decoding `declW_dec`, the copy of `formersW_dec` (`block_shape_formers`,
word `0`). `block_formers` (`IndDeclConsts.lean`) reads it.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`block_shape_declared(p)`'s model `declW`** (generated). -/
l_model blockShapeDeclared_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_field_copy" = some memberFieldCopy)
    (hp : p.lookup "block_shape_declared" = some blockShapeDeclared)
  fns [hp ↦ declW list]
  specs [iwAlloc_specW p ha n, memberFieldCopy_spec p hc n]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- **`block_shape_declared` is `p.members.map (·.declared)`**: the new `IW` slice holds the
members' declared formers (word 4 of each member record). -/
theorem declW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : declW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hq : decBS m p.toNat = some bs)
    (hpt : p.toNat + 9 ≤ iwTop m)
    (hsrc : ∀ o l, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 4 < iwTop m) :
    r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decPL m' (decCVp m') (rdW (m.arr64 CTL) 200).toNat bs.k = some (bs.members.map (·.declared)) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop m' ∧ iwTop m' ≤ (m.arr64 IW).size := by
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  have hlen := decPL_length m hg
  have hk : bs.k = l := by rw [BlockShape.k, hlen]
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e1' : (p + 1).toNat = p.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hsrc' := hsrc o l ho hl
  rcases n with _ | n
  · simp [declW] at h
  rw [declW.arm1, hl'] at h
  rcases hal : allocW m (UInt64.ofNat l) with _ | ⟨q, m1⟩
  · simp [hal, declW.k_iw_alloc.none] at h
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  rw [hal, declW.k_iw_alloc.arm1] at h
  subst hq' hm1
  have hIW := allocMem_IW m (UInt64.ofNat l)
  rw [hIW, ho', hl'] at h
  rcases hcp : fieldCopyW n (allocMem m (UInt64.ofNat l)) (rdW (m.arr64 CTL) 200)
      (UInt64.ofNat o) (UInt64.ofNat l) 4 with _ | m2
  · simp [hcp, declW.k_member_field_copy.none] at h
  simp only [hcp, declW.k_member_field_copy.arm1, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hptr' : ∀ j < (UInt64.ofNat l).toNat,
      (rdW ((allocMem m (UInt64.ofNat l)).arr64 IW) (UInt64.ofNat ((UInt64.ofNat o).toNat + j)) + 4).toNat
        < q.toNat := by
    intro j hj
    rw [hll] at hj
    obtain ⟨v, y, hv, -, -⟩ := decPL_get l o bs.members hg j hj
    have hvb := hptr o l j v ho hl hj hv
    obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
    rw [hIW, hoo, hv']
    simp only [iwTop, hqq] at hvb
    have : (UInt64.ofNat v + 4 : Word).toNat = v + 4 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; simp; omega
    rw [this]; exact hvb
  obtain ⟨hA, hS, hG⟩ := fieldCopyW_get n 4 _ _ _ _ _ hcp
    (by rw [hoo, hll]; simp only [iwTop, hqq] at hsrc'; omega)
    (by rw [hIW, hll]; exact hroom) (by rw [hIW]; exact hsz) hptr'
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = q + UInt64.ofNat l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + UInt64.ofNat l).toNat = q.toNat + l := by
    rw [UInt64.toNat_add]; simp [hll]; omega
  have hER : erecP m2 = erecP m := erecP_frame hfr (by decide) (by decide) (by decide) (by decide)
  have hCV : decCVp m2 = decCVp m := by funext a; simp only [decCVp, erA, hER]
  have hqt : iwTop m = q.toNat := by simp only [iwTop, hqq]
  refine ⟨?_, ?_, ?_, hfr, ?_, ?_⟩
  · have : rdW (m2.arr64 IW) (p + 1) = UInt64.ofNat l := by
      rw [← hl']; simp only [rdW]; rw [hG, ite_eq_right (by rw [e1']; omega)]
    rw [this, hk]
  · rw [hk, hCV]
    have hxs : (bs.members.map (·.declared)).length = l := by simp [hlen]
    have := decPL_of_get (m := m2) (decCVp m) (bs.members.map (·.declared)) q.toNat (fun j hj => by
      have hj' : j < l := by omega
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg j hj'
      obtain ⟨-, ⟨a, hva, hcv⟩, -⟩ := decMS_some hy
      have hGj := hG (q.toNat + j)
      rw [ite_eq_left (by rw [hll]; omega)] at hGj
      have e2 : q.toNat + j - q.toNat = j := by omega
      rw [e2, hoo] at hGj
      have hvb := hptr o l j v ho hl hj' hv
      obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
      have e4 : (UInt64.ofNat v + 4 : Word) = UInt64.ofNat (v + 4) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega),
          UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; simp; omega
      rw [hv', e4] at hGj
      obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
      rw [hva'] at hGj
      have hy' : bs.members[j]'(by omega) = y := by
        simpa [List.getElem?_eq_getElem (show j < bs.members.length by omega)] using hget
      refine ⟨a, ?_, ?_⟩
      · simp only [iwN, nat?, iwA, aread_apply, hGj, Option.map_some]
        rw [UInt64.toNat_ofNat_of_lt' hab]
      · simp [List.getElem_map, hy', hcv])
    rw [hxs] at this
    exact this
  · refine iwGrow_of_frame hfr (N := UInt64.ofNat l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq, hll]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum, hk]
  · simp only [iwTop, htop, hsum]; omega


end L.Ind

end
