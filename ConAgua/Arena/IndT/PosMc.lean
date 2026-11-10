module

public import ConAgua.Arena.IndPartsSpec.PlW
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.AllCtors
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndParts
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen
import ConAgua.L.WordOff

@[expose] public section

/-!
# `block_shape_member_ctors` (`BlockShape.memberCtors`)

`ctorsCopyW` (`member_ctors_copy`: `IW[d + j] := IW[s + j] + 2`), `mctorsW` (`block_shape_member_ctors`:
a fresh slice of pointers to the members' constructor headers, words `2`, `3` of each member
record) with their specs, and `mctorsW_dec`: the fresh slice decodes as the members' constructor
lists with their bounds (`decCNSB`), from the shape's `ShapeSl` (its members' `decMSB`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`member_ctors_copy(d, s, l)`'s model `ctorsCopyW`** (generated): `IW[d + j] := IW[s + j] + 2`. -/
l_model memberCtorsCopy_spec (p : Prog) (hp : p.lookup "member_ctors_copy" = some memberCtorsCopy)
  fns [hp ↦ ctorsCopyW void]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- `ctorsCopyW`'s copy step, the recursive call's memory passed on. -/
theorem ctorsCopyW_step (n : Nat) (m : Mem) (d s l : Word) (hl : l ≠ 0) :
    ctorsCopyW (n + 1) m d s l =
      ctorsCopyW n (m.set64 IW d (rdW (m.arr64 IW) s + 2)) (d + 1) (s + 1) (l - 1) := by
  rw [ctorsCopyW.arm2 (hc1 := hl)]; cases ctorsCopyW n _ _ _ _ <;> rfl

/-- **What `member_ctors_copy` leaves**: each member pointer plus `2`, the records below `d`. -/
theorem ctorsCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), ctorsCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ b : TieredArray, b ≠ ↑IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) + 2)
      else (m.arr64 IW)[i]? := fun m m' d s l h hsd hd hsz =>
  ipCopyW_get (fun n m d s l => ctorsCopyW n m d s l) (fun _ x => x + 2)
    (fun _ _ => True)
    (fun _ _ _ _ => by simp [ctorsCopyW]) (ctorsCopyW.arm1 · · · · ·) (ctorsCopyW_step · · · · ·)
    (fun _ _ _ _ _ => rfl) (fun _ _ h => h) n m m' d s l h hsd hd hsz (fun _ _ => trivial)

/-- The lookups `block_shape_member_ctors` takes. -/
structure McLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "member_ctors_copy" = some memberCtorsCopy
  hp : p.lookup "block_shape_member_ctors" = some blockShapeMemberCtors

/-- **`block_shape_member_ctors(p)`'s model `mctorsW`** (generated). -/
l_model blockShapeMemberCtors_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_ctors_copy" = some memberCtorsCopy)
    (hp : p.lookup "block_shape_member_ctors" = some blockShapeMemberCtors)
  fns [hp ↦ mctorsW list]
  specs [iwAlloc_specW p ha n, memberCtorsCopy_spec p hc n]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- **`block_shape_member_ctors` is `BlockShape.memberCtors`**: the new `IW` slice holds pointers
to the members' constructor headers, decoded with their bounds (from the members' `decMSB`). -/
theorem mctorsW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : mctorsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size)
    (hmB : DecB (fun m => decAt m (decPL m (decMSB m)) p.toNat) m bs.members)
    (hsl : ShapeSl m p) :
    r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    PSlR decCNSB (bs.members.map (·.ctors)) (rdW (m.arr64 CTL) 200) (UInt64.ofNat bs.k) m' ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ iwTop m' ≤ (m.arr64 IW).size := by
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (show decAt (truncM m) _ p.toNat = some bs.members from hmB)
  have hlen := decPL_length (truncM m) hg
  have hk : bs.k = l := by rw [BlockShape.k, hlen]
  obtain ⟨hpo, hoN⟩ := acTr ho
  obtain ⟨hpl, hlN⟩ := acTr hl
  obtain ⟨ho', hob⟩ := iwN_rdW hoN (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hlN (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e1' : (p + 1).toNat = p.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [L.ofNat_toNat] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hsrc' : o + l ≤ iwTop m := hsl.1 o l hoN hlN
  rcases n with _ | n
  · simp [mctorsW] at h
  rw [mctorsW.arm1, hl'] at h
  rcases hal : allocW m (UInt64.ofNat l) with _ | ⟨q, m1⟩
  · simp [hal, mctorsW.k_iw_alloc.none] at h
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  rw [hal, mctorsW.k_iw_alloc.arm1] at h
  subst hq' hm1
  have hIW := allocMem_IW m (UInt64.ofNat l)
  rw [hIW, ho', hl'] at h
  rcases hcp : ctorsCopyW n (allocMem m (UInt64.ofNat l)) (rdW (m.arr64 CTL) 200)
      (UInt64.ofNat o) (UInt64.ofNat l) with _ | m2
  · simp [hcp, mctorsW.k_member_ctors_copy.none] at h
  simp only [hcp, mctorsW.k_member_ctors_copy.arm1, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hqt : iwTop m = q.toNat := by simp only [iwTop, hqq]
  obtain ⟨hA, hS, hG⟩ := ctorsCopyW_get n _ _ _ _ _ hcp
    (by rw [hoo, hll]; omega) (by rw [hIW, hll]; omega) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = q + UInt64.ofNat l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + UInt64.ofNat l).toNat = q.toNat + l := by
    rw [UInt64.toNat_add]; simp [hll]; omega
  have hgr : IWGrow m m2 := by
    refine iwGrow_of_frame hfr (N := UInt64.ofNat l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · rw [hqt, hll]; omega
    · intro i hi
      rw [hqt] at hi
      rw [hG, ite_eq_right (by omega)]
  have htop' : iwTop m2 = q.toNat + l := by simp only [iwTop, htop, hsum]
  refine ⟨?_, ⟨?_, ?_⟩, hgr, hfr, by rw [htop']; omega⟩
  · have : rdW (m2.arr64 IW) (p + 1) = UInt64.ofNat l := by
      rw [← hl']; simp only [rdW]; rw [hG, ite_eq_right (by rw [e1']; omega)]
    rw [this, hk]
  · show decPL (truncM m2) (decCNSB (truncM m2)) q.toNat (UInt64.ofNat bs.k).toNat =
      some (bs.members.map (·.ctors))
    have hxs : (bs.members.map (·.ctors)).length = (UInt64.ofNat bs.k).toNat := by
      simp [hk, hll, hlen]
    rw [← hxs]
    refine decPL_of_get (m := truncM m2) _ _ _ fun j hj => ?_
    have hj' : j < l := by simp only [List.length_map] at hj; omega
    obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg j hj'
    have hy' : bs.members[j]'(by omega) = y := by
      simpa [List.getElem?_eq_getElem (show j < bs.members.length by omega)] using hget
    have hcn := (decMSB_some hy).2
    obtain ⟨co, cl, -, hcl, -, -⟩ := decCNSB_bound (m := m) (q := v + 2) hcn
    have hv3 := (acTr hcl).1
    obtain ⟨-, hvN⟩ := acTr hv
    obtain ⟨hvrd, -⟩ := iwN_rdW hvN (by omega)
    have hGj := hG (q.toNat + j)
    rw [ite_eq_left (by rw [hll]; omega), show q.toNat + j - q.toNat = j by omega, hoo, hvrd] at hGj
    refine ⟨v + 2, ?_, ?_⟩
    · rw [iwN_truncM (by rw [htop']; omega)]
      simp only [iwN, nat?, iwA, aread_apply, hGj, Option.map_some, Option.some.injEq]
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; simp; omega
    · simp only [List.getElem_map, hy']
      exact (show DecB (fun m => decCNSB m (v + 2)) m y.ctors from hcn).grow (decCNSB_mono _) hgr
  · rw [hk, hll, htop']; exact Nat.le_refl _

end L.Ind

end
