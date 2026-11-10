module

public import ConAgua.Front.IndInstallRefine2
import ConAgua.L.WordOff

@[expose] public section

/-!
# `install_ind_d` refines `installIndD`, IV: the three install loops

`inst_types`, `inst_ctors` and `inst_recs` are one loop (`instGo`): for the `j`-th record, its
constant record allocated above `DLP`'s top (`ind_type`/`ind_ctor`/`ind_rec`), its pointer written
at `DLP[bo + j]` (a slot allocated before, below the top). `instGo_twin`: every slot points to a
record that decodes as the twin's constant (`RecAt`), and no other word below the top changed.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)


namespace L.Front.Ind

/-- The install loops: record `j` by `R` at `ptr m j`, its pointer at `bo + j`. -/
def instGo (R : Nat → Mem → Word → Option (Word × Mem)) (ptr : Mem → Word → Word) :
    Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, bo, tn, j =>
    if tn ≤ j then some m
    else allocK (fun q m₁ => instGo R ptr n (m₁.set64 DLP (bo + j) q) bo tn (j + 1)) (R n m (ptr m j))

theorem instTypesW_eq (b : Array UInt8) (to : Word) :
    ∀ n m bo tn j, instTypesW b n m bo to tn j =
      instGo (fun _ m p => typeW b m p) (fun _ j => to + 11 * j) n m bo tn j
  | 0, _, _, _, _ => by rw [instTypesW.eq_1]; rfl
  | n + 1, m, bo, tn, j => by
    simp only [instGo]
    by_cases hc : tn ≤ j
    · rw [instTypesW.arm1 (hc1 := hc), ite_eq_left hc]
    · rw [instTypesW.arm2 (hc1 := hc), ite_eq_right hc]
      cases h : typeW b m (to + 11 * j) with
      | none => rw [instTypesW.k_ind_type.none]; rfl
      | some x =>
        obtain ⟨q, m₁⟩ := x
        rw [instTypesW.k_ind_type.arm1, instTypesW.k_inst_types_id, instTypesW_eq b to n]; rfl

theorem instCtorsW_eq (b : Array UInt8) (oo : Word) :
    ∀ n m bo on j, instCtorsW b n m bo oo on j =
      instGo (fun _ m p => ctorRW b m p) (fun m j => rdW (m.arr64 IFL) (oo + j)) n m bo on j
  | 0, _, _, _, _ => by rw [instCtorsW.eq_1]; rfl
  | n + 1, m, bo, on, j => by
    simp only [instGo]
    by_cases hc : on ≤ j
    · rw [instCtorsW.arm1 (hc1 := hc), ite_eq_left hc]
    · rw [instCtorsW.arm2 (hc1 := hc), ite_eq_right hc]
      cases h : ctorRW b m (rdW (m.arr64 IFL) (oo + j)) with
      | none => rw [instCtorsW.k_ind_ctor.none]; rfl
      | some x =>
        obtain ⟨q, m₁⟩ := x
        rw [instCtorsW.k_ind_ctor.arm1, instCtorsW.k_inst_ctors_id, instCtorsW_eq b oo n]; rfl

theorem instRecsW_eq (b : Array UInt8) (ro : Word) :
    ∀ n m bo rn j, instRecsW b n m bo ro rn j =
      instGo (fun n m p => recRW b n m p) (fun _ j => ro + 11 * j) n m bo rn j
  | 0, _, _, _, _ => by rw [instRecsW.eq_1]; rfl
  | n + 1, m, bo, rn, j => by
    simp only [instGo]
    by_cases hc : rn ≤ j
    · rw [instRecsW.arm1 (hc1 := hc), ite_eq_left hc]
    · rw [instRecsW.arm2 (hc1 := hc), ite_eq_right hc]
      cases h : recRW b n m (ro + 11 * j) with
      | none => rw [instRecsW.k_ind_rec.none]; rfl
      | some x =>
        obtain ⟨q, m₁⟩ := x
        rw [instRecsW.k_ind_rec.arm1, instRecsW.k_inst_recs_id, instRecsW_eq b ro n]; rfl

/-- **The install loop against the twin's `mapM`.** `R` at the `k`-th pointer is the twin's `f`
on the `k`-th element (`hR`, for every memory that only differs from `m₀` in `DLP`). -/
theorem instGo_twin {α : Type} [Inhabited α] {st : StateD} (a : AState) (xs : List α) (f : α → AM IConstantInfo)
    (R : Nat → Mem → Word → Option (Word × Mem)) (ptr : Mem → Word → Word) (m₀ : Mem) (bo tn : Word)
    (htn : tn.toNat = xs.length)
    (hR : ∀ n m k q m', LkR m st → MemFrame [DLP] [] m₀ m → k < xs.length →
      R n m (ptr m (UInt64.ofNat k)) = some (q, m') →
      (f xs[k]!).run a = .ok (resOf (f xs[k]!) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
        LkR m' st ∧ RecAt m' q.toNat (resOf (f xs[k]!) a)) :
    ∀ n (m m' : Mem) (j : Word), LkR m st → MemFrame [DLP] [] m₀ m → j.toNat ≤ xs.length →
      1 ≤ bo.toNat → bo.toNat + xs.length ≤ topN m DLP + 1 →
      instGo R ptr n m bo tn j = some m' →
      MemFrame [DLP] [] m m' ∧ topN m DLP ≤ topN m' DLP ∧ LkR m' st ∧
      (∀ i, 1 ≤ i → i ≤ topN m DLP → (i < bo.toNat + j.toNat ∨ bo.toNat + xs.length ≤ i) →
        wd m' DLP i = wd m DLP i) ∧
      ∀ k, k < xs.length → j.toNat ≤ k →
        (f xs[k]!).run a = .ok (resOf (f xs[k]!) a, a) ∧ topN m DLP < (wd m' DLP (bo.toNat + k)).toNat ∧
        RecAt m' (wd m' DLP (bo.toNat + k)).toNat (resOf (f xs[k]!) a)
  | 0, _, _, _, _, _, _, _, _, h => by simp [instGo] at h
  | n + 1, m, m', j, hL, hf, hj, hbo1, hbo, h => by
    have hps := hL.psize
    have hpt := hL.ptop
    simp only [instGo] at h
    split at h
    · rename_i hlj
      cases h
      have : xs.length ≤ j.toNat := by rw [← htn]; exact UInt64.le_iff_toNat_le.mp hlj
      exact ⟨MemFrame.refl _ _ _, Nat.le_refl _, hL, fun _ _ _ _ => rfl, fun k hk hk' => by omega⟩
    rename_i hlj
    have hjl : j.toNat < xs.length := by
      rw [← htn]; exact Classical.byContradiction fun h' => hlj (UInt64.le_iff_toNat_le.mpr (by omega))
    rcases h1 : R n m (ptr m j) with _ | ⟨q, m₁⟩ <;> simp only [h1, allocK, reduceCtorEq] at h
    have hj' : UInt64.ofNat j.toNat = j := UInt64.ofNat_toNat
    obtain ⟨S1, S2, S3, S4, S5⟩ := hR n m j.toNat q m₁ hL hf hjl (by rw [hj']; exact h1)
    have hbj : (bo + j).toNat = bo.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
    have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_of_lt _ _ (by simp; omega)
    have hs1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := S2.size DLP
    have ht1 : topN (m₁.set64 DLP (bo + j) q) DLP = topN m₁ DLP := by
      unfold topN; rw [wd_set_ne _ _ _ _ _ (by omega)]
    have hfr1 : MemFrame [DLP] [] m₁ (m₁.set64 DLP (bo + j) q) := MemFrame.set64 _ DLP (by decide) _ _
    have hL1 : LkR (m₁.set64 DLP (bo + j) q) st := S4.frame hfr1 (by
      rw [ht1, hfr1.size DLP]; exact S4.ptop)
    have htm : topN m DLP ≤ topN m₁ DLP := S2.top
    obtain ⟨I1, I2, I3, I4, I5⟩ := instGo_twin a xs f R ptr m₀ bo tn htn hR n _ m' (j + 1) hL1
      (hf.trans (S2.frame.trans hfr1)) (by omega) hbo1 (by rw [ht1]; omega) h
    rw [hj1] at I4 I5
    rw [ht1] at I2 I4
    have hslot : wd m' DLP (bo.toNat + j.toNat) = q := by
      rw [I4 _ (by omega) (by omega) (.inl (by omega)), ← hbj,
        wd_set_eq _ _ _ _ _ rfl (by rw [hbj, hs1]; omega)]
    refine ⟨S2.frame.trans (hfr1.trans I1), by omega, I3, fun i h1 h2 h3 => ?_, fun k hk hk' => ?_⟩
    · rw [I4 i h1 (by omega) (by omega), wd_set_ne _ _ _ _ _ (by omega), S2.keep i h1 h2]
    · by_cases hkj : k = j.toNat
      · subst hkj
        rw [hslot]
        refine ⟨S1, by omega, ?_⟩
        refine (S5.keep (m' := m₁.set64 DLP (bo + j) q) (by rw [ht1]; exact Nat.le_refl _) (fun i h1 h2 => by
          rw [wd_set_ne _ _ _ _ _ (by omega)])).keep (by rw [ht1]; exact I2) (fun i h1 h2 => ?_)
        rw [ht1] at h2
        exact I4 i (by omega) (by omega) (.inr (by omega))
      · obtain ⟨T1, T2, T3⟩ := I5 k hk (by omega)
        exact ⟨T1, by omega, T3⟩

end L.Front.Ind
