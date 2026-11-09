module

public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Front.StateDR
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.RecGenSpec.StabDecCRDecB
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndDecStab
import ConAgua.Arena.DeclAndPinIndDec
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# A block's `EREC` pointer slice copied to `IW` (`er_to_iw`) (lane `ronsync2`, stage 3)

`er_to_iw` of a slice of constant-record pointers: the copy at the old `IW` top (`erToIwW_ptrs`),
under `StageR` a pointer slice below the tops decoding to the block (`erToIwW_blkR`). Used by the
`And` pin's inductive arm and the pinned basis blocks' entry points.
-/

noncomputable section

namespace L.Ind

open ConRon.Arena L.Arena

/-- The decoder of a slice of constant-record pointers (`basisDec`'s, as a `PSlR` decoder). -/
abbrev ciF : Mem → Nat → Option IConstantInfo := fun m q => decCI (erA m) q

theorem ciF_mono : ∀ q, OMono (fun m => ciF m q) := fun _ => ⟨fun _ _ _ he h => he.2.decCI h⟩

theorem decB_ciF {m : Mem} {q : Nat} {x : IConstantInfo} :
    DecB (fun m => ciF m q) m x ↔ decCI (erecP m) q = some x := by
  show decCI (erA (truncM m)) q = some x ↔ _
  rw [truncM_erA]; rfl

/-- **`er_to_iw` over any `EREC` slice whose words exist**: the copy at the old `IW` top. -/
theorem erToIwW_ptrs {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hrd : ∀ j < l.toNat, ∃ v, erecP m (o.toNat + j) = some v) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    (∀ j < l.toNat, iwA m' ((rdW (m.arr64 CTL) 200).toNat + j) = erecP m (o.toNat + j)) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' ∧ iwTop m' ≤ (m'.arr64 IW).size := by
  have hol : o.toNat + l.toNat ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | hpos
    · have := o.toNat_lt; omega
    · obtain ⟨v, hv⟩ := hrd (l.toNat - 1) (by omega)
      have : o.toNat + (l.toNat - 1) < 2 ^ 64 := by
        rcases Nat.lt_or_ge (o.toNat + (l.toNat - 1)) (2 ^ 64) with h' | h'
        · exact h'
        · unfold erecP at hv; rw [if_neg (by omega)] at hv; cases hv
      omega
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2 <;> simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hR : ∀ a, erRd (allocMem m l) a = erRd m a := fun a => by
    simp only [allocMem, erRd]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]
  have hEE : (allocMem m l).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨hA, hS, hG⟩ := erCopyW_get (n - 1) _ _ _ _ _ hcp hol
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m l).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨v, hv⟩ := hrd j hj
    simp only [iwA, aread_apply, hG]
    rw [ite_eq_left (by omega), hR, show q.toNat + j - q.toNat = j by omega]
    have e : (UInt64.ofNat (o.toNat + j)).toNat = o.toNat + j := by simp; omega
    have hv' : erecP m (UInt64.ofNat (o.toNat + j)).toNat = some v := by rw [e]; exact hv
    rw [(erRd_of_erecP hv').1, hv]
  · refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · rw [hA EREC (by decide), hEE]
  · simp only [iwTop, htop, hsum]
  · simp only [iwTop, htop, hsum, hS]; omega

/-- A slice of constant records over a reader stays decoded as the reader grows. -/
theorem decCIsR_ext {a b : Nat → Option Word} (he : ArrExt a b) {o l : Nat}
    {xs : List IConstantInfo} (h : L.Front.decCIsR a o l = some xs) :
    L.Front.decCIsR b o l = some xs := by
  refine mapM_imp _ _ h fun j _ y hy => ?_
  simp only [bind, Option.bind_eq_some_iff] at hy ⊢
  obtain ⟨v, hv, hy⟩ := hy
  exact ⟨v, he.nat? hv, he.decCI hy⟩

/-- **`er_to_iw` of a block's `EREC` pointer slice** under `StageR`: the `IW` copy decodes, below
the tops, to the block. -/
theorem erToIwW_blkR {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {o l : Word}
    {r : List Word} {block : List IConstantInfo}
    (h : erToIwW n m o l = some (r, m')) (hS : StageR vis fe m a)
    (hd : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ r = [r.headD 0, l] ∧
      PSlR ciF block (r.headD 0) l m' := by
  have hrd : ∀ j < l.toNat, ∃ v, erecP m (o.toNat + j) = some v := by
    intro j hj
    have := L.Ind.mapM_opt_get _ (List.range l.toNat) block hd j (by simpa using hj)
    simp only [List.getElem_range] at this
    cases e : erecP m (o.toNat + j) with
    | none => simp [nat?, e] at this
    | some v => exact ⟨v, rfl⟩
  obtain ⟨hr, hw, hg, hf, -, ht, hroom⟩ := erToIwW_ptrs h hS.iw.iwSize hS.iw.ctl hrd
  have hEr : erecP m' = erecP m := erecP_frame hf (by decide) (by decide) (by decide) (by decide)
  subst hr
  refine ⟨⟨CheckR.frame_iw hf hS.check, hS.iw.of_iw hf hroom⟩, hg, hf, rfl, ?_, by simp; omega⟩
  show decPL (truncM m') (fun q => decCI (erA (truncM m')) q) _ _ = some block
  simp only [List.headD_cons]
  rw [decPL_truncM_of (f := fun q => decCI (erecP m') q) (fun j hj => by omega)
    (fun _ _ _ _ => by rw [truncM_erA]; rfl)]
  rw [← hd]
  unfold decPL L.Front.decCIsR
  refine mapM_congr_range _ fun j hj => ?_
  have hj' := List.mem_range.mp hj
  simp only [iwN, nat?, hw j hj', hEr]


end L.Ind
