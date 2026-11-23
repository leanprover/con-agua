module

public import ConAgua.Arena.IotaRelRefA

@[expose] public section

/-!
# The ι reading rule, part 2: the lists and a rule's parts (lane ronsync8)

`list_lvl_eq`, `list_ann_eq` (loops over two `IW` slices) against `listLvlEq`, `listAnnEq`;
`params_ann_eq` against `paramsAnnEq`; `iota_parts_rel` against `iotaPartsRel` (the statements
of `IotaRelRef.lean`).
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

section lists
variable {p : Prog} {env : ConLeche.Env} {fe feR : IFEnv} {vis : Word}

/-- The `j`-th word of a decoded `IW` handle slice, at L's address `o + j`. -/
theorem irSliceAt {m : Mem} {o l j : Word} {xs : List EIdx} (h : decHL m o.toNat l.toNat = some xs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hj : j < l) :
    HW (rdW (m.arr64 IW) (o + j)) ∧ xs.drop j.toNat = decE (rdW (m.arr64 IW) (o + j)) :: xs.drop (j + 1).toNat := by
  have hj' : j.toNat < l.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨w, hw, hlt, hx⟩ := decHL_word h hsz j.toNat hj'
  rw [show (j.toNat).toUInt64 = j from UInt64.toNat_inj.mp (by simp)] at hw
  subst hw
  have hlen : xs.length = l.toNat := decHL_length m h
  have hj1 : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
  refine ⟨hlt, ?_⟩
  rw [hj1, List.drop_eq_getElem_cons (by omega)]
  rw [List.getElem?_eq_getElem (by omega)] at hx
  rw [Option.some.inj hx]; rfl

/-- **`list_lvl_eq`'s loop from position `j`** refines `listLvlEq` on the slices' tails. -/
theorem listLvlEq_loop (P : IotaRelProg p) (hf : p.lookup "list_lvl_eq" = some listLvlEqL)
    {ao al bo bl : Word} {as bs : List EIdx} :
    ∀ (k : Nat) (m m' : Mem) (a : AState) (j : Word) (r : List Word),
      listLvlEqW.loop1 p k m ao al bo bl j = some (r, m') → StageR vis feR m a →
      ConRon.Bridge.CheckOK false env fe a →
      decHL m ao.toNat al.toNat = some as → ao.toNat + al.toNat ≤ iwTop m →
      decHL m bo.toNat bl.toNat = some bs → bo.toNat + bl.toNat ≤ iwTop m → j ≤ al → j ≤ bl →
      ∃ b a', (listLvlEq (as.drop j.toNat) (bs.drop j.toNat)).run a = .ok (b, a') ∧
        StageR vis feR m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a'
  | 0, m, m', a, j, r, hW, _, _, _, _, _, _, _, _ => by rw [listLvlEqW.loop1.eq_1] at hW; cases hW
  | k + 1, m, m', a, j, r, hW, hS, hok, ha, hab, hb, hbb, hja, hjb => by
    have hlen1 : as.length = al.toNat := decHL_length m ha
    have hlen2 : bs.length = bl.toNat := decHL_length m hb
    by_cases hc : j < al ∧ j < bl
    · rw [listLvlEqW.loop1.arm1 _ _ _ _ _ _ _ _ hc] at hW
      have hsz := hS.iw.iwSize
      obtain ⟨hx, ex⟩ := irSliceAt ha hsz hc.1
      obtain ⟨hy, ey⟩ := irSliceAt hb hsz hc.2
      rw [ex, ey]
      rcases c1 : callW p k "expr_lvl_eq"
          [rdW (m.arr64 IW) (ao + j), rdW (m.arr64 IW) (bo + j), CWF] m with _ | ⟨r1, m1⟩
      · rw [c1, listLvlEqW.k_expr_lvl_eq.eq_1] at hW; cases hW
      obtain ⟨b1, a1, h1, hS1, hg1, hd1, k1⟩ := exprLvlEq_rel P.ele P.ev P.lvl c1 hS hok hx hy
      rw [CWF_eq] at h1
      simp only [listLvlEq]
      rw [StateT.run_bind, h1, except_ok_bind]
      by_cases hz : r1.headD 0 = 0
      · rw [c1, listLvlEqW.k_expr_lvl_eq.arm1 _ _ _ _ _ _ _ _ _ hz] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hb1 : b1 = false := by have := hd1.1; rw [hz] at this; simpa using this.symm
        subst hb1
        exact ⟨false, a1, rfl, hS1, hg1, by simp [decW0B], k1⟩
      rw [c1, listLvlEqW.k_expr_lvl_eq.arm2 _ _ _ _ _ _ _ _ _ hz] at hW
      have hb1 : b1 = true := by rw [← hd1.1]; exact bne_iff_ne.mpr hz
      subst hb1
      simp only [ite_true]
      have hj1a : j + 1 ≤ al := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hc.1
        simp; have := al.toNat_lt; omega
      have hj1b : j + 1 ≤ bl := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hc.2
        simp; have := bl.toNat_lt; omega
      obtain ⟨b2, a2, h2, hS2, hg2, hd2, k2⟩ := listLvlEq_loop P hf k m1 m' a1 (j + 1) r hW hS1 k1.ok
        (decHL_grow' hg1 hab ha) (Nat.le_trans hab hg1.iw) (decHL_grow' hg1 hbb hb)
        (Nat.le_trans hbb hg1.iw) hj1a hj1b
      exact ⟨b2, a2, h2, hS2, hg1.trans hg2, hd2, k1.trans k2⟩
    rw [listLvlEqW.loop1.arm2 _ _ _ _ _ _ _ _ hc] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨decide (al = bl), a, ?_, hS, IWGrow.refl _, ?_, ConRon.Bridge.CoreStep.refl hok⟩
    · have hja' := UInt64.le_iff_toNat_le.mp hja
      have hjb' := UInt64.le_iff_toNat_le.mp hjb
      have hend : j = al ∨ j = bl := by
        by_cases h : j < al
        · exact .inr (UInt64.le_antisymm hjb (UInt64.not_lt.mp fun h' => hc ⟨h, h'⟩))
        · exact .inl (UInt64.le_antisymm hja (UInt64.not_lt.mp h))
      rcases hend with rfl | rfl
      · rw [List.drop_eq_nil_of_le (by omega)]
        by_cases e : j = bl
        · subst e; rw [List.drop_eq_nil_of_le (by omega)]; simp [listLvlEq]; rfl
        · have : j.toNat < bl.toNat := by
            have : j.toNat ≠ bl.toNat := fun h => e (UInt64.toNat_inj.mp h)
            omega
          rw [List.drop_eq_getElem_cons (by omega)]
          simp [listLvlEq, e]; rfl
      · rw [List.drop_eq_nil_of_le (as := bs) (i := j.toNat) (by omega)]
        by_cases e : al = j
        · subst e; rw [List.drop_eq_nil_of_le (by omega)]; simp [listLvlEq]; rfl
        · have : j.toNat < al.toNat := by
            have : al.toNat ≠ j.toNat := fun h => e (UInt64.toNat_inj.mp h)
            omega
          rw [List.drop_eq_getElem_cons (by omega)]
          simp [listLvlEq, e]; rfl
    · by_cases e : al = bl <;> simp [decW0B, e]

/-- **`list_ann_eq`'s loop from position `j`** refines `listAnnEq feR` on the slices' tails. -/
theorem listAnnEq_loop (P : IotaRelProg p) (hf : p.lookup "list_ann_eq" = some listAnnEqL)
    {ao al bo bl : Word} {as bs : List EIdx} :
    ∀ (k : Nat) (m m' : Mem) (a : AState) (j : Word) (r : List Word),
      listAnnEqW.loop1 p k m vis ao al bo bl j = some (r, m') → StageR vis feR m a →
      ConRon.Bridge.CheckOK false env fe a →
      decHL m ao.toNat al.toNat = some as → ao.toNat + al.toNat ≤ iwTop m →
      decHL m bo.toNat bl.toNat = some bs → bo.toNat + bl.toNat ≤ iwTop m → j ≤ al → j ≤ bl →
      ∃ b a', (listAnnEq feR (as.drop j.toNat) (bs.drop j.toNat)).run a = .ok (b, a') ∧
        StageR vis feR m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a'
  | 0, m, m', a, j, r, hW, _, _, _, _, _, _, _, _ => by rw [listAnnEqW.loop1.eq_1] at hW; cases hW
  | k + 1, m, m', a, j, r, hW, hS, hok, ha, hab, hb, hbb, hja, hjb => by
    have hlen1 : as.length = al.toNat := decHL_length m ha
    have hlen2 : bs.length = bl.toNat := decHL_length m hb
    by_cases hc : j < al ∧ j < bl
    · rw [listAnnEqW.loop1.arm1 _ _ _ _ _ _ _ _ _ hc] at hW
      have hsz := hS.iw.iwSize
      obtain ⟨hx, ex⟩ := irSliceAt ha hsz hc.1
      obtain ⟨hy, ey⟩ := irSliceAt hb hsz hc.2
      rw [ex, ey]
      rcases c1 : callW p k "ann_eq"
          [vis, rdW (m.arr64 IW) (ao + j), rdW (m.arr64 IW) (bo + j), CWF] m with _ | ⟨r1, m1⟩
      · rw [c1, listAnnEqW.k_ann_eq.eq_1] at hW; cases hW
      obtain ⟨b1, a1, h1, hS1, hg1, hd1, k1⟩ := annEq_rel P c1 hS hok hx hy
      rw [CWF_eq] at h1
      simp only [listAnnEq]
      rw [StateT.run_bind, h1, except_ok_bind]
      by_cases hz : r1.headD 0 = 0
      · rw [c1, listAnnEqW.k_ann_eq.arm1 _ _ _ _ _ _ _ _ _ _ hz] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hb1 : b1 = false := by have := hd1.1; rw [hz] at this; simpa using this.symm
        subst hb1
        exact ⟨false, a1, rfl, hS1, hg1, by simp [decW0B], k1⟩
      rw [c1, listAnnEqW.k_ann_eq.arm2 _ _ _ _ _ _ _ _ _ _ hz] at hW
      have hb1 : b1 = true := by rw [← hd1.1]; exact bne_iff_ne.mpr hz
      subst hb1
      simp only [ite_true]
      have hj1a : j + 1 ≤ al := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hc.1
        simp; have := al.toNat_lt; omega
      have hj1b : j + 1 ≤ bl := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hc.2
        simp; have := bl.toNat_lt; omega
      obtain ⟨b2, a2, h2, hS2, hg2, hd2, k2⟩ := listAnnEq_loop P hf k m1 m' a1 (j + 1) r hW hS1 k1.ok
        (decHL_grow' hg1 hab ha) (Nat.le_trans hab hg1.iw) (decHL_grow' hg1 hbb hb)
        (Nat.le_trans hbb hg1.iw) hj1a hj1b
      exact ⟨b2, a2, h2, hS2, hg1.trans hg2, hd2, k1.trans k2⟩
    rw [listAnnEqW.loop1.arm2 _ _ _ _ _ _ _ _ _ hc] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨decide (al = bl), a, ?_, hS, IWGrow.refl _, ?_, ConRon.Bridge.CoreStep.refl hok⟩
    · have hja' := UInt64.le_iff_toNat_le.mp hja
      have hjb' := UInt64.le_iff_toNat_le.mp hjb
      have hend : j = al ∨ j = bl := by
        by_cases h : j < al
        · exact .inr (UInt64.le_antisymm hjb (UInt64.not_lt.mp fun h' => hc ⟨h, h'⟩))
        · exact .inl (UInt64.le_antisymm hja (UInt64.not_lt.mp h))
      rcases hend with rfl | rfl
      · rw [List.drop_eq_nil_of_le (by omega)]
        by_cases e : j = bl
        · subst e; rw [List.drop_eq_nil_of_le (by omega)]; simp [listAnnEq]; rfl
        · have : j.toNat < bl.toNat := by
            have : j.toNat ≠ bl.toNat := fun h => e (UInt64.toNat_inj.mp h)
            omega
          rw [List.drop_eq_getElem_cons (by omega)]
          simp [listAnnEq, e]; rfl
      · rw [List.drop_eq_nil_of_le (as := bs) (i := j.toNat) (by omega)]
        by_cases e : al = j
        · subst e; rw [List.drop_eq_nil_of_le (by omega)]; simp [listAnnEq]; rfl
        · have : j.toNat < al.toNat := by
            have : al.toNat ≠ j.toNat := fun h => e (UInt64.toNat_inj.mp h)
            omega
          rw [List.drop_eq_getElem_cons (by omega)]
          simp [listAnnEq, e]; rfl
    · by_cases e : al = bl <;> simp [decW0B, e]


/-- **`list_lvl_eq(ao, al, bo, bl)` refines `listLvlEq as bs`** (two decoded `IW` slices). -/
@[refines ConRon.Arena.listLvlEq]
theorem listLvlEq_rel (P : IotaRelProg p) (hf : p.lookup "list_lvl_eq" = some listLvlEqL) {n : Nat}
    {m m' : Mem} {a : AState} {ao al bo bl : Word} {r : List Word} {as bs : List EIdx}
    (hc : callW p n "list_lvl_eq" [ao, al, bo, bl] m = some (r, m')) (hS : StageR vis feR m a)
    (hok : ConRon.Bridge.CheckOK false env fe a)
    (ha : decHL m ao.toNat al.toNat = some as) (hab : ao.toNat + al.toNat ≤ iwTop m)
    (hb : decHL m bo.toNat bl.toNat = some bs) (hbb : bo.toNat + bl.toNat ≤ iwTop m) :
    ∃ b a', (listLvlEq as bs).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧ IWGrow m m' ∧
      decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (listLvlEq_specW p hf n _ ao al bo bl) hc
  rcases n with _ | n
  · rw [listLvlEqW.eq_1] at hW; cases hW
  rw [listLvlEqW.arm1] at hW
  simpa using listLvlEq_loop P hf (n + 1) m _ a 0 r hW hS hok ha hab hb hbb UInt64.zero_le
    UInt64.zero_le

/-- **`list_ann_eq(vis, ao, al, bo, bl)` refines `listAnnEq feR as bs`**. -/
@[refines ConRon.Arena.listAnnEq]
theorem listAnnEq_rel (P : IotaRelProg p) (hf : p.lookup "list_ann_eq" = some listAnnEqL) {n : Nat}
    {m m' : Mem} {a : AState} {ao al bo bl : Word} {r : List Word} {as bs : List EIdx}
    (hc : callW p n "list_ann_eq" [vis, ao, al, bo, bl] m = some (r, m')) (hS : StageR vis feR m a)
    (hok : ConRon.Bridge.CheckOK false env fe a)
    (ha : decHL m ao.toNat al.toNat = some as) (hab : ao.toNat + al.toNat ≤ iwTop m)
    (hb : decHL m bo.toNat bl.toNat = some bs) (hbb : bo.toNat + bl.toNat ≤ iwTop m) :
    ∃ b a', (listAnnEq feR as bs).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧ IWGrow m m' ∧
      decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (listAnnEq_specW p hf n _ vis ao al bo bl) hc
  rcases n with _ | n
  · rw [listAnnEqW.eq_1] at hW; cases hW
  rw [listAnnEqW.arm1] at hW
  simpa using listAnnEq_loop P hf (n + 1) m _ a 0 r hW hS hok ha hab hb hbb UInt64.zero_le
    UInt64.zero_le

end lists

end L.Ind
