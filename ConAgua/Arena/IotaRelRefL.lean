module

public import ConAgua.Arena.IotaRelRefA
public import ConAgua.Arena.IlpRd
public import ConAgua.Arena.IndPartsSpec.EqW
public import ConAgua.Arena.RecLayout.RuleDec

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

/-- **`params_ann_eq(vis, cnP, q, pdO, pdL)` refines `paramsAnnEq feR cnP cv pd`**. -/
@[refines ConRon.Arena.paramsAnnEq]
theorem paramsAnnEq_rel (P : IotaRelProg p) {n : Nat} {m m' : Mem} {a : AState}
    {cnP q pdO pdL : Word} {r : List Word} {cv : IConstantVal} {pd : List EIdx}
    (hc : callW p n "params_ann_eq" [vis, cnP, q, pdO, pdL] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a)
    (hcv : decCV (erecP m) q.toNat = some cv)
    (hpd : decHL m pdO.toNat pdL.toNat = some pd) (hpdb : pdO.toNat + pdL.toNat ≤ iwTop m) :
    ∃ b a', (paramsAnnEq feR cnP.toNat cv pd).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧
      IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (paramsAnnEq_specW p P.pae n _ vis cnP q pdO pdL) hc
  rcases n with _ | n
  · rw [paramsAnnEqW.eq_1] at hW; cases hW
  rw [paramsAnnEqW.arm1] at hW
  obtain ⟨-, -, -, -, hty, hhw⟩ := decCV_rd (erRdOK m) hcv
  rcases c1 : callW p n "strip_pis" [cnP, erRd m (q + CV.type)] m with _ | ⟨r1, m1⟩
  · rw [c1, paramsAnnEqW.k_strip_pis.none] at hW; cases hW
  obtain ⟨x1, a1, h1, hS1, hg1, hd1⟩ :=
    stripF_pis_ok vis feR cnP _ hhw m m1 a r1 (stripF_of_callW P.strip c1) hS
  have ha1 : a1 = a := stripPis_st _ _ _ _ _ h1
  subst ha1
  simp only [paramsAnnEq]
  rw [hty, StateT.run_bind, h1, except_ok_bind]
  rcases x1 with _ | ⟨rd, rest⟩
  · simp only [decOLE] at hd1
    rw [c1, paramsAnnEqW.k_strip_pis.arm1 _ _ _ _ _ _ _ hd1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a1, rfl, hS1, hg1, by simp [decW0B], ConRon.Bridge.CoreStep.refl hok⟩
  obtain ⟨h1w, ⟨hrd, hrdb⟩, -⟩ := hd1
  rw [c1, paramsAnnEqW.k_strip_pis.arm2 _ _ _ _ _ _ _ (by rw [h1w]; decide)] at hW
  dsimp only
  rcases c2 : callW p n "list_ann_eq" [vis, r1.tail.headD 0, r1.tail.tail.headD 0, pdO, pdL] m1
    with _ | ⟨r2, m2⟩
  · rw [c2, paramsAnnEqW.k_list_ann_eq.none] at hW; cases hW
  rw [c2, paramsAnnEqW.k_list_ann_eq.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [L.getD_one, L.getD_two] at hrd hrdb
  obtain ⟨b2, a2, h2, hS2, hg2, hd2, k2⟩ := listAnnEq_rel P P.lae c2 hS1 hok hrd hrdb
    (decHL_grow' hg1 hpdb hpd) (Nat.le_trans hpdb hg1.iw)
  exact ⟨b2, a2, h2, hS2, hg1.trans hg2, hd2, k2⟩

theorem irMapDecI : ∀ (ws1 ws2 : List Word), (∀ w ∈ ws1, w.toNat < 2 ^ 32) → (∀ w ∈ ws2, w.toNat < 2 ^ 32) →
    ws1.map (decI : Word → EIdx) = ws2.map decI → ws1 = ws2
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [decI_inj (h1 x (by simp)) (h2 y (by simp)) h.1,
      irMapDecI xs ys (fun w hw => h1 w (by simp [hw])) (fun w hw => h2 w (by simp [hw])) h.2]

/-- `sl_eq` on two decoded `IW` handle slices: the memory kept, `1` iff the lists are equal. -/
theorem irSlEq (P : IotaRelProg p) {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    {xs ys : List EIdx} (hc : callW p n "sl_eq" [o1, l1, o2, l2] m = some (r, m'))
    (h1 : decHL m o1.toNat l1.toNat = some xs) (hb1 : o1.toNat + l1.toNat < 2 ^ 64)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat < 2 ^ 64) :
    m' = m ∧ r.headD 0 = if xs = ys then 1 else 0 := by
  obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (slEq_spec p P.sleq n _ o1 l1 o2 l2) hc
  refine ⟨hs' ▸ hm, ?_⟩
  obtain ⟨ws1, hw1, rfl, hl1⟩ := slR_of_decHL m _ _ _ h1 hb1
  obtain ⟨ws2, hw2, rfl, hl2⟩ := slR_of_decHL m _ _ _ h2 hb2
  simp only [UInt64.ofNat_toNat] at hw1 hw2
  rw [eqW_ok n m _ _ _ _ _ ws1 ws2 hw1 hw2 hW]
  have hinj : ws1.map (decI : Word → EIdx) = ws2.map decI ↔ ws1 = ws2 :=
    ⟨irMapDecI ws1 ws2 hl1 hl2, fun e => by rw [e]⟩
  by_cases e : ws1 = ws2 <;> simp [e, hinj]

/-- `decIPAt 0` at seven words, unfolded. -/
theorem irDecIP {m : Mem} {w1 w2 w3 w4 w5 w6 w7 : Word} {x : IIotaParts}
    (h : decIPAt 0 m [w1, w2, w3, w4, w5, w6, w7] x) :
    decHL m w1.toNat w2.toNat = some x.fieldDoms ∧ w1.toNat + w2.toNat ≤ iwTop m ∧
    decHL m w3.toNat w4.toNat = some x.idx ∧ w3.toNat + w4.toNat ≤ iwTop m ∧
    HW w5 ∧ decI w5 = x.us ∧
    decHL m w6.toNat w7.toNat = some x.params ∧ w6.toNat + w7.toNat ≤ iwTop m := by
  obtain ⟨⟨h1, h1b⟩, ⟨h2, h2b⟩, ⟨h3, h3e⟩, ⟨h4, h4b⟩⟩ := h
  exact ⟨h1, h1b, h2, h2b, h3, h3e, h4, h4b⟩

/-- **`iota_parts_rel(vis, cnP, q, r, IIotaParts', IIotaParts, pdO, pdL)` refines
`iotaPartsRel feR cnP cv rl p' p pd`**. -/
@[refines ConRon.Arena.iotaPartsRel]
theorem iotaPartsRel_rel (P : IotaRelProg p) {n : Nat} {m m' : Mem} {a : AState}
    {cnP q rw a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 pdO pdL : Word} {r : List Word}
    {cv : IConstantVal} {rl : IRecRule} {x y : IIotaParts} {pd : List EIdx}
    (hc : callW p n "iota_parts_rel" [vis, cnP, q, rw, a1, a2, a3, a4, a5, a6, a7,
      b1, b2, b3, b4, b5, b6, b7, pdO, pdL] m = some (r, m'))
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a)
    (hx : decIPAt 0 m [a1, a2, a3, a4, a5, a6, a7] x) (hy : decIPAt 0 m [b1, b2, b3, b4, b5, b6, b7] y)
    (hcv : decCV (erecP m) q.toNat = some cv) (hrl : decRule (erecP m) rw.toNat = some rl)
    (hpd : decHL m pdO.toNat pdL.toNat = some pd) (hpdb : pdO.toNat + pdL.toNat ≤ iwTop m) :
    ∃ b a', (iotaPartsRel feR cnP.toNat cv rl x y pd).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧
      IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaPartsRel_specW p P.ipr n _ vis cnP q rw a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 pdO pdL) hc
  rcases n with _ | n
  · rw [iotaPartsRelW.eq_1] at hW; cases hW
  rw [iotaPartsRelW.arm1] at hW
  obtain ⟨xf, xfb, xi, xib, xu, xue, xp, xpb⟩ := irDecIP hx
  obtain ⟨yf, yfb, yi, yib, yu, yue, yp, ypb⟩ := irDecIP hy
  have hsz := hS.iw.iwSize
  have hT := hS.iw.iw
  have z0 : ∀ {mm : Mem} {b : Bool}, b = false → decW0B mm [0] b := fun h => by subst h; simp [decW0B]
  simp only [iotaPartsRel]
  -- the indices
  rcases c1 : callW p n "sl_eq" [a3, a4, b3, b4] m with _ | ⟨r1, m1⟩
  · rw [c1, iotaPartsRelW.k_sl_eq.none] at hW; cases hW
  obtain ⟨hm1, e1⟩ := irSlEq P c1 xi (by omega) yi (by omega)
  subst m1
  by_cases hi : x.idx ≠ y.idx
  · rw [c1, iotaPartsRelW.k_sl_eq.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [e1]; simp [hi])] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a, by simp [hi]; rfl, hS, IWGrow.refl _, z0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
  have hi : x.idx = y.idx := Classical.not_not.mp hi
  have hz1 : r1.headD 0 ≠ 0 := by rw [e1]; simp [hi]
  simp only [hi, beq_self_eq_true, ite_true]
  -- the levels
  by_cases hu : a5 ≠ b5
  · rw [c1, iotaPartsRelW.k_sl_eq.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz1 hu] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : (x.us == y.us) = false := by
      rw [← xue, ← yue, decI_beq _ _ xu yu]; simp [hu]
    exact ⟨false, a, by simp only [this, Bool.false_eq_true, ite_false]; rfl, hS, IWGrow.refl _, z0 rfl,
      ConRon.Bridge.CoreStep.refl hok⟩
  have hu : a5 = b5 := Classical.not_not.mp hu
  rw [c1, iotaPartsRelW.k_sl_eq.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz1 hu] at hW
  have : (x.us == y.us) = true := by rw [← xue, ← yue, hu]; exact beq_self_eq_true _
  simp only [this, ite_true]
  -- the parameters
  rcases c2 : callW p n "sl_eq" [a6, a7, b6, b7] m with _ | ⟨r2, m2⟩
  · rw [c2, iotaPartsRelW.k_sl_eq_2.none] at hW; cases hW
  obtain ⟨hm2, e2⟩ := irSlEq P c2 xp (by omega) yp (by omega)
  subst m2
  by_cases hp : x.params ≠ y.params
  · rw [c2, iotaPartsRelW.k_sl_eq_2.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [e2]; simp [hp])] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a, by simp [hp]; rfl, hS, IWGrow.refl _, z0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
  have hp : x.params = y.params := Classical.not_not.mp hp
  rw [c2, iotaPartsRelW.k_sl_eq_2.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [e2]; simp [hp])] at hW
  simp only [hp, beq_self_eq_true, ite_true]
  -- the fields' domains up to levels
  rcases c3 : callW p n "list_lvl_eq" [a1, a2, b1, b2] m with _ | ⟨r3, m3⟩
  · rw [c3, iotaPartsRelW.k_list_lvl_eq.none] at hW; cases hW
  obtain ⟨b3, a3', h3, hS3, hg3, hd3, k3⟩ := listLvlEq_rel P P.lle c3 hS hok xf xfb yf yfb
  rw [StateT.run_bind, h3, except_ok_bind]
  by_cases hz3 : r3.headD 0 ≠ 0
  · rw [c3, iotaPartsRelW.k_list_lvl_eq.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb3 : b3 = true := by rw [← hd3.1]; exact bne_iff_ne.mpr hz3
    subst hb3
    exact ⟨true, a3', rfl, hS3, hg3, by simp [decW0B], k3⟩
  have hz3 : r3.headD 0 = 0 := Classical.not_not.mp hz3
  have hb3 : b3 = false := by have := hd3.1; rw [hz3] at this; simpa using this.symm
  subst hb3
  simp only [Bool.false_eq_true, ite_false]
  -- the rule's fire kind
  have hrl3 : decRule (erecP m3) rw.toNat = some rl := ArrExt.decRule hg3.ext hrl
  rcases decRule_fireE (erRdOK m3) hrl3 with ⟨hf0, hfp⟩ | ⟨hf0, lvls, hfl, -⟩
  rotate_left
  · rw [c3, iotaPartsRelW.k_list_lvl_eq.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz3 hf0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a3', ?_, hS3, hg3, z0 rfl, k3⟩
    rcases hfl with hfl | ⟨pins, hfl⟩ <;> rw [hfl] <;> rfl
  rw [c3, iotaPartsRelW.k_list_lvl_eq.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz3 hf0] at hW
  rw [hfp]
  dsimp only
  rcases c4 : callW p n "params_ann_eq" [vis, cnP, q, pdO, pdL] m3 with _ | ⟨r4, m4⟩
  · rw [c4, iotaPartsRelW.k_params_ann_eq.none] at hW; cases hW
  obtain ⟨b4, a4, h4, hS4, hg4, hd4, k4⟩ := paramsAnnEq_rel P c4 hS3 k3.ok (ArrExt.decCV hg3.ext hcv)
    (decHL_grow' hg3 hpdb hpd) (Nat.le_trans hpdb hg3.iw)
  rw [StateT.run_bind, h4, except_ok_bind]
  by_cases hz4 : r4.headD 0 = 0
  · rw [c4, iotaPartsRelW.k_params_ann_eq.arm1 _ _ _ _ _ _ _ _ _ hz4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb4 : b4 = false := by have := hd4.1; rw [hz4] at this; simpa using this.symm
    subst hb4
    exact ⟨false, a4, rfl, hS4, hg3.trans hg4, z0 rfl, k3.trans k4⟩
  rw [c4, iotaPartsRelW.k_params_ann_eq.arm2 _ _ _ _ _ _ _ _ _ hz4] at hW
  have hb4 : b4 = true := by rw [← hd4.1]; exact bne_iff_ne.mpr hz4
  subst hb4
  simp only [ite_true]
  rcases c5 : callW p n "list_ann_eq" [vis, a1, a2, b1, b2] m4 with _ | ⟨r5, m5⟩
  · rw [c5, iotaPartsRelW.k_list_ann_eq.none] at hW; cases hW
  rw [c5, iotaPartsRelW.k_list_ann_eq.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have g34 := hg3.trans hg4
  obtain ⟨b5, a5', h5, hS5, hg5, hd5, k5⟩ := listAnnEq_rel P P.lae c5 hS4 k4.ok
    (decHL_grow' g34 xfb xf) (Nat.le_trans xfb g34.iw) (decHL_grow' g34 yfb yf) (Nat.le_trans yfb g34.iw)
  exact ⟨b5, a5', h5, hS5, g34.trans hg5, hd5, k3.trans (k4.trans k5)⟩

end lists

end L.Ind
