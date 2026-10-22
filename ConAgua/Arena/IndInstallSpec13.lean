import ConAgua.Arena.IndInstallSpec12

/-!
# Refinements of `IndInstall`, part 13 (lane `indproofs2`, helper `install`): `blockCapsAt`, the
relation

`block_caps_fin`'s record (`CapsWords`, the two `EREC` name slices `ESl`), then the capability
record's decoding `CapsAt`: in every array that holds the 15 words and agrees with the record pool
below its top, `decCaps` reads the twin's `IIndCaps`.
-/

set_option linter.deprecated false

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The lookups of `block_caps_at`. -/
structure CapsProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  rec5 : p.lookup "rec5" = some rec5
  namesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  names : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  erAlloc : p.lookup "erec_alloc" = some erecAlloc
  erCopyGo : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo
  erCopy : p.lookup "block_caps_at_er_copy" = some blockCapsAtErCopy
  ctorNames : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames
  fin : p.lookup "block_caps_fin" = some blockCapsFin
  head : p.lookup "block_caps_head" = some blockCapsHead
  one : p.lookup "block_caps_one" = some blockCapsOne
  caps : p.lookup "block_caps_at" = some blockCapsAt

/-- Words `ws` at `IW[q‥]`, below the top. -/
def CapsWords (m : Mem) (q : Nat) (ws : List Word) : Prop :=
  q + ws.length ≤ iwTop m ∧ ∀ i < ws.length, (iwA m)[q + i]? = ws[i]?

/-- A handle slice of the record pool below its top. -/
def ESl (m : Mem) (o l : Word) (xs : List NIdx) : Prop :=
  o.toNat + l.toNat ≤ erTop m ∧ hslice? (erA m) o.toNat l.toNat = some xs

theorem CapsWords.grow {m m' : Mem} {q : Nat} {ws : List Word} (h : CapsWords m q ws)
    (hg : IWGrow m m') : CapsWords m' q ws :=
  ⟨Nat.le_trans h.1 hg.1, fun i hi => by
    simp only [iwA]; rw [hg.2.2.1 _ (by have := h.1; omega)]; exact h.2 i hi⟩

theorem installHslice_ext {a b : Array Word} {o l : Nat} {xs : List NIdx}
    (he : ∀ j < l, b[o + j]? = a[o + j]?) (h : hslice? a o l = some xs) : hslice? b o l = some xs := by
  rw [← h]; unfold hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  simp only [hd?, he j this]

theorem ESl.grow {m m' : Mem} {o l : Word} {xs : List NIdx} (h : ESl m o l xs) (hg : IWGrow m m') :
    ESl m' o l xs :=
  ⟨Nat.le_trans h.1 hg.2.1, installHslice_ext (fun j hj => by
    simp only [erA]; rw [hg.2.2.2 _ (by have := h.1; omega)]) h.2⟩

/-- An `IW` handle slice copied into `EREC` words. -/
theorem installHslice_copy {a b : Array Word} {o e l : Nat} {xs : List NIdx}
    (he : ∀ j < l, b[e + j]? = a[o + j]?) (h : hslice? a o l = some xs) : hslice? b e l = some xs := by
  rw [← h]; unfold hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  simp only [hd?, he j this]

theorem ctorNamesW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : ctorNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + l.toNat ≤ (m.arr64 IW).size := by
  unfold ctorNamesW at h
  cases hal : allocW m l with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

/-- The members' slice of a shape record lies below the top. -/
def ShapeSrc (m : Mem) (q : Word) : Prop :=
  ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m

/-- An `EREC` copy of an `IW` handle slice, under the stage relation. -/
theorem installErCopy {p : Prog} (hP : CapsProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {o l : Word} {r : List Word} {xs : List NIdx}
    (h : callW p n "block_caps_at_er_copy" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ ESl m' (r.headD 0) (r.tail.headD 0) xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockCapsAtErCopy_spec p hP.erAlloc hP.erCopyGo hP.erCopy n _ o l) h
  simp only at hW
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.2
  obtain ⟨hr, htq, hcp, hf, hlow, htop, hroom, -⟩ := capsErCopyW_post hW hsz hEs (by omega) (by omega)
  obtain ⟨hS', hg⟩ := StageR.erec hS hf hlow (by omega) (by omega)
  refine ⟨hS', hg, ?_⟩
  subst hr
  simp only [List.headD_cons, List.tail_cons]
  refine ⟨by rw [htq, htop]; exact Nat.le_refl _, ?_⟩
  rw [htq]
  exact installHslice_copy (a := iwA m) (o := o.toNat) (fun j hj => hcp j hj) hd

theorem installRec5 {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {ws r : List Word}
    (h : recW m 5 ws = some (r, m')) (hS : StageR dn vis fe m a) (hl : ws.length = 5) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200] ∧
      (rdW (m.arr64 CTL) 200).toNat = iwTop m ∧ CapsWords m' (iwTop m) ws ∧ iwTop m' = iwTop m + 5 := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage h hS (by rw [hl]; rfl)
  refine ⟨hS', hg, hr, rfl, ⟨by rw [htop, hl]; exact Nat.le_refl _, fun i hi => ?_⟩, by rw [htop, hl]⟩
  exact hget i hi

/-- **`block_caps_fin`'s record**: the stage relation kept, the 15 words at the returned pointer,
the member names and the ctor names as `EREC` slices below the record pool's top. -/
theorem icfW_ok {p : Prog} (hP : CapsProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
    {pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word} {r : List Word} {bs : BlockShape}
    {cs : List (IConstantVal × Nat)}
    (h : icfW p n m pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ ∃ aq al cq cl : Word,
      CapsWords m' (r.headD 0).toNat
        [w0, w1, w2, w3, w4, w2, w6, z0, z1, z2, aq, al, UInt64.ofNat bs.nP, cq, cl] ∧
      ESl m' aq al bs.memberNames ∧ ESl m' cq cl (cs.map (·.1.name)) := by
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.2
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr1⟩ := partsShapeFacts hq hsrc
  have hptr0 : ∀ o l j v, iwN m pp.toNat = some o → iwN m (pp.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v < iwTop m :=
    fun o l j v h1 h2 h3 h4 => by have := hptr1 o l j v h1 h2 h3 h4; omega
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    have : bs.k = (UInt64.ofNat bs.k).toNat := by
      obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']
      rw [UInt64.toNat_ofNat_of_lt' this.2]
    rw [this]; exact UInt64.toNat_lt _
  unfold icfW at h
  -- the member names
  cases h1 : callW p n "block_shape_member_names" [pp] m with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, icaK2_some] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.alloc hP.namesCopy hP.names n _ pp) h1
  simp only at hW1; subst hs1
  obtain ⟨hr1, hd1, hg1, hf1, ht1⟩ := memberNamesW_dec hW1 hsz hcl hq' (by omega) hsrc hptr0
  have hS1 : StageR dn vis fe s1.mem a := stage_frame_iw hS hf1 (by
    have := memberNamesW_room hW1 hsz; rw [hkw, UInt64.toNat_ofNat_of_lt' hkb] at this
    simp only [iwTop] at this ht1 ⊢; omega)
  subst hr1
  simp only [List.headD_cons, List.tail_cons] at h
  -- their `EREC` copy
  cases h2 : callW p n "block_caps_at_er_copy" [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] s1.mem with
  | none => rw [h2] at h; cases h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, icaK3_some] at h
  obtain ⟨hS2, hg2, hE2⟩ := installErCopy hP h2 hS1
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; exact hd1)
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; omega)
  -- the ctor names
  have hcs2 := hcs.grow decCN_mono (hg1.trans hg2)
  obtain ⟨hI2, hE2', hsz2, hEs2, hcl2⟩ := hS2.2
  cases h3 : callW p n "block_caps_ctor_names" [coff, clen] m2 with
  | none => rw [h3] at h; cases h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, icaK4_some] at h
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.alloc hP.namesCopy hP.ctorNames n _ coff clen) h3
  simp only at hW3; subst hs3
  have hcsd : decPL (truncM m2) (decCN (truncM m2)) coff.toNat clen.toNat = some cs := hcs2.1
  have hlen := decPL_length _ hcsd
  obtain ⟨hr3, hd3, hg3, hf3, ht3⟩ := ctorNamesW_dec hW3 hsz2 hcl2 hcs2.2 (cs.map (·.1))
    (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get clen.toNat coff.toNat cs hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := rec2IwN_trunc hv
      obtain ⟨hvlt2, hva'⟩ := rec2IwN_trunc hva
      have hj' : j < cs.length := by omega
      have hy' : cs[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS3 : StageR dn vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    have := ctorNamesW_room hW3 hsz2; simp only [iwTop] at this ht3 ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons, List.map_map] at h hd3
  -- their `EREC` copy
  cases h4 : callW p n "block_caps_at_er_copy" [rdW (m2.arr64 CTL) 200, clen] s3.mem with
  | none => rw [h4] at h; cases h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, icaK5_some] at h
  obtain ⟨hS4, hg4, hE4⟩ := installErCopy hP h4 hS3 hd3 (by omega)
  have hg04 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg04 hq hq9
  rw [hnpw] at h
  -- the three records
  cases h5 : recW m4 5 [w0, w1, w2, w3, w4] with
  | none => rw [h5] at h; cases h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5, icaK5b_some] at h
  obtain ⟨hS5, hg5, hr5, hq5, hw5, ht5⟩ := installRec5 h5 hS4 rfl
  cases h6 : recW m5 5 [w2, w6, z0, z1, z2] with
  | none => rw [h6] at h; cases h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6, icaK6_some] at h
  obtain ⟨hS6, hg6, -, -, hw6, ht6⟩ := installRec5 h6 hS5 rfl
  cases h7 : recW m6 5 [r2.headD 0, r2.tail.headD 0, UInt64.ofNat bs.nP, r4.headD 0, r4.tail.headD 0] with
  | none => rw [h7] at h; cases h
  | some x7 =>
  obtain ⟨r7, m7⟩ := x7
  rw [h7, icaK7_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS7, hg7, -, -, hw7, ht7⟩ := installRec5 h7 hS6 rfl
  have hg47 := (hg5.trans hg6).trans hg7
  refine ⟨hS7, hg04.trans hg47, r2.headD 0, r2.tail.headD 0, r4.headD 0, r4.tail.headD 0, ?_,
    (hE2.grow (hg3.trans hg4)).grow hg47, hE4.grow hg47⟩
  subst hr5
  simp only [List.headD_cons]
  rw [hq5]
  have w5' := (hw5.grow (hg6.trans hg7))
  have w6' := hw6.grow hg7
  refine ⟨by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · have := w5'.2 i (by simpa using hi5)
    rw [this]
    rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | omega
  rcases Nat.lt_or_ge i 10 with hi10 | hi10
  · have := w6'.2 (i - 5) (by simp; omega)
    rw [show iwTop m4 + i = iwTop m5 + (i - 5) by omega, this]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega
  · have := hw7.2 (i - 10) (by simp; omega)
    rw [show iwTop m4 + i = iwTop m6 + (i - 10) by omega, this]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega

end L.Ind
