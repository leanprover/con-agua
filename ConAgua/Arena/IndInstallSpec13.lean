import ConAgua.Arena.IndInstallSpec12
import ConAgua.Arena.IndInstallSpec9

/-!
# Refinements of `IndInstall`, part 13 (lane `indproofs2`, helper `install`): `blockCapsAt`, the
relation

`block_caps_fin`'s record (`CapsWords`, the two `EREC` name slices `ESl`), then the capability
record's decoding `CapsAt`: in every array that holds the 15 words and agrees with the record pool
below its top, `decCaps` reads the twin's `IIndCaps`.
-/

noncomputable section


open ConRon.Arena
open Std.WP
open scoped Lean.Order

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
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl; rw [icaK2_some] at h
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
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [icaK3_some] at h
  obtain ⟨hS2, hg2, hE2⟩ := installErCopy hP h2 hS1
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; exact hd1)
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; omega)
  -- the ctor names
  have hcs2 := hcs.grow decCN_mono (hg1.trans hg2)
  obtain ⟨hI2, hE2', hsz2, hEs2, hcl2⟩ := hS2.2
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [icaK4_some] at h
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
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl; rw [icaK5_some] at h
  obtain ⟨hS4, hg4, hE4⟩ := installErCopy hP h4 hS3 hd3 (by omega)
  have hg04 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg04 hq hq9
  rw [hnpw] at h
  -- the three records
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl; rw [icaK5b_some] at h
  obtain ⟨hS5, hg5, hr5, hq5, hw5, ht5⟩ := installRec5 h5 hS4 rfl
  obtain ⟨⟨r6, m6⟩, h6, h⟩ := of_K h rfl; rw [icaK6_some] at h
  obtain ⟨hS6, hg6, -, -, hw6, ht6⟩ := installRec5 h6 hS5 rfl
  obtain ⟨⟨r7, m7⟩, h7, h⟩ := of_K h rfl; rw [icaK7_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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

/-! ## The capability record's decoding -/

/-- **`IIndCaps` at `IW[q‥q+15)`**, decoded in every array that holds those words (at any `e`) and
agrees with the record pool below its top (where `cons_block_inds` copies them). -/
def CapsAt (dn : NIdx → Option ConLeche.Name) (m : Mem) (q : Nat) (c : IIndCaps) : Prop :=
  q + 15 ≤ iwTop m ∧ ∀ (a : Array Word) (e : Nat), (∀ i < 15, a[e + i]? = (iwA m)[q + i]?) →
    (∀ i < erTop m, a[i]? = (erA m)[i]?) → decCaps a dn e = some c

theorem CapsAt.grow {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {q : Nat} {c : IIndCaps}
    (h : CapsAt dn m q c) (hg : IWGrow m m') : CapsAt dn m' q c := by
  refine ⟨Nat.le_trans h.1 hg.1, fun a e h1 h2 => h.2 a e (fun i hi => ?_) (fun i hi => ?_)⟩
  · rw [h1 i hi]; simp only [iwA]; rw [hg.2.2.1 _ (by have := h.1; omega)]
  · rw [h2 i (Nat.lt_of_lt_of_le hi hg.2.1)]; simp only [erA]; rw [hg.2.2.2 _ hi]

theorem installDecPW {a : Array Word} {dn : NIdx → Option ConLeche.Name} {e : Nat} {z0 z1 z2 : Word}
    (h7 : a[e + 7]? = some z0) (h8 : a[e + 8]? = some z1) (h9 : a[e + 9]? = some z2) :
    decPW a dn (e + 7) = pwWords dn a z0 z1 z2 := by
  unfold decPW pwWords
  simp only [nat?, hlist?, h7, show e + 7 + 1 = e + 8 by omega, show e + 8 + 1 = e + 9 by omega, h8, h9,
    Option.map_some, bind, Option.bind_some]
  rfl

/-- **`decCaps` of 15 words.** -/
theorem installDecCaps {a : Array Word} {dn : NIdx → Option ConLeche.Name} {e : Nat}
    {w0 w1 w2 w3 w4 w5 w6 z0 z1 z2 aq al np cq cl : Word} {z : ConLeche.PropWhen} {xs ys : List NIdx}
    (h : ∀ i < 15, a[e + i]? = [w0, w1, w2, w3, w4, w5, w6, z0, z1, z2, aq, al, np, cq, cl][i]?)
    (hw1 : H w1) (hz : pwWords dn a z0 z1 z2 = some z) (hx : hslice? a aq.toNat al.toNat = some xs)
    (hy : hslice? a cq.toNat cl.toNat = some ys) :
    decCaps a dn e = some (IIndCaps.mk (w0 != 0) (decI w1) w2.toNat w3.toNat (w4 != 0) w5.toNat
      (w6 != 0) z xs np.toNat ys) := by
  have g : ∀ i (hi : i < 15), a[e + i]? = some ([w0, w1, w2, w3, w4, w5, w6, z0, z1, z2, aq, al, np, cq, cl][i]'(by simpa using hi)) :=
    fun i hi => by rw [h i hi]; simp
  have e0 := g 0 (by decide); have e1 := g 1 (by decide); have e2 := g 2 (by decide)
  have e3 := g 3 (by decide); have e4 := g 4 (by decide); have e5 := g 5 (by decide)
  have e6 := g 6 (by decide); have e7 := g 7 (by decide); have e8 := g 8 (by decide)
  have e9 := g 9 (by decide); have e10 := g 10 (by decide); have e11 := g 11 (by decide)
  have e12 := g 12 (by decide); have e13 := g 13 (by decide); have e14 := g 14 (by decide)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e8 e9 e10 e11 e12 e13 e14
  have hpw := installDecPW (dn := dn) e7 e8 e9
  unfold decCaps
  rw [hpw, hz]
  simp only [bool?, hd?, nat?, hlist?, e0, e1, e2, e3, e4, e5, e6, e10, e12, e13,
    show e + 10 + 1 = e + 11 by omega, show e + 13 + 1 = e + 14 by omega, e11, e14, Option.map_some,
    hw1, ite_true, hx, hy, bind, Option.bind_some, pure]

/-! ## `block_caps_at`'s relation -/

theorem installEvalW3 (c1 c2 c3 : Cmp) (a1 b1 a2 b2 a3 b3 : Word) :
    (Cmp.evalW c1 a1 b1 &&& Cmp.evalW c2 a2 b2 &&& Cmp.evalW c3 a3 b3 != 0) =
      (c1.eval a1 b1 && c2.eval a2 b2 && c3.eval a3 b3) := by
  unfold Cmp.evalW
  cases c1.eval a1 b1 <;> cases c2.eval a2 b2 <;> cases c3.eval a3 b3 <;> decide

theorem installOfNatBeq {x c : Nat} (hx : x < 2 ^ 64) (hc : c < 2 ^ 64) :
    (UInt64.ofNat x == UInt64.ofNat c) = (x == c) := by
  by_cases h : x = c
  · subst h; simp
  · have : UInt64.ofNat x ≠ UInt64.ofNat c := fun e => h (by
      have := congrArg UInt64.toNat e
      rwa [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hc] at this)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem installNeEval (w : Word) : Cmp.eval .eq (Cmp.evalW .ne w 0) 0 = !(w != 0) := by
  unfold Cmp.evalW; cases h : Cmp.eval .ne w 0 <;> simp_all [Cmp.eval]

/-- A pure callee's run: the memory unchanged, the result its model. -/
theorem installPureCall {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m m' : Mem}
    {R r : List Word}
    (h : ⦃fun st => st = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' ⟨m, Locals.init []⟩ ∧ s'.mem = m ∧ r = R; ⊤⦄)
    (hc : callW p n f args m = some (r, m')) : r = R ∧ m' = m := by
  obtain ⟨s', rfl, -, h1, h2⟩ := triple_of_callW h hc
  exact ⟨h2, h1⟩

/-- **After `lv_zero_caps`: the record.** `block_caps_fin`'s run gives a capability record with the
branch words, the zero-ness, the member names and the ctor names. -/
theorem installCapsTail {p : Prog} (hP : CapsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a : AState} {pp coff clen w0 w1 w2 w3 w4 w6 : Word}
    {r1 r2 : List Word} {bs : BlockShape} {lv : ConLeche.Level} {cs : List (IConstantVal × Nat)}
    (hS1 : StageR dn vis fe m1 a) (hg1 : IWGrow m m1) (hz : decZC dn m1 r1 lv)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m1) (hw1 : H w1)
    (h2 : callW p (n + 1) "block_caps_fin" [pp, coff, clen, w0, w1, w2, w3, w4, w6, r1.headD 0,
      r1.tail.headD 0, r1.tail.tail.headD 0] m1 = some (r2, m2)) :
    StageR dn vis fe m2 a ∧ IWGrow m m2 ∧ CapsAt dn m2 (r2.headD 0).toNat
      (IIndCaps.mk (w0 != 0) (decI w1) w2.toNat w3.toNat (w4 != 0) w2.toNat (w6 != 0)
        (ConLeche.Level.zeronessOf lv) bs.memberNames bs.nP (cs.map (·.1.name))) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (icf_spec p hP.alloc hP.rec5 hP.fin n _ pp coff clen w0 w1 w2 w3 w4 w6 _ _ _) h2
  simp only at hW
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨-, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  obtain ⟨hS2, hg2, aq, al, cq, cl, hcw, hEa, hEc⟩ :=
    icfW_ok hP hW hS1 (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hcs
  refine ⟨hS2, hg1.trans hg2, by have := hcw.1; simpa using this, fun a e ha he => ?_⟩
  have hag : ∀ i < erTop m1, a[i]? = (erA m1)[i]? := fun i hi => by
    rw [he i (Nat.lt_of_lt_of_le hi hg2.2.1)]; simp only [erA]; rw [hg2.2.2.2 i hi]
  have hd := installDecCaps (dn := dn) (e := e) (a := a)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w2) (w6 := w6)
    (z0 := r1.headD 0) (z1 := r1.tail.headD 0) (z2 := r1.tail.tail.headD 0) (aq := aq) (al := al)
    (np := UInt64.ofNat bs.nP) (cq := cq) (cl := cl)
    (fun i hi => (ha i hi).trans (hcw.2 i (by simpa using hi))) hw1 (hz a hag)
    (installHslice_ext (fun j hj => he _ (by have := hEa.1; omega)) hEa.2)
    (installHslice_ext (fun j hj => he _ (by have := hEc.1; omega)) hEc.2)
  rw [hd, UInt64.toNat_ofNat_of_lt' hnpb]

/-- **`block_caps_at`'s model refines `blockCapsAt`**, from a refinement `hLZ` of its one
twin-visible callee `lv_zero_caps` at the entry memory and state (the twin's only effect is that
`readLevelM`), whose extra post `T` on the twin's state is passed through. -/
theorem icaW_simG {p : Prog} (hP : CapsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {T : AState → Prop}
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b)
    (hLZ : ∀ k, Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m) (readLevelM bs.resSort) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ T a')) :
    Sim (icaW p n m pp mi isRec) (ConRon.Arena.blockCapsAt bs mi.toNat b) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CapsAt dn m' (r.headD 0).toNat x) ∧
        T a') := by
  rcases n with _ | n
  · rw [icaW, callW_zero]; exact Sim.of_none
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  -- the lv_zero_caps step and the record, shared by the branches
  have hlz : ∀ (ws : List Word) (cs : List (IConstantVal × Nat)) (coff clen : Word)
      (R : ConLeche.Level → IIndCaps), PSlR decCN cs coff clen m → H (ws.tail.headD 0) →
      (∀ lv, R lv = IIndCaps.mk (ws.headD 0 != 0) (decI (ws.tail.headD 0)) (ws.tail.tail.headD 0).toNat
        (ws.tail.tail.tail.headD 0).toNat (ws.tail.tail.tail.tail.headD 0 != 0)
        (ws.tail.tail.headD 0).toNat (ws.tail.tail.tail.tail.tail.headD 0 != 0)
        (ConLeche.Level.zeronessOf lv) bs.memberNames bs.nP (cs.map (·.1.name))) →
      Sim (icaKW p (n + 1) pp coff clen (some (ws, m)))
        (readLevelM bs.resSort >>= fun l => pure (R l)) a
        (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CapsAt dn m' (r.headD 0).toNat x) ∧
          T a') := by
    intro ws cs coff clen R hcs hw1 hR
    rw [icaKW_some]
    refine Sim.bindK (K := icaK1 p (n + 1) pp coff clen ws) (body := fun r1 m1 => icaKF (callW p (n + 1)
        "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0, ws.tail.tail.headD 0,
          ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.tail.headD 0,
          r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m1)) rfl (fun _ _ => rfl)
      (hLZ (n + 1)) ?_
    rintro r1 lv m1 a1 ⟨⟨hS1, hg1, hz⟩, hT1⟩
    refine Sim.mstep (K := icaKF) rfl (fun _ _ => rfl) fun r2 m2 h2 => ?_
    obtain ⟨hS2, hg2, hca⟩ := installCapsTail hP n hS1 hg1 hz hq hsrc (hcs.grow decCN_mono hg1) hw1 h2
    refine Sim.ret ⟨⟨hS2, hg2, ?_⟩, hT1⟩
    rw [hR]; simpa using hca
  unfold icaW
  refine Sim.mstep (K := icaKH p (n + 1) pp isRec) rfl (fun _ _ => rfl) fun r0 m0 h0 => ?_
  obtain ⟨hr0, hm0⟩ := installPureCall (capsHead_spec p hP.head n _ pp mi) h0
  subst m0; subst r0
  unfold ConRon.Arena.blockCapsAt
  dsimp only
  rcases Nat.lt_or_ge mi.toNat bs.k with hmi | hmi
  case inr =>
    have hnone : bs.members[mi.toNat]? = none :=
        List.getElem?_eq_none (by unfold BlockShape.k at hmi; omega)
    have hh : capsHead m pp mi = [0, 0, 0, 0] := by
      unfold capsHead; rw [ite_eq_left]
      rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega
    rw [hh, icaKH_rest (h := by decide)]
    simp only [hnone]
    exact hlz [0, 0, 0, 0, 0, 0] [] 0 0 _ (PSlR.nil decCN m) (by decide) (fun _ => rfl)
  -- member `mi`
  have hl0 : l.toNat ≠ 0 := by omega
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left (fun h => hl0 (by rw [h]; rfl))
  obtain ⟨v, hv, hmsd⟩ := decPL_getH (truncM m) hdm' mi.toNat (by omega)
  generalize hmsh : bs.members[mi.toNat]'(by rw [decPL_length _ hdm']; omega) = msh at hmsd
  have hsome : bs.members[mi.toNat]? = some msh := by rw [← hmsh]; exact List.getElem?_eq_getElem _
  simp only [hsome]
  have hom : (o + mi).toNat = o.toNat + mi.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hwv, hvb, hvlt⟩ := partsIwRd hv (w := o + mi) hom
  have hv' : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hvb
  obtain ⟨⟨cvp, hcvp, hcvT⟩, hni, hct⟩ := decMS_some hmsd
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono hct
  have hv3 : v + 3 < iwTop m := partsIwLt hcl
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := UInt64.ofNat v + 2) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat v + 3) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw1n, hnb, -⟩ := partsIwRd hni (w := UInt64.ofNat v + 1) (by rw [UInt64.toNat_add, hv']; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  have hcd' : decPL (truncM m) (decCN (truncM m)) co.toNat cl.toNat = some msh.ctors := hcd
  have hlenc : msh.ctors.length = cl.toNat := decPL_length _ hcd'
  have hhd : capsHead m pp mi = if cl = 0 then [0, 0, 0, UInt64.ofNat v]
      else [co, cl, Cmp.evalW .eq cl 1, UInt64.ofNat v] := by
    unfold capsHead
    rw [ite_eq_right (by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega)]
    simp only [hw0, hwv, hw2, hw3]
  rcases hcs : msh.ctors with _ | ⟨c, _ | ⟨c2, cs⟩⟩
  · -- no constructor
    have hcl0 : cl = 0 := by
      apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    rw [hhd, ite_eq_left hcl0, icaKH_rest (h := by simp)]
    exact hlz [0, 0, 0, 0, 0, 0] [] 0 0 _ (PSlR.nil decCN m) (by decide) (fun _ => rfl)
  · -- one constructor
    have hcl1 : cl = 1 := by apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    subst hcl1
    rw [hhd, ite_eq_right (by decide), icaKH_one (h := rfl)]
    refine Sim.mstep (K := icaKW p (n + 1) pp co 1) rfl (fun _ _ => rfl) fun r1 m1 h1 => ?_
    obtain ⟨hr1, hm1⟩ := installPureCall (capsOne_spec p hP.one n _ pp (UInt64.ofNat v) isRec) h1
    subst m1; subst r1
    -- the constructor's words
    obtain ⟨cp, hcp, hcd0⟩ := decPL_getH (truncM m) hcd' 0 (by decide)
    simp only [hcs, List.getElem_cons_zero, Nat.add_zero] at hcd0 hcp
    obtain ⟨⟨cvp2, hcvp2, hcv2⟩, hnF⟩ := decCN_some hcd0
    obtain ⟨hwc, hcpb, -⟩ := partsIwRd hcp (w := co) rfl
    have hcp' : (UInt64.ofNat cp : Word).toNat = cp := UInt64.toNat_ofNat_of_lt' hcpb
    obtain ⟨hwcv, hcvb, -⟩ := partsIwRd hcvp2 (w := UInt64.ofNat cp) hcp'
    have hcpN : cp + 1 < iwTop m := partsIwLt hnF
    obtain ⟨hwnF, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat cp + 1) (by rw [UInt64.toNat_add, hcp']; simp; omega)
    obtain ⟨hn32, hnm⟩ := partsCVName (IWGrow.refl m) hcv2 hcvb
    -- the `isProp` word
    have hpr' := hpr
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr'
    obtain ⟨w8, hw8, hw8p⟩ := hpr'
    obtain ⟨-, hw8i⟩ := truncM_iw_get hw8
    have h8 : (pp + 8).toNat = pp.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    have hrw8 : rdW (m.arr64 IW) (pp + 8) = w8 := rdW_of_get? h8.symm (by simpa [iwA] using hw8i)
    have hcb1 : co.toNat + (1 : Word).toNat ≤ iwTop m := hcb.resolve_left (by decide)
    refine hlz (capsOne m pp (UInt64.ofNat v) isRec) [c] co 1 _ ⟨by rw [← hcs]; exact hcd, hcb1⟩
      (by simp only [capsOne, List.headD_cons, List.tail_cons, hw2, hwc, hwcv]; exact hn32)
      (fun lv => ?_)
    simp only [capsOne, List.headD_cons, List.tail_cons, hw2, hwc, hwcv, hw1n, hwnF, hnpw, hkw, hrw8,
      hnm, installEvalW3, installNeEval]
    have e1 : (UInt64.ofNat msh.nIdx == (0 : Word)) = (msh.nIdx == 0) := installOfNatBeq (c := 0) hnb (by decide)
    have e2 : (UInt64.ofNat c.snd == (0 : Word)) = (c.snd == 0) := installOfNatBeq (c := 0) hnFb (by decide)
    have e3 : (UInt64.ofNat bs.k == (1 : Word)) = (bs.k == 1) := installOfNatBeq (c := 1) hkb (by decide)
    have e4 : (isRec == 0) = !b := by rw [← hb]; simp [bne]
    simp only [Cmp.eval, e1, e2, e3, e4, hw8p, UInt64.toNat_ofNat_of_lt' hnpb,
      UInt64.toNat_ofNat_of_lt' hnFb, List.map_cons, List.map_nil]
    by_cases h1 : msh.nIdx = 0 <;> by_cases h2 : c.snd = 0 <;> cases bs.isProp <;> cases b <;> simp [h1, h2, bne]
  · -- two or more
    have hcl2 : 2 ≤ cl.toNat := by rw [← hlenc, hcs]; simp
    have hne0 : cl ≠ 0 := fun e => by rw [e] at hcl2; simp at hcl2
    have hne1 : Cmp.evalW .eq cl 1 ≠ 1 := by
      have : cl ≠ 1 := fun e => by rw [e] at hcl2; simp at hcl2
      simp [Cmp.evalW, Cmp.eval, this]
    rw [hhd, ite_eq_right hne0, icaKH_rest (h := by simpa using hne1)]
    have hbd : co.toNat + cl.toNat ≤ iwTop m := hcb.resolve_left hne0
    exact hlz [0, 0, 0, 0, 0, 0] (c :: c2 :: cs) co cl _ ⟨by rw [← hcs]; exact hcd, hbd⟩ (by decide)
      (fun _ => rfl)

/-- **`block_caps_at` refines `blockCapsAt`, as a call** (`icaW_simG`: from a refinement of its
`lv_zero_caps` call, whose extra post `T` is passed through). -/
theorem blockCapsAt_simG {p : Prog} (hP : CapsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {T : AState → Prop}
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp) (hb : (isRec != 0) = b)
    (hLZ : ∀ k, Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m) (readLevelM bs.resSort) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ T a')) :
    Sim (callW p n "block_caps_at" [pp, mi, isRec] m) (ConRon.Arena.blockCapsAt bs mi.toNat b) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CapsAt dn m' (r.headD 0).toNat x) ∧
        T a') := by
  intro r m' e
  rcases n with _ | k
  · rw [callW_zero] at e; cases e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ica_spec p hP.caps k _ pp mi isRec) e
  exact icaW_simG hP k hq hsrc hb hLZ r _ hW

end L.Ind
