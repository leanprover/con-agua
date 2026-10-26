import ConAgua.Arena.IndRealBph

/-!
# `basis_pin_hit(off, len)` refines `basisPinHit` (lane `indproofs4`, helper `bph`)

The models of `IndRealBph.lean` against the twin's `basisPinHitGo` over
`[eqK, natK, emptyK, falseK]`: per kind the pinned block (`rom_basis_decls`, `RomRefs.basis`), the
name pre-filter (`blockNames pinned == blockNames block`: the inner loop compares the name words,
`bphNW_iff`, `bphNames_iff`), then the block copied to `IW` (`er_to_iw`, `erToIw_blk`) and the
canonical comparison (`canonEqList_refines`, whose literal premise `LitInj` comes from the twin
state's `StateOK`, threaded through the pinned blocks' interning: `BasisKind.decls_run`).
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The lookups `basis_pin_hit` reaches (beyond the ROM readers' and the canonical comparisons'). -/
structure BphProg (p : Prog) : Prop where
  bph : p.lookup "basis_pin_hit" = some L.Checker.basisPinHitL
  canon : CanonProg p
  rom : L.Rom.RomRefs p
  iw_alloc : p.lookup "iw_alloc" = some iwAlloc
  er_copy : p.lookup "er_copy" = some erCopy
  er_to_iw : p.lookup "er_to_iw" = some erToIw

/-- The kinds `basisPinHit` tries, in order. -/
def bphKinds : List ConLeche.BasisKind := [.eqK, .natK, .emptyK, .falseK]

theorem bphKinds_drop (k : Nat) (hk : k < 4) :
    bphKinds.drop k = basisOfW k :: bphKinds.drop (k + 1) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem bph_decls_ne (k : Nat) (hk : k < 4) : (ConLeche.BasisKind.decls (basisOfW k)).length ≠ 0 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp [basisOfW, ConLeche.BasisKind.decls, ConLeche.eqBasis, ConLeche.natBasis,
      ConLeche.emptyBasis, ConLeche.falseBasis]

/-- The twin's verdict against the results `(ok, kind)`. -/
def BphR : Option ConLeche.BasisKind → List Word → Prop
  | none, r => r.headD 0 = 0
  | some k, r => r.headD 0 ≠ 0 ∧ (r.tail.headD 0).toNat < 4 ∧ basisOfW (r.tail.headD 0).toNat = k

theorem bphDecI_inj {v w : Word} (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (h : (decI v : NIdx) = decI w) : v = w := by
  have := (word_decI (decI v : NIdx) w hw).mpr h
  rw [← this]
  apply UInt64.toNat_inj.mp
  simp [decI]; omega

theorem bphDecEBlk_get {dn : NIdx → Option ConLeche.Name} {m : Mem} {o l : Nat}
    {blk : List IConstantInfo} (h : decEBlk dn m o l = some blk) (j : Nat) (hj : j < l) :
    ∃ q, nat? (erA m) (o + j) = some q ∧
      decCI (erA m) dn q = some (blk[j]'(by rw [mapM_opt_length _ _ _ h]; simpa using hj)) := by
  have := mapM_opt_get _ (List.range l) blk h j (by simpa using hj)
  simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at this
  exact this

/-! ## The name words -/

/-- A pointer word and the name word of its record, read in the real pools. -/
theorem bphNameAt {dn : NIdx → Option ConLeche.Name} {m : Mem} {A : Array Word} {base i : Word}
    {v : Nat} {ci : IConstantInfo} (hA : A.size < 2 ^ 64) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hv : nat? A (base.toNat + i.toNat) = some v) (hci : decCI (erA (truncM m)) dn v = some ci) :
    ∃ w, rdW (m.arr64 EREC) (rdW A (base + i) + 1) = w ∧ w.toNat < 2 ^ 32 ∧ ci.name = decI w := by
  simp only [nat?, Option.map_eq_some_iff] at hv
  obtain ⟨w0, hw0, rfl⟩ := hv
  have hlt := (Array.getElem?_eq_some_iff.mp hw0).1
  have hoi : (base + i).toNat = base.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have e1 : rdW A (base + i) = w0 := by simp [rdW, hoi, hw0]
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCI_name hci
  obtain ⟨-, hwn'⟩ := truncM_er_get hwn
  have hlt2 := (Array.getElem?_eq_some_iff.mp hwn').1
  simp only [erA] at hlt2 hwn'
  have h1 : (w0 + 1).toNat = w0.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨wn, ?_, hwnl, hname⟩
  rw [e1]; simp [rdW, h1, hwn']

/-- The pinned block's name word `i`. -/
theorem bphPinName {dn : NIdx → Option ConLeche.Name} {m : Mem} {o l : Word}
    {pinned : List IConstantInfo}
    (hP : decPL (truncM m) (fun q => decCI (erA (truncM m)) dn q) o.toNat l.toNat = some pinned)
    (hI : (m.arr64 IW).size < 2 ^ 64) (hE : (m.arr64 EREC).size < 2 ^ 64) (i : Word)
    (hi : i.toNat < l.toNat) :
    ∃ w ci, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + i) + 1) = w ∧ w.toNat < 2 ^ 32 ∧
      pinned[i.toNat]? = some ci ∧ ci.name = decI w := by
  obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hP i.toNat hi
  have hv' : nat? (m.arr64 IW) (o.toNat + i.toNat) = some v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨w, (truncM_iw_get hw).2, rfl⟩
  obtain ⟨w, h1, h2, h3⟩ := bphNameAt hI hE hv' hci
  exact ⟨w, ci, h1, h2, hget, h3⟩

/-- The block's name word `i`. -/
theorem bphBlkName {dn : NIdx → Option ConLeche.Name} {m : Mem} {bo l : Word}
    {blk : List IConstantInfo} (hB : decEBlk dn (truncM m) bo.toNat l.toNat = some blk)
    (hE : (m.arr64 EREC).size < 2 ^ 64) (i : Word) (hi : i.toNat < l.toNat) :
    ∃ w ci, rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + i) + 1) = w ∧ w.toNat < 2 ^ 32 ∧
      blk[i.toNat]? = some ci ∧ ci.name = decI w := by
  obtain ⟨q, hq, hci⟩ := bphDecEBlk_get hB i.toNat hi
  have hq' : nat? (m.arr64 EREC) (bo.toNat + i.toNat) = some q := by
    simp only [nat?, Option.map_eq_some_iff] at hq ⊢
    obtain ⟨w, hw, rfl⟩ := hq
    exact ⟨w, (truncM_er_get hw).2, rfl⟩
  obtain ⟨w, h1, h2, h3⟩ := bphNameAt hE hE hq' hci
  exact ⟨w, _, h1, h2, List.getElem?_eq_getElem _, h3⟩

/-- **The name pre-filter**: the name words agree pointwise exactly when the member names do. -/
theorem bphNames_iff {dn : NIdx → Option ConLeche.Name} {m : Mem} {o bo l : Word}
    {pinned blk : List IConstantInfo}
    (hP : decPL (truncM m) (fun q => decCI (erA (truncM m)) dn q) o.toNat l.toNat = some pinned)
    (hB : decEBlk dn (truncM m) bo.toNat l.toNat = some blk)
    (hI : (m.arr64 IW).size < 2 ^ 64) (hE : (m.arr64 EREC).size < 2 ^ 64) :
    (∀ i : Word, i < l → rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + i) + 1) =
        rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + i) + 1)) ↔
      blockNames pinned = blockNames blk := by
  have hlp : pinned.length = l.toNat := decPL_length (truncM m) hP
  have hlb : blk.length = l.toNat := by rw [mapM_opt_length _ _ _ hB]; simp
  constructor
  · intro h
    unfold blockNames
    apply List.ext_getElem (by simp [hlp, hlb])
    intro n h1 h2
    simp only [List.length_map] at h1 h2
    have hn : n < 2 ^ 64 := by have := l.toNat_lt; omega
    have hi : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hn)
    obtain ⟨wa, ca, ha1, ha2, ha3, ha4⟩ := bphPinName hP hI hE (UInt64.ofNat n) (by rw [hi]; omega)
    obtain ⟨wb, cb, hb1, hb2, hb3, hb4⟩ := bphBlkName hB hE (UInt64.ofNat n) (by rw [hi]; omega)
    have hab := h (UInt64.ofNat n) (UInt64.lt_iff_toNat_lt.mpr (by rw [hi]; omega))
    rw [ha1, hb1] at hab
    subst hab
    rw [hi] at ha3 hb3
    simp only [List.getElem_map]
    rw [List.getElem?_eq_getElem h1, Option.some.injEq] at ha3
    rw [List.getElem?_eq_getElem h2, Option.some.injEq] at hb3
    rw [ha3, hb3, ha4, hb4]
  · intro h i hi
    have hi' := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨wa, ca, ha1, ha2, ha3, ha4⟩ := bphPinName hP hI hE i hi'
    obtain ⟨wb, cb, hb1, hb2, hb3, hb4⟩ := bphBlkName hB hE i hi'
    rw [ha1, hb1]
    have e : (blockNames pinned)[i.toNat]? = (blockNames blk)[i.toNat]? := by rw [h]
    simp only [blockNames, List.getElem?_map, ha3, hb3, Option.map_some, Option.some.injEq] at e
    exact bphDecI_inj ha2 hb2 (by rw [← ha4, ← hb4, e])

/-- **The inner loop's model**: it reaches `l` exactly when the name words agree from `j` on. -/
theorem bphNW_iff (m : Mem) (bo o l : Word) : ∀ (f : Nat) (j jf : Word),
    bphNW f m bo o l j = some jf → j ≤ l →
    (jf = l ↔ ∀ i : Word, j ≤ i → i < l → rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + i) + 1) =
        rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + i) + 1)) := by
  intro f
  induction f with
  | zero => intro j jf h; simp [bphNW] at h
  | succ f ih =>
  intro j jf h hjl
  have hjl' := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : j < l
  · have hj' := UInt64.lt_iff_toNat_lt.mp hj
    by_cases hd : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 1) =
        rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + j) + 1)
    · rw [bphNW_next f m bo o l j hj hd] at h
      have hj1 : (j + 1).toNat = j.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
      rw [ih (j + 1) jf h (UInt64.le_iff_toNat_le.mpr (by omega))]
      constructor
      · intro H i h1 h2
        by_cases e : i = j
        · subst e; exact hd
        · have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h')
          exact H i (UInt64.le_iff_toNat_le.mpr (by have := UInt64.le_iff_toNat_le.mp h1; omega)) h2
      · intro H i h1 h2
        exact H i (UInt64.le_iff_toNat_le.mpr (by have := UInt64.le_iff_toNat_le.mp h1; omega)) h2
    · rw [bphNW_brk f m bo o l j hj hd, Option.some.injEq] at h
      subst h
      constructor
      · intro e; subst e; exact absurd hj (by simp)
      · intro H; exact absurd (H j (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hj) hd
  · rw [bphNW_exit f m bo o l j hj, Option.some.injEq] at h
    subst h
    have : j.toNat = l.toNat := by
      have : ¬ j.toNat < l.toNat := fun h' => hj (UInt64.lt_iff_toNat_lt.mpr h')
      omega
    have e : j = l := UInt64.toNat_inj.mp this
    constructor
    · intro _ i h1 h2
      have := UInt64.le_iff_toNat_le.mp h1; have := UInt64.lt_iff_toNat_lt.mp h2; omega
    · intro _; exact e

/-! ## The loop over the kinds -/

/-- The block, read in the record pool (`decCIs` of `erecP`), and its bound, from a stable
decoding of a non-empty block. -/
theorem bphBlk_erec {dn : NIdx → Option ConLeche.Name} {m : Mem} {bo bl : Word}
    {blk : List IConstantInfo} (hB : decEBlk dn (truncM m) bo.toNat bl.toNat = some blk)
    (hne : bl.toNat ≠ 0) :
    L.Front.decCIs (erecP m) dn bo.toNat bl.toNat = some blk ∧ bo.toNat + bl.toNat ≤ erTop m := by
  refine ⟨mapM_imp _ _ hB fun j _ y hy => ?_, ?_⟩
  · simp only [bind, Option.bind_eq_some_iff] at hy ⊢
    obtain ⟨v, hv, hy⟩ := hy
    exact ⟨v, (truncM_erecP m).nat? hv, ArrExt.decCI (truncM_erecP m) hy⟩
  · obtain ⟨q, hq, -⟩ := bphDecEBlk_get hB (bl.toNat - 1) (by omega)
    simp only [nat?, Option.map_eq_some_iff] at hq
    obtain ⟨w, hw, -⟩ := hq
    have := (truncM_er_get hw).1
    omega

theorem bph_run_step (blk pinned : List IConstantInfo) (K : ConLeche.BasisKind)
    (ks : List ConLeche.BasisKind) (a a1 : AState)
    (h : (BasisKind.decls K).run a = .ok (pinned, a1)) :
    (basisPinHitGo blk (K :: ks)).run a =
      (if blockNames pinned == blockNames blk then
        (do if ← canonEqList blk pinned then pure (some K) else pure none)
      else basisPinHitGo blk ks).run a1 := by
  simp only [basisPinHitGo, StateT.run_bind, h, exc_ok_bind']

theorem bph_run_hit (blk pinned : List IConstantInfo) (K : ConLeche.BasisKind) (a1 a2 : AState)
    (b : Bool) (h : (canonEqList blk pinned).run a1 = .ok (b, a2)) :
    (do if ← canonEqList blk pinned then pure (some K) else pure none : AM _).run a1 =
      .ok (if b then some K else none, a2) := by
  simp only [StateT.run_bind, h, exc_ok_bind']
  cases b <;> rfl

/-- **The loop over the kinds refines `basisPinHitGo`** on the kinds from `k`. -/
theorem bphGoW_ok {p : Prog} (P : BphProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (bo bl : Word) (blk : List IConstantInfo) :
    ∀ (f : Nat) (m m' : Mem) (a : AState) (k : Word) (r : List Word),
      bphGoW p f m bo bl k = some (r, m') → StageR dn vis fe m a → ConRon.Bridge.StateOK a →
      DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m blk → k.toNat ≤ 4 →
      ∃ x a', (basisPinHitGo blk (bphKinds.drop k.toNat)).run a = .ok (x, a') ∧
        StageR dn vis fe m' a' ∧ IWGrow m m' ∧ BphR x r := by
  intro f
  induction f with
  | zero => intro m m' a k r h; simp [bphGoW] at h
  | succ f ih =>
  intro m m' a k r h hS hok hB hk4
  by_cases hk : k < 4
  rotate_left
  · rw [bphGoW_exit p f m bo bl k hk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : k.toNat = 4 := by
      have : ¬ k.toNat < 4 := fun h' => hk (UInt64.lt_iff_toNat_lt.mpr (by simpa using h'))
      omega
    rw [this]
    exact ⟨none, a, rfl, hS, IWGrow.refl m, rfl⟩
  have hkn : k.toNat < 4 := by simpa using UInt64.lt_iff_toNat_lt.mp hk
  have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [bphKinds_drop _ hkn]
  rcases h1 : callW p f "rom_basis_decls" [k] m with _ | ⟨r1, m1⟩
  · rw [bphGoW_none1 p f m bo bl k hk h1] at h; cases h
  rw [bphGoW_step p f m m1 bo bl k r1 hk h1] at h
  obtain ⟨pinned, a1, hrun1, hS1, hg1, hDR1⟩ := P.rom.basis dn vis fe k hkn f m a r1 m1 hS h1
  have hrun1' : BasisKind.decls (basisOfW k.toNat) a = .ok (pinned, a1) := hrun1
  obtain ⟨hok1, -, -, -, hden1⟩ := ConRon.Bridge.BasisKind.decls_run hok hrun1'
  have hpne : pinned.length ≠ 0 := by
    rw [denoteCIList_length _ _ hden1]; exact bph_decls_ne _ hkn
  have hB1 : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m1 blk := DecB.grow (decEBlk_mono dn _ _) hg1 hB
  have hD1 : decPL (truncM m1) (fun q => decCI (erA (truncM m1)) dn q) (r1.headD 0).toNat
      (r1.tail.headD 0).toNat = some pinned := hDR1.1
  have hl1 : pinned.length = (r1.tail.headD 0).toNat := decPL_length (truncM m1) hD1
  have hlb : blk.length = bl.toNat := by
    have : decEBlk dn (truncM m1) bo.toNat bl.toNat = some blk := hB1
    rw [mapM_opt_length _ _ _ this]; simp
  rw [bph_run_step blk pinned _ _ a a1 hrun1]
  -- the next kind
  have next : bphGoW p f m1 bo bl (k + 1) = some (r, m') →
      blockNames pinned ≠ blockNames blk →
      ∃ x a', (if blockNames pinned == blockNames blk then
          (do if ← canonEqList blk pinned then pure (some (basisOfW k.toNat)) else pure none)
        else basisPinHitGo blk (bphKinds.drop (k.toNat + 1))).run a1 = .ok (x, a') ∧
        StageR dn vis fe m' a' ∧ IWGrow m m' ∧ BphR x r := by
    intro h hne
    rw [if_neg (by simpa using hne)]
    obtain ⟨x, a', hr, hS', hg', hR'⟩ := ih m1 m' a1 (k + 1) r h hS1 hok1 hB1 (by omega)
    rw [hk1] at hr
    exact ⟨x, a', hr, hS', hg1.trans hg', hR'⟩
  by_cases hl : r1.tail.headD 0 = bl
  rotate_left
  · rw [if_neg hl] at h
    refine next h fun he => hl (UInt64.toNat_inj.mp ?_)
    have := congrArg List.length he
    simp only [blockNames, List.length_map] at this
    omega
  rw [if_pos hl] at h
  cases hn : bphNW (f + 1) m1 bo (r1.headD 0) (r1.tail.headD 0) 0 with
  | none => rw [hn] at h; cases h
  | some j =>
  rw [hn, bphK2_some] at h
  have hI1 := hS1.2.2.2.1
  have hE1 := hS1.2.2.2.2.1
  have hB1' : decEBlk dn (truncM m1) bo.toNat (r1.tail.headD 0).toNat = some blk := by
    rw [hl]; exact hB1
  have hiff := bphNW_iff m1 bo (r1.headD 0) (r1.tail.headD 0) (f + 1) 0 j hn
    (UInt64.le_iff_toNat_le.mpr (by simp))
  have hnames := bphNames_iff hD1 hB1' hI1 hE1
  by_cases hj : j = r1.tail.headD 0
  rotate_left
  · rw [if_neg hj] at h
    refine next h fun he => hj ?_
    exact hiff.mpr fun i _ hi => hnames.mpr he i hi
  rw [if_pos hj] at h
  have heq : blockNames pinned = blockNames blk :=
    hnames.mp fun i hi => hiff.mp hj i (UInt64.le_iff_toNat_le.mpr (by simp)) hi
  rw [if_pos (by simpa using heq)]
  have hne : bl.toNat ≠ 0 := by rw [← hl, ← hl1]; exact hpne
  -- `er_to_iw`
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [bphK3_some] at h
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (L.Ind.erToIw_specW p P.iw_alloc P.er_copy P.er_to_iw f ⟨m1, Locals.init []⟩ _ _) h2
  subst hs2
  obtain ⟨hdc, hbb⟩ := bphBlk_erec hB1 hne
  obtain ⟨hS2, hg2, hl2, hd2, hb2⟩ := erToIw_blk hW2 hS1 hdc hbb
  obtain ⟨hp1, hpb1⟩ := decRBlk_canon hDR1 hpne
  have hp2 := decPL_growAP hp1 hpb1 hg2
  -- `canon_eq_list`
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [bphK4_some] at h
  rw [hl2] at h3
  obtain ⟨s3, hs3, -, hok3, ⟨⟨hS3, hg3, hd3⟩, -⟩, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (canonEqList_refines p P.canon dn vis fe _ _ _ _ blk pinned f ⟨s2.mem, Locals.init []⟩ a1
      ⟨hS2, hd2, hp2, hb2, by show _ ≤ iwTop s2.mem; have := hg2.1; dsimp only at this; omega, poolSmall_of_stage hS2,
        fun x y l hx hy => hok1.view_inj hx hy⟩) h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  generalize AM.res (canonEqList blk pinned) a1 = b at hrun3 hd3
  generalize AM.st (canonEqList blk pinned) a1 = a3 at hrun3 hS3
  refine ⟨if b then some (basisOfW k.toNat) else none, a3, bph_run_hit _ _ _ _ _ _ hrun3, ?_⟩
  obtain ⟨hd3a, -⟩ := hd3
  by_cases hb : r3.headD 0 = 0
  · rw [if_neg (by simpa using hb), Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : b = false := by rw [← hd3a, hb]; rfl
    subst this
    exact ⟨hS3, hg1.trans (hg2.trans hg3), rfl⟩
  · rw [if_pos hb, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : b = true := by rw [← hd3a]; simpa using hb
    subst this
    exact ⟨hS3, hg1.trans (hg2.trans hg3), by simp, hkn, rfl⟩

/-- **`basis_pin_hit(off, len)` refines `basisPinHit`** on the block's `EREC` slice of constant
records (`decEBlk`, decoded below the tops), at a well-formed twin state (`StateOK`: canon's
`LitInj`); `rom_basis_decls` by its refinement (`RomRefs.basis`). -/
@[refines ConRon.Arena.basisPinHit ConRon.Arena.basisPinHitGo]
theorem basisPinHit_ok {p : Prog} (P : BphProg p) :
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a : AState)
    (o l : Word) (blk : List IConstantInfo) (r : List Word),
    StageR dn vis fe m a → ConRon.Bridge.StateOK a →
    DecB (fun m => decEBlk dn m o.toNat l.toNat) m blk →
    callW p n "basis_pin_hit" [o, l] m = some (r, m') →
    ∃ x a', (basisPinHit blk).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      match x with
      | none => r.headD 0 = 0
      | some k => r.headD 0 ≠ 0 ∧ (r.tail.headD 0).toNat < 4 ∧ basisOfW (r.tail.headD 0).toNat = k := by
  intro n dn vis fe m m' a o l blk r hS hok hB hc
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bph_specW p P.bph n ⟨m, Locals.init []⟩ o l) hc
  subst hs'
  obtain ⟨x, a', hrun, hS', hg, hR⟩ := bphGoW_ok P dn vis fe o l blk (n + 1) m s'.mem a 0 r hW hS hok
    hB (by simp)
  refine ⟨x, a', hrun, hS', hg, ?_⟩
  cases x <;> exact hR

end L.Ind
