import ConAgua.Checker.PrepLoopRef
import ConAgua.Checker.PrepCopyRef
import ConAgua.Census.Attr

/-!
# `prepare_prelude` refines `preparePrelude` (lane `front4`)

The assembly: two slices (the order `ord`, the marks `mk`), the marks zeroed, the front
(`pFront_ok`: `frontOf`), the rest (`pRest_ok`), the ground hoist (`hNatOpGround_ok`), then `DECL`
rewritten in the hoisted order (`pCopyBack_ok`). The records before are the prelude's then the
stream's (`pre.decls ++ ds`); after, `DECL` represents the prepared array, with the same
per-record facts (`RecOK`), and the store relation and the pins hold at the twin's state after.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind
open Std.WP
open scoped Lean.Order

namespace L.Checker

/-- A record's representation reads its eight words and the pool only. -/
theorem declAtF_congr {D D' P : Array Word} {i j : Nat} {d : IDeclaration}
    (h : ∀ k < 8, dw D' i k = dw D j k) (hd : DeclAtF D P j d) : DeclAtF D' P i d := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  cases d <;> simp_all [DeclAtF, DeclAt, CVAt, IndDeclAt]

theorem recOK_congr {D D' P : Array Word} {i j : Nat} (h : ∀ k < 8, dw D' i k = dw D j k)
    (hd : RecOK D P j) : RecOK D' P i := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  simp only [RecOK, h0, h1, h2, h3, h4, h5]
  exact hd

/-- The stream's positions, all unmarked, are the stream. -/
theorem recsAt_range (pre ds : Array IDeclaration) :
    recsAt (pre ++ ds) (List.range' pre.size ds.size) = ds := by
  apply Array.ext
  · simp [recsAt]
  · intro k h1 h2
    simp only [recsAt, List.getElem_toArray, List.getElem_map, List.getElem_range']
    rw [getElem!_pos (pre ++ ds) _ (by simp; omega), Array.getElem_append_right (by omega)]
    congr 1; omega

/-- **`prepare_prelude` on the model**: from the records `pre.decls ++ ds` (the prelude's `np =
CTL[240]` first), when L returns, the twin's `preparePrelude pre ds` succeeds, and `DECL`
represents its result (each record with `RecOK`), the store relation and the pins hold at the
twin's state after, the pool only grew. -/
theorem pPrepCore_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m' : Mem) (a : AState) (pre : PreludeIx)
    (ds : Array IDeclaration) (np r : Word)
    (hD : ∀ x (h : x < (pre.decls ++ ds).size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x (pre.decls ++ ds)[x] ∧
      RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hn : (rdW (m.arr64 DECL) 0).toNat = (pre.decls ++ ds).size)
    (hnp : np.toNat = pre.decls.size)
    (hDsz : 1 + 8 * (pre.decls ++ ds).size ≤ (m.arr64 DECL).size) (hDsz' : (m.arr64 DECL).size < 2 ^ 64)
    (hA : ArenaR m a) (hseen : ∃ s, SeenR m s) (hnix : ∃ idx, NixR m idx) (hI : IWOK m)
    (hP : PinsR m a.pins) (hnpw : rdW (m.arr64 CTL) 240 = np) (h : pPrepW p n m = some (r, m')) :
    ∃ ds' a', (preparePrelude pre ds).run a = .ok (ds', a') ∧
      (rdW (m'.arr64 DECL) 0).toNat = ds'.size ∧
      (∀ x (h : x < ds'.size), DeclAtF (m'.arr64 DECL) (m'.arr64 DLP) x ds'[x] ∧
        RecOK (m'.arr64 DECL) (m'.arr64 DLP) x) ∧
      ArenaR m' a' ∧ IWOK m' ∧ PinsR m' a'.pins ∧ m'.arr64 DLP = m.arr64 DLP ∧
      (m'.arr64 DECL).size = (m.arr64 DECL).size ∧ a'.store.pers = a.store.pers ∧
      a'.store.scr = a.store.scr ∧ a'.pins = a.pins ∧ ds'.size ≤ (pre.decls ++ ds).size := by
  -- the big frame of the passes (the store tier's arrays and `IW`; `CTL` words below 64)
  let A : List ArrId := lowTierArrs ++ [IW]
  let C : List Word := (List.range 64).map UInt64.ofNat ++ [200]
  have hA75 : HSEEN ∉ A := by decide
  have hA76 : HNIX ∉ A := by decide
  have hC73 : (73 : Word) ∉ C := by decide
  have hC75 : (75 : Word) ∉ C := by decide
  have pfr_mf : ∀ {ord mk nw : Word} {m₁ m₂ : Mem}, PFr ord mk nw m₁ m₂ → MemFrame A C m₁ m₂ := by
    intro ord mk nw m₁ m₂ hf
    refine ⟨fun b hb _ => hf.1 b ?_ ?_, fun x hx => hf.2.1 x ?_, hf.2.2.1, hf.2.2.2.1⟩
    · exact fun hl => hb (List.mem_append_left _ hl)
    · intro e; exact hb (List.mem_append_right _ (by simp [e]))
    · exact Nat.le_of_not_lt fun hlt =>
        hx (List.mem_append_left _ (List.mem_map.mpr ⟨x.toNat, List.mem_range.mpr hlt, by simp⟩))
  have iw_mf : ∀ {m₁ m₂ : Mem}, MemFrame [IW] [200] m₁ m₂ → MemFrame A C m₁ m₂ := fun hf =>
    hf.mono (by simp [A]) (by intro x hx; simp at hx; subst hx; simp [C])
  have iw_mf0 : ∀ {m₁ m₂ : Mem}, MemFrame [IW] [] m₁ m₂ → MemFrame A C m₁ m₂ := fun hf =>
    hf.mono (by simp [A]) (by simp)
  have seen_mf : ∀ {m₁ m₂ : Mem}, MemFrame A C m₁ m₂ → (∃ s, SeenR m₁ s) → ∃ s, SeenR m₂ s :=
    fun hf ⟨s, hs⟩ => ⟨s, memoRG_frame hsSch hsSch_wf bmKey _ A C hA75 hC73 _ _ hf _ hs⟩
  have nix_mf : ∀ {m₁ m₂ : Mem}, MemFrame A C m₁ m₂ → (∃ idx, NixR m₁ idx) → ∃ idx, NixR m₂ idx :=
    fun hf ⟨idx, hs⟩ => ⟨idx, memoRV_frame hnSch hnSch_wf nmKey _ A C hA76 hC75 _ _ hf
      (fun _ _ h => h) idx hs⟩
  -- the checks
  generalize hdsA : pre.decls ++ ds = dsAll at hD hn hDsz
  have hsz := hI.2.2.1
  have htsz : iwTop m ≤ (m.arr64 IW).size := hI.1
  cases n with
  | zero => simp [pPrepW] at h
  | succ n =>
  simp only [pPrepW, hnpw] at h
  by_cases hlt : rdW (m.arr64 DECL) 0 < np
  · rw [if_pos hlt] at h; cases h
  rw [if_neg hlt] at h
  by_cases hbig : 576460752303423488 ≤ rdW (m.arr64 DECL) 0
  · rw [if_pos hbig] at h; cases h
  rw [if_neg hbig] at h
  generalize hnw : rdW (m.arr64 DECL) 0 = nw at h hn hlt hbig
  have hn59 : nw.toNat < 2 ^ 59 := by
    have := UInt64.not_le.mp hbig; rw [UInt64.lt_iff_toNat_lt] at this; simpa using this
  have hnpn : np.toNat ≤ nw.toNat := by
    have := UInt64.not_lt.mp hlt; rw [UInt64.le_iff_toNat_le] at this; exact this
  -- the two slices
  cases ha₁ : allocW m nw with
  | none => rw [ha₁] at h; simp [pPrepW.k_iw_alloc.eq_1] at h
  | some rr =>
  obtain ⟨ord, m₁⟩ := rr
  rw [ha₁, pPrepW.k_iw_alloc.arm1] at h
  obtain ⟨hA₁, hord, htop₁, hroom₁⟩ := allocW_afr ha₁ hI
  cases ha₂ : allocW m₁ nw with
  | none => rw [ha₂] at h; simp [pPrepW.k_iw_alloc_2.eq_1] at h
  | some rr =>
  obtain ⟨mk, m₂⟩ := rr
  rw [ha₂, pPrepW.k_iw_alloc_2.arm1] at h
  obtain ⟨hA₂, hmk, htop₂, hroom₂⟩ := allocW_afr ha₂ hA₁.2.2
  have hsz₁ : (m₁.arr64 IW).size = (m.arr64 IW).size := hA₁.1.2.2.1 IW
  have hsz₂ : (m₂.arr64 IW).size = (m.arr64 IW).size := by rw [hA₂.1.2.2.1 IW, hsz₁]
  -- the marks zeroed
  cases hz : hZeroW n m₂ mk nw 0 with
  | none => rw [hz] at h; simp [pPrepW.k_hoist_zero.eq_1] at h
  | some rr =>
  obtain ⟨z₃, m₃⟩ := rr
  rw [hz, pPrepW.k_hoist_zero.arm1] at h
  obtain ⟨hf₃, hrd₃⟩ := hZero_ok n m₂ m₃ mk nw 0 z₃ (by rw [hsz₂]; omega) (by rw [hsz₂]; exact hsz) hz
  have hsz₃ : (m₃.arr64 IW).size = (m.arr64 IW).size := by rw [hf₃.2.2.1 IW, hsz₂]
  have htop₃ : iwTop m₃ = iwTop m₂ := by simp only [iwTop]; rw [hf₃.2.1 200 (by simp)]
  have hmf₃ : MemFrame A C m m₃ :=
    ((iw_mf hA₁.1).trans (iw_mf hA₂.1)).trans (iw_mf0 hf₃)
  have hDECL₃ : m₃.arr64 DECL = m.arr64 DECL := hmf₃.1 DECL (by decide) (by decide)
  have hDLP₃ : m₃.arr64 DLP = m.arr64 DLP := hmf₃.1 DLP (by decide) (by decide)
  have hI₃ : IWOK m₃ := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hA₂.2.2
    have hER : m₃.arr64 EREC = m₂.arr64 EREC := hf₃.1 EREC (by decide) (by decide)
    have h129 : erTop m₃ = erTop m₂ := by simp only [erTop]; rw [hf₃.2.1 129 (by simp)]
    exact ⟨by rw [htop₃, hf₃.2.2.1 IW]; exact h1, by rw [h129, hER]; exact h2,
      by rw [hf₃.2.2.1 IW]; exact h3, by rw [hER]; exact h4, by rw [hf₃.2.2.1 CTL]; exact h5⟩
  have hA₃ : ArenaR m₃ a := by
    refine ArenaR.frame_ext [IW] [200]
      (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide)
      m m₃ ?_ a hA
    exact (hA₁.1.trans hA₂.1).trans (hf₃.mono (by simp) (by simp))
  have hE₃ : PEnv m₃ a dsAll np nw ord mk := by
    refine ⟨fun x hx => by rw [hDECL₃, hDLP₃]; exact hD x hx, by omega, hn59, hnpn,
      by omega, by omega, hI₃, hA₃⟩
  -- the marks are zero: the whole stream is unmarked
  have hunm₃ : unm m₃ mk np.toNat nw.toNat = List.range' np.toNat (nw.toNat - np.toNat) := by
    unfold unm
    apply List.filter_eq_self.mpr
    intro x hx
    have hx' := List.mem_range'.mp hx
    rw [addrN, ← rd, hrd₃ _ (by omega), if_pos (by simp; omega)]
    simp
  -- the front
  cases hfr : pFrontW n m₃ np nw ord mk 0 with
  | none => rw [hfr] at h; simp [pPrepW.k_prep_front.eq_1] at h
  | some rr =>
  obtain ⟨z₄, m₄⟩ := rr
  rw [hfr, pPrepW.k_prep_front.arm1] at h
  obtain ⟨front, rest, a₁, hrunF, hfs, hfront, hrest, hE₄, hpins₁, hpe₁, hse₁, hpf₄⟩ :=
    pFront_ok dsAll np nw ord mk n m₃ m₄ a 0 z₄ #[] hE₃ (by simp) rfl (by simp) hfr
  have hpre : (dsAll.toList.take np.toNat).drop (0 : Word).toNat = pre.decls.toList := by
    rw [← hdsA, hnp]; simp
  have hstream : recsAt dsAll (unm m₃ mk np.toNat nw.toNat) = ds := by
    rw [hunm₃, ← hdsA, hnp]
    have : nw.toNat - pre.decls.size = ds.size := by rw [hn, ← hdsA, Array.size_append]; omega
    rw [this]; exact recsAt_range pre.decls ds
  rw [hpre, hstream] at hrunF
  -- the rest
  cases hrs : pRestW n m₄ nw ord mk np np with
  | none => rw [hrs] at h; simp [pPrepW.k_prep_rest.eq_1] at h
  | some rr =>
  obtain ⟨c, m₅⟩ := rr
  rw [hrs, pPrepW.k_prep_rest.arm1] at h
  have hsz₄ : (m₄.arr64 IW).size = (m.arr64 IW).size := by rw [hpf₄.2.2.1 IW, hsz₃]
  obtain ⟨hc, hrestW, hmf₅', hkeep₅⟩ := pRest_ok nw ord mk n m₄ m₅ np np c hE₄.rg1
    (by have := hE₄.rg2; have := hE₄.iwok.1; omega) (by rw [hsz₄]; exact hsz) (Nat.le_refl _) hnpn hrs
  have hmf₅ : MemFrame A C m m₅ := (hmf₃.trans (pfr_mf hpf₄)).trans (iw_mf0 hmf₅')
  have hDECL₅ : m₅.arr64 DECL = m.arr64 DECL := hmf₅.1 DECL (by decide) (by decide)
  have hDLP₅ : m₅.arr64 DLP = m.arr64 DLP := hmf₅.1 DLP (by decide) (by decide)
  have hsz₅ : (m₅.arr64 IW).size = (m.arr64 IW).size := by rw [hmf₅.2.2.1 IW]
  have hrg2 := hE₄.rg2; have hrg1 := hE₄.rg1; have hiw4 := hE₄.iwok.1
  generalize hU : unm m₄ mk np.toNat nw.toNat = U at hrest hc hrestW
  have hUlt : ∀ x ∈ U, np.toNat ≤ x ∧ x < nw.toNat := by
    intro x hx; rw [← hU] at hx; have := mem_unm.mp hx; omega
  have hUlen : U.length ≤ nw.toNat - np.toNat := by
    rw [← hU]; unfold unm; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hFR : (front ++ rest).size = c.toNat := by
    rw [Array.size_append, hfs, hrest, hc]; simp [recsAt]
  have hO₅ : OrdR m₅ ord (front ++ rest) := by
    intro k hk
    rw [hFR] at hk
    by_cases hkn : k < np.toNat
    · have e : rdW (m₅.arr64 IW) (ord + UInt64.ofNat k) = rdW (m₄.arr64 IW) (ord + UInt64.ofNat k) := by
        rw [rdW_addr _ _ _ (by omega), rdW_addr _ _ _ (by omega), hkeep₅ _ (Or.inl (by omega))]
      obtain ⟨hlt, hfk⟩ := hfront k hkn
      rw [e, Array.getElem_append_left (by rw [hfs]; exact hkn), hDECL₅, hDLP₅]
      have hfk' : front[k] = dsAll[(rdW (m₄.arr64 IW) (ord + UInt64.ofNat k)).toNat] := by
        rw [← getElem!_pos front k (by omega), hfk, getElem!_pos dsAll _ (by omega)]
      rw [hfk']
      refine ⟨by omega, hD _ (by omega)⟩
    · have hj : k - np.toNat < U.length := by rw [hc] at hk; omega
      have e := hrestW (k - np.toNat) hj
      rw [show np.toNat + (k - np.toNat) = k by omega] at e
      have hx := hUlt _ (List.getElem_mem hj)
      have hxw : (UInt64.ofNat U[k - np.toNat]).toNat = U[k - np.toNat] := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      rw [e, hxw, Array.getElem_append_right (by rw [hfs]; omega), hDECL₅, hDLP₅]
      have hrk : rest[k - front.size]'(by rw [hrest]; simp [recsAt]; rw [hfs]; omega) =
          dsAll[U[k - np.toNat]] := by
        simp only [hrest, recsAt, List.getElem_toArray, List.getElem_map, hfs]
        exact getElem!_pos dsAll _ (by omega)
      rw [hrk]
      exact ⟨by omega, hD _ (by omega)⟩
  -- the hoist
  have hP₅ : PinsR m₅ a₁.pins := by
    rw [hpins₁]; exact hP.congr (hmf₅.1 PINS (by decide) (by decide))
  have hI₅ : IWOK m₅ := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hE₄.iwok
    have hER : m₅.arr64 EREC = m₄.arr64 EREC := hmf₅'.1 EREC (by decide) (by decide)
    have h200 : iwTop m₅ = iwTop m₄ := by simp only [iwTop]; rw [hmf₅'.2.1 200 (by simp)]
    have h129 : erTop m₅ = erTop m₄ := by simp only [erTop]; rw [hmf₅'.2.1 129 (by simp)]
    exact ⟨by rw [h200, hmf₅'.2.2.1 IW]; exact h1, by rw [h129, hER]; exact h2,
      by rw [hmf₅'.2.2.1 IW]; exact h3, by rw [hER]; exact h4, by rw [hmf₅'.2.2.1 CTL]; exact h5⟩
  have htop₅ : iwTop m₅ = iwTop m₄ := by simp only [iwTop]; rw [hmf₅'.2.1 200 (by simp)]
  have hA₅ : ArenaR m₅ a₁ := by
    refine ArenaR.frame_ext [IW] [] (by
      intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide)
      (by simp) m₄ m₅ hmf₅' a₁ hE₄.arena
  cases hho : hNatOpGroundW p n m₅ ord c with
  | none => rw [hho] at h; simp [pPrepW.k_hoist_nat_op_ground.eq_1] at h
  | some rr =>
  obtain ⟨ord', m₆⟩ := rr
  rw [hho, pPrepW.k_hoist_nat_op_ground.arm1] at h
  obtain ⟨res, hrunH, hres, hO₆, hA₆, hI₆, hG₆, hord₆, hP₆, hmf₆⟩ :=
    hNatOpGround_ok p hx n m₅ m₆ a₁ (front ++ rest) ord c ord' hA₅ (seen_mf hmf₅ hseen)
      (nix_mf hmf₅ hnix) hO₅ hFR (by omega) hI₅ (by rw [htop₅]; omega) hP₅ hho
  -- the rewrite of `DECL`
  cases ha₃ : allocW m₆ (8 * c) with
  | none => rw [ha₃] at h; simp [pPrepW.k_iw_alloc_3.eq_1] at h
  | some rr =>
  obtain ⟨t, m₇⟩ := rr
  rw [ha₃, pPrepW.k_iw_alloc_3.arm1] at h
  have hc8 : (8 * c).toNat = 8 * c.toNat := by
    rw [UInt64.toNat_mul]; have : (8 : Word).toNat = 8 := rfl; rw [this]; omega
  obtain ⟨hA₇, ht, htop₇, hroom₇⟩ := allocW_afr ha₃ hI₆
  rw [hc8] at htop₇ hroom₇
  cases hcp : pCopyW n m₇ ord' c t 0 with
  | none => rw [hcp] at h; simp [pPrepW.k_prep_copy.eq_1] at h
  | some rr =>
  obtain ⟨z₈, m₈⟩ := rr
  rw [hcp, pPrepW.k_prep_copy.arm1] at h
  cases hbk : pBackW n m₈ t c 0 with
  | none => rw [hbk] at h; simp [pPrepW.k_prep_back.eq_1] at h
  | some rr =>
  obtain ⟨z₉, m₉⟩ := rr
  rw [hbk, pPrepW.k_prep_back.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hD₆ : m₆.arr64 DECL = m₅.arr64 DECL := hmf₆.1 DECL (by decide) (by decide)
  have hP₆' : m₆.arr64 DLP = m₅.arr64 DLP := hmf₆.1 DLP (by decide) (by decide)
  have hD₇ : m₇.arr64 DECL = m₆.arr64 DECL := hA₇.1.1 DECL (by decide) (by decide)
  have hP₇ : m₇.arr64 DLP = m₆.arr64 DLP := hA₇.1.1 DLP (by decide) (by decide)
  have hDs₇ : (m₇.arr64 DECL).size = (m.arr64 DECL).size := by rw [hD₇, hD₆, hDECL₅]
  have hcn : c.toNat ≤ nw.toNat := by rw [hc]; omega
  have hIW₇ : ∀ i < c.toNat, rdW (m₇.arr64 IW) (ord' + UInt64.ofNat i) =
      rdW (m₆.arr64 IW) (ord' + UInt64.ofNat i) := by
    intro i hi
    have hn : (ord' + UInt64.ofNat i).toNat = ord'.toNat + i :=
      addW_toNat _ _ (by have := hI₆.1; have := hI₆.2.2.1; omega)
    simp only [rdW, hn]; rw [hA₇.2.1.2.2.1 _ (by omega)]
  obtain ⟨hdw, hmf₉, -, hD0, -⟩ := pCopyBack_ok n n m₇ m₈ m₉ ord' c t z₈ z₉
    (fun i hi => by rw [hIW₇ i hi]; exact (hO₆ i (by omega)).1)
    (by rw [hDs₇, ← hdsA] at *; omega) (by rw [ht]; exact hord₆)
    (by rw [hA₇.1.2.2.1 IW]; omega) hA₇.2.2.2.2.1 (by rw [hDs₇]; exact hDsz') hcp hbk
  have hD₉s : (m₉.arr64 DECL).size = (m.arr64 DECL).size := by rw [hmf₉.2.2.1 DECL, hDs₇]
  have hP₉ : m₉.arr64 DLP = m₆.arr64 DLP := by rw [hmf₉.1 DLP (by decide) (by decide), hP₇]
  have hfin : (m₉.set64 DECL 0 c).arr64 DECL = (m₉.arr64 DECL).set! 0 c := Mem.arr64_set64_same _ _ _ _
  have hfinP : (m₉.set64 DECL 0 c).arr64 DLP = m₉.arr64 DLP := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  -- record `i` after is record `ord'[i]` before
  have hdw' : ∀ i < c.toNat, ∀ k < 8, dw ((m₉.set64 DECL 0 c).arr64 DECL) i k =
      dw (m₆.arr64 DECL) (rdW (m₆.arr64 IW) (ord' + UInt64.ofNat i)).toNat k := by
    intro i hi k hk
    rw [hfin, ← hD₇, ← hIW₇ i hi, ← hdw i hi k hk]
    simp only [dw, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    rw [if_neg (by omega)]
  refine ⟨res.1, a₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpe₁, hse₁, hpins₁, by rw [hres]; omega⟩
  · simp only [preparePrelude, prepareD]
    rw [HoistTwin.run_bind, HoistTwin.run_bind, hrunF]
    simp only
    rw [HoistTwin.run_bind, hrunH]
    rfl
  · have h0 : 0 < (m₉.arr64 DECL).size := by rw [hD₉s]; omega
    rw [hfin]
    simp only [rdW, UInt64.toNat_zero, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      h0, and_self, if_true, Option.getD_some, hres]
  · intro x hx
    have hx' : x < c.toNat := hres ▸ hx
    obtain ⟨-, hDx, hRx⟩ := hO₆ x hx
    rw [hfinP, hP₉]
    exact ⟨declAtF_congr (hdw' x hx') hDx, recOK_congr (hdw' x hx') hRx⟩
  · have hf : MemFrame [IW, DECL] [200] m₆ (m₉.set64 DECL 0 c) :=
      ((hA₇.1.mono (by simp) (by simp)).trans (hmf₉.mono (by simp) (by simp))).trans
        ((MemFrame.set64 m₉ DECL (by decide) _ _).mono (by simp) (by simp))
    exact ArenaR.frame_ext _ _
      (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl <;> decide)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide)
      _ _ hf a₁ hA₆
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hA₇.2.2
    have hf : MemFrame [IW, DECL] [] m₇ (m₉.set64 DECL 0 c) :=
      hmf₉.trans ((MemFrame.set64 m₉ DECL (by decide) _ _).mono (by simp) (by simp))
    have hER : (m₉.set64 DECL 0 c).arr64 EREC = m₇.arr64 EREC := hf.1 EREC (by decide) (by decide)
    have h200 : iwTop (m₉.set64 DECL 0 c) = iwTop m₇ := by simp only [iwTop]; rw [hf.2.1 200 (by simp)]
    have h129 : erTop (m₉.set64 DECL 0 c) = erTop m₇ := by simp only [erTop]; rw [hf.2.1 129 (by simp)]
    exact ⟨by rw [h200, hf.2.2.1 IW]; exact h1, by rw [h129, hER]; exact h2,
      by rw [hf.2.2.1 IW]; exact h3, by rw [hER]; exact h4, by rw [hf.2.2.1 CTL]; exact h5⟩
  · refine hP₆.congr ?_
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hmf₉.1 PINS (by decide) (by decide),
      hA₇.1.1 PINS (by decide) (by decide)]
  · rw [hfinP, hP₉, hP₆', hDLP₅]
  · rw [hfin]; simp [hD₉s]

/-- **`prepare_prelude()` refines `preparePrelude pre ds`**: from the prelude's records followed by
the stream's in `DECL` (their number in its word `0`, the prelude's in `CTL[240]`), when L returns,
the twin succeeds, `DECL` represents the prepared array (with the same per-record facts), and
the store relation and the pins hold at the twin's state after. (`movedNames`, which
`preparePrelude` drops, is not computed: D30.) -/
@[refines ConRon.Arena.Frontend.preparePrelude]
theorem preparePrelude_refines (p : Prog) (hp : PrepProg p) (hn : PrepExt p) (hh : HoistProg p)
    (hx : HoistExt p) (n : Nat) (s₀ : St) (a : AState) (pre : PreludeIx) (ds : Array IDeclaration)
    (hD : ∀ x (h : x < (pre.decls ++ ds).size),
      DeclAtF (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x (pre.decls ++ ds)[x] ∧
      RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x)
    (hns : (rdW (s₀.mem.arr64 DECL) 0).toNat = (pre.decls ++ ds).size)
    (hnp : (rdW (s₀.mem.arr64 CTL) 240).toNat = pre.decls.size)
    (hDsz : 1 + 8 * (pre.decls ++ ds).size ≤ (s₀.mem.arr64 DECL).size)
    (hDsz' : (s₀.mem.arr64 DECL).size < 2 ^ 64)
    (hA : ArenaR s₀.mem a) (hseen : ∃ s, SeenR s₀.mem s) (hnix : ∃ idx, NixR s₀.mem idx)
    (hI : IWOK s₀.mem) (hP : PinsR s₀.mem a.pins) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "prepare_prelude" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ ds' a', (preparePrelude pre ds).run a = .ok (ds', a') ∧
      (rdW (s'.mem.arr64 DECL) 0).toNat = ds'.size ∧
      (∀ x (h : x < ds'.size), DeclAtF (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x ds'[x] ∧
        RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x) ∧
      ArenaR s'.mem a' ∧ IWOK s'.mem ∧ PinsR s'.mem a'.pins ∧ s'.mem.arr64 DLP = s₀.mem.arr64 DLP ∧
      (s'.mem.arr64 DECL).size = (s₀.mem.arr64 DECL).size ∧ a'.store.pers = a.store.pers ∧
      a'.store.scr = a.store.scr ∧ a'.pins = a.pins ∧ ds'.size ≤ (pre.decls ++ ds).size; ⊤⦄ :=
  triple_post (preparePrelude_spec p hp hn hh hx n s₀) (fun r s' h =>
    ⟨h.1, pPrepCore_ok p hx n s₀.mem s'.mem a pre ds _ (r.headD 0) hD hns hnp hDsz hDsz' hA hseen
      hnix hI hP rfl h.2⟩)

attribute [refines ConRon.Arena.Frontend.frontOf] pFront_ok

end L.Checker
