import ConAgua.Front.FrontPreOK1
import ConAgua.Front.IndApplyTwin

/-!
# The frontend's records, word by word, II: an inductive line (lane `pipeline`)

`applyIndW_grow`: a successful `apply_ind` (on con-leche's `ok` path of the block's scan) appends
one record of kind `6` whose block offset is the old top of `DLP` plus one, and changes neither the
old records nor the pool up to its old top (`DGrow`). `installW_grow` is the first part of
`installW_twin`'s proof (`IndInstallRefine5.lean`, up to the record's push): the frames come out of
the twin's install loop (`instGo_twin`), so the twin's hypotheses stay.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec DeclRec scanIndDecl)


namespace L.Front.Ind

/-- **`install_ind_d` appends one inductive record.** -/
theorem installW_grow {b : ByteArray} {n : Nat} {m m' : Mem} (a : AState) {st : StateD}
    (hD : StateDR m st)
    {to tn co cn ro rn oo np : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {ordered : List IndCtorRec}
    (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (hIFL : topN m IFL < 2 ^ 62) (hord : ordered.length = cts.length)
    (hoo : oo.toNat + cts.length < 2 ^ 63)
    (hptr : ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
      wd m IFL (oo.toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k])
    (h : installW n b.data m to tn oo cn ro rn np = some m') : DGrow m m' := by
  obtain ⟨hTn, hTy, hCn, hCt, hRn, hRc⟩ := hF
  have hL := StateDR.lkR hD
  have hps := hL.psize
  have hpt := hL.ptop
  have hTyB := hTy.2.1
  have hCtB := hCt.2.1
  have hRcB := hRc.2.1
  cases n with
  | zero => simp [installW] at h
  | succ n =>
  simp only [installW] at h
  split at h; cases h; rename_i hbig
  have ht32 : tn.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (.inl (UInt64.le_iff_toNat_le.mpr (by simp; omega)))
  have hc32 : cn.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (.inr (.inl (UInt64.le_iff_toNat_le.mpr (by simp; omega))))
  have hr32 : rn.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (.inr (.inr (UInt64.le_iff_toNat_le.mpr (by simp; omega))))
  have hN : (tn + cn + rn).toNat = tys.length + cts.length + rcs.length := by
    rw [UInt64.toNat_add, UInt64.toNat_add]; omega
  rcases h1 : allocW m DLP (tn + cn + rn) with _ | ⟨bo, m₁⟩ <;> simp only [h1, allocK, reduceCtorEq] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hps hpt h1
  rw [hN] at P3 P4
  have hL1 : LkR m₁ st := hL.frame P1.frame (by rw [P3, P1.size DLP]; omega)
  rcases h2 : instTypesW n b.data m₁ bo to tn 0 with _ | m₂ <;> simp only [h2, mK, reduceCtorEq] at h
  rcases h3 : instCtorsW n b.data m₂ (bo + tn) oo cn 0 with _ | m₃ <;> simp only [h3, reduceCtorEq] at h
  rcases h4 : instRecsW n b.data m₃ (bo + tn + cn) ro rn 0 with _ | m₄ <;> simp only [h4, reduceCtorEq] at h
  have hifr1 : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hifl1 : m₁.arr64 IFL = m.arr64 IFL := P1.other IFL (by decide) (by decide)
  -- the types
  rw [instTypesW_eq] at h2
  obtain ⟨T1, T2, T3, T4, T5⟩ := instGo_twin a tys (tyT st) (fun _ m p => typeW b.data m p)
    (fun _ j => to + 11 * j) m₁ bo tn hTn (fun n' mi k q mo hLi hf hk hR => by
      have hifr : mi.arr64 IFR = m.arr64 IFR := by rw [hf.1 IFR (by decide) (by decide), hifr1]
      have hk' := ofNat_toNat_lt k (by omega)
      have hw : (to + 11 * UInt64.ofNat k).toNat = to.toNat + 11 * k := by
        have := w_addmul to (UInt64.ofNat k) 11 (by decide) (by rw [hk']; omega)
        rw [hk'] at this; exact this
      rw [getElem!_eq _ _ hk]
      exact typeW_twin a hLi (by rw [hw]; exact ((hTy.2.2 k hk).1).congr hifr) (by rw [hw]; omega) hR)
    n m₁ m₂ 0 hL1 (MemFrame.refl _ _ _) (by simp) (by omega) (by omega) h2
  simp only [UInt64.toNat_zero, Nat.add_zero] at T4 T5
  -- the constructors
  have hbt : (bo + tn).toNat = bo.toNat + tys.length := by rw [widx2 _ _ (by omega), hTn]
  rw [instCtorsW_eq] at h3
  obtain ⟨C1, C2, C3, C4, C5⟩ := instGo_twin a ordered (ctT st) (fun _ m p => ctorRW b.data m p)
    (fun m j => rdW (m.arr64 IFL) (oo + j)) m₂ (bo + tn) cn (by rw [hCn, hord])
    (fun n' mi p q mo hLi hf hp hR => by
      have hifr : mi.arr64 IFR = m.arr64 IFR := by
        rw [hf.1 IFR (by decide) (by decide), T1.1 IFR (by decide) (by decide), hifr1]
      have hifl : mi.arr64 IFL = m.arr64 IFL := by
        rw [hf.1 IFL (by decide) (by decide), T1.1 IFL (by decide) (by decide), hifl1]
      obtain ⟨k, hk, hw, hok⟩ := hptr p hp
      have hp' := ofNat_toNat_lt p (by omega)
      have hrd : rdW (mi.arr64 IFL) (oo + UInt64.ofNat p) = co + 10 * UInt64.ofNat k := by
        rw [hifl, rdW_wdI _ _ _ _ (by rw [hp']; omega), hp', hw]
      have hk' := ofNat_toNat_lt k (by omega)
      have hw' : (co + 10 * UInt64.ofNat k).toNat = co.toNat + 10 * k := by
        have := w_addmul co (UInt64.ofNat k) 10 (by decide) (by rw [hk']; omega)
        rw [hk'] at this; exact this
      rw [getElem!_eq _ _ hp, hok]
      rw [hrd] at hR
      exact ctorRW_twin a hLi (by rw [hw']; exact (hCt.2.2 k hk).congr hifr) (by rw [hw']; omega) hR)
    n m₂ m₃ 0 T3 (MemFrame.refl _ _ _) (by simp) (by rw [hbt]; omega) (by rw [hbt, hord]; omega) h3
  rw [hbt, hord] at C4 C5
  simp only [UInt64.toNat_zero, Nat.add_zero] at C4 C5
  -- the recursors
  have hbtc : (bo + tn + cn).toNat = bo.toNat + tys.length + cts.length := by
    rw [widx2 _ _ (by rw [hbt]; omega), hbt, hCn]
  rw [instRecsW_eq] at h4
  obtain ⟨R1, R2, R3, R4, R5⟩ := instGo_twin a rcs (recT st) (fun n m p => recRW n b.data m p)
    (fun _ j => ro + 11 * j) m₃ (bo + tn + cn) rn hRn
    (fun n' mi k q mo hLi hf hk hR => by
      have hifr : mi.arr64 IFR = m.arr64 IFR := by
        rw [hf.1 IFR (by decide) (by decide), C1.1 IFR (by decide) (by decide),
          T1.1 IFR (by decide) (by decide), hifr1]
      have hifl : mi.arr64 IFL = m.arr64 IFL := by
        rw [hf.1 IFL (by decide) (by decide), C1.1 IFL (by decide) (by decide),
          T1.1 IFL (by decide) (by decide), hifl1]
      have hk' := ofNat_toNat_lt k (by omega)
      have hw : (ro + 11 * UInt64.ofNat k).toNat = ro.toNat + 11 * k := by
        have := w_addmul ro (UInt64.ofNat k) 11 (by decide) (by rw [hk']; omega)
        rw [hk'] at this; exact this
      rw [getElem!_eq _ _ hk]
      exact recRW_twin a hLi (by rw [hw]; exact (hRc.2.2 k hk).congr hifr hifl) (by rw [hw]; omega)
        (by unfold topN wd; rw [hifl]; exact hIFL) hR)
    n m₃ m₄ 0 C3 (MemFrame.refl _ _ _) (by simp) (by rw [hbtc]; omega) (by rw [hbtc]; omega) h4
  rw [hbtc] at R4 R5
  simp only [UInt64.toNat_zero, Nat.add_zero] at R4 R5
  -- the push
  have hfr4 : MemFrame [DLP] [] m m₄ := P1.frame.trans (T1.trans (C1.trans R1))
  have hdecl4 : m₄.arr64 DECL = m.arr64 DECL := hfr4.1 DECL (by decide) (by decide)
  obtain ⟨G1, G2, G3, G4, G5, w0, w1, w2, w3, w4, w5, w6, w7⟩ :=
    pushW_facts m₄ m' _ _ _ _ _ _ _ _ (rdW (m.arr64 DECL) 0) (by rw [hdecl4]) h
      (by rw [hdecl4]; exact hD.decls.dsize)
  have hm'P : m'.arr64 DLP = m₄.arr64 DLP := G1.1 DLP (by simp) (by decide)
  have hs4 : (m₄.arr64 DLP).size = (m.arr64 DLP).size := hfr4.2.2.1 DLP
  have hkeep : ∀ j, 1 ≤ j → j ≤ topN m DLP → wd m₄ DLP j = wd m DLP j := fun j h1 h2 => by
    rw [R4 j h1 (by omega) (.inl (by omega)), C4 j h1 (by omega) (.inl (by omega)),
      T4 j h1 (by omega) (.inl (by omega)), P1.keep j h1 h2]
  have hc1 : (rdW (m.arr64 DECL) 0 + 1).toNat = (rdW (m.arr64 DECL) 0).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hcnt : dcnt m = (rdW (m.arr64 DECL) 0).toNat := rfl
  have hcnt' : dcnt m' = dcnt m + 1 := by
    rw [show dcnt m' = (rdW (m.arr64 DECL) 0 + 1).toNat by unfold dcnt; rw [G4]; rfl, hc1, hcnt]
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun x h1 h2 => ?_⟩
  · rw [G5 j h1 (by omega), hdecl4]
  · have h2' : j ≤ topN m DLP := h2
    rw [hm'P]; exact getElem?_of_wd hs4 (by omega) (hkeep j h1 h2')
  · have hx : x = (rdW (m.arr64 DECL) 0).toNat := by omega
    subst hx
    refine ⟨fun h6 => absurd w0 h6, fun _ => ?_⟩
    rw [w2]
    intro h0
    have := congrArg UInt64.toNat h0
    simp only [UInt64.toNat_zero] at this
    omega

theorem DGrow.ofDK {m m₁ m' : Mem} (hk : DK m m₁) (hg : DGrow m₁ m') : DGrow m m' := by
  have hc : dcnt m₁ = dcnt m := by simp only [dcnt, hk.1]
  have ht : dtop m₁ = dtop m := by simp only [dtop, hk.2]
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun x h1 h2 => hg.new x (by omega) h2⟩
  · rw [hg.decl j h1 (by omega), hk.1]
  · rw [hg.dlp j h1 (by omega), hk.2]

/-- **`apply_ind` appends one inductive record.** -/
theorem applyIndW_grow {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) {v : USize}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {e : USize}
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e)
    (h : applyIndW n b.data m v.toUInt64 = some m') : DGrow m m' := by
  cases n with
  | zero => simp [applyIndW] at h
  | succ n =>
  simp only [applyIndW] at h
  rcases h1 : indFieldsW b.data m v.toUInt64 with _ | ⟨r, m₁⟩ <;> simp only [h1, lK, reduceCtorEq] at h
  have hifs := hD.ifs
  obtain ⟨to, tn, co, cn, ro, rn, rfl, hF, hfR⟩ :=
    indFields_link b h64 hsize m m₁ ⟨by omega, by omega⟩ v tys cts rcs e hscan _ h1
  have hfr1 : MemFrame [IFR, IFL] [] m m₁ := hfR.1
  have hRoom : Room m₁ := hfR.2
  simp only [List.headD, List.tail] at h
  rcases h2 : validateW n m₁ to tn co cn ro rn with _ | ⟨⟨oo, np⟩, m₂⟩ <;> simp only [h2, pmK, reduceCtorEq] at h
  have hA1 : ArenaD m₁ a :=
    ⟨ArenaR.frame_ext _ _ (by simp [IFR, IFL]) (by simp) _ _ hfr1 _ hA.1,
      DerR.frameT hfr1 (by simp [IFR, IFL]) hA.2⟩
  have hD1 : StateDR m₁ st := hD.frame hfr1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1 : (m₁.arr64 IFR).size = (m.arr64 IFR).size := hfr1.2.2.1 IFR
  have hs1' : (m₁.arr64 IFL).size = (m.arr64 IFL).size := hfr1.2.2.1 IFL
  have hT1 : TopOK m₁ := ⟨by have := hRoom.2.1; exact this, Nat.le_of_lt hRoom.2.2.2⟩
  have hIFR1 : topN m₁ IFR < 2 ^ 62 := by have := hRoom.2.2.1; omega
  obtain ⟨ordered, V1, V2, V3, V4, V5, V6, V7, V8⟩ := validateW_twin hA1.1 hD1 hok hT1 hF hIFR1 h2
  have hfr2 := V2.frame
  have hA2 : ArenaD m₂ a :=
    ⟨ArenaR.frame_ext _ _ (by simp [IFL, LH]) (by simp) _ _ hfr2 _ hA1.1,
      DerR.frameT hfr2 (by simp [IFL, LH]) hA1.2⟩
  have hD2 : StateDR m₂ st := hD1.frame hfr2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hifr2 : m₂.arr64 IFR = m₁.arr64 IFR := V2.ifr
  have hs2' : (m₂.arr64 IFL).size = (m.arr64 IFL).size := by rw [hfr2.2.2.1 IFL, hs1']
  have hIFR2 : topN m₂ IFR < 2 ^ 62 := by unfold topN wd; rw [hifr2]; exact hIFR1
  have hIFL2 : topN m₂ IFL < 2 ^ 62 := by have := V3.2; omega
  have hk : DK m m₂ := (DK.ofFrame hfr1 (by decide) (by decide)).trans
    (DK.ofFrame hfr2 (by decide) (by decide))
  exact DGrow.ofDK hk (installW_grow a hD2 (hF.ext V2) hIFR2 hIFL2 V4 (by omega) V7 h)

end L.Front.Ind
