import ConAgua.Front.IndInstallRefine4
import ConAgua.Front.IndApplyRefine5
import ConAgua.Front.IndInstallRefine3
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `install_ind_d` refines `installIndD`, V: the block

`installW_twin`: `install_ind_d` (after `validate_ind_d`) against the twin's `installIndD`: the
block's slots and constant records in `DLP`, above the old top, pushed as one `DECL` record of kind
`6`; the result is the twin's state with the `indDecl` pushed (`StateDR`, `IndDeclAt` with `t` the
final top), the arena untouched (`ArenaD`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)


namespace L.Front.Ind

instance : Inhabited IndTypeRec := ⟨⟨⟨0, [], 0⟩, [], false, false, false, 0, 0, 0⟩⟩
instance : Inhabited IndRecRec := ⟨⟨⟨0, [], 0⟩, false, false, 0, 0, 0, 0, []⟩⟩

theorem CVF.congr {b : ByteArray} {m m' : Mem} {p : Nat} {cv : CVRec} (h : m'.arr64 IFR = m.arr64 IFR)
    (hF : CVF b m p cv) : CVF b m' p cv := by
  unfold CVF wd at *; rw [h]; exact hF

theorem CtF.congr {b : ByteArray} {m m' : Mem} {p : Nat} {ct : IndCtorRec} (h : m'.arr64 IFR = m.arr64 IFR)
    (hF : CtF b m p ct) : CtF b m' p ct := by
  unfold CtF CVF OptW NumW wd at *; rw [h]; exact hF

theorem RecF.congr {b : ByteArray} {m m' : Mem} {p : Nat} {rc : IndRecRec} (h : m'.arr64 IFR = m.arr64 IFR)
    (h' : m'.arr64 IFL = m.arr64 IFL) (hF : RecF b m p rc) : RecF b m' p rc := by
  unfold RecF RuleF CVF BoolW NumW topN wd at *; rw [h, h']; exact hF

theorem ofNat_toNat_lt (k : Nat) (h : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)

theorem getElem!_eq {α : Type} [Inhabited α] (l : List α) (k : Nat) (h : k < l.length) : l[k]! = l[k] :=
  getElem!_pos l k h

/-- A memory from which a frame keeps the words outside `[lo, hi)` below the top keeps a slot outside
it and a record above `hi`. -/
theorem slot_keep {m m' : Mem} {lo hi : Nat}
    (ht : topN m DLP ≤ topN m' DLP)
    (hk : ∀ i, 1 ≤ i → i ≤ topN m DLP → (i < lo ∨ hi ≤ i) → wd m' DLP i = wd m DLP i)
    {s : Nat} (hs1 : 1 ≤ s) (hs2 : s ≤ topN m DLP) (hs : s < lo ∨ hi ≤ s)
    {ci : IConstantInfo} (hhi : 1 ≤ hi) (hp : hi ≤ (wd m DLP s).toNat) (hr : RecAt m (wd m DLP s).toNat ci) :
    wd m' DLP s = wd m DLP s ∧ RecAt m' (wd m' DLP s).toNat ci := by
  have e := hk s hs1 hs2 hs
  refine ⟨e, ?_⟩
  rw [e]
  exact hr.keep ht (fun i h1 h2 => hk i (by omega) h2 (.inr (by omega)))

theorem block_get {α : Type} [Inhabited α] (A B C : List α) (j : Nat) :
    (A ++ B ++ C)[j]! = if j < A.length then A[j]! else if j < A.length + B.length then B[j - A.length]!
      else C[j - A.length - B.length]! := by
  rw [List.append_assoc]
  by_cases h1 : j < A.length
  · rw [ite_eq_left h1, getElem!_pos (A ++ (B ++ C)) j (by simp; omega), getElem!_pos A j h1,
      List.getElem_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : j < A.length + B.length
    · rw [ite_eq_left h2, getElem!_pos (A ++ (B ++ C)) j (by simp; omega), getElem!_pos B (j - A.length) (by omega),
        List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
    · rw [ite_eq_right h2]
      by_cases h3 : j < A.length + B.length + C.length
      · rw [getElem!_pos (A ++ (B ++ C)) j (by simp; omega), getElem!_pos C (j - A.length - B.length) (by omega),
          List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      · rw [getElem!_neg (A ++ (B ++ C)) j (by simp; omega), getElem!_neg C (j - A.length - B.length) (by omega)]

theorem getElem?_of_wd {m m' : Mem} {j : Nat} (hs : (m'.arr64 DLP).size = (m.arr64 DLP).size)
    (hj : j < (m.arr64 DLP).size) (h : wd m' DLP j = wd m DLP j) : (m'.arr64 DLP)[j]? = (m.arr64 DLP)[j]? := by
  rw [wd_some _ _ _ (by omega), wd_some _ _ _ hj, h]

/-- **`install_ind_d` refines `installIndD`.** -/
@[refines ConRon.Arena.Frontend.installIndD]
theorem installW_twin {b : ByteArray} {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hA : ArenaD m a) (hD : StateDR m st)
    {to tn co cn ro rn oo np : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {ordered : List IndCtorRec}
    (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (hIFL : topN m IFL < 2 ^ 62) (hord : ordered.length = cts.length)
    (hoo : oo.toNat + cts.length < 2 ^ 63)
    (hptr : ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
      wd m IFL (oo.toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k])
    (h : installW n b.data m to tn oo cn ro rn np = some m') :
    ∃ st', (ConRon.Arena.Frontend.installIndD st tys ordered rcs np.toNat).run a = .ok (st', a) ∧
      ArenaD m' a ∧ StateDR m' st' ∧ MemFrame [DLP, DECL] [] m m' := by
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
  -- the twin
  have rT : (tys.mapM (tyT st)).run a = .ok (tys.map fun t => resOf (tyT st t) a, a) :=
    mapM_run _ _ a tys (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      have := (T5 k hk (Nat.zero_le _)).1; rwa [getElem!_eq _ _ hk] at this)
  have rC : (ordered.mapM (ctT st)).run a = .ok (ordered.map fun c => resOf (ctT st c) a, a) :=
    mapM_run _ _ a ordered (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      have := (C5 k (hord ▸ hk) (Nat.zero_le _)).1; rwa [getElem!_eq _ _ hk] at this)
  have rR : (rcs.mapM (recT st)).run a = .ok (rcs.map fun r => resOf (recT st r) a, a) :=
    mapM_run _ _ a rcs (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      have := (R5 k hk (Nat.zero_le _)).1; rwa [getElem!_eq _ _ hk] at this)
  refine ⟨{ st with decls := st.decls.push (.indDecl ((tys.map fun t => resOf (tyT st t) a) ++
    (ordered.map fun c => resOf (ctT st c) a) ++ (rcs.map fun r => resOf (recT st r) a)) np.toNat) },
    ?_, ?_, ?_, (hfr4.mono (by simp) (by simp)).trans (G1.mono (by simp) (by simp))⟩
  · have rT' : (tys.mapM fun t => (do pure (IConstantInfo.indInfo (← parseCVD st t.cv) {}) : AM _)).run a =
        .ok (tys.map fun t => resOf (tyT st t) a, a) := rT
    have rC' : (ordered.mapM fun c => (do
        pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields) : AM _)).run a =
        .ok (ordered.map fun c => resOf (ctT st c) a, a) := rC
    have rR' : (rcs.mapM fun r => (do
        let rules ← r.rules.mapM (ConRon.Arena.Frontend.parseRuleD st)
        pure (IConstantInfo.recInfo (← parseCVD st r.cv)
          (r.numParams + r.numMotives + r.numMinors + r.numIndices)
          (r.numParams + r.numMotives + r.numMinors) rules) : AM _)).run a =
        .ok (rcs.map fun r => resOf (recT st r) a, a) := rR
    unfold ConRon.Arena.Frontend.installIndD
    rw [run_bind _ _ a _ rT', run_bind _ _ a _ rC', run_bind _ _ a _ rR']; rfl
  · have hf : MemFrame [DLP, DECL] [] m m' :=
      (hfr4.mono (by simp) (by simp)).trans (G1.mono (by simp) (by simp))
    exact ⟨ArenaR.frame_ext _ _ (by simp [DLP, DECL]) (by simp) _ _ hf _ hA.1,
      DerR.frameT hf (by simp [DLP, DECL]) hA.2⟩
  · -- `StateDR`: the record pushed
    have hf : MemFrame [DLP, DECL] [] m m' :=
      (hfr4.mono (by simp) (by simp)).trans (G1.mono (by simp) (by simp))
    have hfr : ∀ B, B ≠ DLP → B ≠ DECL → B ≠ CTL → m'.arr64 B = m.arr64 B :=
      fun B h1 h2 h3 => hf.1 B (by simp [h1, h2]) h3
    have hcn' : (rdW (m.arr64 DECL) 0).toNat = st.decls.size := hD.decls.count
    have hm'P : m'.arr64 DLP = m₄.arr64 DLP := G1.1 DLP (by simp) (by decide)
    have hc1 : (rdW (m.arr64 DECL) 0 + 1).toNat = (rdW (m.arr64 DECL) 0).toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hD0 : (m'.arr64 DECL)[0]?.getD 0 = rdW (m.arr64 DECL) 0 + 1 := by rw [G4]; rfl
    have hs4 : (m₄.arr64 DLP).size = (m.arr64 DLP).size := hfr4.2.2.1 DLP
    have hpt4 := R3.ptop
    have hP0 : ((m'.arr64 DLP)[0]?.getD 0).toNat = topN m₄ DLP := by rw [hm'P]; rfl
    have hP00 : ((m.arr64 DLP)[0]?.getD 0).toNat = topN m DLP := rfl
    have hkeep : ∀ j, 1 ≤ j → j ≤ topN m DLP → wd m₄ DLP j = wd m DLP j := fun j h1 h2 => by
      rw [R4 j h1 (by omega) (.inl (by omega)), C4 j h1 (by omega) (.inl (by omega)),
        T4 j h1 (by omega) (.inl (by omega)), P1.keep j h1 h2]
    refine ⟨hD.names.frame hf (.inl rfl) (by simp [DLP, DECL, idArrs]) (by simp),
      hD.levels.frame hf (.inr (.inl rfl)) (by simp [DLP, DECL, idArrs]) (by simp),
      hD.exprs.frame hf (.inr (.inr rfl)) (by simp [DLP, DECL, idArrs]) (by simp), ?_,
      by rw [hf.2.2.1, hf.2.2.1]; exact hD.ifs⟩
    rw [hcn'] at G3 G5
    refine DeclsF.push _ _ _ _ _ _ hD.decls (by rw [G1.2.2.1, hdecl4]) (by rw [hm'P, hs4])
      (by rw [hD0, hc1, hcn']) (by rw [← hdecl4]; omega)
      (by rw [hP0, hP00]; omega) (by rw [hP0]; rw [hs4] at hpt4; omega)
      (fun j hj0 hj => by rw [G5 j hj0 hj, hdecl4])
      (fun j hj0 hj => by rw [hm'P]; exact getElem?_of_wd hs4 (by omega) (hkeep j hj0 (by omega))) ?_
    -- the new record
    unfold DeclAtF
    rw [← hcn']
    refine ⟨w0, by rw [w4], topN m₄ DLP, by rw [hP0]; exact Nat.le_refl _, ?_⟩
    rw [w2, w3, hN, hm'P]
    unfold decCIs
    have hAg : ∀ p, 1 ≤ p → AgreesFrom (trunc (m₄.arr64 DLP) (topN m₄ DLP)) m₄ p := fun p hp i h1 h2 => by
      rw [trunc_get _ _ _ (by omega) h2 (by omega), wd_some _ _ _ (by omega)]
    have hslot : ∀ s ci, 1 ≤ s → s ≤ topN m₄ DLP → 1 ≤ (wd m₄ DLP s).toNat →
        RecAt m₄ (wd m₄ DLP s).toNat ci →
        (do L.Arena.decCI (trunc (m₄.arr64 DLP) (topN m₄ DLP)) (fun _ => none)
                (← L.Arena.nat? (trunc (m₄.arr64 DLP) (topN m₄ DLP)) s)) = some ci := by
      intro s ci h1 h2 h3 hr
      have e : (trunc (m₄.arr64 DLP) (topN m₄ DLP))[s]? = some (wd m₄ DLP s) := hAg 1 (Nat.le_refl _) s h1 h2
      simp [L.Arena.nat?, e, hr _ (hAg _ h3)]
    have hTlen : (tys.map fun t => resOf (tyT st t) a).length = tys.length := by simp
    have hClen : (ordered.map fun c => resOf (ctT st c) a).length = cts.length := by simp [hord]
    have hRlen : (rcs.map fun r => resOf (recT st r) a).length = rcs.length := by simp
    rw [mapM_some_ofI _ (fun j => ((tys.map fun t => resOf (tyT st t) a) ++
        (ordered.map fun c => resOf (ctT st c) a) ++ (rcs.map fun r => resOf (recT st r) a))[j]!) _
      (fun j hj => ?_)]
    · congr 1
      have := range_map_getElem! ((tys.map fun t => resOf (tyT st t) a) ++
        (ordered.map fun c => resOf (ctT st c) a) ++ (rcs.map fun r => resOf (recT st r) a)) id
      simp only [List.map_id, List.length_append, hTlen, hClen, hRlen, id] at this
      exact this
    have hj' := List.mem_range.mp hj
    rw [block_get, hTlen, hClen]
    by_cases h1 : j < tys.length
    · rw [ite_eq_left h1, getElem!_pos _ _ (by simp; omega), List.getElem_map]
      obtain ⟨-, x2, x3⟩ := T5 j h1 (Nat.zero_le _)
      rw [getElem!_eq _ _ h1] at x3
      obtain ⟨y1, y2⟩ := slot_keep C2 C4 (s := bo.toNat + j) (by omega) (by omega) (.inl (by omega))
        (by omega) (by omega) x3
      obtain ⟨z1, z2⟩ := slot_keep R2 R4 (s := bo.toNat + j) (by omega) (by omega) (.inl (by omega))
        (by omega) (by rw [y1]; omega) y2
      exact hslot _ _ (by omega) (by omega) (by rw [z1, y1]; omega) z2
    rw [ite_eq_right h1]
    by_cases h2 : j < tys.length + cts.length
    · rw [ite_eq_left h2, getElem!_pos _ _ (by simp; omega), List.getElem_map]
      obtain ⟨-, x2, x3⟩ := C5 (j - tys.length) (by omega) (Nat.zero_le _)
      rw [getElem!_eq _ _ (by omega), show bo.toNat + tys.length + (j - tys.length) = bo.toNat + j by omega]
        at x3
      rw [show bo.toNat + tys.length + (j - tys.length) = bo.toNat + j by omega] at x2
      obtain ⟨z1, z2⟩ := slot_keep R2 R4 (s := bo.toNat + j) (by omega) (by omega) (.inl (by omega))
        (by omega) (by omega) x3
      exact hslot _ _ (by omega) (by omega) (by rw [z1]; omega) z2
    · rw [ite_eq_right h2, getElem!_pos _ _ (by simp; omega), List.getElem_map]
      obtain ⟨-, x2, x3⟩ := R5 (j - tys.length - cts.length) (by omega) (Nat.zero_le _)
      rw [getElem!_eq _ _ (by omega),
        show bo.toNat + tys.length + cts.length + (j - tys.length - cts.length) = bo.toNat + j by omega] at x3
      rw [show bo.toNat + tys.length + cts.length + (j - tys.length - cts.length) = bo.toNat + j by omega] at x2
      exact hslot _ _ (by omega) (by omega) (by omega) x3

end L.Front.Ind
