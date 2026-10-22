import ConAgua.Front.IndApplyRefine8
import ConAgua.Front.IndValidTwin

/-!
# The apply step of an `inductive` line against the twin, IX: `validate_ind_d` refines `validateIndD`

`validateW_twin`: a run of `validate_ind_d`'s model on the records of an inductive line
(`IndFR`) establishes the clean facts `VFacts` of the twin's validation (`IndValidTwin.lean`), so
`validateIndD` succeeds with the ordered constructors, which the model left as record pointers at
`oo`.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option linter.unusedSimpArgs false

namespace L.Front.Ind

theorem psum_fpos {b : ByteArray} {m : Mem} {to : Word} {tys : List IndTypeRec}
    (hF : ∀ k (hk : k < tys.length), TyF b m (to.toNat + 11 * k) tys[k])
    {LS : List (List NIdx)} (hLS : LS.map List.length = tys.map fun t : IndTypeRec => t.ctors.length) :
    ∀ i, i ≤ tys.length → psum m to i = fpos LS i := by
  have hl : LS.length = tys.length := by
    have := congrArg List.length hLS; simpa using this
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [psum_succ, fpos_succ LS i (by omega), ih (by omega)]
    congr 1
    obtain ⟨-, h4, -⟩ := hF i (by omega)
    have := congrArg (fun l => l[i]?) hLS
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < LS.length by omega),
      List.getElem?_eq_getElem (show i < tys.length by omega), Option.map_some, Option.some.injEq] at this
    rw [this]; exact h4

theorem fpos_lt (LS : List (List NIdx)) (i c : Nat) (hi : i < LS.length) (hc : c < LS[i].length) :
    fpos LS i + c < LS.flatten.length := by
  induction LS generalizing i with
  | nil => simp at hi
  | cons l L ih =>
    cases i with
    | zero => simp [fpos] at hc ⊢; omega
    | succ i =>
      have := ih i (by simpa using hi) (by simpa using hc)
      simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
        List.length_append] at this ⊢
      omega

theorem getElem_flatten' (LS : List (List NIdx)) (i c : Nat) (hi : i < LS.length) (hc : c < LS[i].length) :
    LS[i][c] = LS.flatten[fpos LS i + c]'(fpos_lt LS i c hi hc) := by
  induction LS generalizing i with
  | nil => simp at hi
  | cons l L ih =>
    cases i with
    | zero => simp [fpos, List.getElem_append_left (show c < l.length by simpa using hc)]
    | succ i =>
      have h1 := ih i (by simpa using hi) (by simpa using hc)
      simp only [List.getElem_cons_succ] at h1 ⊢
      rw [h1]
      simp only [List.flatten_cons]
      rw [List.getElem_append_right (by simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons]; omega)]
      congr 1
      simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons]; omega

theorem flat_pos (LS : List (List NIdx)) (p : Nat) (hp : p < LS.flatten.length) :
    ∃ i c, ∃ (hi : i < LS.length), c < LS[i].length ∧ fpos LS i + c = p := by
  induction LS generalizing p with
  | nil => simp at hp
  | cons l L ih =>
    by_cases hpl : p < l.length
    · exact ⟨0, p, by simp, by simpa using hpl, by simp [fpos]⟩
    · obtain ⟨i, c, hi, hc, he⟩ := ih (p - l.length) (by rw [List.flatten_cons, List.length_append] at hp; omega)
      refine ⟨i + 1, c, by simpa using hi, by simpa using hc, ?_⟩
      simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons] at he ⊢
      omega

/-- A write set of the level heap only is an `IExt`. -/
theorem iext_of_heap {m m' : Mem} (h : MemFrame [LH] [192] m m') : IExt m m' := by
  have hI : m'.arr64 IFL = m.arr64 IFL := h.1 IFL (by decide) (by decide)
  refine ⟨h.mono (by simp) (by simp), by simp [topN, wd, hI], fun i _ _ => by simp [wd, hI]⟩


/-- **`validate_ind_d` refines `validateIndD`.** -/
theorem validateW_twin {b : ByteArray} {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hR : ArenaR m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hT : TopOK m)
    {to tn co cn ro rn oo np : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (h : validateW n m to tn co cn ro rn = some ((oo, np), m')) :
    ∃ ordered : List IndCtorRec,
      (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inr (ordered, np.toNat), a) ∧
      IExt m m' ∧ TopOK m' ∧ ordered.length = cts.length ∧ 1 ≤ oo.toNat ∧
      oo.toNat + cts.length ≤ topN m' IFL + 1 ∧
      (∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
        wd m' IFL (oo.toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k]) ∧
      np.toNat < 10 ^ 18 := by
  obtain ⟨hTn, hTy, hCn, hCt, hRn, hRc⟩ := hF
  have hto : to.toNat + 11 * tys.length < 2 ^ 63 := by have := hTy.2.1; omega
  have hco : co.toNat + 10 * cts.length < 2 ^ 63 := by have := hCt.2.1; omega
  have hro : ro.toNat + 11 * rcs.length < 2 ^ 63 := by have := hRc.2.1; omega
  cases n with
  | zero => simp [validateW] at h
  | succ n =>
  simp only [validateW] at h
  -- `vi_unsafe`
  cases h1 : unsafeW n m to tn 0 with
  | none => rw [h1, uK_none] at h; cases h
  | some u1 =>
  rw [h1, uK_some] at h
  have hu := unsafeW_twin hTy hTn hto n 0 h1
  -- `vi_nparams`
  cases h2 : nparamsW n m to tn with
  | none => rw [h2, wK_none] at h; cases h
  | some np' =>
  rw [h2, wK_some] at h
  obtain ⟨np1, np2, np3⟩ := nparamsW_twin hTy hTn hto h2
  -- the type names
  cases h3 : mapW n m to tn 11 0 0 with
  | none => rw [h3, pmK_none] at h; cases h
  | some q =>
  obtain ⟨⟨tyn, x1⟩, m₁⟩ := q
  rw [h3, pmK_some] at h
  have hidT : ∀ s : Word, s.toNat < 11 → ∀ k (hk : k < tys.length),
      rdW (m.arr64 IFR) (to + 11 * UInt64.ofNat k + s) = wd m IFR (to.toNat + 11 * k + s.toNat) := by
    intro s hs k hk
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [wd_eq, widx _ _ _ _ (by rw [hk']; simp; omega), hk']; rfl
  obtain ⟨t1, t2, t3, -, t5, t6, t7⟩ := mapW_twin hT h3 a tys (fun t => t.cv.name) st.name
    (by rw [hTn])
    (fun k hk => by
      have := hidT 0 (by decide) k hk
      simp only [Nat.add_zero, show (0 : Word).toNat = 0 from rfl] at this
      rw [this]; exact (hTy.2.2 k hk).1.1.1)
    (fun x w hw => lkW_name hD a (by simpa [mapLk] using hw))
  have hD₁ : StateDR m₁ st := hD.frame t2.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hR₁ : ArenaR m₁ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₁ t2.frame a hR
  -- the type types
  cases h4 : mapW n m₁ to tn 11 2 1 with
  | none => rw [h4, pmK_none] at h; cases h
  | some q =>
  obtain ⟨⟨tyt, x2⟩, m₂⟩ := q
  rw [h4, pmK_some] at h
  obtain ⟨u1, u2, u3, -, u5, u6, u7⟩ := mapW_twin t3 h4 a tys (fun t => t.cv.type) (getDeclD st)
    (by rw [hTn])
    (fun k hk => by
      have := hidT 2 (by decide) k hk
      rw [t2.ifr, this]; exact (hTy.2.2 k hk).1.2.2.1)
    (fun x w hw => by
      have := lkW_expr hD₁ a (by simpa [mapLk] using hw)
      rw [decE_eq] at this; exact this)
  have e12 := t2.trans u2
  have hD₂ : StateDR m₂ st := hD.frame e12.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the listed constructor names
  cases h5 : listedW n m₂ to tn with
  | none => rw [h5, pmK_none] at h; cases h
  | some q =>
  obtain ⟨⟨fo, x⟩, m₃⟩ := q
  rw [h5, pmK_some] at h
  obtain ⟨LS, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := listedW_twin hD a tys to tn
    (fun k hk => hTy.2.2 k hk) hTn (by omega) h5 e12 u3
  have e13 := e12.trans l2
  have hD₃ : StateDR m₃ st := hD.frame e13.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the constructor records' names
  cases h6 : mapW n m₃ co cn 10 0 0 with
  | none => rw [h6, pmK_none] at h; cases h
  | some q =>
  obtain ⟨⟨cno, x3⟩, m₄⟩ := q
  rw [h6, pmK_some] at h
  obtain ⟨v1, v2, v3, -, v5, v6, v7⟩ := mapW_twin l3 h6 a cts (fun c => c.cv.name) st.name
    (by rw [hCn])
    (fun k hk => by
      have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      rw [e13.ifr, wd_eq, widx _ _ _ _ (by rw [hk']; simp; omega), hk']
      exact (hCt.2.2 k hk).1.1.1)
    (fun x w hw => lkW_name hD₃ a (by simpa [mapLk] using hw))
  have e14 := e13.trans v2
  -- `ifl_nodup`, the count
  cases h7 : nodupW n m₄ fo x 0 with
  | none => rw [h7, wK_none] at h; cases h
  | some u =>
  rw [h7, wK_some] at h
  split at h
  · cases h
  rename_i hu0
  split at h
  · cases h
  rename_i hxcn
  have hxcn' : x = cn := Classical.byContradiction hxcn
  have hflen : LS.flatten.length = cts.length := by rw [← l5, hxcn', hCn]
  have hfo3 : fo.toNat + LS.flatten.length ≤ topN m₃ IFL + 1 := by rw [l6, l4]; omega
  have hkeep34 : ∀ c, c < LS.flatten.length → wd m₄ IFL (fo.toNat + c) = wd m₃ IFL (fo.toNat + c) :=
    fun c hc => v2.keep _ (by omega) (by omega)
  have hnd : LS.flatten.Nodup := by
    rw [l7]
    apply islice_nodup (fun c hc => l8 c hc)
    intro i i' hii hi'
    have := nodupW_facts n m₄ fo x 0 u h7 (by have := l3.1; have := l3.2; omega) hu0 i i' (Nat.zero_le _)
      hii (by rw [l5]; exact hi')
    rw [hkeep34 _ (by omega), hkeep34 _ hi'] at this
    exact this
  -- the tail
  cases h8 : tailW n m₄ to tn co cn ro rn np' tyn tyt fo cno with
  | none => rw [h8, allocK_none] at h; cases h
  | some q =>
  obtain ⟨oo', m₅⟩ := q
  rw [h8, allocK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨hoo, hnp⟩, hmm⟩ := h
  subst oo' np' m₅
  cases n with
  | zero => simp [tailW] at h8
  | succ n =>
  simp only [tailW] at h8
  cases h9 : storeFuelW n m₄ with
  | none => rw [h9, wK_none] at h8; cases h8
  | some fuel =>
  rw [h9, wK_some] at h8
  have hR₄ : ArenaR m₄ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₄ e14.frame a hR
  have hD₄ : StateDR m₄ st := hD.frame e14.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfuel := storeFuelW_ok hR₄ h9
  cases h10 : orderW n m₄ to tn tyn fo cno co cn fuel np with
  | none => rw [h10, allocK_none] at h8; cases h8
  | some q =>
  obtain ⟨oo₅, m₅⟩ := q
  rw [h10, allocK_some] at h8
  cases h11 : kExpW n m₅ to tn tyt oo₅ fuel with
  | none => rw [h11, allocK_none] at h8; cases h8
  | some q =>
  obtain ⟨ke, m₆⟩ := q
  rw [h11, allocK_some] at h8
  cases h12 : recsW n m₆ to tn ro rn np cn ke tyn tyt fuel with
  | none => rw [h12, uK_none] at h8; cases h8
  | some u12 =>
  rw [h12, uK_some] at h8
  simp only [Option.some.injEq, Prod.mk.injEq] at h8
  obtain ⟨hoo5, hm6⟩ := h8
  subst oo₅ m₆
  -- the order
  have hps4 : ∀ i, i ≤ tys.length → psum m₄ to i = fpos LS i := fun i hi => by
    rw [psum_congr e14.ifr]; exact psum_fpos (fun k hk => hTy.2.2 k hk) l9 i hi
  have hLSl : LS.length = tys.length := by have := congrArg List.length l9; simpa using this
  have hcnt : ∀ k (hk : k < tys.length), cntF m₄ to k = tys[k].ctors.length := fun k hk => by
    simp only [cntF, wd, e14.ifr]; exact (hTy.2.2 k hk).2.1
  obtain ⟨o1, o2, o3, o4, o5⟩ := orderW_twin hR₄ hD₄ v3 (hCt.ext e14 (fun _ _ x => x.ext e14)) hCn v7
    (by rw [v6, v5]; omega) np3 hco ⟨by omega, by omega, by omega⟩ (by rw [hTn]; omega)
    (by rw [hTn]; omega)
    (fun p hp => by
      rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full] at hp
      refine ⟨by omega, ?_⟩
      rw [hkeep34 p hp]; exact l8 p hp)
    (by rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full, hflen]; exact Nat.le_refl _) h10
  sorry

end L.Front.Ind
