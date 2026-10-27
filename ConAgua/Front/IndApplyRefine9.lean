import ConAgua.Front.IndApplyRefine8
import ConAgua.Front.IndValidTwin
import ConAgua.Front.IndApplyRefine6
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

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

theorem ordList_get (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l p : Nat)
    (hp : p < (ordList m oo co cts l).length) :
    (ordList m oo co cts l)[p] = cts.getD (((wd m IFL (oo + p)).toNat - co) / 10) default := by
  simp [ordList]

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
@[refines ConRon.Arena.Frontend.validateIndD]
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
  rcases h1 : unsafeW n m to tn 0 with _ | u1 <;> simp only [h1, uK, reduceCtorEq] at h
  have hu := unsafeW_twin hTy hTn hto n 0 h1
  -- `vi_nparams`
  rcases h2 : nparamsW n m to tn with _ | np' <;> simp only [h2, wK, reduceCtorEq] at h
  obtain ⟨np1, np2, np3⟩ := nparamsW_twin hTy hTn hto h2
  -- the type names
  rcases h3 : mapW n m to tn 11 0 0 with _ | ⟨⟨tyn, x1⟩, m₁⟩ <;> simp only [h3, pmK, reduceCtorEq] at h
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
  rcases h4 : mapW n m₁ to tn 11 2 1 with _ | ⟨⟨tyt, x2⟩, m₂⟩ <;> simp only [h4, reduceCtorEq] at h
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
  rcases h5 : listedW n m₂ to tn with _ | ⟨⟨fo, x⟩, m₃⟩ <;> simp only [h5, reduceCtorEq] at h
  obtain ⟨LS, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := listedW_twin hD a tys to tn
    (fun k hk => hTy.2.2 k hk) hTn (by omega) h5 e12 u3
  have e13 := e12.trans l2
  have hD₃ : StateDR m₃ st := hD.frame e13.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the constructor records' names
  rcases h6 : mapW n m₃ co cn 10 0 0 with _ | ⟨⟨cno, x3⟩, m₄⟩ <;> simp only [h6, reduceCtorEq] at h
  obtain ⟨v1, v2, v3, -, v5, v6, v7⟩ := mapW_twin l3 h6 a cts (fun c => c.cv.name) st.name
    (by rw [hCn])
    (fun k hk => by
      have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      rw [e13.ifr, wd_eq, widx _ _ _ _ (by rw [hk']; simp; omega), hk']
      exact (hCt.2.2 k hk).1.1.1)
    (fun x w hw => lkW_name hD₃ a (by simpa [mapLk] using hw))
  have e14 := e13.trans v2
  -- `ifl_nodup`, the count
  rcases h7 : nodupW n m₄ fo x 0 with _ | u <;> simp only [h7, reduceCtorEq] at h
  split at h; cases h; rename_i hu0
  split at h; cases h; rename_i hxcn
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
  rcases h8 : tailW n m₄ to tn co cn ro rn np' tyn tyt fo cno with _ | ⟨oo', m₅⟩ <;> simp only [h8, allocK, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨hoo, hnp⟩, hmm⟩ := h
  subst oo' np' m₅
  cases n with
  | zero => simp [tailW] at h8
  | succ n =>
  simp only [tailW] at h8
  rcases h9 : storeFuelW n m₄ with _ | fuel <;> simp only [h9, wK, reduceCtorEq] at h8
  have hR₄ : ArenaR m₄ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₄ e14.frame a hR
  have hD₄ : StateDR m₄ st := hD.frame e14.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfuel := storeFuelW_ok hR₄ h9
  rcases h10 : orderW n m₄ to tn tyn fo cno co cn fuel np with _ | ⟨oo₅, m₅⟩ <;> simp only [h10, allocK, reduceCtorEq] at h8
  rcases h11 : kExpW n m₅ to tn tyt oo₅ fuel with _ | ⟨ke, m₆⟩ <;> simp only [h11, reduceCtorEq] at h8
  rcases h12 : recsW n m₆ to tn ro rn np cn ke tyn tyt fuel with _ | u12 <;> simp only [h12, uK, reduceCtorEq] at h8
  obtain ⟨hoo5, hm6⟩ := Prod.mk.inj (Option.some.inj h8)
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
  have e15 := e14.trans o2
  have hR₅ : ArenaR m₅ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₅ e15.frame a hR
  -- `kExpected?`
  obtain ⟨k1, k2, k3⟩ := kExpW_twin hR₅ hok h11
  have e56 := iext_of_heap k1
  have e16 := e15.trans e56
  have hR₆ : ArenaR m' a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m' e16.frame a hR
  have hD₆ : StateDR m' st := hD.frame e16.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hIFL56 : m'.arr64 IFL = m₅.arr64 IFL := k1.1 IFL (by decide) (by decide)
  -- the words the twin's lists are read from
  have hTNw : ∀ i, i < tys.length → wd m' IFL (tyn.toNat + i) = wd m₁ IFL (tyn.toNat + i) := fun i hi =>
    ((u2.trans (l2.trans (v2.trans (o2.trans e56)))).keep _ (by omega) (by omega))
  have hTTw : ∀ i, i < tys.length → wd m' IFL (tyt.toNat + i) = wd m₂ IFL (tyt.toNat + i) := fun i hi =>
    ((l2.trans (v2.trans (o2.trans e56))).keep _ (by omega) (by omega))
  have hTN : islice (k := .name) m' tyn.toNat tn.toNat = islice m₁ tyn.toNat tys.length := by
    rw [hTn]; simp only [islice]; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi; rw [hTNw i hi]
  have hTT : islice (k := .expr) m' tyt.toNat tn.toNat = islice m₂ tyt.toNat tys.length := by
    rw [hTn]; simp only [islice]; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi; rw [hTTw i hi]
  have hke : ke = 0 ∨ ke = 1 ∨ ke = 2 := by
    by_cases hc : tn = 1 ∧ rdW (m₅.arr64 IFR) (to + 4) = 1
    · obtain ⟨r, v, -, -, hn, hs⟩ := k3 hc.1 hc.2
      by_cases hv : ∃ s, v = .sort s
      · obtain ⟨s, hs'⟩ := hv
        obtain ⟨L, -, hk⟩ := hs s hs'
        rw [hk]; split <;> simp
      · exact .inl (hn (fun s hs' => hv ⟨s, hs'⟩))
    · exact .inr (.inl (k2 (by
        rcases Classical.not_and_iff_not_or_not.mp hc with h | h
        · exact .inl h
        · exact .inr h)))
  -- the recursors
  cases n with
  | zero => simp [recsW] at h12
  | succ n =>
  simp only [recsW] at h12
  rcases h13 : nestedW n m' to tn 0 with _ | un <;> simp only [h13, wK, reduceCtorEq] at h12
  have hTy₆ : ListF (TyF b m') m' 11 to.toNat tys := hTy.ext e16 (fun _ _ x => x.ext e16)
  have hRc₆ : ListF (RecF b m') m' 11 ro.toNat rcs := hRc.ext e16 (fun _ _ x => x.ext e16)
  obtain ⟨n1, n2⟩ := nestedW_twin hTy₆ hTn hto n 0 un h13
  have hrecs : ∀ r ∈ (if (tys.any fun x => x.numNested != 0) = true then [] else rcs),
      RecOK st a (islice m₁ tyn.toNat tys.length) (islice m₂ tyt.toNat tys.length) np.toNat
        tys.length (ordList m₅ oo.toNat co.toNat cts cts.length).length (keOf ke) fuel.toNat r := by
    intro r hr
    by_cases hun : un = 0
    · have hany : (tys.any fun x => x.numNested != 0) = false := by
        rw [List.any_eq_false]
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        simp [n1 hun k hk (Nat.zero_le _)]
      rw [hany] at hr
      simp only [Bool.false_eq_true, ite_false] at hr
      rw [ite_eq_right (by simpa using hun)] at h12
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
      have := recsGoW_twin hR₆ hD₆ hRc₆ hRn hro np3 hke
        (by have := t3.1; have := t3.2; have := u2.top; have := l2.top; have := v2.top; omega)
        (by have := u3.1; have := u3.2; omega)
        (fun i hi => by rw [hTn] at hi; rw [hTNw i hi]; exact t7 i hi) n 0 h12 k hk (Nat.zero_le _)
      rw [hTN, hTT, hTn, hCn] at this
      rw [ordList_length]; exact this
    · obtain ⟨k, hk, hk'⟩ := n2 hun
      have hany : (tys.any fun x => x.numNested != 0) = true := by
        rw [List.any_eq_true]; exact ⟨tys[k], List.getElem_mem hk, by simpa using hk'⟩
      rw [hany] at hr
      simp at hr
  -- the order's facts, per type and position
  have hordf : ∀ i (hi : i < LS.length) c (hc : c < LS[i].length), ∃ k,
      ∃ _ : fpos LS i + c < (ordList m₅ oo.toNat co.toNat cts cts.length).length,
        (ordList m₅ oo.toNat co.toNat cts cts.length)[fpos LS i + c] = cts[k]! ∧
        CtorOK st a cts (islice m₄ cno.toNat cts.length) LS[i][c] c
          ((islice (k := .name) m₁ tyn.toNat tys.length)[i]!) np.toNat fuel.toNat k := by
    intro i hi c hc
    have hi' : i < tys.length := by omega
    have hcn' : c < cntF m₄ to i := by
      rw [hcnt i hi']
      have := congrArg (fun l => l[i]?) l9
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
        Option.map_some, Option.some.injEq] at this
      rw [← this]; exact hc
    obtain ⟨kk, w1, w2⟩ := o5 i (by omega) c hcn'
    rw [hps4 i (by omega)] at w1 w2
    have hpl := fpos_lt LS i c hi hc
    have hkk : kk < cts.length := w2.1
    refine ⟨kk, by rw [ordList_length]; omega, ?_, ?_⟩
    · rw [ordList_get, ← Nat.add_assoc, ptr_rec cts co kk hkk hco _ w1, getElem!_pos cts kk hkk]
    · have hnn : LS[i][c] = decI (wd m₄ IFL (fo.toNat + (fpos LS i + c))) := by
        rw [getElem_flatten' LS i c hi hc, List.getElem_of_eq l7, islice_get, hkeep34 _ hpl]
      have htt : (islice (k := .name) m₁ tyn.toNat tys.length)[i]! = decI (wd m₄ IFL (tyn.toNat + i)) := by
        rw [getElem!_pos _ i (by rw [islice_length]; exact hi'), islice_get,
          ((u2.trans (l2.trans v2)).keep _ (by omega) (by omega))]
      rw [hnn, htt, ← Nat.add_assoc]
      exact w2
  -- the type records' first constructor count
  have hR4 : rdW (m₅.arr64 IFR) (to + 4) = wd m IFR (to.toNat + 4) := by
    rw [wd_eq, widx2 _ _ (by simp; omega)]; simp only [wd, e15.ifr]; rfl
  have hc0 : ∀ h0 : 0 < tys.length, (wd m IFR (to.toNat + 4)).toNat = tys[0].ctors.length := fun h0 => by
    have := (hTy.2.2 0 h0).2.1; simpa using this
  have hLS0 : ∀ hd, LS = [[hd]] → tys.length = 1 ∧ ∃ h0 : 0 < tys.length, tys[0].ctors.length = 1 := by
    intro hd hL
    have h1 : tys.length = 1 := by rw [← hLSl, hL]; rfl
    refine ⟨h1, by omega, ?_⟩
    have := congrArg (fun l => l[0]?) l9
    rw [hL] at this
    simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, List.length_cons, List.length_nil,
      List.getElem?_map, List.getElem?_eq_getElem (show 0 < tys.length by omega), Option.map_some,
      Option.some.injEq] at this
    rw [← this]
  -- the first ordered constructor's pointer
  have hfirst : ∀ (h0 : 0 < tys.length) (hc : 0 < cntF m₄ to 0), ∃ kk, ∃ hk : kk < cts.length,
      wd m₅ IFL oo.toNat = co + 10 * UInt64.ofNat kk ∧
      ∀ hp : 0 < (ordList m₅ oo.toNat co.toNat cts cts.length).length,
        (ordList m₅ oo.toNat co.toNat cts cts.length)[0] = cts[kk] := by
    intro h0 hc
    obtain ⟨kk, w1, w2⟩ := o5 0 (by omega) 0 hc
    simp only [show psum m₄ to 0 = 0 from rfl, Nat.add_zero] at w1
    refine ⟨kk, w2.1, w1, fun hp => ?_⟩
    rw [ordList_get, Nat.add_zero, ptr_rec cts co kk w2.1 hco _ w1]
  -- the facts
  have hV : VFacts st a tys cts rcs (islice m₁ tyn.toNat tys.length) (islice m₂ tyt.toNat tys.length) LS
      (islice m₄ cno.toNat cts.length) fuel.toNat np.toNat (ordList m₅ oo.toNat co.toNat cts cts.length)
      (keOf ke) := by
    refine ⟨?_, np1, np2, by simpa using t1, by simpa using u1, l1, by simpa using v1, hnd, hflen,
      hfuel.symm, islice_length _ _ _, islice_length _ _ _, hLSl, ordList_length _ _ _ _ _, hordf,
      ?_, ?_, hrecs⟩
    · rw [List.any_eq_false]
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      simp [hu k hk (Nat.zero_le _)]
    · intro hnot
      by_cases hc : tn = 1 ∧ rdW (m₅.arr64 IFR) (to + 4) = 1
      · exfalso; apply hnot
        have h1 : tys.length = 1 := by rw [← hTn, hc.1]; rfl
        refine ⟨by rw [islice_length]; exact h1, ?_⟩
        rw [l9]
        cases htys : tys with
        | nil => rw [htys] at h1; simp at h1
        | cons t ts =>
          cases ts with
          | cons _ _ => rw [htys] at h1; simp at h1
          | nil =>
            have := hc0 (by omega)
            rw [← hR4, hc.2] at this
            simp only [htys, List.getElem_cons_zero] at this
            simp [← this]
      · have := k2 (by
          rcases Classical.not_and_iff_not_or_not.mp hc with h | h
          · exact .inl h
          · exact .inr h)
        rw [this]; rfl
    · intro ty hd c hTT hLS hord
      obtain ⟨h1, h0, hlen1⟩ := hLS0 hd hLS
      have htn : tn = 1 := UInt64.toNat_inj.mp (by rw [hTn, h1]; rfl)
      have h4 : rdW (m₅.arr64 IFR) (to + 4) = 1 := by
        rw [hR4]; apply UInt64.toNat_inj.mp; rw [hc0 h0, hlen1]; rfl
      obtain ⟨r, v, hr, hv, hn, hs⟩ := k3 htn h4
      have hty : ty = decE (rdW (m₅.arr64 IFL) tyt) := by
        have := congrArg (fun l => l[0]?) hTT
        simp only [List.getElem?_cons_zero, List.getElem?_eq_getElem (show 0 < (islice (k := .expr) m₂ tyt.toNat tys.length).length by rw [islice_length]; omega),
          Option.some.injEq, islice_get, Nat.add_zero] at this
        rw [← this, decE_eq, wd_eq, (l2.trans (v2.trans o2)).keep _ (by omega) (by omega)]
      obtain ⟨kk, hk, hw, hget⟩ := hfirst h0 (by rw [hcnt 0 h0, hlen1]; decide)
      have hc' : c = cts[kk] := by
        have := hget (by rw [hord]; exact Nat.zero_lt_one)
        simp only [hord, List.getElem_cons_zero] at this
        exact this
      refine ⟨r, v, by rw [hty]; exact hr, hv, fun hns => by rw [hn hns]; rfl, fun s hvs => ?_⟩
      obtain ⟨L, hL, hke'⟩ := hs s hvs
      refine ⟨L, hL, ?_⟩
      have hkw : (UInt64.ofNat kk).toNat = kk :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hnf : rdW (m₅.arr64 IFR) (rdW (m₅.arr64 IFL) oo + 4) = wd m IFR (co.toNat + 10 * kk + 4) := by
        rw [wd_eq (A := IFL), hw, wd_eq, widx _ _ _ _ (by rw [hkw]; simp; omega), hkw]
        simp only [wd, e15.ifr]; rfl
      obtain ⟨-, c4, -⟩ := hCt.2.2 kk hk
      rw [hnf] at hke'
      rw [hke', hc']
      by_cases hz : cts[kk].numFields = 0
      · have hz' : wd m IFR (co.toNat + 10 * kk + 4) = 0 := UInt64.toNat_inj.mp (by rw [c4.1, hz]; rfl)
        by_cases he : L.isEquiv .zero = some true
        · simp [hz', he, hz, keOf]
        · simp [hz', he, hz, keOf]
      · have hz' : wd m IFR (co.toNat + 10 * kk + 4) ≠ 0 := fun e => hz (by rw [← c4.1, e]; rfl)
        simp [hz', hz, keOf]
  have hsz5 : (m'.arr64 IFL).size = (m₅.arr64 IFL).size := k1.2.2.1 IFL
  have htop56 : topN m' IFL = topN m₅ IFL := by simp only [topN, wd, hIFL56]
  refine ⟨_, validateIndD_ok hV, e16, ⟨by rw [hsz5]; exact o3.1, by rw [hsz5, htop56]; exact o3.2⟩,
    ordList_length _ _ _ _ _, by omega, by rw [htop56, o4, o1]; omega, fun p hp => ?_, np3⟩
  rw [ordList_length] at hp
  obtain ⟨i, c, hi, hc, hpe⟩ := flat_pos LS p (by rw [hflen]; exact hp)
  have hi' : i < tys.length := by omega
  have hcn' : c < cntF m₄ to i := by
    rw [hcnt i hi']
    have := congrArg (fun l => l[i]?) l9
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at this
    rw [← this]; exact hc
  obtain ⟨kk, w1, w2⟩ := o5 i (by omega) c hcn'
  rw [hps4 i (by omega), Nat.add_assoc, hpe] at w1
  refine ⟨kk, w2.1, by simp only [wd, hIFL56] at w1 ⊢; exact w1, ?_⟩
  rw [ordList_get, ptr_rec cts co kk w2.1 hco _ w1]


end L.Front.Ind
