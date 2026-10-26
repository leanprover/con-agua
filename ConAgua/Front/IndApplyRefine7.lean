import ConAgua.Front.IndApplyRefine6

/-!
# The apply step of an `inductive` line against the twin, VII: the recursor records

`recW_twin`: `vi_rec` on a recursor record passes the twin's checks of it (`RecOK`): its name is
bound, its counts are the block's, its `k` is `kExpected?`'s, and if it is named `T.rec`, every type
named `T` has a sort telescope of `nP + numIndices` binders, if any. `recsGoW_twin` for all of
them, `nestedW_twin` the `nested` flag.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)


namespace L.Front.Ind

/-- **The twin's checks of one recursor record pass.** -/
def RecOK (st : StateD) (a : AState) (TN : List NIdx) (TT : List EIdx) (nPd nTypes nCtors : Nat)
    (KE : Option Bool) (fuel : Nat) (rc : IndRecRec) : Prop :=
  ∃ rn, (st.name rc.cv.name).run a = .ok (rn, a) ∧ rc.numParams = nPd ∧ rc.numMotives = nTypes ∧
    rc.numMinors = nCtors ∧ (∀ kE, KE = some kE → rc.k = kE) ∧
    ∃ v, (viewN rn).run a = .ok (v, a) ∧
      ∀ T, v = .str T "rec" → ∀ j (hj : j < TN.length) (hj' : j < TT.length), TN[j] = T →
        ∃ o, (piSortTeleLen? fuel TT[j]).run a = .ok (o, a) ∧ ∀ k, o = some k → nPd + rc.numIndices = k

/-- `kExpected?` from its word (`0` none, `1` `some false`, `2` `some true`). -/
def keOf (ke : Word) : Option Bool := if ke = 0 then none else some (ke = 2)

theorem recIdxW_twin {m : Mem} {a : AState} (hR : ArenaR m a) {T ni np tn tyn tyt fuel : Word}
    (hnp : np.toNat < 10 ^ 18) (hni : ni.toNat < 10 ^ 18) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63) :
    ∀ n j, recIdxW n m T ni np tn tyn tyt fuel j = some () →
      ∀ k, j.toNat ≤ k → k < tn.toNat → wd m IFL (tyn.toNat + k) = T →
        ∃ o, (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k)))).run a = .ok (o, a) ∧
          ∀ x, o = some x → np.toNat + ni.toNat = x := by
  intro n
  induction n with
  | zero => intro j h; simp [recIdxW] at h
  | succ n ih =>
    intro j h k h1 h2 hT
    simp only [recIdxW] at h
    split at h
    · rename_i hle; have := UInt64.le_iff_toNat_le.mp hle; omega
    rename_i hlt
    have hj1 := wsucc j tn (UInt64.not_le.mp hlt)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    have ex1 : rdW (m.arr64 IFL) (tyn + j) = wd m IFL (tyn.toNat + j.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega)]
    have ex2 : rdW (m.arr64 IFL) (tyt + j) = wd m IFL (tyt.toNat + j.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega)]
    rw [ex1, ex2] at h
    by_cases hk : k = j.toNat
    · subst hk
      rw [ite_eq_left hT] at h
      rcases hs : sortTeleW n m fuel (wd m IFL (tyt.toNat + j.toNat)) with _ | ⟨ok, kk⟩ <;> simp only [hs, pK, reduceCtorEq] at h
      obtain ⟨s1, -⟩ := sortTeleW_ok m a hR n fuel _ ok kk hs
      refine ⟨_, s1, fun x hx => ?_⟩
      split at h; cases h; rename_i hc
      by_cases hok : ok = 0
      · simp [hok] at hx
      · simp only [hok, ite_false, Option.some.injEq] at hx
        have : np + ni = kk := Classical.byContradiction fun hne => hc ⟨hok, hne⟩
        rw [← hx, ← this, widx2 _ _ (by omega)]
    · have hrest : recIdxW n m T ni np tn tyn tyt fuel (j + 1) = some () := by
        split at h
        · cases hs : sortTeleW n m fuel (wd m IFL (tyt.toNat + j.toNat)) with
          | none => rw [hs, pK_none] at h; cases h
          | some q =>
          obtain ⟨ok, kk⟩ := q
          rw [hs, pK_some] at h
          split at h; cases h
          · exact h
        · exact h
      exact ih (j + 1) hrest k (by rw [hj1]; omega) h2 hT


/-- **`vi_rec` against the twin's checks of one recursor record.** -/
theorem recW_twin {b : ByteArray} {n : Nat} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {rc : IndRecRec} {r np tn cn ke tyn tyt fuel : Word}
    (hrec : RecF b m r.toNat rc) (hr : r.toNat + 11 < 2 ^ 63) (hnp : np.toNat < 10 ^ 18)
    (hke : ke = 0 ∨ ke = 1 ∨ ke = 2) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63)
    (hTN : ∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32)
    (h : recW n m r np tn cn ke tyn tyt fuel = some ()) :
    RecOK st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat cn.toNat
      (keOf ke) fuel.toNat rc := by
  cases n with
  | zero => simp [recW] at h
  | succ n =>
  simp only [recW] at h
  have ix : ∀ s : Word, s.toNat ≤ 10 → rdW (m.arr64 IFR) (r + s) = wd m IFR (r.toNat + s.toNat) := by
    intro s hs; rw [wd_eq, widx2 _ _ (by omega)]
  obtain ⟨⟨c1, -, -⟩, c2, c3, c4, c5, c6, -⟩ := hrec
  rcases hl : lkW m NID (rdW (m.arr64 IFR) r) with _ | rnw <;> simp only [hl, wK, reduceCtorEq] at h
  rw [wd_eq] at hl
  have hname := (lkW_name hD a hl).1
  rw [c1.1] at hname
  split at h; cases h; rename_i h8
  split at h; cases h; rename_i h7
  split at h; cases h; rename_i h6
  split at h; cases h; rename_i h4
  have e8 : rdW (m.arr64 IFR) (r + 8) = np := Classical.byContradiction h8
  have e7 : rdW (m.arr64 IFR) (r + 7) = tn := Classical.byContradiction h7
  have e6 : rdW (m.arr64 IFR) (r + 6) = cn := Classical.byContradiction h6
  rw [ix 8 (by decide)] at e8; rw [ix 7 (by decide)] at e7; rw [ix 6 (by decide)] at e6
  simp only [show (8 : Word).toNat = 8 from rfl, show (7 : Word).toNat = 7 from rfl,
    show (6 : Word).toNat = 6 from rfl] at e8 e7 e6
  refine ⟨_, hname, by rw [← c6.1, e8], by rw [← c5.1, e7], by rw [← c4.1, e6], fun kE hkE => ?_, ?_⟩
  · simp only [keOf] at hkE
    split at hkE; cases hkE; rename_i hk0
    simp only [Option.some.injEq] at hkE
    have e4 : rdW (m.arr64 IFR) (r + 4) = ke - 1 := Classical.byContradiction fun hne => h4 ⟨hk0, hne⟩
    rw [ix 4 (by decide)] at e4
    simp only [show (4 : Word).toNat = 4 from rfl] at e4
    rw [c2] at e4
    rcases hke with rfl | rfl | rfl
    · exact absurd rfl hk0
    · subst hkE; cases hk : rc.k <;> simp_all
    · subst hkE; cases hk : rc.k <;> simp_all
  · cases hn : nrpW m rnw with
    | none => rw [hn, pK_none] at h; cases h
    | some q =>
    obtain ⟨f, tt⟩ := q
    rw [hn, pK_some] at h
    obtain ⟨v, hv, hv1, hv0⟩ := nrpW_ok hR rnw f tt hn
    refine ⟨v, hv, fun T hT j hj hj' hTj => ?_⟩
    by_cases hf : f = 0
    · exact absurd hT (hv0 hf T)
    obtain ⟨hvs, htt⟩ := hv1 hf
    rw [hvs] at hT
    simp only [NNodeView.str.injEq, and_true] at hT
    subst hT
    rw [ite_eq_left hf] at h
    simp only [islice_length] at hj hj'
    rw [islice_get] at hTj ⊢
    have hw : wd m IFL (tyn.toNat + j) = tt := decI_inj' _ _ (hTN j hj) htt hTj
    have e5 : rdW (m.arr64 IFR) (r + 5) = wd m IFR (r.toNat + 5) := by
      have := ix 5 (by decide); simpa using this
    rw [e5] at h
    obtain ⟨o, ho1, ho2⟩ := recIdxW_twin hR hnp (by rw [c3.1]; exact c3.2) hb hb' n 0 h j
      (Nat.zero_le _) hj hw
    exact ⟨o, ho1, fun x hx => by rw [← ho2 x hx, c3.1]⟩


theorem recsGoW_twin {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {rcs : List IndRecRec} {ro rn np tn cn ke tyn tyt fuel : Word}
    (hL : ListF (RecF b m) m 11 ro.toNat rcs) (hrn : rn.toNat = rcs.length)
    (hro : ro.toNat + 11 * rcs.length < 2 ^ 63) (hnp : np.toNat < 10 ^ 18)
    (hke : ke = 0 ∨ ke = 1 ∨ ke = 2) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63)
    (hTN : ∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32) :
    ∀ n j, recsGoW n m ro rn np tn cn ke tyn tyt fuel j = some () →
      ∀ k (hk : k < rcs.length), j.toNat ≤ k →
        RecOK st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
          cn.toNat (keOf ke) fuel.toNat rcs[k] := by
  intro n
  induction n with
  | zero => intro j h; simp [recsGoW] at h
  | succ n ih =>
    intro j h k hk hjk
    simp only [recsGoW] at h
    split at h
    · rename_i hle; have := UInt64.le_iff_toNat_le.mp hle; omega
    rename_i hlt
    have hj1 := wsucc j rn (UInt64.not_le.mp hlt)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    rcases hr : recW n m (ro + 11 * j) np tn cn ke tyn tyt fuel with _ | u <;> simp only [hr, uK, reduceCtorEq] at h
    by_cases hkj : k = j.toNat
    · subst hkj
      have hix : (ro + 11 * j).toNat = ro.toNat + 11 * j.toNat := by
        have := widx ro 11 j 0 (by simp; omega); simpa using this
      have hrec := hL.2.2 j.toNat hk
      rw [← hix] at hrec
      exact recW_twin hR hD hrec (by rw [hix]; omega) hnp hke hb hb' hTN hr
    · exact ih (j + 1) h k hk (by rw [hj1]; omega)

theorem nestedW_twin {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) :
    ∀ n j u, nestedW n m to tn j = some u →
      (u = 0 → ∀ k (hk : k < tys.length), j.toNat ≤ k → tys[k].numNested = 0) ∧
      (u ≠ 0 → ∃ k, ∃ hk : k < tys.length, tys[k].numNested ≠ 0) := by
  intro n
  induction n with
  | zero => intro j u h; simp [nestedW] at h
  | succ n ih =>
    intro j u h
    simp only [nestedW] at h
    split at h
    · rename_i hle
      cases h
      have := UInt64.le_iff_toNat_le.mp hle
      exact ⟨fun _ k hk h1 => by omega, fun h => absurd rfl h⟩
    rename_i hlt
    have hj1 := wsucc j tn (UInt64.not_le.mp hlt)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    have hix : (to + 11 * j + 9).toNat = to.toNat + 11 * j.toNat + 9 := widx _ _ _ _ (by simp; omega)
    have hty := hL.2.2 j.toNat (by omega)
    obtain ⟨-, -, -, -, h9, -⟩ := hty
    split at h
    · rename_i hne
      cases h
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨j.toNat, by omega, fun h0 => hne ?_⟩⟩
      rw [wd_eq, hix, show to.toNat + 11 * j.toNat + 9 = to.toNat + 11 * j.toNat + 9 from rfl]
      apply UInt64.toNat_inj.mp; rw [h9.1, h0]; rfl
    · rename_i h0
      obtain ⟨i1, i2⟩ := ih (j + 1) u h
      rw [hj1] at i1
      refine ⟨fun hu k hk hjk => ?_, i2⟩
      by_cases hkj : k = j.toNat
      · subst hkj
        have : rdW (m.arr64 IFR) (to + 11 * j + 9) = 0 := Classical.byContradiction h0
        rw [wd_eq, hix] at this
        rw [← h9.1, this]; rfl
      · exact i1 hu k hk (by omega)


theorem unsafeW_twin {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) :
    ∀ n j, unsafeW n m to tn j = some () →
      ∀ k (hk : k < tys.length), j.toNat ≤ k → tys[k].isUnsafe = false := by
  intro n
  induction n with
  | zero => intro j h; simp [unsafeW] at h
  | succ n ih =>
    intro j h k hk hjk
    simp only [unsafeW] at h
    split at h
    · rename_i hle; have := UInt64.le_iff_toNat_le.mp hle; omega
    rename_i hlt
    have hj1 := wsucc j tn (UInt64.not_le.mp hlt)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    split at h; cases h; rename_i h0
    by_cases hkj : k = j.toNat
    · subst hkj
      have hix : (to + 11 * j + 7).toNat = to.toNat + 11 * j.toNat + 7 := widx _ _ _ _ (by simp; omega)
      have : rdW (m.arr64 IFR) (to + 11 * j + 7) = 0 := Classical.byContradiction h0
      rw [wd_eq, hix] at this
      obtain ⟨-, -, -, h7, -, -⟩ := hL.2.2 j.toNat hk
      rw [this] at h7
      cases hu : tys[j.toNat].isUnsafe
      · rfl
      · rw [hu] at h7; simp [BoolW] at h7
    · exact ih (j + 1) h k hk (by rw [hj1]; omega)

theorem npGoW_twin {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn d : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) :
    ∀ n j, npGoW n m to tn d j = some () →
      ∀ k (hk : k < tys.length), j.toNat ≤ k → tys[k].numParams = d.toNat := by
  intro n
  induction n with
  | zero => intro j h; simp [npGoW] at h
  | succ n ih =>
    intro j h k hk hjk
    simp only [npGoW] at h
    split at h
    · rename_i hle; have := UInt64.le_iff_toNat_le.mp hle; omega
    rename_i hlt
    have hj1 := wsucc j tn (UInt64.not_le.mp hlt)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    split at h; cases h; rename_i h0
    by_cases hkj : k = j.toNat
    · subst hkj
      have hix : (to + 11 * j + 10).toNat = to.toNat + 11 * j.toNat + 10 := widx _ _ _ _ (by simp; omega)
      have : rdW (m.arr64 IFR) (to + 11 * j + 10) = d := Classical.byContradiction h0
      rw [wd_eq, hix] at this
      obtain ⟨-, -, -, -, -, h10⟩ := hL.2.2 j.toNat hk
      rw [← h10.1, this]
    · exact ih (j + 1) h k hk (by rw [hj1]; omega)

/-- **`vi_nparams` is `nPd`, and every type agrees.** -/
theorem nparamsW_twin {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn np : Word} {n : Nat}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (h : nparamsW n m to tn = some np) :
    np.toNat = ((tys.map fun x => x.numParams).head?.getD 0) ∧
      ((tys.map fun x => x.numParams).all fun x => x == np.toNat) = true ∧ np.toNat < 10 ^ 18 := by
  cases n with
  | zero => simp [nparamsW] at h
  | succ n =>
  simp only [nparamsW] at h
  split at h
  · rename_i h0
    cases h
    have : tys = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← htn, h0]; rfl
    subst this
    simp
  rename_i h0
  have hne : tys ≠ [] := fun e => h0 (by apply UInt64.toNat_inj.mp; rw [htn, e]; rfl)
  rcases hg : npGoW n m to tn (rdW (m.arr64 IFR) (to + 10)) 0 with _ | u <;> simp only [hg, unitK, reduceCtorEq] at h
  cases h
  have hall := npGoW_twin hL htn hto n 0 hg
  have h0' : 0 < tys.length := by cases tys with | nil => exact absurd rfl hne | cons _ _ => simp
  have hfirst := hall 0 h0' (Nat.zero_le _)
  have hix : (to + 10).toNat = to.toNat + 10 := widx2 _ _ (by simp; omega)
  obtain ⟨-, -, -, -, -, h10⟩ := hL.2.2 0 h0'
  simp only [Nat.mul_zero, Nat.add_zero] at h10
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfirst]
    cases tys with
    | nil => exact absurd rfl hne
    | cons t ts => rfl
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    simp [hall k hk (Nat.zero_le _)]
  · rw [← hfirst]; exact h10.2

end L.Front.Ind
