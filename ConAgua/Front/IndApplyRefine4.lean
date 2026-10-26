import ConAgua.Front.IndApplyRefine3

/-!
# The apply step of an `inductive` line against the twin, IV: one constructor in the block's order

`ctorW_twin`: `vi_ctor` on the name `nn` (the `jj`-th constructor of the type named `tt`) finds the
record the twin's `ctorIx` finds, and the twin's checks of it (`cidx`, `induct`, the telescope
against `numFields`) pass.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend


namespace L.Front.Ind

/-- **`vi_ctor` against the twin's constructor lookup and checks.** -/
theorem ctorW_twin {b : ByteArray} {n : Nat} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {cts : List ConLeche.Frontend.IndCtorRec} {nn j tt np fuel cno cn co c : Word}
    (hCt : ListF (CtF b m) m 10 co.toNat cts) (hcn : cn.toNat = cts.length)
    (hCN : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32)
    (hcnb : cno.toNat + cts.length < 2 ^ 63) (hnn : nn.toNat < 2 ^ 32) (hnp : np.toNat < 10 ^ 18)
    (hco : co.toNat + 10 * cts.length < 2 ^ 63)
    (h : ctorW n m nn j tt np fuel cno cn co = some c) :
    ∃ k, ∃ hk : k < cts.length, c = co + 10 * UInt64.ofNat k ∧
      ((islice (k := .name) m cno.toNat cts.length).foldl
        (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1[(decI nn : NIdx)]? =
        some k ∧
      (∀ ci, cts[k].cidx = some ci → ci = j.toNat) ∧
      (∀ iw, cts[k].induct = some iw → (st.name iw).run a = .ok (decI tt, a)) ∧
      ∃ cty, (getDeclD st cts[k].cv.type).run a = .ok (cty, a) ∧
        (ConRon.Arena.Frontend.indPiTeleLen fuel.toNat cty).run a =
          .ok (np.toNat + cts[k].numFields, a) := by
  cases n with
  | zero => simp [ctorW] at h
  | succ n =>
  simp only [ctorW] at h
  rcases hf : findLastW n m cno nn cn with _ | ⟨f, k⟩ <;> simp only [hf, pK, reduceCtorEq] at h
  split at h; cases h; rename_i hf0
  obtain ⟨f1, f2, f3⟩ := findLastW_facts n m cno nn cn f k hf (by omega) hf0
  rw [hcn] at f1 f3
  have hkk : (UInt64.ofNat k.toNat) = k := UInt64.ofNat_toNat
  obtain ⟨-, -, hct⟩ := hCt
  obtain ⟨⟨c1, -, c3⟩, c4, c5, c6, c7⟩ := hct k.toNat f1
  -- the record's words
  have hk10 : (10 : Word).toNat = 10 := rfl
  have ix : ∀ s : Word, s.toNat < 10 → (co + 10 * k + s).toNat = co.toNat + 10 * k.toNat + s.toNat := by
    intro s hs; rw [widx _ _ _ _ (by rw [hk10]; omega), hk10]
  have rd : ∀ s : Word, s.toNat < 10 → rdW (m.arr64 IFR) (co + 10 * k + s) = wd m IFR (co.toNat + 10 * k.toNat + s.toNat) := by
    intro s hs; rw [wd_eq, ix s hs]
  have rd0 : rdW (m.arr64 IFR) (co + 10 * k) = wd m IFR (co.toNat + 10 * k.toNat) := by
    have := rd 0 (by decide); simpa using this
  -- the lookup
  have hfold : ((islice (k := .name) m cno.toNat cts.length).foldl
      (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1[(decI nn : NIdx)]? =
      some k.toNat := by
    have := ctorIx_last (islice m cno.toNat cts.length) ∅ 0 (decI nn) k.toNat
      (by rw [islice_length]; exact f1) (by rw [islice_get, f2]) (fun k' h1 h2 => by
        rw [islice_get]; intro e
        rw [islice_length] at h2
        exact f3 k' h1 h2 (decI_inj' _ _ (hCN k' h2) hnn e))
    simpa using this
  unfold ctorAt at h
  split at h; cases h; rename_i hcidx
  have hcidx' : ∀ ci, cts[k.toNat].cidx = some ci → ci = j.toNat := by
    intro ci hci
    rw [hci] at c6
    obtain ⟨e1, e2⟩ := c6
    have : rdW (m.arr64 IFR) (co + 10 * k + 6) ≠ 0 := by rw [rd 6 (by decide)]; simp only [show (6 : Word).toNat = 6 from rfl]; rw [e1]; decide
    have hj : rdW (m.arr64 IFR) (co + 10 * k + 7) = j :=
      Classical.byContradiction fun hne => hcidx ⟨this, hne⟩
    rw [rd 7 (by decide)] at hj
    simp only [show (7 : Word).toNat = 7 from rfl, show co.toNat + 10 * k.toNat + 7 = co.toNat + 10 * k.toNat + 6 + 1 by omega] at hj
    rw [← e2.1, hj]
  -- the `induct` check, then the telescope
  have htail : ∀ c', ctorTail n m np fuel (co + 10 * k) = some c' → c' = co + 10 * k ∧
      ∃ cty, (getDeclD st cts[k.toNat].cv.type).run a = .ok (cty, a) ∧
        (ConRon.Arena.Frontend.indPiTeleLen fuel.toNat cty).run a =
          .ok (np.toNat + cts[k.toNat].numFields, a) := by
    intro c' hc'
    unfold ctorTail at hc'
    cases ht : lkW m EID (rdW (m.arr64 IFR) (co + 10 * k + 2)) with
    | none => rw [ht, wK_none] at hc'; cases hc'
    | some t =>
    rw [ht, wK_some] at hc'
    cases hx : teleW n m fuel t with
    | none => rw [hx, wK_none] at hc'; cases hc'
    | some x =>
    rw [hx, wK_some] at hc'
    split at hc'
    · cases hc'
    rename_i hnx
    cases hc'
    refine ⟨rfl, decE t, ?_, ?_⟩
    · rw [rd 2 (by decide)] at ht
      have := (lkW_expr hD a ht).1
      simp only [show (2 : Word).toNat = 2 from rfl] at this
      rw [c3.1] at this; exact this
    · obtain ⟨t1, -⟩ := teleW_ok m a hR n fuel t x hx
      rw [t1]
      have hx' : x = np + rdW (m.arr64 IFR) (co + 10 * k + 4) :=
        Classical.byContradiction fun hne => hnx (fun e => hne e.symm)
      rw [hx', rd 4 (by decide)]
      simp only [show (4 : Word).toNat = 4 from rfl]
      rw [widx2 _ _ (by rw [c4.1]; have := c4.2; omega), c4.1]
  split at h
  · rename_i hfl
    rcases hl : lkW m NID (rdW (m.arr64 IFR) (co + 10 * k + 9)) with _ | x <;> simp only [hl, wK, reduceCtorEq] at h
    split at h; cases h; rename_i hxt
    have hxt' : x = tt := by simpa using hxt
    obtain ⟨e1, e2⟩ := htail c h
    refine ⟨k.toNat, f1, by rw [e1, hkk], hfold, hcidx', fun iw hiw => ?_, e2⟩
    rw [hiw] at c7
    obtain ⟨-, d2⟩ := c7
    rw [rd 9 (by decide)] at hl
    simp only [show (9 : Word).toNat = 9 from rfl, show co.toNat + 10 * k.toNat + 9 = co.toNat + 10 * k.toNat + 8 + 1 by omega] at hl
    have := (lkW_name hD a hl).1
    rw [d2.1, hxt'] at this
    exact this
  · rename_i hfl
    obtain ⟨e1, e2⟩ := htail c h
    refine ⟨k.toNat, f1, by rw [e1, hkk], hfold, hcidx', fun iw hiw => ?_, e2⟩
    rw [hiw] at c7
    obtain ⟨d1, -⟩ := c7
    exfalso; apply hfl
    rw [rd 8 (by decide)]
    simp only [show (8 : Word).toNat = 8 from rfl]
    rw [d1]; decide

end L.Front.Ind
