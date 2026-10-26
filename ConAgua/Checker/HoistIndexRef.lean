import ConAgua.Checker.HoistRefBase

/-!
# The hoist's name index refines `nameIndex` (lane `front4`)

`hoist_index_go` (each position's names `hoist_ins`-ed into the memo `HNIX`, the first position
declaring a name winning) against `nameIndex ds idx k` (`insertNames`), and `hoist_ix` against the
map's lookup.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-! ## Helpers -/

theorem insertNames_lt (ds : Array IDeclaration) (i : Nat) (hi : i < ds.size) :
    ∀ (ns : List NIdx) (idx : Std.HashMap NIdx Nat),
    (∀ (n : NIdx) (j : Nat), idx[n]? = some j → j < ds.size) →
    ∀ (n : NIdx) (j : Nat), (insertNames idx i ns)[n]? = some j → j < ds.size
  | [], idx, h => h
  | x :: ns, idx, h => by
    refine insertNames_lt ds i hi ns _ ?_
    intro n j hj
    split at hj
    · exact h n j hj
    · rw [Std.HashMap.getElem?_insert] at hj
      split at hj
      · cases hj; exact hi
      · exact h n j hj

/-- The name index's value relation reads no memory. -/
theorem nix_vstable : VStable hnSch (fun (_ : Mem) (w : Word) (j : Nat) => w.toNat = j + 1) :=
  fun _ _ _ _ _ h => h

theorem hIns_ok (m m' : Mem) (w k r : Word) (idx : Std.HashMap NIdx Nat) (hR : NixR m idx)
    (hw : w.toNat < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 64) (h : hInsW m w k = some (r, m')) :
    NixR m' (if idx.contains (decI w) then idx else idx.insert (decI w) k.toNat) ∧
      MemFrame [HNIX] [75, 76] m m' := by
  have hok : nmKey.ok w 0 := ⟨hw, rfl⟩
  by_cases h0 : mfindG hnSch m w 0 = []
  · simp [hInsW, h0] at h
  by_cases h1 : (mfindG hnSch m w 0).headD 0 = 0
  · rw [hInsW.arm1 m w k h0 h1] at h
    have hmiss := memoRV_miss hnSch nmKey _ m idx hR w 0 hok h0 h1
    simp only [nmKey] at hmiss
    cases hp : mputG hnSch m w 0 (k + 1) ((mfindG hnSch m w 0).headD 0)
        ((mfindG hnSch m w 0).tail.headD 0) with
    | none => rw [hp] at h; cases h
    | some m₁ =>
      rw [hp, hInsW.k_hn_put.arm1] at h
      cases h
      have hs : msetG hnSch m w 0 (k + 1) = some m' := by rw [msetG_eq _ _ _ _ _ h0]; exact hp
      have hc : idx.contains (decI w) = false := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, hmiss]; rfl
      rw [hc, if_neg (by simp)]
      refine ⟨memoRV_set hnSch ⟨by decide, by decide⟩ nmKey _ nix_vstable m idx hR w 0 (k + 1) hok
        k.toNat (by rw [UInt64.toNat_add]; simp; omega) m' hs, ?_⟩
      exact (mputG_frame hnSch ⟨by decide, by decide⟩ m m' _ _ _ _ _ hp).mono (by simp)
        (by simp)
  · rw [hInsW.arm2 m w k h0 h1] at h
    cases h
    obtain ⟨v, hv, -⟩ := memoRV_hit hnSch nmKey _ m idx hR w 0 h0 h1 hok
    simp only [nmKey] at hv
    have hc : idx.contains (decI w) = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hv]; rfl
    rw [hc, if_pos rfl]
    exact ⟨hR, MemFrame.refl _ _ _⟩

theorem hix_hd?_some {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  split at h
  · cases h; exact ⟨w, hw, by assumption, rfl⟩
  · cases h

theorem hix_decCV_name {a : Array Word} {q : Nat} {v : IConstantVal} (h : decCV a q = some v) :
    ∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ v.name = decI w := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨n, hn, l, -, t, -, rfl⟩ := h
  exact hix_hd?_some hn

theorem hix_decCI_name {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ w, a[p + 1]? = some w ∧ w.toNat < 2 ^ 32 ∧ ci.name = decI w := by
  simp only [decCI, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, -, h⟩ := h
  split at h <;>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      reduceCtorEq] at h
  · obtain ⟨v, hv, rfl⟩ := h; exact hix_decCV_name hv
  · obtain ⟨v, hv, _, _, _, _, rfl⟩ := h; exact hix_decCV_name hv
  · obtain ⟨v, hv, rfl⟩ := h; exact hix_decCV_name hv
  · obtain ⟨v, hv, _, _, rfl⟩ := h; exact hix_decCV_name hv
  · obtain ⟨v, hv, _, _, _, _, rfl⟩ := h; exact hix_decCV_name hv
  · obtain ⟨v, hv, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h; exact hix_decCV_name hv

theorem hix_trunc_get {P : Array Word} {t i : Nat} {v : Word} (h : (trunc P t)[i]? = some v)
    (hi : i ≠ 0) : P[i]? = some v ∧ i ≤ t := by
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.getElem?_extract, Array.size_extract] at h
  rw [if_neg (by omega)] at h
  split at h
  · simp only [Nat.zero_add] at h
    exact ⟨h, by omega⟩
  · cases h

theorem hix_decCIs_succ (a : Array Word) (dn : NIdx → Option ConLeche.Name) (o k : Nat) :
    decCIs a dn o (k + 1) = (do
      let x ← (do let v ← nat? a o; decCI a dn v)
      let xs ← decCIs a dn (o + 1) k
      pure (x :: xs)) := by
  simp only [decCIs, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  simp only [Function.comp_def]
  congr 1; funext j; congr 2; omega

theorem hix_rdW {P : Array Word} {x : Word} {i : Nat} {v : Word} (h : P[i]? = some v)
    (hx : x.toNat = i) : rdW P x = v := by
  simp [rdW, hx, h]

/-- **`hoist_names_go` inserts the block members' names** (the pointers `DIND[o + q ‥ o + c)`,
decoded below `t` by `decCIs`; the slice does not start at the pool's word `0`). -/
theorem hNamesGo_ok (n : Nat) : ∀ (m m' : Mem) (k o c q r : Word) (P : Array Word) (t : Nat)
    (cs : List IConstantInfo) (idx : Std.HashMap NIdx Nat),
    NixR m idx → m.arr64 DIND = P → t ≤ (P[0]?.getD 0).toNat → o.toNat ≠ 0 →
    decCIs (trunc P t) (fun _ => none) (o.toNat + q.toNat) (c.toNat - q.toNat) = some cs →
    k.toNat + 1 < 2 ^ 64 → hNamesGoW n m k o c q = some (r, m') →
    NixR m' (insertNames idx k.toNat (cs.map (·.name))) ∧ MemFrame [HNIX] [75, 76] m m' := by
  induction n with
  | zero => intro m m' k o c q r P t cs idx _ _ _ _ _ _ h; simp [hNamesGoW.eq_1] at h
  | succ n ih =>
    intro m m' k o c q r P t cs idx hR hP ht ho hd hk h
    by_cases hcq : c ≤ q
    · rw [hNamesGoW.arm1 n m k o c q hcq] at h
      cases h
      have : c.toNat - q.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hcq; omega
      rw [this, decCIs] at hd
      simp at hd; subst hd
      exact ⟨hR, MemFrame.refl _ _ _⟩
    · rw [hNamesGoW.arm2 n m k o c q hcq] at h
      have hqc : q.toNat < c.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hcq); omega
      rw [show c.toNat - q.toNat = (c.toNat - q.toNat - 1) + 1 by omega, hix_decCIs_succ] at hd
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hd
      obtain ⟨ci, ⟨p, hp, hci⟩, cs', hcs', rfl⟩ := hd
      simp only [nat?, Option.map_eq_some_iff] at hp
      obtain ⟨pw, hpw, rfl⟩ := hp
      obtain ⟨hPq, hqt⟩ := hix_trunc_get hpw (by omega)
      obtain ⟨w, hw, hw32, hname⟩ := hix_decCI_name hci
      obtain ⟨hPw, hpt⟩ := hix_trunc_get hw (by omega)
      have hP0 : (P[0]?.getD 0).toNat < 2 ^ 64 := UInt64.toNat_lt _
      have e1 : rdW (m.arr64 DIND) (o + q) = pw :=
        hix_rdW (hP ▸ hPq) (by rw [UInt64.toNat_add]; omega)
      have e2 : rdW (m.arr64 DIND) (pw + 1) = w :=
        hix_rdW (hP ▸ hPw) (by rw [UInt64.toNat_add]; simp; omega)
      rw [e1, e2] at h
      rcases hi : hInsW m w k with _ | ⟨z, m₁⟩ <;> rw [hi] at h
      · simp [hNamesGoW.k_hoist_ins] at h
      rw [hNamesGoW.k_hoist_ins.arm1] at h
      obtain ⟨hR₁, hF₁⟩ := hIns_ok m m₁ w k z idx hR hw32 hk hi
      have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      obtain ⟨hR', hF'⟩ := ih m₁ m' k o c (q + 1) r P t cs' _ hR₁
        (by rw [hF₁.1 DIND (by decide) (by decide)]; exact hP) ht ho
        (by rw [hq1, show o.toNat + (q.toNat + 1) = o.toNat + q.toNat + 1 by omega,
          show c.toNat - (q.toNat + 1) = c.toNat - q.toNat - 1 by omega]; exact hcs') hk h
      refine ⟨?_, hF₁.trans hF'⟩
      simp only [List.map_cons, insertNames, hname]
      exact hR'

/-- Word `j` of `DECL` record `r` (below `2 ^ 59`), read at `1 + 8 r + j`. -/
theorem hix_rd_dw (D : Array Word) (r j : Word) (hr : r.toNat < 2 ^ 59) (hj : j.toNat < 8) :
    rdW D (1 + 8 * r + j) = dw D r.toNat j.toNat := by
  have : (1 + 8 * r + j).toNat = 1 + 8 * r.toNat + j.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  simp [rdW, dw, this]

theorem hix_rd_dw0 (D : Array Word) (r : Word) (hr : r.toNat < 2 ^ 59) :
    rdW D (1 + 8 * r) = dw D r.toNat 0 := by
  have := hix_rd_dw D r 0 hr (by decide)
  simpa using this

theorem hix_declAt_names {D P : Array Word} {i : Nat} {d : IDeclaration} (h : DeclAt D P i d) :
    dw D i 0 ≠ 6 ∧ d.names = [decI (dw D i 1)] := by
  cases d <;> simp only [DeclAt, CVAt] at h <;>
    first | exact h.elim | exact ⟨by rw [h.1]; decide, by simp [IDeclaration.names, h.2.1]⟩

theorem hix_declAtF {D P : Array Word} {i : Nat} {d : IDeclaration}
    (hd : ∀ b nP, d ≠ .indDecl b nP) (h : DeclAtF D P i d) : DeclAt D P i d := by
  cases d <;> simp_all [DeclAtF]

/-- **`hoist_names` inserts a record's names** (record `r` of `DECL`, `x = 1 + 8 r`). -/
theorem hNames_ok (n : Nat) (m m' : Mem) (k r z : Word) (d : IDeclaration)
    (idx : Std.HashMap NIdx Nat) (hR : NixR m idx) (hr : r.toNat < 2 ^ 59)
    (hD : DeclAtF (m.arr64 DECL) (m.arr64 DLP) r.toNat d) (hok : RecOK (m.arr64 DECL) (m.arr64 DLP) r.toNat)
    (hk : k.toNat + 1 < 2 ^ 64) (h : hNamesW n m k (1 + 8 * r) = some (z, m')) :
    NixR m' (insertNames idx k.toNat d.names) ∧ MemFrame [HNIX] [75, 76] m m' := by
  cases n with
  | zero => cases h
  | succ n =>
  have e0 := hix_rd_dw0 (m.arr64 DECL) r hr
  have e1 := hix_rd_dw (m.arr64 DECL) r 1 hr (by decide)
  have e2 := hix_rd_dw (m.arr64 DECL) r 2 hr (by decide)
  have e3 := hix_rd_dw (m.arr64 DECL) r 3 hr (by decide)
  simp only [UInt64.reduceToNat] at e1 e2 e3
  by_cases hind : ∃ b nP, d = .indDecl b nP
  · obtain ⟨b, nP, rfl⟩ := hind
    obtain ⟨h6, -, t, ht, hb⟩ := hD
    rw [hNamesW.arm2 n m k _ (by rw [e0, h6]), e2, e3] at h
    cases hg : hNamesGoW n m k (dw (m.arr64 DECL) r.toNat 2) (dw (m.arr64 DECL) r.toNat 3) 0 with
    | none => rw [hg] at h; cases h
    | some zm =>
      obtain ⟨z', m₁⟩ := zm
      rw [hg] at h; simp only [hNamesW.k_hoist_ins, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hNamesGo_ok n m m₁ k _ _ 0 z' _ t b idx hR rfl ht (hok.2 h6).1
        (by simpa using hb) hk hg
  · have hD' := hix_declAtF (fun b nP e => hind ⟨b, nP, e⟩) hD
    obtain ⟨h6, hn⟩ := hix_declAt_names hD'
    rw [hNamesW.arm1 n m k _ (by rw [e0]; exact h6), e1] at h
    cases hi : hInsW m (dw (m.arr64 DECL) r.toNat 1) k with
    | none => rw [hi] at h; cases h
    | some zm =>
      obtain ⟨z', m₁⟩ := zm
      rw [hi] at h; simp only [hNamesW.k_hoist_ins, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [hn]
      exact hIns_ok m m₁ _ k z' idx hR (hok.1 h6).1 hk hi

/-- `hoistIndexGo_ok`, generalized over the memory, position and map for the induction. -/
private theorem hoistIndexGo_ok' (n : Nat) (ord c : Word) (ds : Array IDeclaration)
    (hc : ds.size = c.toNat) (hc60 : c.toNat < 2 ^ 60) :
    ∀ (m m' : Mem) (k r : Word) (idx : Std.HashMap NIdx Nat), OrdR m ord ds →
    k ≤ c → NixR m idx → hIndexGoW n m ord c k = some (r, m') →
    NixR m' (nameIndex ds idx k.toNat) ∧ MemFrame [HNIX] [75, 76] m m' := by
  induction n with
  | zero => intro m m' k r idx _ _ _ h; simp [hIndexGoW.eq_1] at h
  | succ n ih =>
    intro m m' k r idx hO hk hR h
    by_cases hck : c ≤ k
    · rw [hIndexGoW.arm1 n m ord c k hck] at h
      cases h
      have : k.toNat = ds.size := by
        have := UInt64.le_iff_toNat_le.mp hck; have := UInt64.le_iff_toNat_le.mp hk; omega
      rw [nameIndex, dif_neg (by omega)]
      exact ⟨hR, MemFrame.refl _ _ _⟩
    · rw [hIndexGoW.arm2 n m ord c k hck] at h
      have hkc : k.toNat < ds.size := by
        have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hck); omega
      obtain ⟨hr, hD, hok⟩ := hO k.toNat hkc
      simp only [UInt64.ofNat_toNat] at hr hD hok
      rcases hi : hNamesW n m k (1 + 8 * rdW (m.arr64 IW) (ord + k)) with _ | ⟨z, m₁⟩ <;> rw [hi] at h
      · simp [hIndexGoW.k_hoist_names] at h
      rw [hIndexGoW.k_hoist_names.arm1] at h
      obtain ⟨hR₁, hF₁⟩ := hNames_ok n m m₁ k _ z _ idx hR hr hD hok (by omega) hi
      have hIW : m₁.arr64 IW = m.arr64 IW := hF₁.1 IW (by decide) (by decide)
      have hDE : m₁.arr64 DECL = m.arr64 DECL := hF₁.1 DECL (by decide) (by decide)
      have hDL : m₁.arr64 DLP = m.arr64 DLP := hF₁.1 DLP (by decide) (by decide)
      have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      obtain ⟨hR', hF'⟩ := ih m₁ m' (k + 1) r _
        (by unfold OrdR; rw [hIW, hDE, hDL]; exact hO)
        (UInt64.le_iff_toNat_le.mpr (by omega)) hR₁ h
      refine ⟨?_, hF₁.trans hF'⟩
      rw [nameIndex, dif_pos hkc, ← hk1]
      exact hR'

/-! ## The refinements -/

/-- **`hoist_ix` is the lookup**: the position `+ 1`, or `0`. -/
theorem hoistIx_ok (m m' : Mem) (w r : Word) (idx : Std.HashMap NIdx Nat) (hR : NixR m idx)
    (hw : w.toNat < 2 ^ 32) (h : hIxW m w = some (r, m')) :
    m' = m ∧ r = tgW idx[(decI w : NIdx)]? := by
  have hok : nmKey.ok w 0 := ⟨hw, rfl⟩
  by_cases h0 : mfindG hnSch m w 0 = []
  · simp [hIxW, h0] at h
  by_cases h1 : (mfindG hnSch m w 0).headD 0 = 0
  · rw [hIxW.arm1 m w h0 h1] at h
    cases h
    have := memoRV_miss hnSch nmKey _ m idx hR w 0 hok h0 h1
    exact ⟨rfl, by simp only [nmKey] at this; rw [this]; rfl⟩
  · rw [hIxW.arm2 m w h0 h1] at h
    cases h
    obtain ⟨v, hv, hw'⟩ := memoRV_hit hnSch nmKey _ m idx hR w 0 h0 h1 hok
    simp only [nmKey] at hv
    refine ⟨rfl, ?_⟩
    rw [hv, tgW, ← hw']
    simp [mvG]


/-- **`hoist_index_go` builds `nameIndex`** from position `k` on (the stream `ds` in the order
`ord`, below `2 ^ 60` records). -/
theorem hoistIndexGo_ok (n : Nat) (m m' : Mem) (ord c k r : Word) (ds : Array IDeclaration)
    (idx : Std.HashMap NIdx Nat) (hO : OrdR m ord ds) (hc : ds.size = c.toNat)
    (hc60 : c.toNat < 2 ^ 60) (hord : ord.toNat + c.toNat < 2 ^ 64) (hk : k ≤ c)
    (hR : NixR m idx) (h : hIndexGoW n m ord c k = some (r, m')) :
    NixR m' (nameIndex ds idx k.toNat) ∧ MemFrame [HNIX] [75, 76] m m' := by
  exact hoistIndexGo_ok' n ord c ds hc hc60 m m' k r idx hO hk hR h

/-- The name index's positions are positions of the stream. -/
theorem nameIndex_lt (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (k : Nat)
    (h : ∀ (n : NIdx) (j : Nat), idx[n]? = some j → j < ds.size) :
    ∀ (n : NIdx) (j : Nat), (nameIndex ds idx k)[n]? = some j → j < ds.size := by
  induction idx, k using nameIndex.induct ds with
  | case1 idx k hk ih =>
    rw [nameIndex, dif_pos hk]
    exact ih (insertNames_lt ds k hk _ idx h)
  | case2 idx k hk =>
    rw [nameIndex, dif_neg hk]; exact h


end L.Checker
