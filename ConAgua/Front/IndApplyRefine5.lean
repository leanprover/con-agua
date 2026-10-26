import ConAgua.Front.IndApplyRefine4

/-!
# The apply step of an `inductive` line against the twin, V: the constructors in the block's order

`vi_order_in`/`vi_order_go`/`vi_order`: every constructor of every type, in the block's order,
passes `vi_ctor` (`ctorW_twin`), its record's pointer written to the ordered slice at `oo`. The
facts are collected per position (`CtorOK`); `ordList` reads the ordered constructors back from
the slice.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)


namespace L.Front.Ind

instance : Inhabited IndCtorRec := ⟨⟨⟨0, [], 0⟩, false, 0, 0, none, none⟩⟩

/-- `m'` is `m` but for `IFL` at `B` and above. -/
def IOnly (B : Nat) (m m' : Mem) : Prop :=
  MemFrame [IFL] [] m m' ∧ ∀ i, i < B → wd m' IFL i = wd m IFL i

theorem IOnly.refl (B : Nat) (m : Mem) : IOnly B m m := ⟨MemFrame.refl _ _ _, fun _ _ => rfl⟩

theorem IOnly.trans {B : Nat} {m₁ m₂ m₃ : Mem} (h₁ : IOnly B m₁ m₂) (h₂ : IOnly B m₂ m₃) :
    IOnly B m₁ m₃ := ⟨h₁.1.trans h₂.1, fun i hi => (h₂.2 i hi).trans (h₁.2 i hi)⟩

theorem IOnly.set {B : Nat} {m₁ m₂ : Mem} (h : IOnly B m₁ m₂) (i v : Word) (hi : B ≤ i.toNat) :
    IOnly B m₁ (m₂.set64 IFL i v) :=
  ⟨h.1.trans (MemFrame.set64 _ _ (by decide) _ _), fun j hj => by
    rw [wd_setA, ite_eq_right (by omega)]; exact h.2 j hj⟩

theorem IOnly.ifr {B : Nat} {m m' : Mem} (h : IOnly B m m') : m'.arr64 IFR = m.arr64 IFR :=
  h.1.1 IFR (by decide) (by decide)

theorem IOnly.other {B : Nat} {m m' : Mem} (h : IOnly B m m') (A : ArrId) (h1 : A ≠ IFL) (h2 : A ≠ CTL) :
    m'.arr64 A = m.arr64 A := h.1.1 A (by simp [h1]) h2

theorem IOnly.arena {B : Nat} {m m' : Mem} {a : AState} (h : IOnly B m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext [IFL] [] (by decide) (by simp) m m' h.1 a hR

theorem IOnly.stateDR {B : Nat} {m m' : Mem} {st : StateD} (h : IOnly B m m') (hD : StateDR m st) :
    StateDR m' st :=
  hD.frame h.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [IFL, idArrs])
    (by simp)

theorem IOnly.wdR {B : Nat} {m m' : Mem} (h : IOnly B m m') (i : Nat) : wd m' IFR i = wd m IFR i := by
  simp only [wd, h.ifr]

theorem IOnly.listF {B : Nat} {m m' : Mem} {b : ByteArray} {co : Nat} {cts : List IndCtorRec}
    (h : IOnly B m m') (hC : ListF (CtF b m) m 10 co cts) : ListF (CtF b m') m' 10 co cts := by
  obtain ⟨h1, h2, h3⟩ := hC
  refine ⟨h1, by simp only [topN, h.wdR]; exact h2, fun j hj => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := h3 j hj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [CVF, h.wdR] at c1 ⊢; exact c1
  · simpa only [h.wdR] using c2
  · simpa only [h.wdR] using c3
  · cases hc : cts[j].cidx <;> rw [hc] at c4 <;> simp only [OptW, h.wdR] at c4 ⊢ <;> exact c4
  · cases hc : cts[j].induct <;> rw [hc] at c5 <;> simp only [OptW, h.wdR] at c5 ⊢ <;> exact c5

theorem IOnly.islice {B : Nat} {m m' : Mem} (h : IOnly B m m') (o l : Nat) (hb : o + l ≤ B) :
    islice (k := .name) m' o l = islice m o l := by
  simp only [L.Front.Ind.islice]
  apply List.map_congr_left
  intro c hc
  simp only [List.mem_range] at hc
  rw [h.2 _ (by omega)]

/-- **The twin's checks of one constructor pass**: record `k` is the last one named `nn` among the
constructor names `CN`, and its `cidx`, `induct` and telescope agree. -/
def CtorOK (st : StateD) (a : AState) (cts : List IndCtorRec) (CN : List NIdx) (nn : NIdx)
    (j : Nat) (T : NIdx) (np fuel : Nat) (k : Nat) : Prop :=
  ∃ hk : k < cts.length,
    (CN.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1[nn]? =
      some k ∧
    (∀ ci, cts[k].cidx = some ci → ci = j) ∧
    (∀ iw, cts[k].induct = some iw → (st.name iw).run a = .ok (T, a)) ∧
    ∃ cty, (getDeclD st cts[k].cv.type).run a = .ok (cty, a) ∧
      (ConRon.Arena.Frontend.indPiTeleLen fuel cty).run a = .ok (np + cts[k].numFields, a)

/-- The ordered constructors read back from the slice at `oo`: record `(w - co) / 10` for each
pointer `w`. -/
def ordList (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) : List IndCtorRec :=
  (List.range l).map fun p => cts.getD (((wd m IFL (oo + p)).toNat - co) / 10) default

theorem ordList_length (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) :
    (ordList m oo co cts l).length = l := by simp [ordList]

/-- A pointer `co + 10 k` reads back as record `k`. -/
theorem ptr_rec (cts : List IndCtorRec) (co : Word) (k : Nat) (hk : k < cts.length)
    (hb : co.toNat + 10 * cts.length < 2 ^ 63) (w : Word) (hw : w = co + 10 * UInt64.ofNat k) :
    cts.getD ((w.toNat - co.toNat) / 10) default = cts[k] := by
  have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  subst hw
  rw [widx2 _ _ (by rw [UInt64.toNat_mul, hk']; simp; omega), UInt64.toNat_mul, hk']
  simp only [show (10 : Word).toNat = 10 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), show co.toNat + 10 * k - co.toNat = 10 * k by omega,
    Nat.mul_div_cancel_left _ (by decide)]
  simp [List.getD_eq_getElem?_getD, hk]

/-! ## `vi_order_in` -/

section order
variable {b : ByteArray} {m₀ : Mem} {a : AState} {st : StateD} (hR : ArenaR m₀ a)
  (hD : StateDR m₀ st) {cts : List IndCtorRec} {fo cno co cn fuel np oo : Word}
  (hCt : ListF (CtF b m₀) m₀ 10 co.toNat cts) (hcn : cn.toNat = cts.length)
  (hCN : ∀ k, k < cts.length → (wd m₀ IFL (cno.toNat + k)).toNat < 2 ^ 32)
  (hcnB : cno.toNat + cts.length ≤ oo.toNat) (hnp : np.toNat < 10 ^ 18)
  (hco : co.toNat + 10 * cts.length < 2 ^ 63) (hsz : oo.toNat + cts.length ≤ (m₀.arr64 IFL).size)
  (hsz63 : (m₀.arr64 IFL).size < 2 ^ 63)
include hR hD hCt hcn hCN hcnB hnp hco hsz hsz63

theorem orderInW_twin : ∀ (n : Nat) (m m' : Mem) (t tt jj pos pos' : Word),
    orderInW n m fo cno co cn fuel np oo t tt jj pos = some (pos', m') → IOnly oo.toNat m₀ m →
    t.toNat + 4 < 2 ^ 63 → jj.toNat ≤ (wd m₀ IFR (t.toNat + 4)).toNat →
    pos.toNat + ((wd m₀ IFR (t.toNat + 4)).toNat - jj.toNat) ≤ cts.length →
    (∀ c, jj.toNat ≤ c → c < (wd m₀ IFR (t.toNat + 4)).toNat →
      fo.toNat + pos.toNat + (c - jj.toNat) < oo.toNat ∧
      (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat))).toNat < 2 ^ 32) →
    IOnly oo.toNat m₀ m' ∧ pos'.toNat = pos.toNat + ((wd m₀ IFR (t.toNat + 4)).toNat - jj.toNat) ∧
    (∀ i, i < oo.toNat + pos.toNat → wd m' IFL i = wd m IFL i) ∧
    ∀ c, jj.toNat ≤ c → c < (wd m₀ IFR (t.toNat + 4)).toNat →
      ∃ k, wd m' IFL (oo.toNat + pos.toNat + (c - jj.toNat)) = co + 10 * UInt64.ofNat k ∧
        CtorOK st a cts (islice m₀ cno.toNat cts.length)
          (decI (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat)))) c (decI tt) np.toNat fuel.toNat k := by
  intro n
  induction n with
  | zero => intro m m' t tt jj pos pos' h; simp [orderInW] at h
  | succ n ih =>
    intro m m' t tt jj pos pos' h hI ht hjj hpos hfo
    simp only [orderInW] at h
    have h4 : rdW (m.arr64 IFR) (t + 4) = wd m₀ IFR (t.toNat + 4) := by
      rw [wd_eq, widx2 _ _ (by simp; omega), hI.wdR]; rfl
    rw [h4] at h
    split at h
    · rename_i hle
      cases h
      have := UInt64.le_iff_toNat_le.mp hle
      exact ⟨hI, by omega, fun _ _ => rfl, fun c h1 h2 => by omega⟩
    rename_i hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    obtain ⟨hf1, hf2⟩ := hfo jj.toNat (Nat.le_refl _) hlt'
    simp only [Nat.sub_self, Nat.add_zero] at hf1 hf2
    have hfp : (fo + pos).toNat = fo.toNat + pos.toNat := widx2 _ _ (by omega)
    have hop : (oo + pos).toNat = oo.toNat + pos.toNat := widx2 _ _ (by omega)
    have hnn : rdW (m.arr64 IFL) (fo + pos) = wd m₀ IFL (fo.toNat + pos.toNat) := by
      rw [wd_eq, hfp, hI.2 _ hf1]
    rw [hnn] at h
    rcases hc : ctorW n m (wd m₀ IFL (fo.toNat + pos.toNat)) jj tt np fuel cno cn co with _ | c <;> simp only [hc, wK, reduceCtorEq] at h
    -- the constructor, against the twin
    have hCN' : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32 := fun k hk => by
      rw [hI.2 _ (by omega)]; exact hCN k hk
    obtain ⟨k, hk, hck, hfold, hcidx, hind, htele⟩ := ctorW_twin (hI.arena hR) (hI.stateDR hD)
      (hI.listF hCt) hcn hCN' (by omega) hf2 hnp hco hc
    rw [hI.islice _ _ hcnB] at hfold
    -- the rest of the loop
    have hj1 := wsucc jj _ (UInt64.not_le.mp hlt)
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := widx2 _ _ (by simp; omega)
    obtain ⟨y1, y2, y3, y4⟩ := ih (m.set64 IFL (oo + pos) c) m' t tt (jj + 1) (pos + 1) pos' h
      (hI.set _ _ (by rw [hop]; omega)) ht (by rw [hj1]; omega) (by rw [hj1, hp1]; omega)
      (fun c' h1 h2 => by
        rw [hj1] at h1; rw [hp1, hj1]
        have := hfo c' (by omega) h2
        rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega]
        exact this)
    rw [hj1, hp1] at y2 y4
    rw [hp1] at y3
    have hwc : wd m' IFL (oo.toNat + pos.toNat) = c := by
      rw [y3 _ (by omega), wd_setA, ite_eq_left ⟨rfl, hop, by
        have := hI.1.2.2.1 IFL; rw [this]; omega⟩]
    refine ⟨y1, by omega, fun i hi => by rw [y3 _ (by omega), wd_setA, ite_eq_right (by omega)], fun c' h1 h2 => ?_⟩
    by_cases hcj : c' = jj.toNat
    · subst hcj
      simp only [Nat.sub_self, Nat.add_zero]
      exact ⟨k, by rw [hwc, hck], hk, hfold, hcidx, hind, htele⟩
    · obtain ⟨k', e1, e2⟩ := y4 c' (by omega) h2
      rw [show oo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = oo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e1
      rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e2
      exact ⟨k', e1, e2⟩

end order

/-! ## `vi_order_go` -/

/-- The constructor count of type record `k` (at `to + 11 k`). -/
def cntF (m : Mem) (to : Word) (k : Nat) : Nat := (wd m IFR (to.toNat + 11 * k + 4)).toNat

/-- The position of type `i`'s first constructor in the block's order. -/
def psum (m : Mem) (to : Word) (i : Nat) : Nat := ((List.range i).map (cntF m to)).sum

theorem psum_succ (m : Mem) (to : Word) (i : Nat) : psum m to (i + 1) = psum m to i + cntF m to i := by
  simp [psum, List.range_succ]

theorem psum_mono (m : Mem) (to : Word) (i j : Nat) (h : i ≤ j) : psum m to i ≤ psum m to j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rw [psum_succ]
    by_cases hij : i = j + 1
    · subst hij; rw [psum_succ]; exact Nat.le_refl _
    · have := ih (by omega); omega

section orderGo
variable {b : ByteArray} {m₀ : Mem} {a : AState} {st : StateD} (hR : ArenaR m₀ a)
  (hD : StateDR m₀ st) {cts : List IndCtorRec} {to tn tyn fo cno co cn fuel np oo : Word}
  (hCt : ListF (CtF b m₀) m₀ 10 co.toNat cts) (hcn : cn.toNat = cts.length)
  (hCN : ∀ k, k < cts.length → (wd m₀ IFL (cno.toNat + k)).toNat < 2 ^ 32)
  (hcnB : cno.toNat + cts.length ≤ oo.toNat) (hnp : np.toNat < 10 ^ 18)
  (hco : co.toNat + 10 * cts.length < 2 ^ 63) (hsz : oo.toNat + cts.length ≤ (m₀.arr64 IFL).size)
  (hsz63 : (m₀.arr64 IFL).size < 2 ^ 63)
  (hto : to.toNat + 11 * tn.toNat < 2 ^ 63) (htyn : tyn.toNat + tn.toNat ≤ oo.toNat)
  (hfo : ∀ p, p < psum m₀ to tn.toNat → fo.toNat + p < oo.toNat ∧ (wd m₀ IFL (fo.toNat + p)).toNat < 2 ^ 32)
  (hps : psum m₀ to tn.toNat ≤ cts.length)
include hR hD hCt hcn hCN hcnB hnp hco hsz hsz63 hto htyn hfo hps

theorem orderGoW_twin : ∀ (n : Nat) (m m' : Mem) (ti pos : Word),
    orderGoW n m to tn tyn fo cno co cn fuel np oo ti pos = some m' → IOnly oo.toNat m₀ m → ti ≤ tn →
    pos.toNat = psum m₀ to ti.toNat →
    IOnly oo.toNat m₀ m' ∧ (∀ i, i < oo.toNat + pos.toNat → wd m' IFL i = wd m IFL i) ∧
    ∀ k, ti.toNat ≤ k → k < tn.toNat → ∀ c, c < cntF m₀ to k →
      ∃ kk, wd m' IFL (oo.toNat + psum m₀ to k + c) = co + 10 * UInt64.ofNat kk ∧
        CtorOK st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k + c)))
          c (decI (wd m₀ IFL (tyn.toNat + k))) np.toNat fuel.toNat kk := by
  intro n
  induction n with
  | zero => intro m m' ti pos h; simp [orderGoW] at h
  | succ n ih =>
    intro m m' ti pos h hI hti hpos
    simp only [orderGoW] at h
    split at h
    · rename_i hle
      cases h
      have := UInt64.le_iff_toNat_le.mp hle
      have := UInt64.le_iff_toNat_le.mp hti
      exact ⟨hI, fun _ _ => rfl, fun k h1 h2 => by omega⟩
    rename_i hlt
    have hlt' := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    have hti1 := wsucc ti tn (UInt64.not_le.mp hlt)
    have htt : rdW (m.arr64 IFL) (tyn + ti) = wd m₀ IFL (tyn.toNat + ti.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega), hI.2 _ (by omega)]
    rw [htt] at h
    have hmono := psum_mono m₀ to (ti.toNat + 1) tn.toNat (by omega)
    rw [psum_succ] at hmono
    rcases hin : orderInW n m fo cno co cn fuel np oo (to + 11 * ti) (wd m₀ IFL (tyn.toNat + ti.toNat)) 0 pos with _ | ⟨q, m₁⟩ <;> simp only [hin, allocK, reduceCtorEq] at h
    have ht : (to + 11 * ti).toNat = to.toNat + 11 * ti.toNat := by
      have := widx to 11 ti 0 (by simp; omega); simpa using this
    have hc4 : wd m₀ IFR ((to + 11 * ti).toNat + 4) = wd m₀ IFR (to.toNat + 11 * ti.toNat + 4) := by rw [ht]
    obtain ⟨x1, x2, x3, x4⟩ := orderInW_twin hR hD hCt hcn hCN hcnB hnp hco hsz hsz63 n m m₁
      (to + 11 * ti) _ 0 pos q hin hI (by rw [ht]; omega) (by simp)
      (by simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero]; rw [hc4]; unfold cntF at hmono; omega)
      (fun c h1 h2 => by
        simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at h2 ⊢
        rw [hc4] at h2
        have := hfo (pos.toNat + c) (by rw [hpos]; unfold cntF at hmono; omega)
        rw [Nat.add_assoc]; exact this)
    simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at x2
    rw [hc4] at x2
    obtain ⟨y1, y2, y3⟩ := ih m₁ m' (ti + 1) q h x1 (UInt64.le_iff_toNat_le.mpr (by rw [hti1]; exact hlt'))
      (by rw [hti1, psum_succ, x2, hpos]; rfl)
    rw [hti1] at y3
    refine ⟨y1, fun i hi => by rw [y2 _ (by rw [x2]; omega), x3 _ hi], fun k h1 h2 c hc => ?_⟩
    by_cases hk : k = ti.toNat
    · subst hk
      obtain ⟨kk, e1, e2⟩ := x4 c (Nat.zero_le _) (by rw [hc4]; exact hc)
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at e1 e2
      refine ⟨kk, ?_, by rw [← hpos]; exact e2⟩
      rw [y2 _ (by rw [x2]; unfold cntF at hc; omega), ← hpos]; exact e1
    · exact y3 k (by omega) h2 c hc

end orderGo

end L.Front.Ind
