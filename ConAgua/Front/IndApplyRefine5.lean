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

set_option linter.unusedSimpArgs false

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
    rw [wd_set64, if_neg (by omega)]; exact h.2 j hj⟩

theorem IOnly.ifr {B : Nat} {m m' : Mem} (h : IOnly B m m') : m'.arr64 IFR = m.arr64 IFR :=
  h.1.1 IFR (by decide) (by decide)

theorem IOnly.other {B : Nat} {m m' : Mem} (h : IOnly B m m') (A : ArrId) (h1 : A ≠ IFL) (h2 : A ≠ CTL) :
    m'.arr64 A = m.arr64 A := h.1.1 A (by simp [h1]) h2

theorem IOnly.arena {B : Nat} {m m' : Mem} {a : AState} (h : IOnly B m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext [IFL] [] (by decide) (by simp) m m' h.1 a hR

theorem IOnly.stateDR {B : Nat} {m m' : Mem} {st : StateD} (h : IOnly B m m') (hD : StateDR m st) :
    StateDR m' st :=
  hD.frame h.1 (by decide) (by decide) (by decide) (by decide) (by decide)

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

theorem ordList_succ (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) :
    ordList m oo co cts (l + 1) =
      ordList m oo co cts l ++ [cts.getD (((wd m IFL (oo + l)).toNat - co) / 10) default] := by
  simp [ordList, List.range_succ]

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
    cases hc : ctorW n m (wd m₀ IFL (fo.toNat + pos.toNat)) jj tt np fuel cno cn co with
    | none => rw [hc, wK_none] at h; cases h
    | some c =>
    rw [hc, wK_some] at h
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
      rw [y3 _ (by omega), wd_set64, if_pos ⟨rfl, hop, by
        have := hI.1.2.2.1 IFL; rw [this]; omega⟩]
    refine ⟨y1, by omega, fun i hi => by rw [y3 _ (by omega), wd_set64, if_neg (by omega)], fun c' h1 h2 => ?_⟩
    by_cases hcj : c' = jj.toNat
    · subst hcj
      simp only [Nat.sub_self, Nat.add_zero]
      exact ⟨k, by rw [hwc, hck], hk, hfold, hcidx, hind, htele⟩
    · obtain ⟨k', e1, e2⟩ := y4 c' (by omega) h2
      rw [show oo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = oo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e1
      rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e2
      exact ⟨k', e1, e2⟩

end order

end L.Front.Ind
