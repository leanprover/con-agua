import ConAgua.Checker.PrepLeafRef

/-!
# `prepare_prelude`'s loops: `prep_front` refines `frontOf`, `prep_rest` its rest (lane `front4`)

The stream not yet picked is the list of stream positions `x ∈ [np, n)` not marked in `mk`
(`unm`): the twin's array after `pick`'s erasures is that list mapped through the records. Each
prelude record `a` is replaced by the first such record declaring its key (marked: it leaves the
stream), or kept; `ord[a]` is the position chosen.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- The positions `x ∈ [lo, hi)` not marked in `IW[mk ..]`. -/
def unm (m : Mem) (mk : Word) (lo hi : Nat) : List Nat :=
  (List.range' lo (hi - lo)).filter fun x => rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0

/-- The records at the positions of a list. -/
def recsAt (dsAll : Array IDeclaration) (xs : List Nat) : Array IDeclaration :=
  (xs.map fun x => dsAll[x]!).toArray

/-- **The prepare stage's setting**: the `n` records of `DECL` represent `dsAll` (each with
`RecOK`), `n < 2 ^ 59`, the prelude's `np ≤ n`; the slices `ord` and `mk` of `n` words each,
consecutive, below the pool top; the store relation. -/
structure PEnv (m : Mem) (a : AState) (dsAll : Array IDeclaration) (np nw ord mk : Word) : Prop where
  recs : ∀ x (h : x < dsAll.size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x dsAll[x] ∧
    RecOK (m.arr64 DECL) (m.arr64 DLP) x
  size : nw.toNat = dsAll.size
  n59 : nw.toNat < 2 ^ 59
  np : np.toNat ≤ nw.toNat
  rg1 : ord.toNat + nw.toNat ≤ mk.toNat
  rg2 : mk.toNat + nw.toNat ≤ iwTop m
  iwok : IWOK m
  arena : ArenaR m a

/-- What `prep_front`/`prep_rest` keep: arrays and `CTL` words from `64` on but `IW`, every
size, and the `IW` words outside `[ord, mk + n)`. -/
def PFr (ord mk nw : Word) (m m' : Mem) : Prop :=
  (∀ b : ArrId, 64 ≤ b → b ≠ IW → m'.arr64 b = m.arr64 b) ∧
    (∀ x : Word, 64 ≤ x.toNat → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) ∧
    (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size ∧
    ∀ x : Nat, (x < ord.toNat ∨ mk.toNat + nw.toNat ≤ x) → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?


/-! ## The unmarked positions -/

theorem unm_nil (m : Mem) (mk : Word) (lo hi : Nat) (h : hi ≤ lo) : unm m mk lo hi = [] := by
  simp [unm, Nat.sub_eq_zero_of_le h]

theorem unm_succ (m : Mem) (mk : Word) (lo hi : Nat) (h : lo < hi) :
    unm m mk lo hi = if rdW (m.arr64 IW) (mk + UInt64.ofNat lo) = 0 then lo :: unm m mk (lo + 1) hi
      else unm m mk (lo + 1) hi := by
  unfold unm
  rw [show hi - lo = (hi - (lo + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
  simp

theorem unm_congr (m m' : Mem) (mk : Word) (lo hi : Nat)
    (h : ∀ x, lo ≤ x → x < hi →
      rdW (m'.arr64 IW) (mk + UInt64.ofNat x) = rdW (m.arr64 IW) (mk + UInt64.ofNat x)) :
    unm m' mk lo hi = unm m mk lo hi := by
  unfold unm
  apply List.filter_congr
  intro x hx
  rw [List.mem_range'_1] at hx
  rw [h x hx.1 (by omega)]

theorem mem_unm {m : Mem} {mk : Word} {lo hi x : Nat} :
    x ∈ unm m mk lo hi ↔ lo ≤ x ∧ x < hi ∧ rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 := by
  simp only [unm, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

theorem unm_sorted (m : Mem) (mk : Word) (lo hi : Nat) : (unm m mk lo hi).Pairwise (· < ·) :=
  (List.pairwise_lt_range' 1).filter _

theorem rdW_of_get? {A B : Array Word} {x : Word} (h : A[x.toNat]? = B[x.toNat]?) : rdW A x = rdW B x := by
  simp only [rdW, h]

/-- **`prep_front` is `frontOf`** from the prelude record `aw` on (`acc` the front so far, the
twin's stream the unmarked records). -/
theorem pFront_ok (dsAll : Array IDeclaration) (np nw ord mk : Word) :
    ∀ (fuel : Nat) (m m' : Mem) (a : AState) (aw r : Word) (acc : Array IDeclaration),
    PEnv m a dsAll np nw ord mk → aw.toNat ≤ np.toNat → acc.size = aw.toNat →
    (∀ k (hk : k < aw.toNat), (rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
      acc[k]! = dsAll[(rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat]!) →
    pFrontW fuel m np nw ord mk aw = some (r, m') →
    ∃ (front rest : Array IDeclaration) (a' : AState),
      (frontOf acc ((dsAll.toList.take np.toNat).drop aw.toNat)
        (recsAt dsAll (unm m mk np.toNat nw.toNat))).run a = .ok ((front, rest), a') ∧
      front.size = np.toNat ∧
      (∀ k (hk : k < np.toNat), (rdW (m'.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
        front[k]! = dsAll[(rdW (m'.arr64 IW) (ord + UInt64.ofNat k)).toNat]!) ∧
      rest = recsAt dsAll (unm m' mk np.toNat nw.toNat) ∧
      PEnv m' a' dsAll np nw ord mk ∧ a'.pins = a.pins ∧ PFr ord mk nw m m' := by
  sorry

/-- **`prep_rest` writes the unmarked records `[j, n)` to `ord[c ..]`.** -/
theorem pRest_ok (nw ord mk : Word) :
    ∀ (fuel : Nat) (m m' : Mem) (c j r : Word),
    ord.toNat + nw.toNat ≤ mk.toNat → mk.toNat + nw.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 → c.toNat ≤ j.toNat → j.toNat ≤ nw.toNat →
    pRestW fuel m nw ord mk c j = some (r, m') →
    r.toNat = c.toNat + (unm m mk j.toNat nw.toNat).length ∧
      (∀ k (hk : k < (unm m mk j.toNat nw.toNat).length),
        rdW (m'.arr64 IW) (ord + UInt64.ofNat (c.toNat + k)) =
          UInt64.ofNat ((unm m mk j.toNat nw.toNat)[k]'hk)) ∧
      MemFrame [IW] [] m m' ∧
      ∀ x : Nat, (x < ord.toNat + c.toNat ∨ ord.toNat + nw.toNat ≤ x) →
        (m'.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  intro fuel
  induction fuel with
  | zero => intro m m' c j r _ _ _ _ _ h; simp [pRestW.eq_1] at h
  | succ fuel ih =>
    intro m m' c j r h1 h2 h3 hcj hjn h
    by_cases hj : nw ≤ j
    · rw [pRestW.arm1 _ _ _ _ _ _ _ hj] at h
      cases h
      have : nw.toNat ≤ j.toNat := UInt64.le_iff_toNat_le.mp hj
      rw [unm_nil _ _ _ _ this]
      exact ⟨by simp, fun k hk => by simp at hk, MemFrame.refl _ _ _, fun _ _ => rfl⟩
    · have hjlt : j.toNat < nw.toNat := by
        have := mt UInt64.le_iff_toNat_le.mpr hj; omega
      have hj1 := toNat_succ j (by omega)
      have hmkj : mk + j = mk + UInt64.ofNat j.toNat := by simp
      by_cases hz : rdW (m.arr64 IW) (mk + j) = 0
      · rw [pRestW.arm2 _ _ _ _ _ _ _ hj hz, pRestW.k1.arm1] at h
        have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_succ c (by omega)
        have hsz : ((m.set64 IW (ord + c) j).arr64 IW).size = (m.arr64 IW).size := size_set64 _ _ _ _ _
        obtain ⟨hr, hk, hfr, hout⟩ := ih _ m' (c + 1) (j + 1) r h1 (hsz ▸ h2) (hsz ▸ h3)
          (by omega) (by omega) h
        have hoc : (ord + c).toNat = ord.toNat + c.toNat := by
          rw [UInt64.toNat_add]; omega
        have hU : unm (m.set64 IW (ord + c) j) mk (j + 1).toNat nw.toNat =
            unm m mk (j.toNat + 1) nw.toNat := by
          rw [hj1]
          apply unm_congr
          intro x hx1 hx2
          rw [rdW_set64]
          have : ¬ (ord + c = mk + UInt64.ofNat x) := by
            intro e
            have := congrArg UInt64.toNat e
            rw [hoc, addW_toNat mk x (by omega)] at this
            omega
          simp [this]
        rw [hU] at hr hk
        rw [unm_succ _ _ _ _ hjlt]; simp only [← hmkj, hz, ↓reduceIte]
        refine ⟨by simp [hr, hc1]; omega, fun k hk' => ?_, ?_, ?_⟩
        · cases k with
          | zero =>
            simp only [List.getElem_cons_zero, Nat.add_zero]
            have hx := hout (ord.toNat + c.toNat) (Or.inl (by omega))
            rw [rdW_addr _ _ _ (by omega), hx, Mem.arr64_set64_same, hoc]
            simp [Array.getElem?_setIfInBounds]
            simp only [show ord.toNat + c.toNat < (m.arr64 IW).size by omega, ↓reduceIte,
              Option.getD_some]
          | succ k =>
            simp only [List.getElem_cons_succ]
            have := hk k (by simp only [List.length_cons] at hk'; omega)
            rw [hc1, show c.toNat + 1 + k = c.toNat + (k + 1) by omega] at this
            exact this
        · exact (MemFrame.set64 m IW (by decide) _ _).trans hfr
        · intro x hx
          rw [hout x (by omega), Mem.arr64_set64_same, hoc]
          simp [Array.getElem?_setIfInBounds]
          omega
      · rw [pRestW.arm3 _ _ _ _ _ _ _ hj hz, pRestW.k1.arm1] at h
        obtain ⟨hr, hk, hfr, hout⟩ := ih m m' c (j + 1) r h1 h2 h3 (by omega) (by omega) h
        rw [hj1] at hr hk
        rw [unm_succ _ _ _ _ hjlt]; simp only [← hmkj, hz, ↓reduceIte]
        exact ⟨hr, hk, hfr, hout⟩

end L.Checker
