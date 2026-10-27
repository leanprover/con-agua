import ConAgua.Checker.PrepLeafRef
import ConAgua.Checker.HoistClosureL
import ConAgua.Checker.HoistOrderRef3

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
  (∀ b : ArrId, b ∉ lowTierArrs → b ≠ IW → m'.arr64 b = m.arr64 b) ∧
    (∀ x : Word, 64 ≤ x.toNat → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) ∧
    (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size ∧
    ∀ x : Nat, (x < ord.toNat ∨ mk.toNat + nw.toNat ≤ x) → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?


/-! ## The unmarked positions -/

private theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]


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

theorem unm_mark (m m' : Mem) (mk : Word) (lo hi x : Nat)
    (h : ∀ y, lo ≤ y → y < hi → y ≠ x →
      rdW (m'.arr64 IW) (mk + UInt64.ofNat y) = rdW (m.arr64 IW) (mk + UInt64.ofNat y))
    (hx : rdW (m'.arr64 IW) (mk + UInt64.ofNat x) ≠ 0) :
    unm m' mk lo hi = (unm m mk lo hi).filter (· != x) := by
  unfold unm
  rw [List.filter_filter]
  apply List.filter_congr
  intro y hy
  rw [List.mem_range'_1] at hy
  by_cases e : y = x
  · subst e; simp [hx]
  · rw [h y hy.1 (by omega) e]; simp [e]

/-! ## `pick` on the unmarked records -/

/-- The first hit of a sorted list, mapped: its index, the element, the erasure. -/
theorem findIdx_hit (g : Nat → IDeclaration) (p : IDeclaration → Bool) (x : Nat) :
    ∀ l : List Nat, l.Pairwise (· < ·) → x ∈ l → p (g x) = true →
      (∀ y ∈ l, y < x → p (g y) = false) →
      ∃ i, (l.map g).findIdx p = i ∧ (l.map g)[i]? = some (g x) ∧
        (l.map g).eraseIdx i = (l.filter (· != x)).map g
  | [], _, hx, _, _ => by simp at hx
  | y :: t, hl, hx, hp, hb => by
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.mp hx with rfl | hxt
    · refine ⟨0, by simp [List.findIdx_cons, hp], rfl, ?_⟩
      have : t.filter (· != x) = t :=
        List.filter_eq_self.mpr fun z hz => by have := hl.1 z hz; simp; omega
      simp [this]
    · have hyx : y < x := hl.1 x hxt
      obtain ⟨i, h1, h2, h3⟩ := findIdx_hit g p x t hl.2 hxt hp (fun z hz => hb z (.tail _ hz))
      refine ⟨i + 1, by simp [List.findIdx_cons, hb y (.head _) hyx, ← h1], by simpa using h2, ?_⟩
      simp [List.eraseIdx_cons_succ, h3, Nat.ne_of_lt hyx]

theorem pick_hit (k : NIdx) (dsAll : Array IDeclaration) (l : List Nat) (x : Nat)
    (hl : l.Pairwise (· < ·)) (hx : x ∈ l) (hp : declares k dsAll[x]! = true)
    (hb : ∀ y ∈ l, y < x → declares k dsAll[y]! = false) :
    pick k (recsAt dsAll l) = (some dsAll[x]!, recsAt dsAll (l.filter (· != x))) := by
  obtain ⟨i, h1, h2, h3⟩ := findIdx_hit (fun x => dsAll[x]!) (declares k) x l hl hx hp hb
  simp only [pick, recsAt, List.findIdx_toArray, h1, List.eraseIdxIfInBounds_toArray,
    List.getElem?_toArray, h2, h3]

theorem pick_miss (k : NIdx) (dsAll : Array IDeclaration) (l : List Nat)
    (h : ∀ y ∈ l, declares k dsAll[y]! = false) :
    pick k (recsAt dsAll l) = (none, recsAt dsAll l) := by
  have hf : List.findIdx (declares k) (l.map fun x => dsAll[x]!) = (l.map fun x => dsAll[x]!).length := by
    rw [List.findIdx_eq_length]; simpa using h
  simp only [pick, recsAt, List.findIdx_toArray, hf, List.eraseIdxIfInBounds_toArray,
    List.getElem?_toArray, List.getElem?_eq_none (Nat.le_refl _),
    List.eraseIdx_of_length_le (Nat.le_refl _)]

/-! ## The frame -/

theorem PFr.trans {ord mk nw : Word} {m₁ m₂ m₃ : Mem} (h₁ : PFr ord mk nw m₁ m₂)
    (h₂ : PFr ord mk nw m₂ m₃) : PFr ord mk nw m₁ m₃ :=
  ⟨fun b hb hi => (h₂.1 b hb hi).trans (h₁.1 b hb hi), fun x hx => (h₂.2.1 x hx).trans (h₁.2.1 x hx),
    fun b => (h₂.2.2.1 b).trans (h₁.2.2.1 b), h₂.2.2.2.1.trans h₁.2.2.2.1,
    fun x hx => (h₂.2.2.2.2 x hx).trans (h₁.2.2.2.2 x hx)⟩

theorem PFr.refl (ord mk nw : Word) (m : Mem) : PFr ord mk nw m m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl⟩

theorem PFr.of_high {ord mk nw : Word} {m m' : Mem} (h : HighFr m m') : PFr ord mk nw m m' :=
  ⟨fun b hb _ => h.1 b hb, h.2.1, h.2.2.1, h.2.2.2, fun x _ => by rw [h.1 IW (by decide)]⟩

theorem PFr.of_frame {ord mk nw : Word} {m m' : Mem} (h : MemFrame [IW] [] m m')
    (hIW : ∀ x : Nat, (x < ord.toNat ∨ mk.toNat + nw.toNat ≤ x) → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?) :
    PFr ord mk nw m m' :=
  ⟨fun b hl hb => h.1 b (by simpa using hb) (by rintro rfl; exact hl (by decide)),
    fun x _ => h.2.1 x (by simp), h.2.2.1, h.2.2.2, hIW⟩

theorem PEnv.frame {m m' : Mem} {a a' : AState} {dsAll : Array IDeclaration} {np nw ord mk : Word}
    (hE : PEnv m a dsAll np nw ord mk) (hf : PFr ord mk nw m m') (hA : ArenaR m' a') :
    PEnv m' a' dsAll np nw ord mk := by
  have hctl : ∀ x : Word, 64 ≤ x.toNat → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := hf.2.1
  have htop : iwTop m' = iwTop m := by simp only [iwTop, hctl 200 (by decide)]
  refine ⟨fun x hx => ?_, hE.size, hE.n59, hE.np, hE.rg1, htop ▸ hE.rg2, ?_, hA⟩
  · rw [hf.1 DECL (by decide) (by decide), hf.1 DLP (by decide) (by decide)]; exact hE.recs x hx
  · obtain ⟨i1, i2, i3, i4, i5⟩ := hE.iwok
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [htop, hf.2.2.1]; exact i1
    · simp only [erTop, hctl 129 (by decide), hf.2.2.1]; exact i2
    · rw [hf.2.2.1]; exact i3
    · rw [hf.2.2.1]; exact i4
    · rw [hf.2.2.1]; exact i5

theorem getIW_set64 (m : Mem) (w v : Word) (x : Nat) :
    ((m.set64 IW w v).arr64 IW)[x]? =
      if w.toNat = x then (if x < (m.arr64 IW).size then some v else none) else (m.arr64 IW)[x]? := by
  rw [Mem.arr64_set64_same]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split <;> simp_all

theorem rdIW_set64 (m : Mem) (w v y : Word) :
    rdW ((m.set64 IW w v).arr64 IW) y =
      if w.toNat = y.toNat ∧ w.toNat < (m.arr64 IW).size then v else rdW (m.arr64 IW) y := by
  rw [rdW_set64]
  by_cases e : w = y
  · subst e; simp
  · have : w.toNat ≠ y.toNat := fun h => e (UInt64.toNat_inj.mp h)
    simp [e, this]

/-- **`prep_front` is `frontOf`** from the prelude record `aw` on (`acc` the front so far, the
twin's stream the unmarked records). -/
theorem pFront_ok (dsAll : Array IDeclaration) (np nw ord mk : Word) :
    ∀ (fuel : Nat) (m m' : Mem) (a : AState) (aw r : Word) (acc : Array IDeclaration),
    PEnv m a dsAll np nw ord mk → aw.toNat ≤ np.toNat → acc.size = aw.toNat →
    (∀ k (_hk : k < aw.toNat), (rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
      acc[k]! = dsAll[(rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat]!) →
    pFrontW fuel m np nw ord mk aw = some (r, m') →
    ∃ (front rest : Array IDeclaration) (a' : AState),
      (frontOf acc ((dsAll.toList.take np.toNat).drop aw.toNat)
        (recsAt dsAll (unm m mk np.toNat nw.toNat))).run a = .ok ((front, rest), a') ∧
      front.size = np.toNat ∧
      (∀ k (_hk : k < np.toNat), (rdW (m'.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
        front[k]! = dsAll[(rdW (m'.arr64 IW) (ord + UInt64.ofNat k)).toNat]!) ∧
      rest = recsAt dsAll (unm m' mk np.toNat nw.toNat) ∧
            PEnv m' a' dsAll np nw ord mk ∧ a'.pins = a.pins ∧ a'.store.pers = a.store.pers ∧
              a'.store.scr = a.store.scr ∧ PFr ord mk nw m m' := by
  intro fuel
  induction fuel with
  | zero => intro m m' a aw r acc _ _ _ _ h; simp [pFrontW.eq_1] at h
  | succ fuel ih =>
    intro m m' a aw r acc hE haw hacc hIW h
    have hsz := hE.size
    have hn59 := hE.n59
    have hnp := hE.np
    have hrg1 := hE.rg1
    have hrg2 := hE.rg2
    have hiw1 : iwTop m ≤ (m.arr64 IW).size := hE.iwok.1
    have hiw3 : (m.arr64 IW).size < 2 ^ 64 := hE.iwok.2.2.1
    by_cases hstop : np ≤ aw
    · rw [pFrontW.arm1 _ _ _ _ _ _ _ hstop] at h
      cases h
      have he : aw.toNat = np.toNat := by have := UInt64.le_iff_toNat_le.mp hstop; omega
      have hnil : (dsAll.toList.take np.toNat).drop aw.toNat = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      refine ⟨acc, recsAt dsAll (unm m mk np.toNat nw.toNat), a, ?_, by omega,
        fun k _hk => hIW k (by omega), rfl, hE, rfl, rfl, rfl, PFr.refl _ _ _ _⟩
      rw [hnil, frontOf.eq_1]; rfl
    · have hlt : aw.toNat < np.toNat := by have := mt UInt64.le_iff_toNat_le.mpr hstop; omega
      have ha1 : (aw + 1).toNat = aw.toNat + 1 := toNat_succ aw (by omega)
      have hawn : aw.toNat < dsAll.size := by omega
      have hoa : (ord + aw).toNat = ord.toNat + aw.toNat := by rw [UInt64.toNat_add]; omega
      rw [pFrontW.arm2 _ _ _ _ _ _ _ hstop] at h
      cases hK : pKeyW m aw with
      | none => rw [hK, pFrontW.k_decl_key.eq_1] at h; cases h
      | some kv =>
      obtain ⟨key, m1⟩ := kv
      rw [hK, pFrontW.k_decl_key.arm1] at h
      obtain ⟨a1, hrun1, hkey, hA1, hHF, hpins1, hpe1, hse1⟩ :=
        pKey_ok m m1 a aw key dsAll[aw.toNat] (hE.recs _ hawn).1 (hE.recs _ hawn).2 (by omega)
          hE.arena hK
      have hIW1 : m1.arr64 IW = m.arr64 IW := hHF.1 IW (by decide)
      have hE1 : PEnv m1 a1 dsAll np nw ord mk := hE.frame (PFr.of_high hHF) hA1
      cases hF : pFindW fuel m1 mk nw key np with
      | none => rw [hF, pFrontW.k_prep_find.eq_1] at h; cases h
      | some f =>
      rw [hF] at h
      obtain ⟨hf0, hf1⟩ := pFind_ok fuel m1 dsAll mk nw key np f hE1.recs hsz hn59 (by omega) hkey hF
      rw [hIW1] at hf0 hf1
      have hcase : ∃ (m2 : Mem) (v : Word) (o : Option IDeclaration), v.toNat < nw.toNat ∧
          o.getD dsAll[aw.toNat]! = dsAll[v.toNat]! ∧
          pick (decI key) (recsAt dsAll (unm m mk np.toNat nw.toNat)) =
            (o, recsAt dsAll (unm m2 mk np.toNat nw.toNat)) ∧
          MemFrame [IW] [] m1 m2 ∧
          (∀ x : Nat, (x < ord.toNat ∨ mk.toNat + nw.toNat ≤ x) →
            (m2.arr64 IW)[x]? = (m1.arr64 IW)[x]?) ∧
          rdW (m2.arr64 IW) (ord + aw) = v ∧
          (∀ k, k < aw.toNat → rdW (m2.arr64 IW) (ord + UInt64.ofNat k) =
            rdW (m.arr64 IW) (ord + UInt64.ofNat k)) ∧
          pFrontW fuel m2 np nw ord mk (aw + 1) = some (r, m') := by
        by_cases hfz : f ≠ 0
        · rw [pFrontW.k_prep_find.arm1 _ _ _ _ _ _ _ _ hfz, pFrontW.j1.arm1] at h
          obtain ⟨hx, hnpx, hmx, hdx, hbx⟩ := hf1 hfz
          have hf1' : 1 ≤ f := by
            have : f.toNat ≠ 0 := fun e => hfz (UInt64.toNat_inj.mp (by simpa using e))
            exact UInt64.le_iff_toNat_le.mpr (by simp; omega)
          have hv : (f - 1).toNat = f.toNat - 1 := by rw [UInt64.toNat_sub_of_le _ _ hf1']; simp
          have hmkf : mk + f - 1 = mk + UInt64.ofNat (f.toNat - 1) := by
            rw [← hv, UInt64.ofNat_toNat]; grind
          have hmx' : (mk + UInt64.ofNat (f.toNat - 1)).toNat = mk.toNat + (f.toNat - 1) :=
            addW_toNat _ _ (by omega)
          rw [hmkf] at h
          refine ⟨_, f - 1, some dsAll[f.toNat - 1]!, by omega, by simp [hv], ?_, ?_, ?_, ?_, ?_, h⟩
          · rw [pick_hit _ _ _ (f.toNat - 1) (unm_sorted _ _ _ _) (mem_unm.mpr ⟨hnpx, by omega, hmx⟩)
              (by rw [getElem!_pos dsAll _ hx]; exact hdx)
              (fun y hy hyx => by
                obtain ⟨h1, h2, h3⟩ := mem_unm.mp hy
                rw [getElem!_pos dsAll _ (by omega)]; exact hbx y (by omega) h1 hyx h3)]
            congr 2
            symm
            apply unm_mark
            · intro y hy1 hy2 hyx
              have hy' := addW_toNat mk y (by omega)
              rw [rdIW_set64, rdIW_set64, hIW1, ite_f (by rw [hoa, hy']; omega),
                ite_f (by rw [hmx', hy']; omega)]
            · rw [rdIW_set64, rdIW_set64, ite_f (by rw [hoa, hmx']; omega),
                ite_t ⟨rfl, by rw [hmx', hIW1]; omega⟩]
              decide
          · exact (MemFrame.set64 _ IW (by decide) _ _).trans (MemFrame.set64 _ IW (by decide) _ _)
          · intro x hx'
            rw [getIW_set64, getIW_set64, ite_f (by rw [hoa]; omega), ite_f (by rw [hmx']; omega)]
          · rw [rdIW_set64, ite_t ⟨rfl, by rw [size_set64, hoa, hIW1]; omega⟩]
          · intro k _hk
            have hk' := addW_toNat ord k (by omega)
            rw [rdIW_set64, rdIW_set64, hIW1, ite_f (by rw [hoa, hk']; omega),
              ite_f (by rw [hmx', hk']; omega)]
        · rw [pFrontW.k_prep_find.arm2 _ _ _ _ _ _ _ _ (Decidable.of_not_not hfz), pFrontW.j1.arm1] at h
          have hf00 : f = 0 := by simpa using hfz
          refine ⟨_, aw, none, by omega, rfl, ?_, MemFrame.set64 _ IW (by decide) _ _, ?_, ?_, ?_, h⟩
          · have hU : unm (m1.set64 IW (ord + aw) aw) mk np.toNat nw.toNat = unm m mk np.toNat nw.toNat := by
              apply unm_congr
              intro y hy1 hy2
              have hy' := addW_toNat mk y (by omega)
              rw [rdIW_set64, hIW1, ite_f (by rw [hoa, hy']; omega)]
            rw [hU, pick_miss]
            intro y hy
            obtain ⟨h1, h2, h3⟩ := mem_unm.mp hy
            rw [getElem!_pos dsAll _ (by omega)]
            exact hf0 hf00 y (by omega) h1 h3
          · intro x hx'
            rw [getIW_set64, ite_f (by rw [hoa]; omega)]
          · rw [rdIW_set64, ite_t ⟨rfl, by rw [hoa, hIW1]; omega⟩]
          · intro k _hk
            have hk' := addW_toNat ord k (by omega)
            rw [rdIW_set64, hIW1, ite_f (by rw [hoa, hk']; omega)]
      obtain ⟨m2, v, o, hv, hX, hpick, hMF, hreg, hrd, hkeep, h2⟩ := hcase
      have hfr2 : PFr ord mk nw m1 m2 := PFr.of_frame hMF hreg
      have hE2 : PEnv m2 a1 dsAll np nw ord mk :=
        hE1.frame hfr2 (ArenaR.frame_ext [IW] [] (by decide) (by simp) m1 m2 hMF a1 hA1)
      have hIW2 : ∀ k (_hk : k < (aw + 1).toNat), (rdW (m2.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
          (acc.push dsAll[v.toNat]!)[k]! = dsAll[(rdW (m2.arr64 IW) (ord + UInt64.ofNat k)).toNat]! := by
        intro k _hk
        rw [ha1] at _hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp _hk with _hk | rfl
        · rw [hkeep k _hk]
          obtain ⟨h1, h2⟩ := hIW k _hk
          refine ⟨h1, ?_⟩
          rw [getElem!_pos (acc.push _) k (by simp; omega), Array.getElem_push_lt (by omega),
            ← getElem!_pos acc k (by omega)]
          exact h2
        · rw [UInt64.ofNat_toNat, hrd]
          refine ⟨hv, ?_⟩
          rw [getElem!_pos (acc.push _) _ (by simp; omega)]
          simp [Array.getElem_push, hacc]
      obtain ⟨front, rest, a', hrun, hfs, hfk, hrest, hE', hpins', hpe', hse', hfr'⟩ :=
        ih m2 m' a1 (aw + 1) r (acc.push dsAll[v.toNat]!) hE2 (by omega) (by simp [hacc, ha1]) hIW2 h2
      refine ⟨front, rest, a', ?_, hfs, hfk, hrest, hE', hpins'.trans hpins1, hpe'.trans hpe1, hse'.trans hse1,
          (PFr.of_high hHF).trans (hfr2.trans hfr')⟩
      rw [List.drop_eq_getElem_cons (by simp; omega), frontOf.eq_2, HoistTwin.run_bind]
      simp only [List.getElem_take, Array.getElem_toList, hrun1, hpick]
      rw [← getElem!_pos dsAll _ hawn, hX, ← ha1]
      exact hrun

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
      · rw [pRestW.arm2 _ _ _ _ _ _ _ hj hz, pRestW.j1.arm1] at h
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
      · rw [pRestW.arm3 _ _ _ _ _ _ _ hj hz, pRestW.j1.arm1] at h
        obtain ⟨hr, hk, hfr, hout⟩ := ih m m' c (j + 1) r h1 h2 h3 (by omega) (by omega) h
        rw [hj1] at hr hk
        rw [unm_succ _ _ _ _ hjlt]; simp only [← hmkj, hz, ↓reduceIte]
        exact ⟨hr, hk, hfr, hout⟩
end L.Checker
