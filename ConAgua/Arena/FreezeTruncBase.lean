import ConAgua.Arena.FreezeRel

/-!
# The truncation theorem, part 1: what `truncFrozen` does to each array (lane parmode)

`truncFrozen m` (`FreezeRel.lean`) cuts every frozen array to its extent and leaves every other
array, the number of arrays and `CTL` alone:

* `truncFrozen_other`: an array that is not frozen (`fzSrcs`) is unchanged (so is `CTL`);
* `truncFrozen_mem`: a frozen array is its prefix of length `fzExt m z`;
* `truncFrozen_words`: the number of arrays is unchanged;

and reading a prefix below its length reads the array (`rdW_extract`, `get?_extract`).
-/

namespace L.Arena

open ConRon.Arena

/-! ## Prefixes -/

theorem get?_extract (a : Array Word) {e i : Nat} (h : i < e) : (a.extract 0 e)[i]? = a[i]? := by
  simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
  split
  · rfl
  · rename_i hn
    have : a.size ≤ i := by omega
    simp [Array.getElem?_eq_none this]

theorem rdW_extract (a : Array Word) {e : Nat} {x : Word} (h : x.toNat < e) :
    rdW (a.extract 0 e) x = rdW a x := by
  simp only [rdW, get?_extract a h]

theorem size_extract0 (a : Array Word) (e : Nat) : (a.extract 0 e).size = min e a.size := by
  simp [Array.size_extract]

theorem getD_extract (a : Array Word) {e i : Nat} (h : i < e) :
    (a.extract 0 e)[i]?.getD 0 = a[i]?.getD 0 := by rw [get?_extract a h]

/-! ## Replacing one array -/

/-- `m` with array `b` replaced by `v` (no change if `b` is not an array of `m`). -/
def _root_.L.Mem.setA (m : Mem) (b : ArrId) (v : Array Word) : Mem := { m with words := m.words.set! b v }

theorem Mem.setA_arr (m : Mem) (b c : ArrId) (v : Array Word) :
    (m.setA b v).arr64 c = if c = b ∧ b < m.words.size then v else m.arr64 c := by
  simp only [Mem.setA, Mem.arr64, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases h1 : c = b
  · subst h1
    by_cases h2 : c < m.words.size
    · simp [h2]
    · simp [h2]
  · simp [Ne.symm h1, h1]

theorem Mem.setA_words (m : Mem) (b : ArrId) (v : Array Word) :
    (m.setA b v).words.size = m.words.size := by
  simp [Mem.setA]

theorem Mem.arr64_oob (m : Mem) (b : ArrId) (h : ¬ b < m.words.size) : m.arr64 b = #[] := by
  simp [Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- **Replace an array by the one another memory of the same shape holds**: then it is that
memory's (out of range both are empty). -/
theorem Mem.setA_self (m m' : Mem) (b : ArrId) (hw : m'.words.size = m.words.size) :
    (m.setA b (m'.arr64 b)).arr64 b = m'.arr64 b := by
  rw [Mem.setA_arr]
  by_cases h : b < m.words.size
  · simp [h]
  · simp only [h, and_false, ↓reduceIte]
    rw [Mem.arr64_oob m b h, Mem.arr64_oob m' b (hw ▸ h)]

/-! ## `truncList` -/

theorem truncList_words (m₀ : Mem) :
    ∀ (zs : List (ArrId × Fz)) (m : Mem), (truncList m₀ m zs).words.size = m.words.size
  | [], _ => rfl
  | (_, z) :: zs, m => by
    rw [truncList, truncList_words m₀ zs]; simp

theorem truncList_other (m₀ : Mem) (b : ArrId) :
    ∀ (zs : List (ArrId × Fz)) (m : Mem), (∀ e ∈ zs, e.2.src ≠ b) →
      (truncList m₀ m zs).arr64 b = m.arr64 b
  | [], _, _ => rfl
  | (x, z) :: zs, m, h => by
    rw [truncList, truncList_other m₀ b zs _ (fun e he => h e (List.mem_cons_of_mem _ he))]
    have := Mem.setA_arr m z.src b ((m₀.arr64 z.src).extract 0 (fzExt m₀ z))
    simp only [Mem.setA] at this
    rw [this, ite_eq_right (fun hc => h (x, z) (List.mem_cons_self ..) hc.1.symm)]

theorem truncList_mem (m₀ : Mem) (x : ArrId) (z : Fz) :
    ∀ (zs : List (ArrId × Fz)) (m : Mem), (x, z) ∈ zs →
      zs.Pairwise (fun e e' => e.2.src ≠ e'.2.src) → m.words.size = m₀.words.size →
      (∀ b, ¬ b < m.words.size → m.arr64 b = m₀.arr64 b) →
      (truncList m₀ m zs).arr64 z.src = (m₀.arr64 z.src).extract 0 (fzExt m₀ z)
  | [], _, h, _, _, _ => by cases h
  | (x', z') :: zs, m, h, hp, hw, ho => by
    rw [List.pairwise_cons] at hp
    rw [truncList]
    rcases List.mem_cons.mp h with e | e
    · cases e
      rw [truncList_other m₀ z.src zs _ (fun e he => (hp.1 e he).symm)]
      have := Mem.setA_arr m z.src z.src ((m₀.arr64 z.src).extract 0 (fzExt m₀ z))
      simp only [Mem.setA] at this
      rw [this]
      by_cases hz : z.src < m.words.size
      · simp [hz]
      · simp only [hz, and_false, ↓reduceIte]
        rw [ho _ hz, Mem.arr64_oob m₀ _ (hw ▸ hz)]; simp
    · refine truncList_mem m₀ x z zs _ e hp.2 (by simp [hw]) (fun b hb => ?_)
      have := Mem.setA_arr m z'.src b ((m₀.arr64 z'.src).extract 0 (fzExt m₀ z'))
      simp only [Mem.setA] at this hb
      have hb' : ¬ b < m.words.size := by simpa using hb
      rw [this, ite_eq_right (fun (hc : b = z'.src ∧ z'.src < m.words.size) => hb' (hc.1 ▸ hc.2))]
      exact ho b hb'

/-! ## `truncFrozen` -/

/-- The frozen arrays (sources), as a literal. -/
def fzSrcs : List ArrId :=
  [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 55, 56,
   57, 58, 59, 60, 61, 128, 132, 133, 134, 129, 130, 131, 136, 137]

theorem frozen_srcs : (frozen.drop 1).map (·.2.src) = fzSrcs := by decide

theorem fzSrcs_nodup : fzSrcs.Nodup := by decide

theorem frozen_pairwise : (frozen.drop 1).Pairwise (fun e e' => e.2.src ≠ e'.2.src) := by
  have := fzSrcs_nodup
  rw [← frozen_srcs, List.Nodup, List.pairwise_map] at this
  exact this

theorem truncFrozen_words (m : Mem) : (truncFrozen m).words.size = m.words.size :=
  truncList_words m _ m

/-- **An array that is not frozen is unchanged.** -/
theorem truncFrozen_other (m : Mem) (b : ArrId) (hb : b ∉ fzSrcs) :
    (truncFrozen m).arr64 b = m.arr64 b :=
  truncList_other m b _ m (fun e he hs => hb (by
    rw [← frozen_srcs, List.mem_map]; exact ⟨e, he, hs⟩))

theorem truncFrozen_ctl (m : Mem) : (truncFrozen m).arr64 CTL = m.arr64 CTL :=
  truncFrozen_other m CTL (by decide)

/-- **A frozen array is its prefix up to its extent.** -/
theorem truncFrozen_mem (m : Mem) {x : ArrId} {z : Fz} (h : (x, z) ∈ frozen.drop 1) :
    (truncFrozen m).arr64 z.src = (m.arr64 z.src).extract 0 (fzExt m z) :=
  truncList_mem m x z _ m h frozen_pairwise rfl (fun _ _ => rfl)

theorem frozen_drop1 : frozen.drop 1 =
    [(POOL, ⟨POOL, fzCtl 0⟩)] ++
    fzStores.flatMap (fun (ra, sa, w, ca) =>
      [(ra, ⟨ra, .bin .mul (fzCtl ca) (fzC w)⟩), (sa, ⟨sa, fzSlotExt sa⟩)]) ++
    fzCols.map (fun (c, ca) => (c, ⟨c, fzCtl ca⟩)) ++
    [(PINS, ⟨PINS, fzC 71⟩),
     (EIXA, ⟨EIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩),
     (EIXS, ⟨EIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩),
     (EIXN, ⟨EIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩),
     (TIXA, ⟨TIXA, fzCtl nanonCS.ca.toNat⟩),
     (TIXS, ⟨TIXS, fzCtl nstrCS.ca.toNat⟩),
     (TIXN, ⟨TIXN, fzCtl nnumCS.ca.toNat⟩),
     (EREC, ⟨EREC, fzCtl 129⟩),
     (PEND, ⟨PEND, .bin .mul (fzC 3) (fzCtl 130)⟩)] := by
  simp only [frozen, List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append,
    List.append_assoc]

/-! ### The extents -/

theorem fzExt_ctl (m : Mem) (b : ArrId) (k : Nat) :
    fzExt m ⟨b, fzCtl k⟩ = (rdW (m.arr64 CTL) (UInt64.ofNat k)).toNat := by
  simp only [fzExt, fzCtl, Expr.pval, rd64, rdW, Array.getD_eq_getD_getElem?]

theorem fzExt_mulC (m : Mem) (b : ArrId) (k w : Nat) :
    fzExt m ⟨b, .bin .mul (fzCtl k) (fzC w)⟩ =
      (rdW (m.arr64 CTL) (UInt64.ofNat k) * UInt64.ofNat w).toNat := by
  simp only [fzExt, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]

theorem fzExt_Cmul (m : Mem) (b : ArrId) (k w : Nat) :
    fzExt m ⟨b, .bin .mul (fzC w) (fzCtl k)⟩ =
      (UInt64.ofNat w * rdW (m.arr64 CTL) (UInt64.ofNat k)).toNat := by
  simp only [fzExt, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]

theorem fzExt_slot (m : Mem) (sa : ArrId) :
    fzExt m ⟨sa, fzSlotExt sa⟩ = (2 + 2 * (rdW (m.arr64 sa) 0 + SN0)).toNat := by
  simp only [fzExt, fzSlotExt, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]
  rfl

/-! ### Each frozen array -/

theorem truncFrozen_pool (m : Mem) :
    (truncFrozen m).arr64 POOL = (m.arr64 POOL).extract 0 m.top.toNat := by
  have := truncFrozen_mem m (x := POOL) (z := ⟨POOL, fzCtl 0⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]; rfl

theorem truncFrozen_ra (m : Mem) {ra sa : ArrId} {w ca : Nat} (h : (ra, sa, w, ca) ∈ fzStores) :
    (truncFrozen m).arr64 ra = (m.arr64 ra).extract 0
      (rdW (m.arr64 CTL) (UInt64.ofNat ca) * UInt64.ofNat w).toNat := by
  have := truncFrozen_mem m (x := ra) (z := ⟨ra, .bin .mul (fzCtl ca) (fzC w)⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inr ⟨_, h, by simp⟩)))
  rw [this, fzExt_mulC]

theorem truncFrozen_sa (m : Mem) {ra sa : ArrId} {w ca : Nat} (h : (ra, sa, w, ca) ∈ fzStores) :
    (truncFrozen m).arr64 sa = (m.arr64 sa).extract 0 (2 + 2 * (rdW (m.arr64 sa) 0 + SN0)).toNat := by
  have := truncFrozen_mem m (x := sa) (z := ⟨sa, fzSlotExt sa⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inr ⟨_, h, by simp⟩)))
  rw [this, fzExt_slot]

theorem truncFrozen_col (m : Mem) {c : ArrId} {ca : Nat} (h : (c, ca) ∈ fzCols) :
    (truncFrozen m).arr64 c = (m.arr64 c).extract 0 (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat := by
  have := truncFrozen_mem m (x := c) (z := ⟨c, fzCtl ca⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inr ⟨_, h, rfl⟩))
  rw [this, fzExt_ctl]

theorem truncFrozen_pins (m : Mem) : (truncFrozen m).arr64 PINS = (m.arr64 PINS).extract 0 71 := by
  have := truncFrozen_mem m (x := PINS) (z := ⟨PINS, fzC 71⟩) (by rw [frozen_drop1]; simp)
  rw [this]; rfl

theorem truncFrozen_eixa (m : Mem) : (truncFrozen m).arr64 EIXA =
    (m.arr64 EIXA).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nanonCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := EIXA)
    (z := ⟨EIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_eixs (m : Mem) : (truncFrozen m).arr64 EIXS =
    (m.arr64 EIXS).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nstrCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := EIXS)
    (z := ⟨EIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_eixn (m : Mem) : (truncFrozen m).arr64 EIXN =
    (m.arr64 EIXN).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nnumCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := EIXN)
    (z := ⟨EIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_tixa (m : Mem) : (truncFrozen m).arr64 TIXA =
    (m.arr64 TIXA).extract 0 (rdW (m.arr64 CTL) (UInt64.ofNat nanonCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := TIXA) (z := ⟨TIXA, fzCtl nanonCS.ca.toNat⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]

theorem truncFrozen_tixs (m : Mem) : (truncFrozen m).arr64 TIXS =
    (m.arr64 TIXS).extract 0 (rdW (m.arr64 CTL) (UInt64.ofNat nstrCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := TIXS) (z := ⟨TIXS, fzCtl nstrCS.ca.toNat⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]

theorem truncFrozen_tixn (m : Mem) : (truncFrozen m).arr64 TIXN =
    (m.arr64 TIXN).extract 0 (rdW (m.arr64 CTL) (UInt64.ofNat nnumCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := TIXN) (z := ⟨TIXN, fzCtl nnumCS.ca.toNat⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]

theorem truncFrozen_erec (m : Mem) : (truncFrozen m).arr64 EREC = (m.arr64 EREC).extract 0 (erecTop m) := by
  have := truncFrozen_mem m (x := EREC) (z := ⟨EREC, fzCtl 129⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]; rfl

theorem truncFrozen_pend (m : Mem) :
    (truncFrozen m).arr64 PEND = (m.arr64 PEND).extract 0 (3 * rdW (m.arr64 CTL) 130).toNat := by
  have := truncFrozen_mem m (x := PEND) (z := ⟨PEND, .bin .mul (fzC 3) (fzCtl 130)⟩)
    (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

end L.Arena
