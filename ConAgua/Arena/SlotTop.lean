module

public import ConAgua.Arena.SlotRehash

@[expose] public section

/-!
# The growth's top-down sweep keeps every node findable (lane growtop)

`SlotGrowSpec.lean`'s `ktopW` (the model of `ConsLib.lean`'s `ktopL`) sweeps the old half of a
doubled table (`N` slots from word `ob` of array `sa`, the old half the first `n`, the upper half
zeroed) from the top, `H = n - 1 ‥ 0`. A live entry at slot `H` whose new home `j` lies above `H`
is probed upward from `j` past the live unmarked slots without wrapping (`kupW`); at a free slot
it moves there. At `j = H` it stays. Otherwise it gets the mark, and its slot joins one of two
ranges. This file proves the sweep's invariant `TopInv` at the cursor `H`:

* the slots below `H` are as before the sweep;
* the slots from `H` on are free, live unmarked, or marked within the ranges (`SlotOK` with the
  ranges as the re-insertion's mark ranges);
* every node is still in its old slot below `H`, marked somewhere, or found from its new home
  through live unmarked slots without wrapping, on a path from `H` on (`FoundT`).

The sweep writes only at `H` and at free slots above it, and paths consist of live slots from `H`
on, so no path breaks. At `H = 0` the invariant is the re-insertion's `ReinsInv` at the first
range's start, with the second range as the later loop's (`topInv_reins`).
-/

open ConRon.Arena

namespace L.Arena

/-- A walk that does not wrap is the plain sum. -/
theorem walkW_toNat (N h : Word) : ∀ e : Nat, h.toNat + e < N.toNat →
    (walkW N h e).toNat = h.toNat + e
  | 0, _ => rfl
  | e + 1, he => by
    have ih := walkW_toNat N h e (by omega)
    rw [walkW_succ]
    have e1 : (walkW N h e + 1).toNat = h.toNat + e + 1 := by
      rw [UInt64.toNat_add, ih]; have := N.toNat_lt; simp; omega
    have hlt : walkW N h e + 1 < N := UInt64.lt_iff_toNat_lt.mpr (by rw [e1]; omega)
    simp only [hlt, ↓reduceIte, UInt64.mul_one, e1]; omega

/-- **The sweep's probe**: from slot `j < N`, its result is `j + D` (no wrap), after `D` live
unmarked slots, and stops there (not live unmarked, or the top slot). -/
theorem kupW_res (sl : Array Word) (ob N bt : Word) : ∀ j : Word, j < N →
    ∃ D : Nat, j.toNat + D < N.toNat ∧ kupW sl ob N bt j = walkW N j D ∧
      (∀ e < D, bt < vwd sl (ob + walkW N j e) ∧ vwd sl (ob + walkW N j e) < MARK) ∧
      ¬ (bt < vwd sl (ob + kupW sl ob N bt j) ∧ vwd sl (ob + kupW sl ob N bt j) < MARK ∧
        kupW sl ob N bt j + 1 < N) := by
  intro j hj
  induction j using kupW.induct sl ob N bt with
  | case1 j hc ih =>
    obtain ⟨hjN, hl1, hl2, hj1⟩ := hc
    obtain ⟨D, hD, hk, hp, hs⟩ := ih hj1
    have e1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; have := N.toNat_lt; have := UInt64.lt_iff_toNat_lt.mp hjN; simp; omega
    have hw : ∀ e, e ≤ D → walkW N (j + 1) e = walkW N j (e + 1) := fun e he =>
      UInt64.toNat_inj.mp (by rw [walkW_toNat _ _ _ (by omega), walkW_toNat _ _ _ (by omega), e1]; omega)
    rw [kupW]
    simp only [show j < N ∧ bt < vwd sl (ob + j) ∧ vwd sl (ob + j) < MARK ∧ j + 1 < N from
      ⟨hjN, hl1, hl2, hj1⟩, and_self, ↓reduceIte]
    refine ⟨D + 1, by omega, by rw [hk, hw D (Nat.le_refl _)], fun e he => ?_, hs⟩
    rcases e with _ | e
    · exact ⟨hl1, hl2⟩
    · rw [← hw e (by omega)]; exact hp e (by omega)
  | case2 j hc =>
    rw [kupW]
    simp only [hc, ↓reduceIte]
    refine ⟨0, by have := UInt64.lt_iff_toNat_lt.mp hj; omega, rfl, fun e he => absurd he (by omega), ?_⟩
    exact fun h => hc ⟨hj, h⟩

section top
variable (sa : TieredArray) (ob N n bt c : Word) (KPm : Word → Word → Prop) (hsm : Word → Word)

/-- The second mark range, `[b0, b1)`. -/
def InB (k : MkR) (j : Word) : Prop := k.b0 ≤ j ∧ j < k.b1

/-- Node `x` is found from its new home, at or above `H`, through live unmarked slots and
without wrapping. -/
def FoundT (H : Word) (mi : Mem) (x : Word) : Prop :=
  H ≤ homeW (hsm x) N ∧ ∃ d : Nat, (homeW (hsm x) N).toNat + d < N.toNat ∧
    VW sa ob mi (walkW N (homeW (hsm x) N) d) = bt + x + 1 ∧
    ∀ e < d, LiveU bt (VW sa ob mi (walkW N (homeW (hsm x) N) e))

/-- **The sweep's invariant** at the cursor `H` (the slots from `H` on handled), from the memory
`m0` before the sweep, with the mark ranges `k`. -/
structure TopInv (m0 mi : Mem) (H : Word) (k : MkR) : Prop where
  fr : GFr sa m0 mi
  w0 : rdW (mi.arr64 sa) 0 = rdW (m0.arr64 sa) 0
  w1 : rdW (mi.arr64 sa) 1 = rdW (m0.arr64 sa) 1
  /-- The slots below `H` are untouched. -/
  lo : ∀ j, j < H → VW sa ob mi j = VW sa ob m0 j ∧ KW sa ob mi j = KW sa ob m0 j
  /-- The slots from `H` on, as the re-insertion's invariant wants them. -/
  hi : ∀ j, H ≤ j → j < N → SlotOK sa ob k.a1 bt c KPm (InB k) mi k.a0 j
  /-- Every node is in its old slot below `H`, marked, or found above. -/
  node : ∀ x : Word, x.toNat < c.toNat → (∃ j, j < H ∧ VW sa ob mi j = bt + x + 1) ∨
    (∃ j, j < N ∧ VW sa ob mi j = bt + x + 1 + MARK) ∨ FoundT sa ob N bt hsm H mi x
  hn : H ≤ n
  a1 : k.a1 = 0 ∨ H < k.a1
  a1n : k.a1 ≤ n
  b1 : k.b1 = 0 ∨ H < k.b1
  b1n : k.b1 ≤ n

variable (m0 : Mem)
  (hob : 2 ≤ ob.toNat) (hNL : ob.toNat + N.toNat ≤ (m0.arr64 sa).size)
  (hL : (m0.arr64 sa).size < 2 ^ 61)
  (hbt : bt.toNat + c.toNat + 1 < 2 ^ 47) (hnN : n ≤ N) (hN0 : 0 < N)
  (hOld : ∀ j, j < n → VW sa ob m0 j ≤ bt ∨ (LiveU bt (VW sa ob m0 j) ∧
    (VW sa ob m0 j).toNat ≤ bt.toNat + c.toNat ∧ KPm (VW sa ob m0 j - bt - 1) (KW sa ob m0 j)))

omit hob hNL hL hnN hN0 hOld in
include hbt in
theorem node_toNat (x : Word) (hx : x.toNat < c.toNat) : (bt + x + 1).toNat = bt.toNat + x.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega

omit hob hNL hL hnN hN0 hOld in
include hbt in
theorem node_liveU (x : Word) (hx : x.toNat < c.toNat) : LiveU bt (bt + x + 1) := by
  have := node_toNat bt c hbt x hx
  exact ⟨UInt64.lt_iff_toNat_lt.mpr (by omega),
    UInt64.lt_iff_toNat_lt.mpr (by rw [MARK_toNat]; omega)⟩

omit hob hNL hL hnN hN0 hOld in
include hbt in
theorem node_inj (x y : Word) (hx : x.toNat < c.toNat) (hy : y.toNat < c.toNat)
    (h : bt + x + 1 = bt + y + 1) : x = y := by
  have := congrArg UInt64.toNat h
  rw [node_toNat bt c hbt x hx, node_toNat bt c hbt y hy] at this
  exact UInt64.toNat_inj.mp (by omega)

omit hob hNL hL hnN hN0 hOld in
include hbt in
/-- The node of a live unmarked value word `v ≤ bt + c`. -/
theorem node_of_live (v : Word) (hv : bt < v) (hc : v.toNat ≤ bt.toNat + c.toNat) :
    (v - bt - 1).toNat < c.toNat ∧ bt + (v - bt - 1) + 1 = v := by
  have h1 := UInt64.lt_iff_toNat_lt.mp hv
  have e : (v - bt - 1).toNat = v.toNat - bt.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv)]
    · simp
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv)]; simp; omega
  refine ⟨by omega, UInt64.toNat_inj.mp ?_⟩
  rw [node_toNat bt c hbt _ (by omega), e]; omega

omit hob hNL hL hbt hnN hN0 hOld in
/-- A found path stays when the live slots from `H` on keep their value words. -/
theorem foundT_keep (H : Word) (mi mf : Mem) (x : Word) (hx : x.toNat < c.toNat)
    (hk : ∀ j, j < N → H ≤ j → LiveU bt (VW sa ob mi j) → VW sa ob mf j = VW sa ob mi j)
    (hbt : bt.toNat + c.toNat + 1 < 2 ^ 47)
    (h : FoundT sa ob N bt hsm H mi x) : FoundT sa ob N bt hsm H mf x := by
  obtain ⟨hH, d, hd, h1, h2⟩ := h
  have hw : ∀ e, e ≤ d → walkW N (homeW (hsm x) N) e < N ∧ H ≤ walkW N (homeW (hsm x) N) e :=
    fun e he => by
      have := walkW_toNat N (homeW (hsm x) N) e (by omega)
      have := UInt64.le_iff_toNat_le.mp hH
      exact ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), UInt64.le_iff_toNat_le.mpr (by omega)⟩
  refine ⟨hH, d, hd, ?_, fun e he => ?_⟩
  · rw [hk _ (hw d (Nat.le_refl _)).1 (hw d (Nat.le_refl _)).2 (h1 ▸ node_liveU bt c hbt x hx), h1]
  · rw [hk _ (hw e (by omega)).1 (hw e (by omega)).2 (h2 e he)]; exact h2 e he

omit hob hNL hL hbt hnN hN0 hOld in
/-- A found path from `H` on is one from any `i ≤ H` on. -/
theorem foundT_mono (H i : Word) (mi : Mem) (x : Word) (hi : i ≤ H)
    (h : FoundT sa ob N bt hsm H mi x) : FoundT sa ob N bt hsm i mi x :=
  ⟨UInt64.le_trans hi h.1, h.2⟩

/-- The cursor's step: `H ≠ 0` and `i = H - 1`. -/
structure CurStep (H i : Word) : Prop where
  ne : H ≠ 0
  eq : i = H - 1

theorem CurStep.toNat {H i : Word} (h : CurStep H i) : i.toNat + 1 = H.toNat := by
  have : H.toNat ≠ 0 := fun e => h.ne (UInt64.toNat_inj.mp (by simpa using e))
  rw [h.eq, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

omit hob hNL hL hnN hN0 hOld in
include hbt in
/-- **The free slot** (`¬ bt < v`): nothing is written. -/
theorem top_free (mi : Mem) (H i : Word) (k : MkR) (hI : TopInv sa ob N n bt c KPm hsm m0 mi H k)
    (hc : CurStep H i) (hv : ¬ bt < VW sa ob mi i) : TopInv sa ob N n bt c KPm hsm m0 mi i k := by
  have hiH := hc.toNat
  have hn := UInt64.le_iff_toNat_le.mp hI.hn
  have hiH' : i < H := UInt64.lt_iff_toNat_lt.mpr (by omega)
  refine ⟨hI.fr, hI.w0, hI.w1, fun j hj => hI.lo j (UInt64.lt_trans hj hiH'), fun j hj hjN => ?_,
    fun x hx => ?_, UInt64.le_iff_toNat_le.mpr (by omega), ?_, hI.a1n, ?_, hI.b1n⟩
  · by_cases e : j = i
    · subst e; exact .inl (UInt64.not_lt.mp hv)
    · exact hI.hi j (UInt64.le_iff_toNat_le.mpr (by
        have := UInt64.le_iff_toNat_le.mp hj
        have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega)) hjN
  · rcases hI.node x hx with ⟨j, hj, hjx⟩ | h | h
    · by_cases e : j = i
      · subst e; exfalso; apply hv; rw [hjx]; exact (node_liveU bt c hbt x hx).1
      · exact .inl ⟨j, UInt64.lt_iff_toNat_lt.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp hj
          have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega), hjx⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (foundT_mono sa ob N bt hsm H i mi x (UInt64.le_of_lt hiH') h))
  · rcases hI.a1 with h | h
    · exact .inl h
    · exact .inr (UInt64.lt_trans hiH' h)
  · rcases hI.b1 with h | h
    · exact .inl h
    · exact .inr (UInt64.lt_trans hiH' h)

omit hob hNL hL hbt hnN hN0 hOld in
/-- A slot that keeps its words keeps `SlotOK`, if its mark range only widens. -/
theorem slotOK_keep (n1 n2 : Word) (Ex1 Ex2 : Word → Prop) (mi mf : Mem) (i1 i2 j : Word)
    (h : SlotOK sa ob n1 bt c KPm Ex1 mi i1 j) (hv : VW sa ob mf j = VW sa ob mi j)
    (hk : KW sa ob mf j = KW sa ob mi j)
    (hR : MARK ≤ VW sa ob mi j → (i1 ≤ j ∧ j < n1) ∨ Ex1 j → (i2 ≤ j ∧ j < n2) ∨ Ex2 j) :
    SlotOK sa ob n2 bt c KPm Ex2 mf i2 j := by
  unfold SlotOK at h ⊢
  rw [hv, hk]
  rcases h with h | h | ⟨a1, a2, a3, a4, a5⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a1, a2, a3, a4, hR a1 a5⟩)

/-- The ranges after a deferral at slot `i = H - 1`. -/
theorem kdefR_ok (n H i : Word) (k : MkR) (hc : CurStep H i) (hn : H ≤ n)
    (ha : k.a1 = 0 ∨ H < k.a1) (han : k.a1 ≤ n) (hb : k.b1 = 0 ∨ H < k.b1) (hbn : k.b1 ≤ n) :
    ((kdefR n i k).a0 ≤ i ∧ i < (kdefR n i k).a1 ∨ InB (kdefR n i k) i) ∧
    (∀ j, H ≤ j → (k.a0 ≤ j ∧ j < k.a1 ∨ InB k j) →
      ((kdefR n i k).a0 ≤ j ∧ j < (kdefR n i k).a1 ∨ InB (kdefR n i k) j)) ∧
    ((kdefR n i k).a1 = 0 ∨ i < (kdefR n i k).a1) ∧ (kdefR n i k).a1 ≤ n ∧
    ((kdefR n i k).b1 = 0 ∨ i < (kdefR n i k).b1) ∧ (kdefR n i k).b1 ≤ n := by
  have hiH := hc.toNat
  have e1 : (i + 1).toNat = H.toNat := by
    rw [UInt64.toNat_add]; have := H.toNat_lt; simp; omega
  have z : ∀ w : Word, w = 0 ↔ w.toNat = 0 := fun w => by
    constructor
    · rintro rfl; rfl
    · intro h; exact UInt64.toNat_inj.mp (by simpa using h)
  unfold kdefR InB
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, z] at ha han hb hbn hn ⊢
  split <;> split <;> simp only [z, e1] at * <;>
    refine ⟨by omega, fun j hj hr => by omega, by omega, by omega, by omega, by omega⟩

include hob hNL hL hbt hnN hOld in
/-- **The deferral**: slot `i = H - 1`'s live entry gets the mark and joins a range. -/
theorem top_mark (mi : Mem) (H i : Word) (k : MkR) (hI : TopInv sa ob N n bt c KPm hsm m0 mi H k)
    (hc : CurStep H i) (hv : bt < VW sa ob mi i) :
    TopInv sa ob N n bt c KPm hsm m0 (mi.set64 sa (ob + i) (pk (VW sa ob mi i + MARK) (KW sa ob mi i))) i
      (kdefR n i k) := by
  have hiH := hc.toNat
  have hn := UInt64.le_iff_toNat_le.mp hI.hn
  have hnN' := UInt64.le_iff_toNat_le.mp hnN
  have hiH' : i < H := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hin : i < n := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hiN : i < N := UInt64.lt_iff_toNat_lt.mpr (by omega)
  obtain ⟨hv0, hk0⟩ := hI.lo i hiH'
  have hO := hOld i hin
  rw [← hv0, ← hk0] at hO
  rcases hO with hO | ⟨hl, hle, hK⟩
  · exact absurd hv (UInt64.not_lt.mpr hO)
  obtain ⟨R1, R2, R3, R4, R5, R6⟩ := kdefR_ok n H i k hc hI.hn hI.a1 hI.a1n hI.b1 hI.b1n
  have hsz := hI.fr.size sa
  have hqlt : (KW sa ob mi i).toNat < 2 ^ 16 := shr48_lt _
  generalize hV : VW sa ob mi i = v at *
  generalize hQ : KW sa ob mi i = q at *
  have hvt := UInt64.lt_iff_toNat_lt.mp hl.2
  rw [MARK_toNat] at hvt
  have hpk : (v + MARK).toNat < 2 ^ 48 := by rw [add_mark_toNat _ (by omega)]; omega
  have hVf : ∀ j, j < N → VW sa ob (mi.set64 sa (ob + i) (pk (v + MARK) q)) j =
      if i = j then v + MARK else VW sa ob mi j := fun j hj => by
    rw [VW_set sa ob N m0 hob hNL hL mi hsz i j hiN hj, pk_vmask _ _ hpk hqlt]
  have hKf : ∀ j, j < N → KW sa ob (mi.set64 sa (ob + i) (pk (v + MARK) q)) j = KW sa ob mi j :=
    fun j hj => by
      rw [KW_set sa ob N m0 hob hNL hL mi hsz i j hiN hj, pk_shr _ _ hpk hqlt]
      split
      · rename_i e; subst e; exact hQ.symm
      · rfl
  have hsub : v + MARK - MARK = v := UInt64.add_sub_cancel _ _
  -- the other slots keep their words
  have hne : ∀ j, j < N → j ≠ i → VW sa ob (mi.set64 sa (ob + i) (pk (v + MARK) q)) j = VW sa ob mi j ∧
      KW sa ob (mi.set64 sa (ob + i) (pk (v + MARK) q)) j = KW sa ob mi j := fun j hj e =>
    ⟨by rw [hVf j hj, ite_eq_right (Ne.symm e)], hKf j hj⟩
  have ltI : ∀ j, j ≠ i → i ≤ j → H ≤ j := fun j e hj => UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.le_iff_toNat_le.mp hj
    have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega)
  refine ⟨hI.fr.trans (GFr.set64 _ _ _ _), ?_, ?_, fun j hj => ?_, fun j hj hjN => ?_,
    fun x hx => ?_, UInt64.le_of_lt hin, R3, R4, R5, R6⟩
  · rw [rd01_set sa ob N m0 hob hNL hL mi hsz i hiN _ 0 (by simp), hI.w0]
  · rw [rd01_set sa ob N m0 hob hNL hL mi hsz i hiN _ 1 (by simp), hI.w1]
  · have hjN : j < N := UInt64.lt_trans hj hiN
    rw [(hne j hjN (fun e => UInt64.lt_irrefl _ (e ▸ hj))).1, (hne j hjN (fun e => UInt64.lt_irrefl _ (e ▸ hj))).2]
    exact hI.lo j (UInt64.lt_trans hj hiH')
  · by_cases e : j = i
    · subst e
      unfold SlotOK
      rw [hVf j hjN, hKf j hjN, ite_eq_left rfl, hsub, hQ]
      exact .inr (.inr ⟨(mark_le_iff _).mpr (by rw [add_mark_toNat _ (by omega)]; omega), hl.1, hle,
        hK, R1⟩)
    · exact slotOK_keep sa ob bt c KPm _ _ _ _ mi _ _ _ j (hI.hi j (ltI j e hj) hjN)
        (hne j hjN e).1 (hne j hjN e).2 (fun _ h => R2 j (ltI j e hj) h)
  · rcases hI.node x hx with ⟨j, hj, hjx⟩ | ⟨j, hjN, hjx⟩ | h
    · by_cases e : j = i
      · subst e
        refine .inr (.inl ⟨j, hiN, ?_⟩)
        rw [hVf j hiN, ite_eq_left rfl, ← hV, hjx]
      · have hji : j < i := UInt64.lt_iff_toNat_lt.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp hj
          have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega)
        exact .inl ⟨j, hji, by rw [(hne j (UInt64.lt_trans hji hiN) e).1]; exact hjx⟩
    · have e : j ≠ i := fun e => by
        subst e
        have := congrArg UInt64.toNat hjx
        rw [hV, add_mark_toNat _ (by rw [node_toNat bt c hbt x hx]; omega)] at this; omega
      exact .inr (.inl ⟨j, hjN, by rw [(hne j hjN e).1]; exact hjx⟩)
    · refine .inr (.inr (foundT_mono sa ob N bt hsm H i _ x (UInt64.le_of_lt hiH')
        (foundT_keep sa ob N bt c hsm H mi _ x hx (fun j hj hHj _ => ?_) hbt h)))
      exact (hne j hj (fun e => by subst e; exact UInt64.lt_irrefl _ (UInt64.lt_of_lt_of_le hiH' hHj))).1

include hbt hnN hOld in
/-- **The stay**: slot `i = H - 1`'s live entry has its new home at `i`. -/
theorem top_stay (mi : Mem) (H i : Word) (k : MkR) (hI : TopInv sa ob N n bt c KPm hsm m0 mi H k)
    (hc : CurStep H i) (hv : bt < VW sa ob mi i)
    (hj : homeW (hsm (VW sa ob mi i - bt - 1)) N = i) :
    TopInv sa ob N n bt c KPm hsm m0 mi i k := by
  have hiH := hc.toNat
  have hn := UInt64.le_iff_toNat_le.mp hI.hn
  have hnN' := UInt64.le_iff_toNat_le.mp hnN
  have hiH' : i < H := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hin : i < n := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hiN : i < N := UInt64.lt_iff_toNat_lt.mpr (by omega)
  obtain ⟨hv0, hk0⟩ := hI.lo i hiH'
  have hO := hOld i hin
  rw [← hv0, ← hk0] at hO
  rcases hO with hO | ⟨hl, hle, hK⟩
  · exact absurd hv (UInt64.not_lt.mpr hO)
  obtain ⟨hxc, hbx⟩ := node_of_live bt c hbt _ hv hle
  generalize hX : VW sa ob mi i - bt - 1 = X at *
  have ltI : ∀ j, j ≠ i → i ≤ j → H ≤ j := fun j e hj => UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.le_iff_toNat_le.mp hj
    have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega)
  refine ⟨hI.fr, hI.w0, hI.w1, fun j hj => hI.lo j (UInt64.lt_trans hj hiH'), fun j hj hjN => ?_,
    fun x hx => ?_, UInt64.le_of_lt hin, ?_, hI.a1n, ?_, hI.b1n⟩
  · by_cases e : j = i
    · subst e; exact .inr (.inl ⟨hl, hle, by rw [hX]; exact hK⟩)
    · exact hI.hi j (ltI j e hj) hjN
  · rcases hI.node x hx with ⟨j, hj, hjx⟩ | h | h
    · by_cases e : j = i
      · subst e
        have : x = X := node_inj bt c hbt x X hx hxc (by rw [← hjx, hbx])
        subst this
        refine .inr (.inr ⟨by rw [hj]; exact UInt64.le_refl _, 0, by rw [hj]; omega, by rw [walkW, hj, hjx], fun e he => absurd he (by omega)⟩)
      · exact .inl ⟨j, UInt64.lt_iff_toNat_lt.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp hj
          have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega), hjx⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (foundT_mono sa ob N bt hsm H i mi x (UInt64.le_of_lt hiH') h))
  · rcases hI.a1 with h | h
    · exact .inl h
    · exact .inr (UInt64.lt_trans hiH' h)
  · rcases hI.b1 with h | h
    · exact .inl h
    · exact .inr (UInt64.lt_trans hiH' h)

include hob hNL hL hbt hnN hOld in
/-- **The move**: slot `i = H - 1`'s live entry, of new home `h0 > i`, goes to the free slot `j'`
the probe reached after `D` live unmarked slots; slot `i` is cleared. -/
theorem top_move (mi : Mem) (H i : Word) (k : MkR) (hI : TopInv sa ob N n bt c KPm hsm m0 mi H k)
    (hc : CurStep H i) (hv : bt < VW sa ob mi i) (h0 : Word)
    (hh0 : homeW (hsm (VW sa ob mi i - bt - 1)) N = h0) (hih : i < h0) (D : Nat)
    (hD : h0.toNat + D < N.toNat) (hp : ∀ e < D, LiveU bt (VW sa ob mi (walkW N h0 e)))
    (j' : Word) (hj' : walkW N h0 D = j') (hfree : VW sa ob mi j' ≤ bt) :
    TopInv sa ob N n bt c KPm hsm m0
      ((mi.set64 sa (ob + j') (pk (VW sa ob mi i) (KW sa ob mi i))).set64 sa (ob + i) 0) i k := by
  have hiH := hc.toNat
  have hn := UInt64.le_iff_toNat_le.mp hI.hn
  have hnN' := UInt64.le_iff_toNat_le.mp hnN
  have hiH' : i < H := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hin : i < n := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hiN : i < N := UInt64.lt_iff_toNat_lt.mpr (by omega)
  obtain ⟨hv0, hk0⟩ := hI.lo i hiH'
  have hO := hOld i hin
  rw [← hv0, ← hk0] at hO
  rcases hO with hO | ⟨hl, hle, hK⟩
  · exact absurd hv (UInt64.not_lt.mpr hO)
  obtain ⟨hxc, hbx⟩ := node_of_live bt c hbt _ hv hle
  have hsz := hI.fr.size sa
  have hih' := UInt64.lt_iff_toNat_lt.mp hih
  have hwj : j'.toNat = h0.toNat + D := by rw [← hj']; exact walkW_toNat N h0 D hD
  have hjN : j' < N := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hji : j' ≠ i := fun e => by have := congrArg UInt64.toNat e; omega
  have hHj : H ≤ j' := UInt64.le_iff_toNat_le.mpr (by omega)
  generalize hX : VW sa ob mi i - bt - 1 = X at *
  have hvlt : (VW sa ob mi i).toNat < 2 ^ 48 := by
    have := UInt64.lt_iff_toNat_lt.mp hl.2; rw [MARK_toNat] at this; omega
  have hqlt : (KW sa ob mi i).toNat < 2 ^ 16 := shr48_lt _
  have f1 : GFr sa m0 (mi.set64 sa (ob + j') (pk (VW sa ob mi i) (KW sa ob mi i))) :=
    hI.fr.trans (GFr.set64 _ _ _ _)
  have hVf : ∀ j, j < N → VW sa ob ((mi.set64 sa (ob + j') (pk (VW sa ob mi i) (KW sa ob mi i))).set64 sa
      (ob + i) 0) j = if i = j then 0 else if j' = j then (VW sa ob mi i) else VW sa ob mi j := fun j hj => by
    rw [VW_set sa ob N m0 hob hNL hL _ (f1.size sa) i j hiN hj,
      VW_set sa ob N m0 hob hNL hL mi hsz j' j hjN hj, pk_vmask _ _ hvlt hqlt, UInt64.zero_and]
  have hKf : ∀ j, j < N → KW sa ob ((mi.set64 sa (ob + j') (pk (VW sa ob mi i) (KW sa ob mi i))).set64 sa
      (ob + i) 0) j = if i = j then 0 else if j' = j then (KW sa ob mi i) else KW sa ob mi j := fun j hj => by
    rw [KW_set sa ob N m0 hob hNL hL _ (f1.size sa) i j hiN hj,
      KW_set sa ob N m0 hob hNL hL mi hsz j' j hjN hj, pk_shr _ _ hvlt hqlt, UInt64.zero_shiftRight]
  have hr01 : ∀ y : Word, y.toNat < 2 → rdW (((mi.set64 sa (ob + j') (pk (VW sa ob mi i) (KW sa ob mi i))).set64 sa
      (ob + i) 0).arr64 sa) y = rdW (mi.arr64 sa) y := fun y hy => by
    rw [rd01_set sa ob N m0 hob hNL hL _ (f1.size sa) i hiN 0 y hy,
      rd01_set sa ob N m0 hob hNL hL mi hsz j' hjN _ y hy]
  have ltI : ∀ j, j ≠ i → i ≤ j → H ≤ j := fun j e hj => UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.le_iff_toNat_le.mp hj
    have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega)
  have hjL : ¬ LiveU bt (VW sa ob mi j') := fun h => absurd h.1 (UInt64.not_lt.mpr hfree)
  refine ⟨f1.trans (GFr.set64 _ _ _ _), by rw [hr01 0 (by simp), hI.w0], by rw [hr01 1 (by simp), hI.w1],
    fun j hj => ?_, fun j hj hjN' => ?_, fun x hx => ?_, UInt64.le_of_lt hin, ?_, hI.a1n, ?_, hI.b1n⟩
  · have hjN' : j < N := UInt64.lt_trans hj hiN
    have e1 : i ≠ j := fun e => UInt64.lt_irrefl _ (e ▸ hj)
    have e2 : j' ≠ j := fun e => by
      have := UInt64.lt_iff_toNat_lt.mp hj; have := congrArg UInt64.toNat e; omega
    simp only [hVf j hjN', hKf j hjN', e1, e2, ↓reduceIte]
    exact hI.lo j (UInt64.lt_trans hj hiH')
  · unfold SlotOK
    rw [hVf j hjN', hKf j hjN']
    by_cases e1 : i = j
    · subst e1; simp only [↓reduceIte]
      exact .inl (by simp [UInt64.le_iff_toNat_le])
    · simp only [e1, ↓reduceIte]
      by_cases e2 : j' = j
      · subst e2; simp only [↓reduceIte]
        exact .inr (.inl ⟨hl, hle, by rw [hX]; exact hK⟩)
      · simp only [e2, ↓reduceIte]
        exact hI.hi j (ltI j (Ne.symm e1) hj) hjN'
  · rcases hI.node x hx with ⟨j, hj, hjx⟩ | ⟨j, hjN', hjx⟩ | h
    · by_cases e : j = i
      · subst j
        have : x = X := node_inj bt c hbt x X hx hxc (by rw [← hjx, hbx])
        subst this
        refine .inr (.inr ⟨by rw [hh0]; exact UInt64.le_of_lt hih, D, by rw [hh0]; exact hD, ?_,
          fun e he => ?_⟩)
        · rw [hh0, hj', hVf j' hjN, ite_eq_right hji.symm, ite_eq_left rfl, hjx]
        · rw [hh0]
          have hwe := walkW_toNat N h0 e (by omega)
          have hweN : walkW N h0 e < N := UInt64.lt_iff_toNat_lt.mpr (by omega)
          have e1 : i ≠ walkW N h0 e := fun e' => by have := congrArg UInt64.toNat e'; omega
          have e2 : j' ≠ walkW N h0 e := fun e' => by have := congrArg UInt64.toNat e'; omega
          rw [hVf _ hweN, ite_eq_right e1, ite_eq_right e2]; exact hp e he
      · have hji' : j < i := UInt64.lt_iff_toNat_lt.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp hj
          have : i.toNat ≠ j.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm); omega)
        have e2 : j' ≠ j := fun e' => by
          have := UInt64.lt_iff_toNat_lt.mp hji'; have := congrArg UInt64.toNat e'; omega
        refine .inl ⟨j, hji', ?_⟩
        rw [hVf j (UInt64.lt_trans hji' hiN), ite_eq_right (Ne.symm e), ite_eq_right e2]; exact hjx
    · have hm : MARK ≤ VW sa ob mi j := by
        rw [hjx, mark_le_iff, add_mark_toNat _ (by rw [node_toNat bt c hbt x hx]; omega)]; omega
      have e1 : i ≠ j := fun e => by
        subst e; exact absurd hm (UInt64.not_le.mpr hl.2)
      have e2 : j' ≠ j := fun e => by
        subst e; exact absurd (UInt64.le_trans hm hfree) (by
          intro h'; have := UInt64.le_iff_toNat_le.mp h'; rw [MARK_toNat] at this; omega)
      refine .inr (.inl ⟨j, hjN', ?_⟩)
      rw [hVf j hjN', ite_eq_right e1, ite_eq_right e2]; exact hjx
    · refine .inr (.inr (foundT_mono sa ob N bt hsm H i _ x (UInt64.le_of_lt hiH')
        (foundT_keep sa ob N bt c hsm H mi _ x hx (fun j hj hHj hlj => ?_) hbt h)))
      have e1 : i ≠ j := fun e => by subst e; exact UInt64.lt_irrefl _ (UInt64.lt_of_lt_of_le hiH' hHj)
      have e2 : j' ≠ j := fun e => by subst e; exact hjL hlj
      rw [hVf j hj, ite_eq_right e1, ite_eq_right e2]
  · rcases hI.a1 with h | h
    · exact .inl h
    · exact .inr (UInt64.lt_trans hiH' h)
  · rcases hI.b1 with h | h
    · exact .inl h
    · exact .inr (UInt64.lt_trans hiH' h)

include hob hNL hL hbt hnN hN0 hOld in
/-- **One step of the sweep keeps the invariant** (`ktopS` at `i = H - 1`), if `G` of every node
is its hash. -/
theorem ktopS_inv (G : Mem → Word → Word)
    (hGh : ∀ mi : Mem, GFr sa m0 mi → ∀ x, G mi x = hsm x)
    (mi : Mem) (H i : Word) (k : MkR) (hI : TopInv sa ob N n bt c KPm hsm m0 mi H k)
    (hc : CurStep H i) :
    TopInv sa ob N n bt c KPm hsm m0 (ktopS sa G N n ob bt i k mi).1 i
      (ktopS sa G N n ob bt i k mi).2 := by
  have hiH := hc.toNat
  have hn := UInt64.le_iff_toNat_le.mp hI.hn
  have hnN' := UInt64.le_iff_toNat_le.mp hnN
  have hiH' : i < H := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hin : i < n := UInt64.lt_iff_toNat_lt.mpr (by omega)
  unfold ktopS
  by_cases hv : bt < vwd (mi.arr64 sa) (ob + i)
  · simp only [hv, ↓reduceIte]
    have hv' : bt < VW sa ob mi i := hv
    have hj : kjW sa G N ob bt i mi = homeW (hsm (VW sa ob mi i - bt - 1)) N := by
      simp only [kjW]; rw [hGh mi hI.fr]; rfl
    have hh0N := homeW_lt (hsm (VW sa ob mi i - bt - 1)) N hN0
    generalize hh0 : homeW (hsm (VW sa ob mi i - bt - 1)) N = h0 at hj hh0N
    unfold ktopBW ktopQW
    by_cases hih : i < h0
    · obtain ⟨D, hD, hk, hp, -⟩ := kupW_res (mi.arr64 sa) ob N bt h0 hh0N
      have htg : ktgW sa G N ob bt i mi = walkW N h0 D := by
        simp only [ktgW, hj, hih, ↓reduceIte, hk]
      have hx : kxW sa G N ob bt i mi = VW sa ob mi (walkW N h0 D) := by
        simp only [kxW, hj, hih, ↓reduceIte, htg]; rfl
      rw [hx, htg]
      by_cases hf : VW sa ob mi (walkW N h0 D) ≤ bt
      · simp only [hf, ↓reduceIte]
        exact top_move sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN hOld mi H i k hI hc hv' h0 hh0
          hih D hD (fun e he => hp e he) _ rfl hf
      · have hne : walkW N h0 D ≠ i := fun e => by
          have := walkW_toNat N h0 D hD; rw [e] at this
          have := UInt64.lt_iff_toNat_lt.mp hih; omega
        simp only [hf, hne, ↓reduceIte]
        exact top_mark sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN hOld mi H i k hI hc hv'
    · have htg : ktgW sa G N ob bt i mi = h0 := by simp only [ktgW, hj, hih, ↓reduceIte]
      have hx : kxW sa G N ob bt i mi = VW sa ob mi i := by simp only [kxW, hj, hih, ↓reduceIte]; rfl
      rw [hx, htg]
      simp only [UInt64.not_le.mpr hv', ↓reduceIte]
      by_cases hs : h0 = i
      · simp only [hs, ↓reduceIte]
        exact top_stay sa ob N n bt c KPm hsm m0 hbt hnN hOld mi H i k hI hc hv' (hh0.trans hs)
      · simp only [hs, ↓reduceIte]
        exact top_mark sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN hOld mi H i k hI hc hv'
  · simp only [hv, ↓reduceIte]
    exact top_free sa ob N n bt c KPm hsm m0 hbt mi H i k hI hc hv

include hob hNL hL hbt hnN hN0 hOld in
/-- **The sweep keeps the invariant** (`ktopW`), down to the cursor `0`. -/
theorem ktopW_inv (G : Mem → Word → Word)
    (hGh : ∀ mi : Mem, GFr sa m0 mi → ∀ x, G mi x = hsm x)
    (H : Word) (k : MkR) (mi : Mem) (hI : TopInv sa ob N n bt c KPm hsm m0 mi H k) :
    TopInv sa ob N n bt c KPm hsm m0 (ktopW sa G N n ob bt H k mi).1 0
      (ktopW sa G N n ob bt H k mi).2 := by
  fun_induction ktopW sa G N n ob bt H k mi with
  | case1 => exact hI
  | case2 H k mi hH ih =>
    exact ih (ktopS_inv sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN hN0 hOld G hGh mi H _ k hI ⟨hH, rfl⟩)

omit hob hNL hL hbt hnN hN0 hOld in
/-- **At the cursor `0`** the invariant is the re-insertion's at the first range's start, with
the second range as the later loop's. -/
theorem topInv_reins (mi : Mem) (k : MkR) (hI : TopInv sa ob N n bt c KPm hsm m0 mi 0 k) :
    ReinsInv sa ob N k.a1 bt c KPm hsm (InB k) m0 mi k.a0 := by
  refine ⟨hI.fr, hI.w0, hI.w1, fun j hj => hI.hi j (UInt64.zero_le) hj, fun x hx => ?_⟩
  rcases hI.node x hx with ⟨j, hj, -⟩ | h | ⟨-, d, -, h1, h2⟩
  · exact absurd hj (by simp [UInt64.lt_iff_toNat_lt])
  · exact .inl h
  · exact .inr ⟨d, h1, h2⟩

omit hob hNL hL hbt hnN hN0 hOld in
/-- **At the start** (`H = n`, no marks): the upper half is free and every node is in its old
slot. -/
theorem topInv_init (hZ : ∀ j, n ≤ j → j < N → VW sa ob m0 j ≤ bt)
    (hN : ∀ x : Word, x.toNat < c.toNat → ∃ j, j < n ∧ VW sa ob m0 j = bt + x + 1) :
    TopInv sa ob N n bt c KPm hsm m0 m0 n ⟨0, 0, 0, 0⟩ :=
  ⟨GFr.refl _ _, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun j hj hjN => .inl (hZ j hj hjN),
    fun x hx => .inl (hN x hx), UInt64.le_refl _, .inl rfl, UInt64.zero_le, .inl rfl, UInt64.zero_le⟩

end top

end L.Arena
