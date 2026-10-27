import ConAgua.Arena.SlotGrowSpec
import ConAgua.Arena.StoreRel
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The in-place growth's re-insertion keeps every node findable (lane memlay)

`SlotGrowSpec.lean`'s `krehashW` (the model of `ConsLib.lean`'s `krehashL`) re-inserts, in a table
of `N` slots (from word `ob` of array `sa`) whose old half's live slots carry the mark (`MARK`
added to the value word), every marked entry: from its home in the doubled table, past the live
unmarked slots, to its own slot, a free slot (it moves) or a marked one (they swap, and the
displaced entry is next). This file proves the invariant `ReinsInv` of that loop:

* every slot is free (value word at most the base `bt`), live and unmarked (a node's value word
  with an admissible key word), or marked (the same, plus `MARK`) at or after the current slot
  `i` and in the old half;
* every node is either still marked somewhere, or found from the home of its hash through live
  unmarked slots only (`FoundU`).

Marked slots only ever turn into unmarked or free ones, and a path of live unmarked slots never
crosses a slot that is written (written slots are marked, free, or the entry's own), so a node
once found stays found. At the end (`i = n`) no slot is marked, and every node is found: the
table relation's `SlotsOKG` for the doubled table (`StoreGrow.lean`).
-/

open ConRon.Arena


namespace L.Arena

theorem MARK_toNat : MARK.toNat = 2 ^ 63 := rfl

theorem add_mark_toNat (a : Word) (ha : a.toNat < 2 ^ 63) : (a + MARK).toNat = a.toNat + 2 ^ 63 := by
  rw [UInt64.toNat_add, MARK_toNat]; omega

theorem sub_mark_toNat (a : Word) (ha : MARK ≤ a) : (a - MARK).toNat = a.toNat - 2 ^ 63 := by
  rw [UInt64.toNat_sub_of_le _ _ ha, MARK_toNat]

theorem mark_le_iff (a : Word) : MARK ≤ a ↔ 2 ^ 63 ≤ a.toNat := by
  rw [UInt64.le_iff_toNat_le, MARK_toNat]

/-- A read after an in-bounds write. -/
theorem rd_set_in (sa : ArrId) (mi : Mem) (ya v y : Word) (h : ya.toNat < (mi.arr64 sa).size) :
    rdW ((mi.set64 sa ya v).arr64 sa) y = if ya = y then v else rdW (mi.arr64 sa) y := by
  rw [rdW_set64]; simp [h]

section reins
variable (sa : ArrId) (ob N n bt c : Word) (KPm : Word → Word → Prop) (hsm : Word → Word)

/-- The value word of slot `j`. -/
def VW (mi : Mem) (j : Word) : Word := rdW (mi.arr64 sa) (ob + j * 2)
/-- The key word of slot `j`. -/
def KW (mi : Mem) (j : Word) : Word := rdW (mi.arr64 sa) (ob + j * 2 + 1)

/-- A live unmarked value word. -/
def LiveU (v : Word) : Prop := bt < v ∧ v < MARK

/-- What slot `j` may hold while the re-insertion is at slot `i`: free, live and unmarked (a node
`v - bt - 1 < c` with an admissible key word), or marked (the same with `MARK` added), then at
or after `i` and in the old half. -/
def SlotOK (mi : Mem) (i j : Word) : Prop :=
  VW sa ob mi j ≤ bt ∨
  (LiveU bt (VW sa ob mi j) ∧ (VW sa ob mi j).toNat ≤ bt.toNat + c.toNat ∧
    KPm (VW sa ob mi j - bt - 1) (KW sa ob mi j)) ∨
  (MARK ≤ VW sa ob mi j ∧ bt < VW sa ob mi j - MARK ∧
    (VW sa ob mi j - MARK).toNat ≤ bt.toNat + c.toNat ∧
    KPm (VW sa ob mi j - MARK - bt - 1) (KW sa ob mi j) ∧ i ≤ j ∧ j < n)

/-- Node `x` is found from the home of its hash through live unmarked slots. -/
def FoundU (mi : Mem) (x : Word) : Prop :=
  ∃ d : Nat, VW sa ob mi (walkW N (homeW (hsm x) N) d) = bt + x + 1 ∧
    ∀ e < d, LiveU bt (VW sa ob mi (walkW N (homeW (hsm x) N) e))

/-- **The re-insertion's invariant** at slot `i`, from the memory `m0` before it: only array
`sa` changes, and in it not words `0` and `1`; every slot is as `SlotOK` says; every node is
marked in some slot or found. -/
def ReinsInv (m0 mi : Mem) (i : Word) : Prop :=
  GFr sa m0 mi ∧ rdW (mi.arr64 sa) 0 = rdW (m0.arr64 sa) 0 ∧
  rdW (mi.arr64 sa) 1 = rdW (m0.arr64 sa) 1 ∧
  (∀ j, j < N → SlotOK sa ob n bt c KPm mi i j) ∧
  ∀ x : Word, x.toNat < c.toNat →
    (∃ j, j < N ∧ VW sa ob mi j = bt + x + 1 + MARK) ∨ FoundU sa ob N bt hsm mi x

theorem liveU_of_marked_slot (mi : Mem) (i j : Word) (h : SlotOK sa ob n bt c KPm mi i j)
    (hm : MARK ≤ VW sa ob mi j) (hbt' : bt.toNat < 2 ^ 63) :
    bt < VW sa ob mi j - MARK ∧ (VW sa ob mi j - MARK).toNat ≤ bt.toNat + c.toNat ∧
    KPm (VW sa ob mi j - MARK - bt - 1) (KW sa ob mi j) ∧ i ≤ j ∧ j < n := by
  have := (mark_le_iff _).mp hm
  rcases h with h | h | h
  · exfalso; have := UInt64.le_iff_toNat_le.mp h; omega
  · exfalso; have := UInt64.lt_iff_toNat_lt.mp h.1.2; rw [MARK_toNat] at this; omega
  · exact h.2

theorem not_liveU_of_marked (v : Word) (h : MARK ≤ v) : ¬ LiveU bt v := fun hl =>
  absurd h (UInt64.not_le.mpr hl.2)

variable (m0 : Mem)
  (hob : 2 ≤ ob.toNat) (hNL : ob.toNat + 2 * N.toNat ≤ (m0.arr64 sa).size)
  (hL : (m0.arr64 sa).size < 2 ^ 61)

include hob hNL hL

theorem adr_toNat (j : Word) (hj : j < N) :
    (ob + j * 2).toNat = ob.toNat + 2 * j.toNat ∧ (ob + j * 2 + 1).toNat = ob.toNat + 2 * j.toNat + 1 := by
  have := UInt64.lt_iff_toNat_lt.mp hj
  have e1 : (ob + j * 2).toNat = ob.toNat + 2 * j.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  refine ⟨e1, ?_⟩; rw [UInt64.toNat_add, e1]; simp; omega

theorem adr_in (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j : Word) (hj : j < N) :
    (ob + j * 2).toNat < (mi.arr64 sa).size ∧ (ob + j * 2 + 1).toNat < (mi.arr64 sa).size := by
  have a := adr_toNat sa ob N m0 hob hNL hL j hj
  have := UInt64.lt_iff_toNat_lt.mp hj
  rw [hsz, a.1, a.2]; omega

theorem adr_ne (j j' : Word) (hj : j < N) (hj' : j' < N) :
    (ob + j * 2 = ob + j' * 2 ↔ j = j') ∧ (ob + j * 2 + 1 = ob + j' * 2 + 1 ↔ j = j') ∧
    ob + j * 2 + 1 ≠ ob + j' * 2 ∧ ob + j * 2 ≠ ob + j' * 2 + 1 := by
  have a := adr_toNat sa ob N m0 hob hNL hL j hj
  have a' := adr_toNat sa ob N m0 hob hNL hL j' hj'
  refine ⟨⟨fun h => ?_, fun h => by rw [h]⟩, ⟨fun h => ?_, fun h => by rw [h]⟩, fun h => ?_, fun h => ?_⟩
  all_goals have := congrArg UInt64.toNat h
  · exact UInt64.toNat_inj.mp (by omega)
  · exact UInt64.toNat_inj.mp (by omega)
  · omega
  · omega

theorem VW_setV (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j j' : Word)
    (hj : j < N) (hj' : j' < N) (v : Word) :
    VW sa ob (mi.set64 sa (ob + j * 2) v) j' = if j = j' then v else VW sa ob mi j' := by
  simp only [VW, rd_set_in sa mi _ v _ (adr_in sa ob N m0 hob hNL hL mi hsz j hj).1,
    (adr_ne sa ob N m0 hob hNL hL j j' hj hj').1]

theorem VW_setK (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j j' : Word)
    (hj : j < N) (hj' : j' < N) (v : Word) :
    VW sa ob (mi.set64 sa (ob + j * 2 + 1) v) j' = VW sa ob mi j' := by
  simp only [VW, rd_set_in sa mi _ v _ (adr_in sa ob N m0 hob hNL hL mi hsz j hj).2,
    (adr_ne sa ob N m0 hob hNL hL j j' hj hj').2.2.1, ↓reduceIte]

theorem KW_setV (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j j' : Word)
    (hj : j < N) (hj' : j' < N) (v : Word) :
    KW sa ob (mi.set64 sa (ob + j * 2) v) j' = KW sa ob mi j' := by
  simp only [KW, rd_set_in sa mi _ v _ (adr_in sa ob N m0 hob hNL hL mi hsz j hj).1,
    (adr_ne sa ob N m0 hob hNL hL j j' hj hj').2.2.2, ↓reduceIte]

theorem KW_setK (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j j' : Word)
    (hj : j < N) (hj' : j' < N) (v : Word) :
    KW sa ob (mi.set64 sa (ob + j * 2 + 1) v) j' = if j = j' then v else KW sa ob mi j' := by
  simp only [KW, rd_set_in sa mi _ v _ (adr_in sa ob N m0 hob hNL hL mi hsz j hj).2,
    (adr_ne sa ob N m0 hob hNL hL j j' hj hj').2.1]

/-- Writes to slot words keep words `0` and `1`. -/
theorem rd01_setV (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j : Word) (hj : j < N)
    (v y : Word) (hy : y.toNat < 2) :
    rdW ((mi.set64 sa (ob + j * 2) v).arr64 sa) y = rdW (mi.arr64 sa) y := by
  rw [rd_set_in sa mi _ v _ (adr_in sa ob N m0 hob hNL hL mi hsz j hj).1, ite_eq_right]
  intro h'; have := congrArg UInt64.toNat h'
  have a := adr_toNat sa ob N m0 hob hNL hL j hj; omega

theorem rd01_setK (mi : Mem) (hsz : (mi.arr64 sa).size = (m0.arr64 sa).size) (j : Word) (hj : j < N)
    (v y : Word) (hy : y.toNat < 2) :
    rdW ((mi.set64 sa (ob + j * 2 + 1) v).arr64 sa) y = rdW (mi.arr64 sa) y := by
  rw [rd_set_in sa mi _ v _ (adr_in sa ob N m0 hob hNL hL mi hsz j hj).2, ite_eq_right]
  intro h'; have := congrArg UInt64.toNat h'
  have a := adr_toNat sa ob N m0 hob hNL hL j hj; omega

/-! ## The probe -/

/-- **The re-insertion's probe**: its result `j` is on the run from the home `h0`, after slots
that are not `i` and live unmarked, and is `i` or not live unmarked. -/
theorem kprobeW_res (mi : Mem) (i h0 : Word) :
    ∀ (f : Nat) (d j : Word), N.toNat - d.toNat ≤ f →
      (∀ e < d.toNat, walkW N h0 e ≠ i ∧ LiveU bt (VW sa ob mi (walkW N h0 e))) →
      kprobeW (mi.arr64 sa) ob N i bt (walkW N h0 d.toNat) d = some j →
      ∃ D : Nat, j = walkW N h0 D ∧
        (∀ e < D, walkW N h0 e ≠ i ∧ LiveU bt (VW sa ob mi (walkW N h0 e))) ∧
        (j = i ∨ ¬ LiveU bt (VW sa ob mi j)) := by
  intro f
  induction f with
  | zero =>
    intro d j hf hd h
    rw [kprobeW] at h
    have hnd : N ≤ d := UInt64.le_iff_toNat_le.mpr (by omega)
    by_cases hc : walkW N h0 d.toNat ≠ i ∧ bt < rdW (mi.arr64 sa) (ob + walkW N h0 d.toNat * 2) ∧
        rdW (mi.arr64 sa) (ob + walkW N h0 d.toNat * 2) < MARK
    · simp [hc, hnd] at h
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨d.toNat, rfl, hd, ?_⟩
      by_cases hi : walkW N h0 d.toNat = i
      · exact .inl hi
      · exact .inr (fun hl => hc ⟨hi, hl.1, hl.2⟩)
  | succ f ih =>
    intro d j hf hd h
    rw [kprobeW] at h
    by_cases hc : walkW N h0 d.toNat ≠ i ∧ bt < rdW (mi.arr64 sa) (ob + walkW N h0 d.toNat * 2) ∧
        rdW (mi.arr64 sa) (ob + walkW N h0 d.toNat * 2) < MARK
    · by_cases hnd : N ≤ d
      · simp [hc, hnd] at h
      simp only [hc, hnd, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h
      have hlt : d.toNat < N.toNat := by
        have := mt UInt64.le_iff_toNat_le.mpr hnd; omega
      have e1 : (d + 1).toNat = d.toNat + 1 := by
        have := N.toNat_lt; rw [UInt64.toNat_add]; simp; omega
      rw [← walkW_succ, ← e1] at h
      refine ih (d + 1) j (by omega) (fun e he => ?_) h
      rw [e1] at he
      by_cases hed : e = d.toNat
      · subst hed; exact ⟨hc.1, hc.2.1, hc.2.2⟩
      · exact hd e (by omega)
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨d.toNat, rfl, hd, ?_⟩
      by_cases hi : walkW N h0 d.toNat = i
      · exact .inl hi
      · exact .inr (fun hl => hc ⟨hi, hl.1, hl.2⟩)

/-! ## Moving the invariant -/

variable (hbt : bt.toNat + c.toNat + 1 < 2 ^ 63) (hnN : n ≤ N)
include hbt hnN

/-- A node found stays found when the live unmarked slots keep their value words. -/
theorem foundU_keep (mi mf : Mem) (x : Word) (hx : x.toNat < c.toNat)
    (hk : ∀ j', j' < N → LiveU bt (VW sa ob mi j') → VW sa ob mf j' = VW sa ob mi j')
    (hN0 : 0 < N) (h : FoundU sa ob N bt hsm mi x) : FoundU sa ob N bt hsm mf x := by
  obtain ⟨d, h1, h2⟩ := h
  have hw := fun e => walkW_lt N (homeW (hsm x) N) e (homeW_lt _ _ hN0)
  have hl : LiveU bt (bt + x + 1) := by
    constructor
    · rw [UInt64.lt_iff_toNat_lt]; rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
    · rw [UInt64.lt_iff_toNat_lt, MARK_toNat, UInt64.toNat_add, UInt64.toNat_add]; simp; omega
  refine ⟨d, ?_, fun e he => ?_⟩
  · rw [hk _ (hw d) (h1 ▸ hl), h1]
  · rw [hk _ (hw e) (h2 e he)]; exact h2 e he

/-- **One placement keeps the invariant** (`kplaceW`): the marked entry of slot `i` (value word
`X + MARK`, node `X - bt - 1`) goes to slot `j`, the probe's result from the home of its node's
hash. Afterwards the next value word to re-insert is slot `i`'s if marked, and slot `i` is not
marked otherwise. -/
theorem place_inv (mi : Mem) (i : Word) (hi : i < n) (hI : ReinsInv sa ob N n bt c KPm hsm m0 mi i)
    (hv : MARK ≤ VW sa ob mi i) (j : Word) (hjN : j < N) (D : Nat)
    (hD : j = walkW N (homeW (hsm (VW sa ob mi i - MARK - bt - 1)) N) D)
    (hpath : ∀ e < D, walkW N (homeW (hsm (VW sa ob mi i - MARK - bt - 1)) N) e ≠ i ∧
      LiveU bt (VW sa ob mi (walkW N (homeW (hsm (VW sa ob mi i - MARK - bt - 1)) N) e)))
    (hj : j = i ∨ ¬ LiveU bt (VW sa ob mi j)) (hN0 : 0 < N) :
    ReinsInv sa ob N n bt c KPm hsm m0 (kplaceW sa ob i j (VW sa ob mi i - MARK) (KW sa ob mi i) mi).1 i ∧
    (MARK ≤ (kplaceW sa ob i j (VW sa ob mi i - MARK) (KW sa ob mi i) mi).2 →
      (kplaceW sa ob i j (VW sa ob mi i - MARK) (KW sa ob mi i) mi).2 =
        VW sa ob (kplaceW sa ob i j (VW sa ob mi i - MARK) (KW sa ob mi i) mi).1 i) ∧
    (¬ MARK ≤ (kplaceW sa ob i j (VW sa ob mi i - MARK) (KW sa ob mi i) mi).2 →
      ¬ MARK ≤ VW sa ob (kplaceW sa ob i j (VW sa ob mi i - MARK) (KW sa ob mi i) mi).1 i) := by
  obtain ⟨hfr, h0, h1, hslot, hnode⟩ := hI
  have hiN : i < N := UInt64.lt_iff_toNat_lt.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp hi; have := UInt64.le_iff_toNat_le.mp hnN; omega)
  have hsz : (mi.arr64 sa).size = (m0.arr64 sa).size := hfr.2.1 sa
  generalize hX : VW sa ob mi i - MARK = X at *
  generalize hq : KW sa ob mi i = q at *
  obtain ⟨hbX, hXc, hK, -, -⟩ := liveU_of_marked_slot sa ob n bt c KPm mi i i (hslot i hiN) hv (by omega)
  try rw [hX] at hbX hXc hK
  try rw [hq] at hK
  have hvt := (mark_le_iff _).mp hv
  have hXv : VW sa ob mi i = X + MARK := by
    rw [← hX]; exact (UInt64.sub_add_cancel _ _).symm
  have hXl : LiveU bt X := ⟨hbX, by rw [UInt64.lt_iff_toNat_lt, MARK_toNat]; omega⟩
  generalize hxn : X - bt - 1 = xn at *
  have hbx : bt + xn + 1 = X := by rw [← hxn]; grind
  have hxc : xn.toNat < c.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp hbX
    rw [← hxn, UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hbX)]
    · simp; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hbX)]; simp; omega
  -- a node marked at slot `i` is node `xn`
  have hmi : ∀ x, VW sa ob mi i = bt + x + 1 + MARK → x = xn := fun x h => by
    rw [hXv] at h
    have : X = bt + x + 1 := by have := congrArg (· - MARK) h; simpa using this
    rw [← hbx] at this; grind
  -- the found path of node `xn` to `j`
  have hw := fun e => walkW_lt N (homeW (hsm xn) N) e (homeW_lt _ _ hN0)
  have hiL : ¬ LiveU bt (VW sa ob mi i) := not_liveU_of_marked bt _ hv
  have hjL : j = i ∨ ¬ LiveU bt (VW sa ob mi j) := hj
  unfold kplaceW
  by_cases hji : j = i
  · -- it stays
    subst hji
    simp only [↓reduceIte]
    have hV := fun j' hj' => VW_setV sa ob N m0 hob hNL hL mi hsz j j' hiN hj' X
    have hKf := fun j' hj' => KW_setV sa ob N m0 hob hNL hL mi hsz j j' hiN hj' X
    refine ⟨⟨hfr.trans (GFr.set64 _ _ _ _), by rw [rd01_setV sa ob N m0 hob hNL hL mi hsz j hiN X 0 (by simp), h0],
      by rw [rd01_setV sa ob N m0 hob hNL hL mi hsz j hiN X 1 (by simp), h1], fun j' hj' => ?_, fun x hx => ?_⟩,
      fun h => absurd ((mark_le_iff _).mp h) (by simp), fun _ => ?_⟩
    · rw [SlotOK, hV j' hj', hKf j' hj']
      by_cases e : j = j'
      · subst e; simp only [↓reduceIte]; rw [hq, hxn]; exact .inr (.inl ⟨hXl, hXc, hK⟩)
      · simp only [e, ↓reduceIte]; exact hslot j' hj'
    · rcases hnode x hx with ⟨j'', hj'', hm⟩ | hf
      · by_cases e : j'' = j
        · subst e
          have := hmi x hm; subst this
          right
          refine ⟨D, ?_, fun e he => ?_⟩
          · rw [← hD, hV _ hiN]; simp [hbx]
          · obtain ⟨hne, hl⟩ := hpath e he
            rw [hV _ (hw e), ite_eq_right (Ne.symm hne)]; exact hl
        · left; exact ⟨j'', hj'', by rw [hV _ hj'', ite_eq_right (Ne.symm e)]; exact hm⟩
      · right
        refine foundU_keep sa ob N n bt c hsm m0 hob hNL hL hbt hnN mi _ x hx (fun j' hj' hl => ?_) hN0 hf
        rw [hV _ hj', ite_eq_right]; rintro rfl; exact hiL hl
    · rw [hV _ hiN]; simp only [↓reduceIte, mark_le_iff]; have := UInt64.lt_iff_toNat_lt.mp hXl.2
      rw [MARK_toNat] at this; omega
  · simp only [hji, ↓reduceIte]
    have hjnL : ¬ LiveU bt (VW sa ob mi j) := hjL.resolve_left hji
    by_cases hm : MARK ≤ VW sa ob mi j
    · -- swap with the marked entry of slot `j`
      simp only [show MARK ≤ rdW (mi.arr64 sa) (ob + j * 2) from hm, ↓reduceIte]
      generalize hY : rdW (mi.arr64 sa) (ob + j * 2) = Y
      generalize hYk : rdW (mi.arr64 sa) (ob + j * 2 + 1) = Yk
      have hYv : VW sa ob mi j = Y := hY
      have hYkv : KW sa ob mi j = Yk := hYk
      obtain ⟨hbY, hYc, hKY, -, hjn⟩ := liveU_of_marked_slot sa ob n bt c KPm mi i j (hslot j hjN) hm (by omega)
      try rw [hYv] at hbY hYc hKY
      try rw [hYkv] at hKY
      try rw [hYv] at hm
      have f1 : GFr sa m0 (mi.set64 sa (ob + j * 2) X) := hfr.trans (GFr.set64 _ _ _ _)
      have f2 : GFr sa m0 ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) := f1.trans (GFr.set64 _ _ _ _)
      have f3 : GFr sa m0 (((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y) := f2.trans (GFr.set64 _ _ _ _)
      have hV : ∀ j', j' < N → VW sa ob ((((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y).set64 sa (ob + i * 2 + 1) Yk) j' =
          if i = j' then Y else if j = j' then X else VW sa ob mi j' := fun j' hj' => by
        rw [VW_setK sa ob N m0 hob hNL hL (((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y) (f3.2.1 sa) i j' hiN hj',
          VW_setV sa ob N m0 hob hNL hL ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) (f2.2.1 sa) i j' hiN hj',
          VW_setK sa ob N m0 hob hNL hL (mi.set64 sa (ob + j * 2) X) (f1.2.1 sa) j j' hjN hj',
          VW_setV sa ob N m0 hob hNL hL mi hsz j j' hjN hj']
      have hKf : ∀ j', j' < N → KW sa ob ((((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y).set64 sa (ob + i * 2 + 1) Yk) j' =
          if i = j' then Yk else if j = j' then q else KW sa ob mi j' := fun j' hj' => by
        rw [KW_setK sa ob N m0 hob hNL hL (((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y) (f3.2.1 sa) i j' hiN hj',
          KW_setV sa ob N m0 hob hNL hL ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) (f2.2.1 sa) i j' hiN hj',
          KW_setK sa ob N m0 hob hNL hL (mi.set64 sa (ob + j * 2) X) (f1.2.1 sa) j j' hjN hj',
          KW_setV sa ob N m0 hob hNL hL mi hsz j j' hjN hj']
      have hr01 : ∀ y : Word, y.toNat < 2 →
          rdW (((((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y).set64 sa (ob + i * 2 + 1) Yk).arr64 sa) y = rdW (mi.arr64 sa) y := fun y hy => by
        rw [rd01_setK sa ob N m0 hob hNL hL (((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) Y) (f3.2.1 sa) i hiN Yk y hy,
          rd01_setV sa ob N m0 hob hNL hL ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) (f2.2.1 sa) i hiN Y y hy,
          rd01_setK sa ob N m0 hob hNL hL (mi.set64 sa (ob + j * 2) X) (f1.2.1 sa) j hjN q y hy,
          rd01_setV sa ob N m0 hob hNL hL mi hsz j hjN X y hy]
      refine ⟨⟨f3.trans (GFr.set64 _ _ _ _), by rw [hr01 0 (by simp), h0], by rw [hr01 1 (by simp), h1],
        fun j' hj' => ?_, fun x hx => ?_⟩, fun _ => by rw [hV _ hiN]; simp, fun h => (h (by first | exact hm | trivial)).elim⟩
      · rw [SlotOK, hV j' hj', hKf j' hj']
        by_cases e : i = j'
        · subst e; simp only [↓reduceIte]
          exact .inr (.inr ⟨hm, hbY, hYc, hKY, UInt64.le_refl _, hi⟩)
        · simp only [e, ↓reduceIte]
          by_cases e' : j = j'
          · subst e'; simp only [↓reduceIte]; rw [hxn]; exact .inr (.inl ⟨hXl, hXc, hK⟩)
          · simp only [e', ↓reduceIte]; exact hslot j' hj'
      · rcases hnode x hx with ⟨j'', hj'', hmx⟩ | hf
        · by_cases e : j'' = i
          · subst e
            have := hmi x hmx; subst this
            right
            refine ⟨D, ?_, fun e he => ?_⟩
            · rw [← hD, hV _ hjN, ite_eq_right (Ne.symm hji)]; simp [hbx]
            · obtain ⟨hne, hl⟩ := hpath e he
              have hnej : walkW N (homeW (hsm x) N) e ≠ j := fun h' => hjnL (by rw [← h']; exact hl)
              rw [hV _ (hw e), ite_eq_right (Ne.symm hne), ite_eq_right (Ne.symm hnej)]; exact hl
          · by_cases e' : j'' = j
            · subst e'; left; refine ⟨i, hiN, ?_⟩; rw [hV _ hiN]; simp only [↓reduceIte]
              rw [← hmx, hYv]
            · left; exact ⟨j'', hj'', by rw [hV _ hj'', ite_eq_right (Ne.symm e), ite_eq_right (Ne.symm e')]; exact hmx⟩
        · right
          refine foundU_keep sa ob N n bt c hsm m0 hob hNL hL hbt hnN mi _ x hx (fun j' hj' hl => ?_) hN0 hf
          rw [hV _ hj', ite_eq_right (fun h' => hiL (by rw [h']; exact hl)), ite_eq_right (fun h' => hjnL (by rw [h']; exact hl))]
    · -- move to the free slot `j`
      simp only [show ¬ MARK ≤ rdW (mi.arr64 sa) (ob + j * 2) from hm, ↓reduceIte]
      have f1 : GFr sa m0 (mi.set64 sa (ob + j * 2) X) := hfr.trans (GFr.set64 _ _ _ _)
      have f2 : GFr sa m0 ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) := f1.trans (GFr.set64 _ _ _ _)
      have hV : ∀ j', j' < N → VW sa ob (((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) 0) j' =
          if i = j' then 0 else if j = j' then X else VW sa ob mi j' := fun j' hj' => by
        rw [VW_setV sa ob N m0 hob hNL hL ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) (f2.2.1 sa) i j' hiN hj',
          VW_setK sa ob N m0 hob hNL hL (mi.set64 sa (ob + j * 2) X) (f1.2.1 sa) j j' hjN hj',
          VW_setV sa ob N m0 hob hNL hL mi hsz j j' hjN hj']
      have hKf : ∀ j', j' < N → KW sa ob (((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) 0) j' =
          if j = j' then q else KW sa ob mi j' := fun j' hj' => by
        rw [KW_setV sa ob N m0 hob hNL hL ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) (f2.2.1 sa) i j' hiN hj',
          KW_setK sa ob N m0 hob hNL hL (mi.set64 sa (ob + j * 2) X) (f1.2.1 sa) j j' hjN hj',
          KW_setV sa ob N m0 hob hNL hL mi hsz j j' hjN hj']
      have hr01 : ∀ y : Word, y.toNat < 2 →
          rdW ((((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) 0).arr64 sa) y = rdW (mi.arr64 sa) y := fun y hy => by
        rw [rd01_setV sa ob N m0 hob hNL hL ((mi.set64 sa (ob + j * 2) X).set64 sa (ob + j * 2 + 1) q) (f2.2.1 sa) i hiN 0 y hy,
          rd01_setK sa ob N m0 hob hNL hL (mi.set64 sa (ob + j * 2) X) (f1.2.1 sa) j hjN q y hy,
          rd01_setV sa ob N m0 hob hNL hL mi hsz j hjN X y hy]
      refine ⟨⟨f2.trans (GFr.set64 _ _ _ _), by rw [hr01 0 (by simp), h0], by rw [hr01 1 (by simp), h1],
        fun j' hj' => ?_, fun x hx => ?_⟩, fun h => absurd ((mark_le_iff _).mp h) (by simp), fun _ => ?_⟩
      · rw [SlotOK, hV j' hj', hKf j' hj']
        by_cases e : i = j'
        · subst e; simp only [↓reduceIte]; exact .inl (by simp [UInt64.le_iff_toNat_le])
        · simp only [e, ↓reduceIte]
          by_cases e' : j = j'
          · subst e'; simp only [↓reduceIte]; rw [hxn]; exact .inr (.inl ⟨hXl, hXc, hK⟩)
          · simp only [e', ↓reduceIte]; exact hslot j' hj'
      · rcases hnode x hx with ⟨j'', hj'', hmx⟩ | hf
        · by_cases e : j'' = i
          · subst e
            have := hmi x hmx; subst this
            right
            refine ⟨D, ?_, fun e he => ?_⟩
            · rw [← hD, hV _ hjN, ite_eq_right (Ne.symm hji)]; simp [hbx]
            · obtain ⟨hne, hl⟩ := hpath e he
              have hnej : walkW N (homeW (hsm x) N) e ≠ j := fun h' => hjnL (by rw [← h']; exact hl)
              rw [hV _ (hw e), ite_eq_right (Ne.symm hne), ite_eq_right (Ne.symm hnej)]; exact hl
          · have e' : j'' ≠ j := fun h' => hm (by
              rw [← h', hmx, mark_le_iff, add_mark_toNat _ (by
                rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega)]; omega)
            left; exact ⟨j'', hj'', by rw [hV _ hj'', ite_eq_right (Ne.symm e), ite_eq_right (Ne.symm e')]; exact hmx⟩
        · right
          refine foundU_keep sa ob N n bt c hsm m0 hob hNL hL hbt hnN mi _ x hx (fun j' hj' hl => ?_) hN0 hf
          rw [hV _ hj', ite_eq_right (fun h' => hiL (by rw [h']; exact hl)), ite_eq_right (fun h' => hjnL (by rw [h']; exact hl))]
      · rw [hV _ hiN, ite_eq_left rfl, mark_le_iff]; simp

variable (G : Mem → Word → Word) (hGh : ∀ mi : Mem, GFr sa m0 mi → ∀ x K, KPm x K → G mi K = hsm x)
  (hN0 : 0 < N)
include hGh hN0

/-- **The re-insertions at slot `i` keep the invariant** (`kinnerW`), and leave slot `i` unmarked. -/
theorem kinnerW_inv (i : Word) (hi : i < n) (e v : Word) (mi mf : Mem) (e' : Word)
    (hI : ReinsInv sa ob N n bt c KPm hsm m0 mi i) (hv1 : MARK ≤ v → v = VW sa ob mi i)
    (hv2 : ¬ MARK ≤ v → ¬ MARK ≤ VW sa ob mi i)
    (h : kinnerW sa G N ob bt i e v mi = some (mf, e')) :
    ReinsInv sa ob N n bt c KPm hsm m0 mf i ∧ ¬ MARK ≤ VW sa ob mf i := by
  fun_induction kinnerW sa G N ob bt i e v mi generalizing mf e' with
  | case1 => simp at h
  | case2 => simp at h
  | case3 e v mi hv he j hj ih =>
    have hvv := hv1 hv
    subst hvv
    have hiN : i < N := UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.lt_iff_toNat_lt.mp hi; have := UInt64.le_iff_toNat_le.mp hnN; omega)
    obtain ⟨-, -, hK, -, -⟩ := liveU_of_marked_slot sa ob n bt c KPm mi i i (hI.2.2.2.1 i hiN) hv (by omega)
    have hG := hGh mi hI.1 _ _ hK
    simp only [KW] at hG
    rw [hG] at hj
    obtain ⟨D, hD, hpath, hjr⟩ := kprobeW_res sa ob N bt m0 hob hNL hL mi i _ N.toNat 0 j (by simp)
      (fun e he => absurd he (by simp)) (by rw [show (0 : Word).toNat = 0 from rfl, walkW]; exact hj)
    have hjN : j < N := by rw [hD]; exact walkW_lt _ _ _ (homeW_lt _ _ hN0)
    obtain ⟨hI', hn1, hn2⟩ := place_inv sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN mi i hi hI hv j hjN D
      hD hpath hjr hN0
    exact ih mf e' hI' hn1 hn2 h
  | case4 e v mi hv =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, hv2 hv⟩

/-- Past an unmarked slot `i`, the invariant holds at `i + 1`. -/
theorem rinv_succ (mi : Mem) (i : Word) (hi : i < n) (hI : ReinsInv sa ob N n bt c KPm hsm m0 mi i)
    (hm : ¬ MARK ≤ VW sa ob mi i) : ReinsInv sa ob N n bt c KPm hsm m0 mi (i + 1) := by
  obtain ⟨hfr, h0, h1, hslot, hnode⟩ := hI
  refine ⟨hfr, h0, h1, fun j hj => ?_, hnode⟩
  rcases hslot j hj with h | h | ⟨hm', a, b, c', hij, hjn⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨hm', a, b, c', ?_, hjn⟩)
    have hne : i ≠ j := fun e => hm (e ▸ hm')
    have := UInt64.le_iff_toNat_le.mp hij
    have := UInt64.lt_iff_toNat_lt.mp hi
    have hne' : i.toNat ≠ j.toNat := fun e => hne (UInt64.toNat_inj.mp e)
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega

/-- **The re-insertion loop keeps the invariant** (`krehashW`), up to slot `n`. -/
theorem krehashW_inv (i e : Word) (mi mf : Mem) (hin : i ≤ n)
    (hI : ReinsInv sa ob N n bt c KPm hsm m0 mi i)
    (h : krehashW sa G N n ob bt i e mi = some mf) : ReinsInv sa ob N n bt c KPm hsm m0 mf n := by
  fun_induction krehashW sa G N n ob bt i e mi generalizing mf with
  | case1 => simp at h
  | case2 i e mi hi m1 e1 h1 ih =>
    obtain ⟨hI1, hm1⟩ := kinnerW_inv sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN G hGh hN0 i hi e _ mi m1 e1
      hI (fun _ => rfl) (fun h => h) h1
    refine ih mf ?_ (rinv_succ sa ob N n bt c KPm hsm m0 hob hNL hL hbt hnN G hGh hN0 m1 i hi hI1 hm1) h
    have := UInt64.lt_iff_toNat_lt.mp hi
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega
  | case3 i e mi hi =>
    simp at h; subst h
    have : i = n := UInt64.le_antisymm hin (UInt64.not_lt.mp hi)
    subst this; exact hI

end reins

end L.Arena
