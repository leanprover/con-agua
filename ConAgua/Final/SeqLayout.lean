module

public import ConAgua.Compiler.AbiSim
public import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import ConRon.Bridge.Grind

@[expose] public section

/-!
# `ca_check_seq`'s layout (lane parmode)

The sequential driver's entry 2 in place (`ca_check_seq`, `ConAgua/Compiler/Abi.lean`) rewrites
the table of a region that entry 1 left in the partition layout (`abiLayout`): `seqVals` gives
every word array its `ca_setup` slot and length, except `out` and the seed `ctlf` (no memory) and
the header `hdrf` (the first `hw` words of `out`'s slot); the byte arrays get no memory.

* `seqLayout`: that layout; `seqLayout_ok` (`Layout.Ok`).
* `seqMem0 m`: the L memory it holds when the region held `m` (`abiLayout`): `m`'s arrays, except
  `out`, `ctlf` and the byte arrays empty and `hdrf = (m.arr64 out).extract 0 hw`; `m`'s globals.
  `seq_memRel`: the stores `seqVals` relate it to the region.
* `seqMem m … lo hi`: `seqMem0 m` with `plo := lo`, `phi := hi`, `mode := 2` (what the entry runs on).
-/

namespace ConAgua.Final

open L L.Compiler

/-- What `ca_check_seq`'s layout needs of its parameters: `out` and `hdrf` are word arrays of the
layout (`hdrf` apart from `out` and `ctlf`); the minimum lengths (`Tab.min64`) hold in it: `out`
and `ctlf` (no memory) have none, `hdrf` (`hw` words) one of at most `hw`; none of the three is
the table-relative array (`Tab.tbl64`). -/
def seqParamsOk (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) : Bool :=
  (tab.dom64 (TieredArray.t0 out) && tab.dom64 (TieredArray.t0 hdrf) && decide (hdrf ≠ out) &&
    decide (hdrf ≠ ctlf) && decide (hw ≤ abiWords)) &&
  (decide (tab.min64 out = 0) && decide (tab.min64 ctlf = 0) && decide (tab.min64 hdrf ≤ hw)) &&
  ((tab.tbl64 out).isNone && (tab.tbl64 hdrf).isNone && (tab.tbl64 ctlf).isNone)

theorem seqParamsOk_spec {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat}
    (h : seqParamsOk tab out hdrf ctlf hw = true) :
    tab.dom64 (TieredArray.t0 out) = true ∧ tab.dom64 (TieredArray.t0 hdrf) = true ∧ hdrf ≠ out ∧
      hdrf ≠ ctlf ∧ hw ≤ abiWords := by
  simp only [seqParamsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

theorem seqParamsOk_min {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat}
    (h : seqParamsOk tab out hdrf ctlf hw = true) :
    tab.min64 out = 0 ∧ tab.min64 ctlf = 0 ∧ tab.min64 hdrf ≤ hw := by
  simp only [seqParamsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2.1.1, h.1.2.1.2, h.1.2.2⟩

theorem seqParamsOk_tbl {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat}
    (h : seqParamsOk tab out hdrf ctlf hw = true) :
    tab.tbl64 out = none ∧ tab.tbl64 hdrf = none ∧ tab.tbl64 ctlf = none := by
  simp only [seqParamsOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

/-- The table-relative array is none of `out`, `hdrf`, `ctlf`. -/
theorem seq_tbl_ne {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (h : seqParamsOk tab out hdrf ctlf hw = true)
    {s : TieredArray} {c : Nat} (hc : tab.tbl64 s = some c) :
    s ≠ TieredArray.t0 out ∧ s ≠ TieredArray.t0 hdrf ∧ s ≠ TieredArray.t0 ctlf := by
  obtain ⟨no, nh, nc⟩ := seqParamsOk_tbl h
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;> simp_all

/-- The slot of word position `p` in `ca_check_seq`'s layout: `hdrf` in `out`'s. -/
def seqSlot (tab : Tab) (out hdrf : ArrId) (p : Nat) : Nat :=
  if tab.wAt p = TieredArray.t0 hdrf then tab.pos64 (TieredArray.t0 out) else p

/-- `ca_check_seq`'s layout of the region at `base`: the byte positions get no memory, word
position `p` holds `tab.wAt p` (as `seqVals` fills it). -/
def seqLayout (tab : Tab) (base : Nat) (out hdrf ctlf : ArrId) (hw : Nat) : L.Compiler.Layout where
  tab
  T := base
  b p := if p < tab.nb then 0
    else if tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf then 0
    else if tab.wAt p = TieredArray.t0 hdrf then base + abiSlot * abiSlot64 tab out else base + abiOff tab p
  s p := if p < tab.nb then 0
    else if tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf then 0
    else if tab.wAt p = TieredArray.t0 hdrf then hw else abiSz tab (tab.wAt p)
  lo := base + abiSlot
  hi := base + abiSlot + abiStack
  nargs := 0

section
variable (tab : Tab) (base : Nat) (out hdrf ctlf : ArrId) (hw : Nat)
@[simp] theorem seqLayout_tab : (seqLayout tab base out hdrf ctlf hw).tab = tab := rfl
@[simp] theorem seqLayout_T : (seqLayout tab base out hdrf ctlf hw).T = base := rfl
@[simp] theorem seqLayout_lo : (seqLayout tab base out hdrf ctlf hw).lo = base + abiSlot := rfl
@[simp] theorem seqLayout_hi : (seqLayout tab base out hdrf ctlf hw).hi = base + abiSlot + abiStack := rfl
@[simp] theorem seqLayout_nargs : (seqLayout tab base out hdrf ctlf hw).nargs = 0 := rfl
theorem seqLayout_b8 {p : Nat} (hp : p < tab.nb) : (seqLayout tab base out hdrf ctlf hw).b p = 0 := by
  simp [seqLayout, hp]
theorem seqLayout_s8 {p : Nat} (hp : p < tab.nb) : (seqLayout tab base out hdrf ctlf hw).s p = 0 := by
  simp [seqLayout, hp]
theorem seqLayout_b64 {p : Nat} (hp : tab.nb ≤ p) : (seqLayout tab base out hdrf ctlf hw).b p =
    if tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf then 0
    else if tab.wAt p = TieredArray.t0 hdrf then base + abiSlot * abiSlot64 tab out else base + abiOff tab p := by
  simp [seqLayout, show ¬ p < tab.nb by omega]
theorem seqLayout_s64 {p : Nat} (hp : tab.nb ≤ p) : (seqLayout tab base out hdrf ctlf hw).s p =
    if tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf then 0
    else if tab.wAt p = TieredArray.t0 hdrf then hw else abiSz tab (tab.wAt p) := by
  simp [seqLayout, show ¬ p < tab.nb by omega]
end

section
variable {tab : Tab} {base : Nat} {out hdrf ctlf : ArrId} {hw : Nat}

/-- `out`'s position has a slot. -/
theorem seq_out_slot (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true) :
    2 ≤ tab.pos64 (TieredArray.t0 out) ∧ tab.pos64 (TieredArray.t0 out) < tab.nslot ∧
      abiSlot64 tab out = tab.pos64 (TieredArray.t0 out) := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  obtain ⟨dout, -⟩ := seqParamsOk_spec hp
  have := tab.pos64_lt dout
  refine ⟨by omega, slot_lt_nslot hok hnb this.2 (by rw [tab.wAt_pos64 dout]; exact (seqParamsOk_tbl hp).1), ?_⟩
  simp [abiSlot64, Tab.slotOf_eq hnb]

/-- A byte at word position `p` is in slot `seqSlot p` (`≥ 2`, a slot of the region), or (the
table-relative array) in `InTbl`; its array is not `out` or `ctlf`. -/
theorem seq_in64 (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    {p x : Nat} (hp1 : tab.nb ≤ p) (hp' : p < tab.nb + tab.nw) (h : (seqLayout tab base out hdrf ctlf hw).In64 p x) :
    ¬ (tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf) ∧
      ((2 ≤ seqSlot tab out hdrf p ∧ seqSlot tab out hdrf p < tab.nslot ∧
        InSlot base (seqSlot tab out hdrf p) x ∧
        (tab.wAt p ≠ TieredArray.t0 hdrf → tab.tbl64 (tab.wAt p) = none)) ∨
      (∃ c, tab.tbl64 (tab.wAt p) = some c ∧ InTbl tab base x)) := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  obtain ⟨-, -, -, -, hhw⟩ := seqParamsOk_spec hp
  obtain ⟨so1, so2, so3⟩ := seq_out_slot hok hp
  obtain ⟨h1, h2⟩ := h
  rw [seqLayout_b64 _ _ _ _ _ _ hp1] at h1; rw [seqLayout_b64 _ _ _ _ _ _ hp1, seqLayout_s64 _ _ _ _ _ _ hp1] at h2
  by_cases hs : tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf
  · simp only [hs, ite_true] at h1 h2; omega
  · simp only [hs, ite_false] at h1 h2
    refine ⟨hs, ?_⟩
    by_cases hh : tab.wAt p = TieredArray.t0 hdrf
    · simp only [hh, ite_true] at h1 h2
      refine .inl ⟨by simp only [seqSlot, hh, ite_true]; omega, by simp only [seqSlot, hh, ite_true]; exact so2, ?_,
        fun e => absurd hh e⟩
      simp only [seqSlot, hh, ite_true]; rw [so3] at h1 h2
      unfold InSlot; simp only [abiSlot, abiWords] at h1 h2 hhw ⊢; omega
    · simp only [hh, ite_false] at h1 h2
      cases hc : tab.tbl64 (tab.wAt p) with
      | none =>
        rw [abiOff_slot hc, Tab.slotOf_eq hnb] at h1 h2; rw [abiSz_slot hc] at h2
        refine .inl ⟨by simp only [seqSlot, hh, ite_false]; omega,
          by simp only [seqSlot, hh, ite_false]; exact slot_lt_nslot hok hnb hp' hc, ?_, fun _ => rfl⟩
        simp only [seqSlot, hh, ite_false]
        unfold InSlot; simp only [abiSlot, abiWords] at h1 h2 ⊢; omega
      | some c =>
        rw [abiOff_tbl hc] at h1 h2; rw [abiSz_tbl hc] at h2
        exact .inr ⟨c, rfl, abiTabOk_inTbl hok hc h1 h2⟩

/-- Table bytes are in slot `0`. -/
theorem seq_inTab (hok : abiTabOk tab = true) {x : Nat} (h : (seqLayout tab base out hdrf ctlf hw).InTab x) :
    InSlot base 0 x ∧ x < base + 2 ^ 31 := by
  obtain ⟨-, htab, -⟩ := abiTabOk_spec hok
  unfold Layout.InTab Layout.tabEnd at h
  simp only [seqLayout_T, seqLayout_tab, seqLayout_nargs] at h
  unfold InSlot abiSlot; omega

/-- Stack bytes are in slot `1`. -/
theorem seq_inStack {x : Nat} (h : (seqLayout tab base out hdrf ctlf hw).InStack x) : InSlot base 1 x := by
  unfold Layout.InStack at h
  simp only [seqLayout_lo, seqLayout_hi] at h
  unfold InSlot; simp only [abiSlot, abiStack] at h ⊢; omega

theorem seq_notIn8 {p x : Nat} (hp : p < tab.nb) : ¬ (seqLayout tab base out hdrf ctlf hw).In p x := by
  unfold Layout.In; rw [seqLayout_b8 _ _ _ _ _ _ hp, seqLayout_s8 _ _ _ _ _ _ hp]; omega

theorem seq_inArr (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true) {x : Nat}
    (h : (seqLayout tab base out hdrf ctlf hw).InArr x) :
    (∃ j, 2 ≤ j ∧ j < tab.nslot ∧ InSlot base j x) ∨ InTbl tab base x := by
  obtain ⟨p, hp', hx⟩ := h
  simp only [seqLayout_tab] at hp'
  by_cases hb : p < tab.nb
  · exact absurd hx (seq_notIn8 hb)
  · obtain ⟨-, ⟨h2, hlt, hs, -⟩ | ⟨-, -, ht⟩⟩ :=
      seq_in64 hok hp (by omega) hp' (Layout.In.to64 (by simp only [seqLayout_tab]; omega) hx)
    · exact .inl ⟨_, h2, hlt, hs⟩
    · exact .inr ht

/-- A byte outside the region is in no part of the layout. -/
theorem seq_out (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    {blen : Nat} (hneed : abiNeed tab ≤ blen) {x : Nat} (hx : x < base ∨ base + blen ≤ x) :
    ¬ (seqLayout tab base out hdrf ctlf hw).InStack x ∧ ¬ (seqLayout tab base out hdrf ctlf hw).InArr x ∧
      ¬ (seqLayout tab base out hdrf ctlf hw).InTab x := by
  have hns := two_le_nslot hok
  simp only [abiNeed] at hneed
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 := seq_inStack h
    have := h1.lt (n := tab.nslot) (by omega)
    unfold InSlot at h1; omega
  · rcases seq_inArr hok hp h with ⟨j, -, hj, h1⟩ | ⟨h1, h2⟩
    · have := h1.lt hj
      unfold InSlot at h1; omega
    · have := Nat.mul_le_mul_left abiSlot hns; simp only [abiSlot] at *; omega
  · have h1 := (seq_inTab hok h).1
    have := h1.lt (n := tab.nslot) (by omega)
    unfold InSlot at h1; omega

/-- The trampoline's save area (the 32 bytes past the table) is in the table's slot, in its first
`2^31` bytes, and in no array and not in the L stack. -/
theorem seq_save (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true) {x : Nat}
    (h1 : (seqLayout tab base out hdrf ctlf hw).tabEnd ≤ x) (h2 : x < (seqLayout tab base out hdrf ctlf hw).tabEnd + 32) :
    base ≤ x ∧ x < base + 2 ^ 31 ∧ ¬ (seqLayout tab base out hdrf ctlf hw).InStack x ∧
      ¬ (seqLayout tab base out hdrf ctlf hw).InArr x := by
  obtain ⟨-, htab, -⟩ := abiTabOk_spec hok
  simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs] at h1 h2
  refine ⟨by omega, by omega, fun h => ?_, fun h => ?_⟩
  · have := seq_inStack h
    unfold InSlot abiSlot at this; omega
  · rcases seq_inArr hok hp h with ⟨j, hj, -, h3⟩ | ⟨h3, -⟩
    · have : abiSlot * 2 ≤ abiSlot * j := Nat.mul_le_mul_left _ hj
      unfold InSlot at h3; simp only [abiSlot] at this h3; omega
    · omega

theorem seqLayout_ok (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    (hfit : base + abiNeed tab < 2 ^ 64) : (seqLayout tab base out hdrf ctlf hw).Ok := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  obtain ⟨dout, dhdr, hho, hhc, hhw⟩ := seqParamsOk_spec hp
  obtain ⟨so1, so2, so3⟩ := seq_out_slot hok hp
  have hge := abiNeed_ge hok
  have hslot : ∀ j, j < tab.nslot → base + abiSlot * j + abiSlot < 2 ^ 64 := fun j hj => by
    have := (show InSlot base j (base + abiSlot * j) by unfold InSlot; simp only [abiSlot]; omega).lt hj
    simp only [abiNeed, abiSlot] at hfit this ⊢; omega
  constructor
  · simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega
  · simp only [seqLayout_hi, abiSlot, abiStack]; omega
  · simp only [seqLayout_lo, seqLayout_hi]; omega
  · intro p hp'
    simp only [seqLayout_tab] at hp' ⊢
    by_cases hb : p < tab.nb
    · rw [seqLayout_b8 _ _ _ _ _ _ hb, seqLayout_s8 _ _ _ _ _ _ hb]; omega
    rw [seqLayout_b64 _ _ _ _ _ _ (by omega), seqLayout_s64 _ _ _ _ _ _ (by omega),
      show tab.wd p = 8 by simp [Tab.wd, hb]]
    split
    · simp
    · split
      · rw [so3]; have := hslot _ so2; simp only [abiSlot, abiWords] at this hhw ⊢; omega
      · cases hc : tab.tbl64 (tab.wAt p) with
        | none =>
          rw [abiOff_slot hc, abiSz_slot hc, Tab.slotOf_eq hnb]
          have := hslot _ (slot_lt_nslot hok hnb hp' hc); simp only [abiSlot, abiWords] at this ⊢; omega
        | some c =>
          rw [abiOff_tbl hc, abiSz_tbl hc]
          have := abiTabOk_tbl hok hc; omega
  · intro x h1 h2
    exact absurd (InSlot.eq (seq_inTab hok h1).1 (seq_inStack h2)) (by omega)
  · intro x h1 h2
    rcases seq_inArr hok hp h2 with ⟨j, hj, -, hs⟩ | ht
    · exact absurd (InSlot.eq (seq_inTab hok h1).1 hs) (by omega)
    · unfold Layout.InTab Layout.tabEnd at h1
      simp only [seqLayout_T, seqLayout_tab, seqLayout_nargs] at h1
      unfold InTbl at ht; omega
  · intro x h1 h2
    rcases seq_inArr hok hp h2 with ⟨j, hj, -, hs⟩ | ht
    · exact absurd (InSlot.eq (seq_inStack h1) hs) (by omega)
    · exact ht.not_slot (Nat.le_refl _) (seq_inStack h1)
  · intro p hpa q hqb hpq x h1 h2
    simp only [seqLayout_tab] at hpa hqb
    by_cases hbp : p < tab.nb
    · exact absurd h1 (seq_notIn8 hbp)
    by_cases hbq : q < tab.nb
    · exact absurd h2 (seq_notIn8 hbq)
    obtain ⟨ha', ⟨-, -, s1, -⟩ | ⟨c, hc, t1⟩⟩ :=
      seq_in64 hok hp (by omega) hpa (Layout.In.to64 (by simp only [seqLayout_tab]; omega) h1) <;>
    obtain ⟨hb', ⟨-, -, s2, -⟩ | ⟨c', hc', t2⟩⟩ :=
      seq_in64 hok hp (by omega) hqb (Layout.In.to64 (by simp only [seqLayout_tab]; omega) h2)
    · have e := InSlot.eq s1 s2
      unfold seqSlot at e
      have hwo : tab.wAt (tab.pos64 (TieredArray.t0 out)) = TieredArray.t0 out := tab.wAt_pos64 dout
      by_cases e1 : tab.wAt p = TieredArray.t0 hdrf <;> by_cases e2 : tab.wAt q = TieredArray.t0 hdrf
      · exact hpq (tab.wAt_inj hpa hqb (e1.trans e2.symm))
      · rw [ite_eq_left e1, ite_eq_right e2] at e; rw [← e, hwo] at hb'; exact hb' (.inl rfl)
      · rw [ite_eq_right e1, ite_eq_left e2] at e; rw [e, hwo] at ha'; exact ha' (.inl rfl)
      · rw [ite_eq_right e1, ite_eq_right e2] at e; exact hpq e
    · exact t2.not_slot (by unfold seqSlot; split <;> omega) s1
    · exact t1.not_slot (by unfold seqSlot; split <;> omega) s2
    · exact hpq (tbl_pos_eq hok hpa hqb hc hc')
  · intro s hs
    simp only [seqLayout_tab] at hs ⊢
    obtain ⟨mo, mc, mh⟩ := seqParamsOk_min hp
    have := tab.pos64_lt hs
    rw [seqLayout_s64 _ _ _ _ _ _ this.1, tab.wAt_pos64 hs]
    split
    · rename_i h
      rcases h with rfl | rfl
      · exact Nat.le_of_eq mo
      · exact Nat.le_of_eq mc
    · split
      · rename_i _ h; subst h; exact mh
      · exact min64_le_abiSz hok s
  · intro s c hs hc
    simp only [seqLayout_tab, seqLayout_T] at hs hc ⊢
    have := tab.pos64_lt hs
    obtain ⟨no, nh, nc⟩ := seq_tbl_ne hp hc
    have hc' : tab.tbl64 (tab.wAt (tab.pos64 s)) = some c := by rw [tab.wAt_pos64 hs]; exact hc
    rw [seqLayout_b64 _ _ _ _ _ _ this.1, tab.wAt_pos64 hs, ite_eq_right (fun h => h.elim no nc), ite_eq_right nh,
      abiOff_tbl hc']

end

/-! ## The memory -/

/-- `ca_check_seq`'s memory before the globals: `m`'s word arrays and globals, but `out`, `ctlf`
and the byte arrays empty and `hdrf` the first `hw` words of `out`. -/
def seqMem0 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) : Mem where
  bytes _ := #[]
  words s := if s = ↑out ∨ s = ↑ctlf then #[] else if s = ↑hdrf then (m.arr64 out).extract 0 hw else m.words s
  glob := m.glob

/-- `M` with `plo := lo`, `phi := hi`, `mode := w` (what `ca_check_seq_g` stores). -/
def seqNext (M : Mem) (mode plo phi : GVar) (w lo hi : Word) : Mem :=
  ((M.setG plo lo).setG phi hi).setG mode w

/-- **The memory `ca_check_seq_m` runs `check` on**: `seqMem0 m` with `plo := lo`, `phi := hi`,
`mode := w`. -/
def seqMemW (m : Mem) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (w lo hi : Word) : Mem :=
  seqNext (seqMem0 m out hdrf ctlf hw) mode plo phi w lo hi

/-- **The memory `ca_check_seq` runs `check` on**: `seqMem0 m` with `plo := lo`, `phi := hi`,
`mode := 2`. -/
def seqMem (m : Mem) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (lo hi : Word) : Mem :=
  seqMemW m mode plo phi out hdrf ctlf hw 2 lo hi

theorem seqMem0_arr8 (m : Mem) (out hdrf ctlf : ArrId) (hw a : Nat) :
    (seqMem0 m out hdrf ctlf hw).arr8 a = #[] := rfl

theorem seqMem0_arr64 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) (s : TieredArray) :
    (seqMem0 m out hdrf ctlf hw).arr64 s =
      if s = ↑out ∨ s = ↑ctlf then #[] else if s = ↑hdrf then (m.arr64 out).extract 0 hw else m.arr64 s := rfl

/-! ## The stores -/

theorem seqVals_length (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) :
    (seqVals tab out hdrf ctlf hw).length = (abiVals tab).length := by
  rw [abiVals_length tab]
  simp only [seqVals, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
    romVals_length, Tab.romWords, ← tab.romLen_eq]
  omega

theorem seqVals_getElem? (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) :
    (seqVals tab out hdrf ctlf hw)[0]? = some (.addr (abiSlot + abiStack)) ∧
    (seqVals tab out hdrf ctlf hw)[1]? = some (.addr abiSlot) ∧
    (∀ p < tab.nb + tab.nw, (seqVals tab out hdrf ctlf hw)[2 + p]? = some (seqBase tab out hdrf ctlf p) ∧
      (seqVals tab out hdrf ctlf hw)[2 + (tab.nb + tab.nw) + p]? = some (seqLen tab out hdrf ctlf hw p) ∧
      (seqVals tab out hdrf ctlf hw)[2 + 2 * (tab.nb + tab.nw) + p]? = some (seqLen32 tab out hdrf ctlf hw p)) ∧
    (∀ i, (seqVals tab out hdrf ctlf hw)[2 + 3 * (tab.nb + tab.nw) + i]? = (romVals tab.rom)[i]?) := by
  refine ⟨rfl, rfl, fun p hp => ⟨?_, ?_, ?_⟩, fun i => ?_⟩
  · simp only [seqVals]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, show 2 + p - (0 + 1 + 1) = p by omega,
      List.getElem?_map, List.getElem?_range hp, Option.map_some]
  · simp only [seqVals]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
      show 2 + (tab.nb + tab.nw) + p - (0 + 1 + 1 + (tab.nb + tab.nw)) = p by omega,
      List.getElem?_map, List.getElem?_range hp, Option.map_some]
  · simp only [seqVals]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
      show 2 + 2 * (tab.nb + tab.nw) + p - (0 + 1 + 1 + (tab.nb + tab.nw) + (tab.nb + tab.nw)) = p by omega,
      List.getElem?_map, List.getElem?_range hp, Option.map_some]
  · simp only [seqVals]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]
    congr 1; omega

theorem seqVals_noRax (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) :
    ∀ v ∈ seqVals tab out hdrf ctlf hw, v.noRax := by
  intro v hv
  simp only [seqVals, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hv
  rcases hv with ((((h1 | h1) | h1) | h1) | h1) | h1
  · subst h1; trivial
  · subst h1; trivial
  · obtain ⟨_, _, rfl⟩ := h1; simp only [seqBase]; split <;> (try split) <;> (try split) <;> trivial
  · obtain ⟨_, _, rfl⟩ := h1; simp only [seqLen]; split <;> (try split) <;> (try split) <;> trivial
  · obtain ⟨_, _, rfl⟩ := h1; simp only [seqLen32]; split <;> (try split) <;> (try split) <;> trivial
  · exact abiVals_noRax tab v (by simp only [abiVals]; exact List.mem_append_right _ h1)

/-- The base word `ca_check_seq` writes at descriptor position `p`. -/
theorem seqBase_val {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (R : Reg64s) {base : Nat}
    (hR : R.r8.toNat = base) {p : Nat} (hfo : base + abiSlot * abiSlot64 tab out < 2 ^ 64)
    (hfp : base + abiOff tab p < 2 ^ 64) :
    UInt64.ofBitVec ((seqBase tab out hdrf ctlf p).val R) =
      UInt64.ofNat ((seqLayout tab base out hdrf ctlf hw).b p) := by
  unfold seqBase
  by_cases hb : p < tab.nb
  · rw [seqLayout_b8 _ _ _ _ _ _ hb]; simp only [hb, ite_true, SVal.val]; rfl
  rw [seqLayout_b64 _ _ _ _ _ _ (by omega)]
  simp only [hb, ite_false]
  by_cases h1 : tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf
  · simp only [h1, ite_true, SVal.val]; rfl
  · simp only [h1, ite_false]
    by_cases h2 : tab.wAt p = TieredArray.t0 hdrf
    · simp only [h2, ite_true]; rw [addr_val _ _ (by omega)]; try rw [hR]
    · simp only [h2, ite_false]; rw [addr_val _ _ (by omega)]; try rw [hR]

theorem seqLen_val {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (R : Reg64s) (base p : Nat) :
    UInt64.ofBitVec ((seqLen tab out hdrf ctlf hw p).val R) =
      UInt64.ofNat ((seqLayout tab base out hdrf ctlf hw).s p) := by
  unfold seqLen
  by_cases hb : p < tab.nb
  · rw [seqLayout_s8 _ _ _ _ _ _ hb]; simp only [hb, ite_true, SVal.val]; rfl
  rw [seqLayout_s64 _ _ _ _ _ _ (by omega)]
  simp only [hb, ite_false]
  by_cases h1 : tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf
  · simp only [h1, ite_true, SVal.val] <;> rfl
  · simp only [h1, ite_false]
    by_cases h2 : tab.wAt p = TieredArray.t0 hdrf
    · simp only [h2, ite_true, SVal.val] <;> rfl
    · simp only [h2, ite_false, SVal.val] <;> rfl

theorem seqLen32_val {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (R : Reg64s) (base p : Nat)
    (hp : tab.nb ≤ p) :
    UInt64.ofBitVec ((seqLen32 tab out hdrf ctlf hw p).val R) =
      UInt64.ofNat (2 * (seqLayout tab base out hdrf ctlf hw).s p) := by
  unfold seqLen32
  rw [seqLayout_s64 _ _ _ _ _ _ hp]
  simp only [show ¬ p < tab.nb by omega, ite_false]
  by_cases h1 : tab.wAt p = TieredArray.t0 out ∨ tab.wAt p = TieredArray.t0 ctlf
  · simp only [h1, ite_true, SVal.val] <;> rfl
  · simp only [h1, ite_false]
    by_cases h2 : tab.wAt p = TieredArray.t0 hdrf
    · simp only [h2, ite_true, SVal.val]
    · simp only [h2, ite_false, SVal.val]

/-- **The stores of `ca_check_seq`**, on a region that holds `m` in the partition layout, relate
it to `seqMem0 m` in `ca_check_seq`'s layout. -/
theorem seq_memRel {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (hok : abiTabOk tab = true)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) {base inp n pins np : Nat}
    (hfit : base + abiNeed tab < 2 ^ 64) (R : Reg64s) (hR : R.r8.toNat = base) (m : Mem) (d : DataMem)
    (hm : MemRel (abiLayout tab base inp n pins np) m d) :
    MemRel (seqLayout tab base out hdrf ctlf hw) (seqMem0 m out hdrf ctlf hw)
      (stores R base d 0 (seqVals tab out hdrf ctlf hw)) := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  obtain ⟨dout, dhdr, hho, hhc, hhw⟩ := seqParamsOk_spec hp
  obtain ⟨so1, so2, so3⟩ := seq_out_slot hok hp
  have hge := abiNeed_ge hok
  have hL := seqVals_length tab out hdrf ctlf hw
  rw [abiVals_length tab] at hL
  have hend : base + 8 * (seqVals tab out hdrf ctlf hw).length ≤ 2 ^ 64 := by
    rw [hL]; omega
  have honly := stores_only R base (seqVals tab out hdrf ctlf hw) d 0 (by simpa using hend)
  simp only [Nat.add_zero] at honly
  obtain ⟨g0, g1, gw, grom⟩ := seqVals_getElem? tab out hdrf ctlf hw
  have hW : ∀ i v, (seqVals tab out hdrf ctlf hw)[i]? = some v →
      rdW (stores R base d 0 (seqVals tab out hdrf ctlf hw)) (A (base + 8 * i)) = some (UInt64.ofBitVec (v.val R)) :=
    fun i v hv => stores_rdW? R base _ _ i v hv hend
  have hpo := tab.pos64_lt dout
  have hout64 : (m.arr64 out).size = abiWords := by
    rw [hm.size64 _ dout]; simp only [abiLayout_tab]
    rw [abiLayout_s64 _ _ _ _ _ _ (by omega), tab.wAt_pos64 dout, abiSz_slot (seqParamsOk_tbl hp).1]
  -- slots `2 ≤ j < nslot` lie past the stores
  have harr : ∀ j, 2 ≤ j → j < tab.nslot → ∀ i, i < abiWords →
      rdW (stores R base d 0 (seqVals tab out hdrf ctlf hw)) (A (base + abiSlot * j + 8 * i)) =
        rdW d (A (base + abiSlot * j + 8 * i)) := by
    intro j hj2 hj i hi
    have hle : abiSlot * j + abiSlot ≤ abiSlot * tab.nslot := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    have h2 : abiSlot * 2 ≤ abiSlot * j := Nat.mul_le_mul_left _ hj2
    refine honly.rdW_eq ?_ (Or.inr ?_)
    · simp only [abiNeed, abiSlot, abiWords] at hfit hle hi ⊢; omega
    · rw [hL]; simp only [abiSlot] at h2 ⊢; omega
  obtain ⟨no, -, -⟩ := seqParamsOk_tbl hp
  -- a word position's array lies past the stores
  have hoff : ∀ p, tab.nb ≤ p → p < tab.nb + tab.nw →
      base + abiOff tab p + 8 * abiSz tab (tab.wAt p) ≤ base + abiNeed tab ∧
      (∀ i, i < abiSz tab (tab.wAt p) →
        rdW (stores R base d 0 (seqVals tab out hdrf ctlf hw)) (A (base + abiOff tab p + 8 * i)) =
          rdW d (A (base + abiOff tab p + 8 * i))) := by
    intro p hp1 hp'
    cases hc : tab.tbl64 (tab.wAt p) with
    | none =>
      rw [abiOff_slot hc, abiSz_slot hc, Tab.slotOf_eq hnb]
      have hj := slot_lt_nslot hok hnb hp' hc
      have hle : abiSlot * p + abiSlot ≤ abiSlot * tab.nslot := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      refine ⟨by simp only [abiNeed, abiSlot, abiWords] at hle ⊢; omega, fun i hi => harr p (by omega) hj i hi⟩
    | some c =>
      rw [abiOff_tbl hc, abiSz_tbl hc]
      have := abiTabOk_tbl hok hc
      refine ⟨by omega, fun i hi => honly.rdW_eq ?_ (Or.inr ?_)⟩
      · omega
      · rw [hL]; simp only [Tab.romWords] at this ⊢; omega
  constructor
  · intro a ha
    simp only [seqLayout_tab] at ha ⊢
    rw [seqLayout_s8 _ _ _ _ _ _ (tab.pos8_lt ha)]; simp [seqMem0_arr8]
  · intro s hs
    simp only [seqLayout_tab] at hs ⊢
    have := tab.pos64_lt hs
    rw [seqMem0_arr64, seqLayout_s64 _ _ _ _ _ _ this.1, tab.wAt_pos64 hs]
    split
    · rfl
    · split
      · simp only [Array.size_extract, hout64]; omega
      · have := hm.size64 s hs
        simp only [abiLayout_tab] at this
        rw [this, abiLayout_s64 _ _ _ _ _ _ (by omega), tab.wAt_pos64 hs]
  · intro a _ i hi; simp [seqMem0_arr8] at hi
  · intro s hs i hi
    simp only [seqLayout_tab] at hs ⊢
    have hps := tab.pos64_lt hs
    have e := seqMem0_arr64 m out hdrf ctlf hw s
    rw [seqLayout_b64 _ _ _ _ _ _ hps.1, tab.wAt_pos64 hs]
    by_cases h1 : s = ↑out ∨ s = ↑ctlf
    · simp only [e, h1, ite_true] at hi; simp at hi
    · simp only [h1, ite_false]
      simp only [e, ite_eq_right h1] at hi ⊢
      by_cases h2 : s = ↑hdrf
      · simp only [ite_eq_left h2, Array.size_extract, hout64] at hi ⊢
        rw [so3, harr _ so1 so2 i (by omega)]
        have := hm.get64 _ dout i (by omega)
        simp only [abiLayout_tab] at this
        rw [abiLayout_b64 _ _ _ _ _ _ (by omega), abiOff_slot (by rw [tab.wAt_pos64 dout]; exact no),
          Tab.slotOf_eq hnb] at this
        rw [this]; simp
      · simp only [ite_eq_right h2] at hi ⊢
        have hs' := hm.size64 s hs
        simp only [abiLayout_tab] at hs'
        rw [abiLayout_s64 _ _ _ _ _ _ (by omega)] at hs'
        have := (hoff _ hps.1 hps.2).2 i (by rw [← hs']; exact hi)
        rw [this]
        have := hm.get64 s hs i hi
        simp only [abiLayout_tab] at this
        rw [abiLayout_b64 _ _ _ _ _ _ (by omega)] at this
        exact this
  · have := hW 1 _ g1
    rw [addr_val _ _ (by rw [hR]; simp only [abiSlot] at *; omega), hR] at this
    simpa only [seqLayout_T, seqLayout_lo] using this
  · intro p hp'
    simp only [seqLayout_tab] at hp'
    have := hW (2 + p) _ (gw p hp').1
    have hle : abiSlot * abiSlot64 tab out + abiSlot ≤ abiSlot * tab.nslot := by
      rw [so3, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ so2
    rw [seqBase_val (hw := hw) R hR (by simp only [abiNeed] at hfit; omega) (by
      by_cases hb : p < tab.nb
      · simp only [abiOff]; split
        · rename_i c hc; have := abiTabOk_tbl hok hc; omega
        · have : p < 2 := by omega
          have : abiSlot * tab.slotOf p ≤ abiSlot * 2 := Nat.mul_le_mul_left _ (by simp [Tab.slotOf_eq hnb]; omega)
          simp only [abiSlot] at *; omega
      · have := (hoff p (by omega) hp').1; omega)] at this
    simp only [seqLayout_T, Tab.dbase]
    rw [show (16 + 8 * (p : Int)).toNat = 8 * (2 + p) by omega]
    exact this
  · intro p hp'
    simp only [seqLayout_tab] at hp'
    have := hW (2 + (tab.nb + tab.nw) + p) _ (gw p hp').2.1
    rw [seqLen_val (tab := tab) R base p] at this
    simp only [seqLayout_T, seqLayout_tab, Tab.dlen]
    rw [show (16 + 8 * ((tab.nb : Int) + (tab.nw : Int)) + 8 * (p : Int)).toNat =
      8 * (2 + (tab.nb + tab.nw) + p) by omega]
    exact this
  · intro p hp1 hp'
    simp only [seqLayout_tab] at hp' hp1
    have := hW (2 + 2 * (tab.nb + tab.nw) + p) _ (gw p hp').2.2
    rw [seqLen32_val (tab := tab) R base p hp1] at this
    simp only [seqLayout_T, seqLayout_tab, Tab.dlen32]
    rw [show (16 + 16 * ((tab.nb : Int) + (tab.nw : Int)) + 8 * (p : Int)).toNat =
      8 * (2 + 2 * (tab.nb + tab.nw) + p) by omega]
    exact this
  · intro i hi
    simp only [seqLayout_T, seqLayout_tab]
    obtain ⟨w, hw1, hw2⟩ := romVals_byte tab.rom i hi
    have hv : (seqVals tab out hdrf ctlf hw)[2 + 3 * (tab.nb + tab.nw) + i / 8]? = some (.imm w) := by
      rw [grom]; exact hw1
    obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.mp hv
    have := stores_byte R base (seqVals tab out hdrf ctlf hw) d 0 (2 + 3 * (tab.nb + tab.nw) + i / 8) (i % 8) hlt
      (Nat.mod_lt _ (by omega)) (by simpa using hend)
    rw [hv'] at this
    simp only [SVal.val, UInt64.ofBitVec_toBitVec, hw2] at this
    rw [show base + 16 + 24 * (tab.nb + tab.nw) + i = base + 0 + 8 * (2 + 3 * (tab.nb + tab.nw) + i / 8) + i % 8 by omega]
    exact this
  · intro x hx
    exact honly.grows _ (hm.stack x hx)
  · intro x hx
    exact honly.grows _ (hm.res x hx)
  · intro g hg
    simp only [seqLayout_tab] at hg
    have := hm.glob g hg
    simp only [Layout.globAddr, Layout.globStart, abiLayout_T, abiLayout_tab] at this
    simp only [Layout.globAddr, Layout.globStart, seqLayout_T, seqLayout_tab]
    rw [honly.rdW_eq (by omega) (Or.inr (by rw [hL]; omega))]
    exact this

end ConAgua.Final
