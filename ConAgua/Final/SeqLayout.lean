import ConAgua.Final.ParAbi

/-!
# `ca_check_seq`'s layout (lane parmode)

The sequential driver's entry 2 in place (`ca_check_seq`, `ConAgua/Compiler/Abi.lean`) rewrites
the table of a region that entry 1 left in the partition layout (`abiLayout`): `seqVals` gives
every word array its `ca_start` slot and length, except `out` and the seed `ctlf` (no memory) and
the header `hdrf` (the first `hw` words of `out`'s slot); the byte arrays get no memory.

* `seqLayout`: that layout; `seqLayout_ok` (`Layout.Ok`).
* `seqMem0 m`: the L memory it holds when the region held `m` (`abiLayout`): `m`'s arrays, except
  `out`, `ctlf` and the byte arrays empty and `hdrf = (m.arr64 out).extract 0 hw`; `m`'s globals.
  `seq_memRel`: the stores `seqVals` relate it to the region.
* `seqMem m … lo hi`: `seqMem0 m` with `plo := lo`, `phi := hi`, `mode := 2` (what the entry runs on).
-/

namespace ConAgua.Final

open L L.Compiler

/-- What `ca_check_seq`'s layout needs of its parameters. -/
def seqParamsOk (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) : Bool :=
  decide (out < tab.nw) && decide (hdrf < tab.nw) && decide (hdrf ≠ out) && decide (hdrf ≠ ctlf) &&
    decide (hw ≤ abiWords)

theorem seqParamsOk_spec {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat}
    (h : seqParamsOk tab out hdrf ctlf hw = true) :
    out < tab.nw ∧ hdrf < tab.nw ∧ hdrf ≠ out ∧ hdrf ≠ ctlf ∧ hw ≤ abiWords := by
  simpa [seqParamsOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

/-- The slot word array `a` lives in: `hdrf` in `out`'s. -/
def seqSlot (out hdrf a : Nat) : Nat := if a = hdrf then out else a

theorem seqSlot_lt {nw out hdrf a : Nat} (hout : out < nw) (ha : a < nw) : seqSlot out hdrf a < nw := by
  unfold seqSlot; split <;> assumption

/-- `ca_check_seq`'s layout of the region at `base`. -/
def seqLayout (tab : Tab) (base : Nat) (out hdrf ctlf : ArrId) (hw : Nat) : L.Compiler.Layout where
  tab
  T := base
  b8 _ := 0
  s8 _ := 0
  b64 a := if a = out ∨ a = ctlf then 0 else base + abiSlot * abiSlot64 tab (seqSlot out hdrf a)
  s64 a := if a = out ∨ a = ctlf then 0 else if a = hdrf then hw else abiWords
  lo := base + abiSlot
  hi := base + abiSlot + abiStack
  nargs := 0

section
variable (tab : Tab) (base : Nat) (out hdrf ctlf : ArrId) (hw : Nat)
@[simp] theorem seqLayout_tab : (seqLayout tab base out hdrf ctlf hw).tab = tab := rfl
@[simp] theorem seqLayout_T : (seqLayout tab base out hdrf ctlf hw).T = base := rfl
@[simp] theorem seqLayout_b8 (a : Nat) : (seqLayout tab base out hdrf ctlf hw).b8 a = 0 := rfl
@[simp] theorem seqLayout_s8 (a : Nat) : (seqLayout tab base out hdrf ctlf hw).s8 a = 0 := rfl
@[simp] theorem seqLayout_lo : (seqLayout tab base out hdrf ctlf hw).lo = base + abiSlot := rfl
@[simp] theorem seqLayout_hi : (seqLayout tab base out hdrf ctlf hw).hi = base + abiSlot + abiStack := rfl
@[simp] theorem seqLayout_nargs : (seqLayout tab base out hdrf ctlf hw).nargs = 0 := rfl
theorem seqLayout_b64 (a : Nat) : (seqLayout tab base out hdrf ctlf hw).b64 a =
    if a = out ∨ a = ctlf then 0 else base + abiSlot * abiSlot64 tab (seqSlot out hdrf a) := rfl
theorem seqLayout_s64 (a : Nat) : (seqLayout tab base out hdrf ctlf hw).s64 a =
    if a = out ∨ a = ctlf then 0 else if a = hdrf then hw else abiWords := rfl
end

/-- Byte `x` is in slot `j` of the region at `base`. -/
def InSlot (base j x : Nat) : Prop := base + abiSlot * j ≤ x ∧ x < base + abiSlot * j + abiSlot

theorem InSlot.eq {base j j' x : Nat} (h : InSlot base j x) (h' : InSlot base j' x) : j = j' := by
  rcases Nat.lt_trichotomy j j' with h1 | h1 | h1
  · have : abiSlot * j + abiSlot ≤ abiSlot * j' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    unfold InSlot at *; omega
  · exact h1
  · have : abiSlot * j' + abiSlot ≤ abiSlot * j := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    unfold InSlot at *; omega

theorem InSlot.lt {base j x : Nat} (h : InSlot base j x) {n : Nat} (hj : j < n) :
    x < base + abiSlot * n := by
  have : abiSlot * j + abiSlot ≤ abiSlot * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  unfold InSlot at h; omega

section
variable {tab : Tab} {base : Nat} {out hdrf ctlf : ArrId} {hw : Nat}

/-- A byte of word array `a` is in slot `abiSlot64 (seqSlot a)`; `a` has memory. -/
theorem seq_in64 (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    {a x : Nat} (ha : a < tab.nw) (h : (seqLayout tab base out hdrf ctlf hw).In64 a x) :
    ¬ (a = out ∨ a = ctlf) ∧ seqSlot out hdrf a < tab.nw ∧
      InSlot base (abiSlot64 tab (seqSlot out hdrf a)) x := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  obtain ⟨hout, hhdr, -, -, hhw⟩ := seqParamsOk_spec hp
  unfold Layout.In64 at h
  rw [seqLayout_b64, seqLayout_s64] at h
  by_cases hs : a = out ∨ a = ctlf
  · simp only [hs, ite_true] at h; omega
  · simp only [hs, ite_false] at h
    refine ⟨hs, seqSlot_lt hout ha, ?_⟩
    have hle : (if a = hdrf then hw else abiWords) ≤ abiWords := by split <;> omega
    unfold InSlot
    simp only [abiWords, abiSlot] at hle h ⊢
    omega

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

theorem seq_notIn8 {a x : Nat} : ¬ (seqLayout tab base out hdrf ctlf hw).In8 a x := by
  unfold Layout.In8; simp

theorem seq_inArr (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true) {x : Nat}
    (h : (seqLayout tab base out hdrf ctlf hw).InArr x) :
    ∃ j, 2 ≤ j ∧ j < 2 + tab.nw ∧ InSlot base j x := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  rcases h with ⟨a, _, h⟩ | ⟨a, ha, h⟩
  · exact absurd h seq_notIn8
  · simp only [seqLayout_tab] at ha
    obtain ⟨-, hlt, hs⟩ := seq_in64 hok hp ha h
    have hj : abiSlot64 tab (seqSlot out hdrf a) < 2 + tab.nw := by
      simp only [abiSlot64, hnb]; omega
    exact ⟨abiSlot64 tab (seqSlot out hdrf a), by simp only [abiSlot64]; omega, hj, hs⟩

/-- A byte outside the region is in no part of the layout. -/
theorem seq_out (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    {blen : Nat} (hneed : abiNeed tab ≤ blen) {x : Nat} (hx : x < base ∨ base + blen ≤ x) :
    ¬ (seqLayout tab base out hdrf ctlf hw).InStack x ∧ ¬ (seqLayout tab base out hdrf ctlf hw).InArr x ∧
      ¬ (seqLayout tab base out hdrf ctlf hw).InTab x := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  have hn : abiNeed tab = abiSlot * (2 + tab.nw) := by simp [abiNeed, hnb]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 := seq_inStack h
    have := h1.lt (n := 2 + tab.nw) (by omega)
    unfold InSlot at h1; omega
  · obtain ⟨j, -, hj, h1⟩ := seq_inArr hok hp h
    have := h1.lt hj
    unfold InSlot at h1; omega
  · have h1 := (seq_inTab hok h).1
    have := h1.lt (n := 2 + tab.nw) (by omega)
    unfold InSlot at h1; omega

theorem seqLayout_ok (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    (hfit : base + abiNeed tab < 2 ^ 64) : (seqLayout tab base out hdrf ctlf hw).Ok := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  obtain ⟨hout, hhdr, hho, hhc, hhw⟩ := seqParamsOk_spec hp
  have hn : abiNeed tab = abiSlot * (2 + tab.nw) := by simp [abiNeed, hnb]
  constructor
  · simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]
    simp only [hn, abiSlot] at hfit; omega
  · simp only [seqLayout_hi, abiSlot, abiStack]; simp only [hn, abiSlot] at hfit; omega
  · simp only [seqLayout_lo, seqLayout_hi]; omega
  · intro a _; simp
  · intro a ha
    simp only [seqLayout_tab] at ha
    rw [seqLayout_b64, seqLayout_s64]
    split
    · simp
    · have hs : seqSlot out hdrf a < tab.nw := seqSlot_lt hout ha
      have hle : (if a = hdrf then hw else abiWords) ≤ abiWords := by split <;> omega
      have hj : abiSlot64 tab (seqSlot out hdrf a) < 2 + tab.nw := by
        have := hs; simp only [abiSlot64, hnb]; omega
      have := (show InSlot base (abiSlot64 tab (seqSlot out hdrf a)) (base + abiSlot * abiSlot64 tab (seqSlot out hdrf a)) by
        unfold InSlot; simp only [abiSlot]; omega).lt hj
      simp only [hn, abiSlot, abiWords] at hfit hle this ⊢
      omega
  · intro x h1 h2
    exact absurd (InSlot.eq (seq_inTab hok h1).1 (seq_inStack h2)) (by omega)
  · intro x h1 h2
    obtain ⟨j, hj, -, hs⟩ := seq_inArr hok hp h2
    exact absurd (InSlot.eq (seq_inTab hok h1).1 hs) (by omega)
  · intro x h1 h2
    obtain ⟨j, hj, -, hs⟩ := seq_inArr hok hp h2
    exact absurd (InSlot.eq (seq_inStack h1) hs) (by omega)
  · intro a _ b _ _ x h; exact absurd h seq_notIn8
  · intro a ha b hb hab x h1 h2
    simp only [seqLayout_tab] at ha hb
    obtain ⟨ha', hsa, s1⟩ := seq_in64 hok hp ha h1
    obtain ⟨hb', hsb, s2⟩ := seq_in64 hok hp hb h2
    have e := InSlot.eq s1 s2
    simp only [abiSlot64] at e
    have e' : seqSlot out hdrf a = seqSlot out hdrf b := by omega
    unfold seqSlot at e'
    by_cases h1 : a = hdrf <;> by_cases h2 : b = hdrf
    · exact hab (h1.trans h2.symm)
    · rw [if_pos h1, if_neg h2] at e'; exact hb' (Or.inl e'.symm)
    · rw [if_neg h1, if_pos h2] at e'; exact ha' (Or.inl e')
    · rw [if_neg h1, if_neg h2] at e'; exact hab e'
  · intro a _ b _ x h; exact absurd h seq_notIn8

end

/-! ## The memory -/

/-- The word arrays of `ca_check_seq`'s memory. -/
def seqWords (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) : Array (Array Word) :=
  m.words.mapIdx fun a w =>
    if a = out ∨ a = ctlf then #[] else if a = hdrf then (m.arr64 out).extract 0 hw else w

/-- `ca_check_seq`'s memory before the globals: `m`'s word arrays and globals, but `out`, `ctlf`
and the byte arrays empty and `hdrf` the first `hw` words of `out`. -/
def seqMem0 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) : Mem where
  bytes := m.bytes.map fun _ => #[]
  words := seqWords m out hdrf ctlf hw
  glob := m.glob

/-- **The memory `ca_check_seq` runs `check` on**: `seqMem0 m` with `plo := lo`, `phi := hi`,
`mode := 2`. -/
def seqMem (m : Mem) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (lo hi : Word) : Mem :=
  (((seqMem0 m out hdrf ctlf hw).setG plo lo).setG phi hi).setG mode 2

theorem seqMem0_arr8 (m : Mem) (out hdrf ctlf : ArrId) (hw a : Nat) :
    (seqMem0 m out hdrf ctlf hw).arr8 a = #[] := by
  simp only [seqMem0, Mem.arr8, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases m.bytes[a]? <;> rfl

theorem seqMem0_arr64 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) {a : Nat} (ha : a < m.words.size) :
    (seqMem0 m out hdrf ctlf hw).arr64 a =
      if a = out ∨ a = ctlf then #[] else if a = hdrf then (m.arr64 out).extract 0 hw else m.arr64 a := by
  simp only [seqMem0, seqWords, Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx,
    Array.getElem?_eq_getElem ha, Option.map_some, Option.getD_some]

end ConAgua.Final
