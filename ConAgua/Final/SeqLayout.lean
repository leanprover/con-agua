import ConAgua.Compiler.AbiSim
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import ConRon.Bridge.Grind

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

/-- What `ca_check_seq`'s layout needs of its parameters: `out`, `hdrf`, `ctlf` are tier-0 numbers
of today's layout (below `tierOff`), so that they name the arrays `↑out`, `↑hdrf`, `↑ctlf`. -/
def seqParamsOk (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) : Bool :=
  decide (out < tab.nw) && decide (hdrf < tab.nw) && decide (hdrf ≠ out) && decide (hdrf ≠ ctlf) &&
    decide (hw ≤ abiWords) && decide (out < tierOff) && decide (hdrf < tierOff) && decide (ctlf < tierOff)

theorem seqParamsOk_spec {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat}
    (h : seqParamsOk tab out hdrf ctlf hw = true) :
    out < tab.nw ∧ hdrf < tab.nw ∧ hdrf ≠ out ∧ hdrf ≠ ctlf ∧ hw ≤ abiWords := by
  simp only [seqParamsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2⟩

theorem seqParamsOk_tier {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat}
    (h : seqParamsOk tab out hdrf ctlf hw = true) :
    out < tierOff ∧ hdrf < tierOff ∧ ctlf < tierOff := by
  simp only [seqParamsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-- The slot word array `a` lives in: `hdrf` in `out`'s. -/
def seqSlot (out hdrf a : Nat) : Nat := if a = hdrf then out else a

theorem seqSlot_lt {nw out hdrf a : Nat} (hout : out < nw) (ha : a < nw) : seqSlot out hdrf a < nw := by
  unfold seqSlot; split <;> assumption

/-- `ca_check_seq`'s layout of the region at `base`: descriptor position `p` holds word array
number `tab.wposInv p` (as `seqVals` fills it). -/
def seqLayout (tab : Tab) (base : Nat) (out hdrf ctlf : ArrId) (hw : Nat) : L.Compiler.Layout where
  tab
  T := base
  b8 _ := 0
  s8 _ := 0
  b64 p := if tab.wposInv p = out ∨ tab.wposInv p = ctlf then 0
    else base + abiSlot * abiSlot64 tab (seqSlot out hdrf (tab.wposInv p))
  s64 p := if tab.wposInv p = out ∨ tab.wposInv p = ctlf then 0
    else if tab.wposInv p = hdrf then hw else abiWords
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
theorem seqLayout_b64 (p : Nat) : (seqLayout tab base out hdrf ctlf hw).b64 p =
    if tab.wposInv p = out ∨ tab.wposInv p = ctlf then 0
    else base + abiSlot * abiSlot64 tab (seqSlot out hdrf (tab.wposInv p)) := by simp only [seqLayout]
theorem seqLayout_s64 (p : Nat) : (seqLayout tab base out hdrf ctlf hw).s64 p =
    if tab.wposInv p = out ∨ tab.wposInv p = ctlf then 0
    else if tab.wposInv p = hdrf then hw else abiWords := by simp only [seqLayout]
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

/-- A byte at descriptor position `p` (word array number `a = wposInv p`) is in slot
`abiSlot64 (seqSlot a)`; `a` has memory. -/
theorem seq_in64 (hok : abiTabOk tab = true) (hp : seqParamsOk tab out hdrf ctlf hw = true)
    {p x : Nat} (hp' : p < tab.nw) (h : (seqLayout tab base out hdrf ctlf hw).In64 p x) :
    ¬ (tab.wposInv p = out ∨ tab.wposInv p = ctlf) ∧ seqSlot out hdrf (tab.wposInv p) < tab.nw ∧
      InSlot base (abiSlot64 tab (seqSlot out hdrf (tab.wposInv p))) x := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  obtain ⟨hout, hhdr, -, -, hhw⟩ := seqParamsOk_spec hp
  unfold Layout.In64 at h
  rw [seqLayout_b64, seqLayout_s64] at h
  have ha := tab.wposInv_ltN hp'
  generalize tab.wposInv p = a at h ha ⊢
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
    have hj : abiSlot64 tab (seqSlot out hdrf (tab.wposInv a)) < 2 + tab.nw := by
      simp only [abiSlot64, hnb]; omega
    exact ⟨abiSlot64 tab (seqSlot out hdrf (tab.wposInv a)), by simp only [abiSlot64]; omega, hj, hs⟩

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
  · obtain ⟨j, hj, -, h3⟩ := seq_inArr hok hp h
    have : abiSlot * 2 ≤ abiSlot * j := Nat.mul_le_mul_left _ hj
    unfold InSlot at h3; simp only [abiSlot] at this h3; omega

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
  · intro p hp'
    simp only [seqLayout_tab] at hp'
    rw [seqLayout_b64, seqLayout_s64]
    have ha := tab.wposInv_ltN hp'
    generalize tab.wposInv p = a at ha ⊢
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
  · intro p hpa q hqb hpq x h1 h2
    simp only [seqLayout_tab] at hpa hqb
    obtain ⟨ha', hsa, s1⟩ := seq_in64 hok hp hpa h1
    obtain ⟨hb', hsb, s2⟩ := seq_in64 hok hp hqb h2
    have hab : tab.wposInv p ≠ tab.wposInv q := fun e => hpq (by
      rw [← tab.wpos_wposInv hpa, ← tab.wpos_wposInv hqb, e])
    generalize tab.wposInv p = a at ha' hsa s1 hab
    generalize tab.wposInv q = b at hb' hsb s2 hab
    have e := InSlot.eq s1 s2
    simp only [abiSlot64] at e
    have e' : seqSlot out hdrf a = seqSlot out hdrf b := by omega
    unfold seqSlot at e'
    by_cases h1 : a = hdrf <;> by_cases h2 : b = hdrf
    · exact hab (h1.trans h2.symm)
    · rw [ite_eq_left h1, ite_eq_right h2] at e'; exact hb' (Or.inl e'.symm)
    · rw [ite_eq_right h1, ite_eq_left h2] at e'; exact ha' (Or.inl e')
    · rw [ite_eq_right h1, ite_eq_right h2] at e'; exact hab e'
  · intro a _ b _ x h; exact absurd h seq_notIn8

end

/-! ## The memory -/

/-- `ca_check_seq`'s memory before the globals: `m`'s word arrays and globals, but `out`, `ctlf`
and the byte arrays empty and `hdrf` the first `hw` words of `out`. -/
def seqMem0 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) : Mem where
  bytes _ := #[]
  words s := if s = ↑out ∨ s = ↑ctlf then #[] else if s = ↑hdrf then (m.arr64 out).extract 0 hw else m.words s
  glob := m.glob

/-- **The memory `ca_check_seq` runs `check` on**: `seqMem0 m` with `plo := lo`, `phi := hi`,
`mode := 2`. -/
def seqMem (m : Mem) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (lo hi : Word) : Mem :=
  (((seqMem0 m out hdrf ctlf hw).setG plo lo).setG phi hi).setG mode 2

theorem seqMem0_arr8 (m : Mem) (out hdrf ctlf : ArrId) (hw a : Nat) :
    (seqMem0 m out hdrf ctlf hw).arr8 a = #[] := rfl

theorem seqMem0_arr64 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) (s : TieredArray) :
    (seqMem0 m out hdrf ctlf hw).arr64 s =
      if s = ↑out ∨ s = ↑ctlf then #[] else if s = ↑hdrf then (m.arr64 out).extract 0 hw else m.arr64 s := rfl

/-! ## The stores -/

/-- `ca_check_seq`'s base word for word array `a`. -/
def seqBase (tab : Tab) (out hdrf ctlf : ArrId) (a : ArrId) : SVal :=
  if a = out ∨ a = ctlf then .imm 0
  else if a = hdrf then .addr (abiSlot * abiSlot64 tab out)
  else .addr (abiSlot * abiSlot64 tab a)

/-- `ca_check_seq`'s length word for word array `a`. -/
def seqLen (out hdrf ctlf : ArrId) (hw : Nat) (a : ArrId) : SVal :=
  if a = out ∨ a = ctlf then .imm 0
  else if a = hdrf then .imm hw.toUInt64
  else .imm abiWords.toUInt64

theorem seqVals_eq {tab : Tab} (h : tab.nb = 2) (out hdrf ctlf : ArrId) (hw : Nat) :
    seqVals tab out hdrf ctlf hw = [.addr (abiSlot + abiStack), .addr abiSlot, .imm 0, .imm 0, .imm 0, .imm 0] ++
      (List.range tab.nw).map (fun p => seqBase tab out hdrf ctlf (tab.wposInv p)) ++
      (List.range tab.nw).map (fun p => seqLen out hdrf ctlf hw (tab.wposInv p)) ++
      romVals tab.rom := by
  simp only [seqVals, h]; rfl

theorem seqVals_length {tab : Tab} (h : tab.nb = 2) (out hdrf ctlf : ArrId) (hw : Nat) :
    (seqVals tab out hdrf ctlf hw).length = (abiVals tab).length := by
  rw [abiVals_length tab h, seqVals_eq h]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
    romVals_length, Tab.romWords, ← tab.romLen_eq]
  omega

theorem seqVals_getElem? {tab : Tab} (h : tab.nb = 2) (out hdrf ctlf : ArrId) (hw : Nat) :
    (seqVals tab out hdrf ctlf hw)[0]? = some (.addr (abiSlot + abiStack)) ∧
    (seqVals tab out hdrf ctlf hw)[1]? = some (.addr abiSlot) ∧
    (∀ i, 2 ≤ i → i < 6 → (seqVals tab out hdrf ctlf hw)[i]? = some (.imm 0)) ∧
    (∀ p < tab.nw, (seqVals tab out hdrf ctlf hw)[6 + p]? = some (seqBase tab out hdrf ctlf (tab.wposInv p)) ∧
      (seqVals tab out hdrf ctlf hw)[6 + tab.nw + p]? = some (seqLen out hdrf ctlf hw (tab.wposInv p))) ∧
    (∀ i, (seqVals tab out hdrf ctlf hw)[6 + 2 * tab.nw + i]? = (romVals tab.rom)[i]?) := by
  rw [seqVals_eq h]
  refine ⟨rfl, rfl, fun i h1 h2 => ?_, fun p hw => ?_, fun i => ?_⟩
  · have : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  · constructor
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by simp)]
      simp only [List.length_cons, List.length_nil, show 6 + p - (0 + 1 + 1 + 1 + 1 + 1 + 1) = p by omega,
        List.getElem?_map, List.getElem?_range hw, Option.map_some]
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
        show 6 + tab.nw + p - (0 + 1 + 1 + 1 + 1 + 1 + 1 + tab.nw) = p by omega,
        List.getElem?_map, List.getElem?_range hw, Option.map_some]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]
    congr 1; omega

theorem seqVals_noRax (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) (h : tab.nb = 2) :
    ∀ v ∈ seqVals tab out hdrf ctlf hw, v.noRax := by
  intro v hv
  rw [seqVals_eq h] at hv
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hv
  rcases hv with ((h1 | h1) | h1) | h1
  · rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · obtain ⟨_, _, rfl⟩ := h1; unfold seqBase; split <;> (try split) <;> trivial
  · obtain ⟨_, _, rfl⟩ := h1; unfold seqLen; split <;> (try split) <;> trivial
  · exact abiVals_noRax tab v (by simp only [abiVals]; exact List.mem_append_right _ h1)

/-- The base word `ca_check_seq` writes at descriptor position `p`. -/
theorem seqBase_val {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (R : Reg64s) {base : Nat}
    (hR : R.r8.toNat = base) {p : Nat}
    (hfit : base + abiSlot * abiSlot64 tab (seqSlot out hdrf (tab.wposInv p)) < 2 ^ 64) :
    UInt64.ofBitVec ((seqBase tab out hdrf ctlf (tab.wposInv p)).val R) =
      UInt64.ofNat ((seqLayout tab base out hdrf ctlf hw).b64 p) := by
  rw [seqLayout_b64]
  generalize tab.wposInv p = a at hfit ⊢
  unfold seqBase
  by_cases h1 : a = out ∨ a = ctlf
  · simp only [h1, ite_true, SVal.val]; rfl
  · simp only [h1, ite_false]
    unfold seqSlot at hfit ⊢
    by_cases h2 : a = hdrf
    · simp only [h2, ite_true] at hfit ⊢; rw [addr_val _ _ (by omega)]; try rw [hR]
    · simp only [h2, ite_false] at hfit ⊢; rw [addr_val _ _ (by omega)]; try rw [hR]

theorem seqLen_val {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (R : Reg64s) (base p : Nat) :
    UInt64.ofBitVec ((seqLen out hdrf ctlf hw (tab.wposInv p)).val R) =
      UInt64.ofNat ((seqLayout tab base out hdrf ctlf hw).s64 p) := by
  rw [seqLayout_s64]
  generalize tab.wposInv p = a
  unfold seqLen
  by_cases h1 : a = out ∨ a = ctlf
  · simp only [h1, ite_true, SVal.val] <;> rfl
  · simp only [h1, ite_false]
    by_cases h2 : a = hdrf
    · simp only [h2, ite_true, SVal.val] <;> rfl
    · simp only [h2, ite_false, SVal.val] <;> rfl

/-- **The stores of `ca_check_seq`**, on a region that holds `m` in the partition layout, relate
it to `seqMem0 m` in `ca_check_seq`'s layout. -/
theorem seq_memRel {tab : Tab} {out hdrf ctlf : ArrId} {hw : Nat} (hok : abiTabOk tab = true)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) {base inp n pins np : Nat}
    (hfit : base + abiNeed tab < 2 ^ 64) (R : Reg64s) (hR : R.r8.toNat = base) (m : Mem) (d : DataMem)
    (hm : MemRel (abiLayout tab base inp n pins np) m d) :
    MemRel (seqLayout tab base out hdrf ctlf hw) (seqMem0 m out hdrf ctlf hw)
      (stores R base d 0 (seqVals tab out hdrf ctlf hw)) := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  obtain ⟨hout, hhdr, hho, hhc, hhw⟩ := seqParamsOk_spec hp
  obtain ⟨tout, thdr, tctl⟩ := seqParamsOk_tier hp
  have dout : tab.dom64 (TieredArray.t0 out) = true := (tab.dom64_t0_iff out).2 ⟨tout, hout⟩
  have hn : abiNeed tab = abiSlot * (2 + tab.nw) := by simp [abiNeed, hnb]
  have hL := seqVals_length hnb out hdrf ctlf hw
  rw [abiVals_length tab hnb] at hL
  have hend : base + 8 * (seqVals tab out hdrf ctlf hw).length ≤ 2 ^ 64 := by
    rw [hL]; simp only [hn, abiSlot] at hfit; omega
  have honly := stores_only R base (seqVals tab out hdrf ctlf hw) d 0 (by simpa using hend)
  simp only [Nat.add_zero] at honly
  obtain ⟨g0, g1, gb, gw, grom⟩ := seqVals_getElem? hnb out hdrf ctlf hw
  have hW : ∀ i v, (seqVals tab out hdrf ctlf hw)[i]? = some v →
      rdW (stores R base d 0 (seqVals tab out hdrf ctlf hw)) (A (base + 8 * i)) = some (UInt64.ofBitVec (v.val R)) :=
    fun i v hv => stores_rdW? R base _ _ i v hv hend
  have hout64 : (m.arr64 out).size = abiWords := hm.size64 _ dout
  -- word arrays live in slots `≥ 2`, past the stores
  have harr : ∀ a < tab.nw, ∀ i, i < abiWords →
      rdW (stores R base d 0 (seqVals tab out hdrf ctlf hw)) (A (base + abiSlot * abiSlot64 tab a + 8 * i)) =
        rdW d (A (base + abiSlot * abiSlot64 tab a + 8 * i)) := by
    intro a ha i hi
    have hj : abiSlot64 tab a < 2 + tab.nw := by simp only [abiSlot64, hnb]; omega
    have hle : abiSlot * abiSlot64 tab a + abiSlot ≤ abiSlot * (2 + tab.nw) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    refine honly.rdW_eq ?_ (Or.inr ?_)
    · simp only [hn, abiSlot, abiWords] at hfit hle hi ⊢; omega
    · rw [hL]; simp only [abiSlot64, abiSlot, hnb] at hle ⊢; omega
  have hcur : ∀ s, tab.dom64 s = true → tab.wposInv (tab.pos64 s) = curNum s := fun s hs =>
    tab.wposInv_pos64 hs
  constructor
  · intro a _; simp [seqMem0_arr8]
  · intro s hs
    simp only [seqLayout_tab] at hs
    rw [seqMem0_arr64, seqLayout_s64, seqLayout_tab, hcur s hs]
    simp only [curNum_eq_iff tout, curNum_eq_iff tctl, curNum_eq_iff thdr]
    split
    · rfl
    · split
      · simp only [Array.size_extract, hout64]; omega
      · exact hm.size64 s hs
  · intro a _ i hi; simp [seqMem0_arr8] at hi
  · intro s hs i hi
    simp only [seqLayout_tab] at hs
    have e := seqMem0_arr64 m out hdrf ctlf hw s
    rw [seqLayout_b64, seqLayout_tab, hcur s hs]
    simp only [curNum_eq_iff tout, curNum_eq_iff tctl]
    by_cases h1 : s = ↑out ∨ s = ↑ctlf
    · simp only [e, h1, ite_true] at hi; simp at hi
    · simp only [h1, ite_false]
      simp only [e, ite_eq_right h1] at hi ⊢
      unfold seqSlot
      simp only [curNum_eq_iff thdr]
      by_cases h2 : s = ↑hdrf
      · simp only [ite_eq_left h2, Array.size_extract, hout64] at hi ⊢
        rw [harr out hout i (by omega)]
        have := hm.get64 _ dout i (by omega)
        simp only [abiLayout_b64, abiLayout_tab, hcur _ dout, curNum_t0] at this
        rw [this]; simp
      · simp only [ite_eq_right h2] at hi ⊢
        have hs' := hm.size64 s hs
        simp only [abiLayout_s64] at hs'
        rw [harr (curNum s) (tab.curNum_lt hs) i (by omega)]
        have := hm.get64 s hs i hi
        simp only [abiLayout_b64, abiLayout_tab, hcur s hs] at this
        exact this
  · have := hW 1 _ g1
    rw [addr_val _ _ (by rw [hR]; simp only [hn, abiSlot] at hfit ⊢; omega), hR] at this
    simpa only [seqLayout_T, seqLayout_lo] using this
  · intro a ha
    simp only [seqLayout_tab, hnb] at ha
    have := hW (2 + 2 * a) _ (gb _ (by omega) (by omega))
    simp only [SVal.val] at this
    simp only [seqLayout_T, seqLayout_b8, Tab.dbase8]
    rw [show (16 + 16 * (a : Int)).toNat = 8 * (2 + 2 * a) by omega]
    exact this
  · intro a ha
    simp only [seqLayout_tab, hnb] at ha
    have := hW (3 + 2 * a) _ (gb _ (by omega) (by omega))
    simp only [SVal.val] at this
    simp only [seqLayout_T, seqLayout_s8, Tab.dlen8]
    rw [show (24 + 16 * (a : Int)).toNat = 8 * (3 + 2 * a) by omega]
    exact this
  · intro p hp'
    simp only [seqLayout_tab] at hp'
    have ha := tab.wposInv_ltN hp'
    have := hW (6 + p) _ (gw p hp').1
    have hj : abiSlot64 tab (seqSlot out hdrf (tab.wposInv p)) < 2 + tab.nw := by
      have := seqSlot_lt (hdrf := hdrf) hout ha; simp only [abiSlot64, hnb]; omega
    have hle : abiSlot * abiSlot64 tab (seqSlot out hdrf (tab.wposInv p)) + abiSlot ≤ abiSlot * (2 + tab.nw) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    rw [seqBase_val (hw := hw) R hR (by simp only [hn, abiSlot] at hfit hle ⊢; omega)] at this
    simp only [seqLayout_T, seqLayout_tab, Tab.dbase64, hnb]
    rw [show (16 + 16 * ((2 : Nat) : Int) + 8 * (p : Int)).toNat = 8 * (6 + p) by omega]
    exact this
  · intro p hp'
    simp only [seqLayout_tab] at hp'
    have := hW (6 + tab.nw + p) _ (gw p hp').2
    rw [seqLen_val (tab := tab) R base p] at this
    simp only [seqLayout_T, seqLayout_tab, Tab.dlen64, hnb]
    rw [show (16 + 16 * ((2 : Nat) : Int) + 8 * (tab.nw : Int) + 8 * (p : Int)).toNat =
      8 * (6 + tab.nw + p) by omega]
    exact this
  · intro i hi
    simp only [seqLayout_T, seqLayout_tab, hnb]
    obtain ⟨w, hw1, hw2⟩ := romVals_byte tab.rom i hi
    have hv : (seqVals tab out hdrf ctlf hw)[6 + 2 * tab.nw + i / 8]? = some (.imm w) := by rw [grom]; exact hw1
    obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.mp hv
    have := stores_byte R base (seqVals tab out hdrf ctlf hw) d 0 (6 + 2 * tab.nw + i / 8) (i % 8) hlt
      (Nat.mod_lt _ (by omega)) (by simpa using hend)
    rw [hv'] at this
    simp only [SVal.val, UInt64.ofBitVec_toBitVec, hw2] at this
    rw [show base + 16 + 16 * (2 + tab.nw) + i = base + 0 + 8 * (6 + 2 * tab.nw + i / 8) + i % 8 by omega]
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
    rw [honly.rdW_eq (by simp only [hn, abiSlot] at hfit; omega) (Or.inr (by rw [hL]; simp only [hnb]; omega))]
    exact this

end ConAgua.Final
