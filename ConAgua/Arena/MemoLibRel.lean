import ConAgua.Arena.Frame
import ConAgua.Arena.MemoLib

/-!
# The memo library's relation: an L memo represents a `Std.HashMap κ ν`

`MemoRG S K dv m mp`: the live slots of memo `S` (stamp `=` the live stamp) hold distinct keys,
each a valid key (`K.ok`) whose decoding `K.dk` is mapped by `mp` to the slot's value decoded by
`dv`, and every entry of `mp` sits in a live slot on the run from its encoded key's home slot,
after live slots (linear probing; a stale stamp is free space). Generic in the schema, the key
codec `K` (two words per key) and the value decoder `dv`.

The lemmas: a probe hit is `mp`'s entry (`memoRG_hit`), a miss is its absence (`memoRG_miss`),
`put` after a probe is `insert` (`memoRG_set`), `clear` is `∅` (`memoRG_clear`), other writers leave
it alone (`memoRG_frame`), and all-zero memory is the empty map (`memoRG_zero`). An instance
supplies the codec and its one law `ek_dk`; nothing else.
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- How an instance stores its keys: two words per key, decoded by `dk`, encoded by `ek`, valid
words `ok`. -/
structure MemoKey (κ : Type) where
  dk : Word → Word → κ
  ek : κ → Word × Word
  ok : Word → Word → Prop
  ek_dk : ∀ k1 k2, ok k1 k2 → ek (dk k1 k2) = (k1, k2)

/-- What the generic lemmas need of a memo schema. -/
structure MemoSch.WF (S : MemoSch) : Prop where
  arr_ctl : S.arr ≠ CTL
  cs : S.cs.toNat + 2 < 2 ^ 32

/-- The stamp, key words and value of slot `j`. -/
def mstG (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4)
def mk1G (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4 + 1)
def mk2G (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4 + 2)
def mvG (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4 + 3)

/-- Slot `e` of the run from the home slot of key `(k1, k2)`. -/
def mrunG (S : MemoSch) (m : Mem) (k1 k2 : Word) (e : Nat) : Word :=
  walkW (nG S m) (homeW (kh k1 k2) (nG S m)) e

section rel
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)

/-- **The memo relation.** -/
def MemoRG (m : Mem) (mp : Std.HashMap κ ν) : Prop :=
  S.cs.toNat + 2 ≤ (m.arr64 CTL).size ∧ epG S m ≠ 0 ∧
  (∀ j, j < nG S m → (mstG S m j).toNat ≤ (epG S m).toNat) ∧
  (∀ j, j < nG S m → mstG S m j = epG S m →
    K.ok (mk1G S m j) (mk2G S m j) ∧ mp[K.dk (mk1G S m j) (mk2G S m j)]? = some (dv (mvG S m j))) ∧
  (∀ j j', j < nG S m → j' < nG S m → mstG S m j = epG S m → mstG S m j' = epG S m →
    mk1G S m j = mk1G S m j' → mk2G S m j = mk2G S m j' → j = j') ∧
  (∀ (x : κ) (v : ν), mp[x]? = some v → ∃ d : Nat,
    mstG S m (mrunG S m (K.ek x).1 (K.ek x).2 d) = epG S m ∧
    mk1G S m (mrunG S m (K.ek x).1 (K.ek x).2 d) = (K.ek x).1 ∧
    mk2G S m (mrunG S m (K.ek x).1 (K.ek x).2 d) = (K.ek x).2 ∧
    ∀ e < d, mstG S m (mrunG S m (K.ek x).1 (K.ek x).2 e) = epG S m)

end rel

/-! ## The probe -/

/-- The first `d` slots of the run of `(k1, k2)` are live and hold other keys. -/
def MNoMatchG (S : MemoSch) (m : Mem) (k1 k2 : Word) (d : Nat) : Prop :=
  ∀ e < d, mstG S m (mrunG S m k1 k2 e) = epG S m ∧
    ¬ (mk1G S m (mrunG S m k1 k2 e) = k1 ∧ mk2G S m (mrunG S m k1 k2 e) = k2)

/-- What the probe's result `rs` says: a hit is a live slot `rs[1]` with key `(k1, k2)`; a miss is
the non-live slot `rs[1]`, step `rs[2]` of the run, after live slots with other keys. -/
def MProbeOKG (S : MemoSch) (m : Mem) (k1 k2 : Word) (rs : List Word) : Prop :=
  rs ≠ [] →
    (rs.headD 0 ≠ 0 → mstG S m (rs.tail.headD 0) = epG S m ∧ mk1G S m (rs.tail.headD 0) = k1 ∧
      mk2G S m (rs.tail.headD 0) = k2 ∧ rs.tail.headD 0 < nG S m) ∧
    (rs.headD 0 = 0 → rs.tail.headD 0 = mrunG S m k1 k2 (rs.tail.tail.headD 0).toNat ∧
      rs.tail.headD 0 < nG S m ∧ mstG S m (rs.tail.headD 0) ≠ epG S m ∧
      MNoMatchG S m k1 k2 (rs.tail.tail.headD 0).toNat)

theorem mprobeG_ok (S : MemoSch) (m : Mem) (k1 k2 : Word)
    (hx : homeW (kh k1 k2) (nG S m) < nG S m) :
    ∀ (n : Nat) (d : Word), (nG S m).toNat - d.toNat = n → MNoMatchG S m k1 k2 d.toNat →
      MProbeOKG S m k1 k2
        (mprobeG (m.arr64 S.arr) k1 k2 (epG S m) (nG S m) (mrunG S m k1 k2 d.toNat) d) := by
  intro n
  induction n with
  | zero =>
    intro d hk _; rw [mprobeG]; grind [MProbeOKG]
  | succ n ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < nG S m := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    have hlt : mrunG S m k1 k2 d.toNat < nG S m := walkW_lt _ _ _ hx
    rw [hd1, mrunG, walkW_succ, ← mrunG] at this
    rw [mprobeG]
    by_cases h0 : rdW (m.arr64 S.arr) (mrunG S m k1 k2 d.toNat * 4) ≠ epG S m
    · simp only [hd, h0, ↓reduceIte, ne_eq, not_false_eq_true]
      grind [MProbeOKG, mstG]
    by_cases hm : rdW (m.arr64 S.arr) (mrunG S m k1 k2 d.toNat * 4 + 1) = k1 ∧
        rdW (m.arr64 S.arr) (mrunG S m k1 k2 d.toNat * 4 + 2) = k2
    · simp only [hd, h0, hm, ↓reduceIte, ne_eq, not_true_eq_false, and_self]
      grind [MProbeOKG, mstG, mk1G, mk2G]
    · simp only [hd, h0, hm, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
      exact this (by grind [MNoMatchG, mstG, mk1G, mk2G])

/-- The probe `X_find` makes. -/
theorem mfindG_ok (S : MemoSch) (m : Mem) (k1 k2 : Word) : MProbeOKG S m k1 k2 (mfindG S m k1 k2) := by
  by_cases hn : nG S m = 0
  · simp only [mfindG]; rw [mprobeG]; simp [hn, MProbeOKG]
  · have := mprobeG_ok S m k1 k2 (homeW_lt _ _ (by grind)) _ 0 rfl (by simp [MNoMatchG])
    simpa [mrunG, walkW, mfindG] using this

section relLemmas
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **A probe hit is the map's entry.** -/
theorem memoRG_hit (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) (k1 k2 : Word)
    (hr : mfindG S m k1 k2 ≠ []) (hh : (mfindG S m k1 k2).headD 0 ≠ 0) :
    mp[K.dk k1 k2]? = some (dv (mvG S m ((mfindG S m k1 k2).tail.headD 0))) := by
  obtain ⟨h1, h2, h3, h4⟩ := (mfindG_ok S m k1 k2 hr).1 hh
  have := hR.2.2.2.1 _ h4 h1
  rw [h2, h3] at this
  exact this.2

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **A probe miss is the map's absence.** -/
theorem memoRG_miss (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) (k1 k2 : Word)
    (hk : K.ok k1 k2) (hr : mfindG S m k1 k2 ≠ []) (hh : (mfindG S m k1 k2).headD 0 = 0) :
    mp[K.dk k1 k2]? = none := by
  obtain ⟨hj, hlt, hfree, hnm⟩ := (mfindG_ok S m k1 k2 hr).2 hh
  cases hc : mp[K.dk k1 k2]? with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨d, hd1, hd2, hd2', hd3⟩ := hR.2.2.2.2.2 _ _ hc
    rw [K.ek_dk k1 k2 hk] at hd1 hd2 hd2' hd3
    clear hR hc
    by_cases hlt' : d < ((mfindG S m k1 k2).tail.tail.headD 0).toNat
    · exact (hnm d hlt').2 ⟨hd2, hd2'⟩
    · by_cases heq : d = ((mfindG S m k1 k2).tail.tail.headD 0).toNat
      · subst heq; rw [← hj] at hd1; exact hfree hd1
      · have := hd3 ((mfindG S m k1 k2).tail.tail.headD 0).toNat (by omega)
        rw [← hj] at this; exact hfree this

end relLemmas

/-! ## Reads and frames of `put` and `clear` -/

theorem nG_toNat (S : MemoSch) (m : Mem) : (nG S m).toNat = (m.arr64 S.arr).size % 2 ^ 64 / 4 := by
  simp only [nG, len64_eq, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  rfl

theorem nG_lt (S : MemoSch) (m : Mem) : (nG S m).toNat < 2 ^ 62 := by
  rw [nG_toNat]; have := Nat.mod_lt (m.arr64 S.arr).size (show 0 < 2 ^ 64 by decide); omega

/-- Word `f < 4` of slot `x`. -/
theorem adG (S : MemoSch) (m : Mem) (x : Word) (hx : x < nG S m) (f : Word) (hf : f.toNat < 4) :
    (x * 4 + f).toNat = x.toNat * 4 + f.toNat := by
  have := nG_lt S m
  have : x.toNat < (nG S m).toNat := hx
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  rw [show (4 : Word).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem adG_eq (S : MemoSch) (m : Mem) (x y : Word) (hx : x < nG S m) (hy : y < nG S m) (f g : Word)
    (hf : f.toNat < 4) (hg : g.toNat < 4) : (x * 4 + f = y * 4 + g) ↔ (x = y ∧ f = g) := by
  constructor
  · intro h
    have h' := congrArg UInt64.toNat h
    rw [adG S m x hx f hf, adG S m y hy g hg] at h'
    exact ⟨UInt64.toNat_inj.mp (by omega), UInt64.toNat_inj.mp (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem adG_lt (S : MemoSch) (m : Mem) (x : Word) (hx : x < nG S m) (f : Word) (hf : f.toNat < 4) :
    (x * 4 + f).toNat < (m.arr64 S.arr).size := by
  rw [adG S m x hx f hf]
  have h1 : x.toNat < (nG S m).toNat := hx
  rw [nG_toNat] at h1
  have := (m.arr64 S.arr).size.mod_le (2 ^ 64); omega

theorem mputMem_arr (S : MemoSch) (m : Mem) (fd j k1 k2 v : Word) (b : ArrId) (hb : b ≠ S.arr)
    (hc : b ≠ CTL) : (mputMem S m fd j k1 k2 v).arr64 b = m.arr64 b := by
  unfold mputMem; split <;> simp [Mem.arr64_set64_ne _ _ _ _ _ hb, Mem.arr64_set64_ne _ _ _ _ _ hc]

theorem mputMem_frame (S : MemoSch) (hS : S.WF) (m : Mem) (fd j k1 k2 v : Word) :
    MemFrame [S.arr] [S.cs + 1] m (mputMem S m fd j k1 k2 v) := by
  refine ⟨fun b hb hc => mputMem_arr S m fd j k1 k2 v b (by simpa using hb) hc, fun x hx => ?_,
    fun b => ?_, ?_⟩
  · have : x ≠ S.cs + 1 := by simpa using hx
    have := hS.arr_ctl
    unfold mputMem; split <;> simp only [rdW_set64] <;> grind
  · unfold mputMem; split <;> simp only [size_set64]
  · unfold mputMem; split <;> simp only [Mem.words_size_set64]

theorem mputG_frame (S : MemoSch) (hS : S.WF) (m m' : Mem) (k1 k2 v fd j : Word)
    (h : mputG S m k1 k2 v fd j = some m') : MemFrame [S.arr] [S.cs + 1] m m' := by
  simp only [mputG] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact mputMem_frame _ hS _ _ _ _ _ _

theorem msetG_frame (S : MemoSch) (hS : S.WF) (m m' : Mem) (k1 k2 v : Word) (h : msetG S m k1 k2 v = some m') :
    MemFrame [S.arr] [S.cs + 1] m m' := by
  simp only [msetG] at h
  split at h
  · simp at h
  · exact mputG_frame S hS m m' _ _ _ _ _ h

theorem mclearG_frame (S : MemoSch) (m : Mem) : MemFrame [] [S.cs, S.cs + 1] m (mclearG S m) := by
  have h1 := MemFrame.setCtl m S.cs (rdW (m.arr64 CTL) S.cs + 1)
  have h2 := MemFrame.setCtl (m.set64 CTL S.cs (rdW (m.arr64 CTL) S.cs + 1)) (S.cs + 1) 0
  exact (h1.mono (by simp) (by simp)).trans (h2.mono (by simp) (by simp))

/-- A read of the memo after `put`'s writes at slot `j`. -/
theorem mputMem_rd (S : MemoSch) (hS : S.WF) (m : Mem) (fd j k1 k2 v : Word) (hj : j < nG S m)
    (x : Word) :
    rdW ((mputMem S m fd j k1 k2 v).arr64 S.arr) x =
      if x = j * 4 + 3 then v else if fd = 0 ∧ x = j * 4 + 2 then k2
      else if fd = 0 ∧ x = j * 4 + 1 then k1
      else if fd = 0 ∧ x = j * 4 + 0 then epG S m else rdW (m.arr64 S.arr) x := by
  have l := fun f hf => adG_lt S m j hj f hf
  have l0 := l 0 (by decide)
  have l1 := l 1 (by decide)
  have l2 := l 2 (by decide)
  have l3 := l 3 (by decide)
  have ne := fun f g hf hg (hfg : f ≠ g) (h : j * 4 + f = j * 4 + g) =>
    hfg ((adG_eq S m j j hj hj f g hf hg).mp h).2
  have n01 := ne 0 1 (by decide) (by decide) (by decide)
  have n02 := ne 0 2 (by decide) (by decide) (by decide)
  have n03 := ne 0 3 (by decide) (by decide) (by decide)
  have n12 := ne 1 2 (by decide) (by decide) (by decide)
  have n13 := ne 1 3 (by decide) (by decide) (by decide)
  have n23 := ne 2 3 (by decide) (by decide) (by decide)
  have hac := hS.arr_ctl
  simp only [UInt64.add_zero] at l0 n01 n02 n03 ⊢
  unfold mputMem
  by_cases hfd : fd = 0
  · simp only [hfd, ↓reduceIte, rdW_set64, size_set64, true_and, hac, false_and, l0, l1, l2, l3,
      and_true, Mem.arr64_set64_ne _ _ _ _ _ hac]
    by_cases h3 : x = j * 4 + 3
    · subst h3; simp
    by_cases h2 : x = j * 4 + 2
    · subst h2; simp [Ne.symm n23]
    by_cases h1 : x = j * 4 + 1
    · subst h1; simp [Ne.symm n13, Ne.symm n12]
    by_cases h0 : x = j * 4
    · subst h0; simp [Ne.symm n03, Ne.symm n02, Ne.symm n01]
    simp [Ne.symm h3, Ne.symm h2, Ne.symm h1, Ne.symm h0, h3, h2, h1, h0]
  · simp only [hfd, ↓reduceIte, rdW_set64, l3, true_and, false_and, and_true]
    by_cases h3 : x = j * 4 + 3
    · subst h3; simp
    · simp [Ne.symm h3, h3]

/-- Reads of the memo after `put` at slot `j`. -/
theorem mputMem_reads (S : MemoSch) (hS : S.WF) (m : Mem) (fd j k1 k2 v : Word)
    (hj : j < nG S m) :
    epG S (mputMem S m fd j k1 k2 v) = epG S m ∧ nG S (mputMem S m fd j k1 k2 v) = nG S m ∧
    (∀ j', j' < nG S m → mstG S (mputMem S m fd j k1 k2 v) j' =
      if j' = j ∧ fd = 0 then epG S m else mstG S m j') ∧
    (∀ j', j' < nG S m → mk1G S (mputMem S m fd j k1 k2 v) j' =
      if j' = j ∧ fd = 0 then k1 else mk1G S m j') ∧
    (∀ j', j' < nG S m → mk2G S (mputMem S m fd j k1 k2 v) j' =
      if j' = j ∧ fd = 0 then k2 else mk2G S m j') ∧
    (∀ j', j' < nG S m → mvG S (mputMem S m fd j k1 k2 v) j' =
      if j' = j then v else mvG S m j') := by
  have hf := mputMem_frame S hS m fd j k1 k2 v
  have hcs : S.cs ≠ S.cs + 1 := by
    intro h; have := hS.cs; grind
  have e := fun j' (hj' : j' < nG S m) f g hf hg => adG_eq S m j' j hj' hj f g hf hg
  have rd := mputMem_rd S hS m fd j k1 k2 v hj
  refine ⟨by simp only [epG, hf.2.1 S.cs (by simp [hcs])],
    by simp only [nG, len64_eq, hf.2.2.1], fun j' hj' => ?_, fun j' hj' => ?_, fun j' hj' => ?_,
    fun j' hj' => ?_⟩
  · have e3 := e j' hj' 0 3 (by decide) (by decide)
    have e2 := e j' hj' 0 2 (by decide) (by decide)
    have e1 := e j' hj' 0 1 (by decide) (by decide)
    have e0 := e j' hj' 0 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e3 e2 e1 e0
    simp only [mstG, rd, UInt64.add_zero, e3, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]
  · have e3 := e j' hj' 1 3 (by decide) (by decide)
    have e2 := e j' hj' 1 2 (by decide) (by decide)
    have e1 := e j' hj' 1 1 (by decide) (by decide)
    have e0 := e j' hj' 1 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e3 e2 e1 e0
    simp only [mk1G, rd, UInt64.add_zero, e3, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]
  · have e3 := e j' hj' 2 3 (by decide) (by decide)
    have e2 := e j' hj' 2 2 (by decide) (by decide)
    have e1 := e j' hj' 2 1 (by decide) (by decide)
    have e0 := e j' hj' 2 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e3 e2 e1 e0
    simp only [mk2G, rd, UInt64.add_zero, e3, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]
  · have e3 := e j' hj' 3 3 (by decide) (by decide)
    have e2 := e j' hj' 3 2 (by decide) (by decide)
    have e1 := e j' hj' 3 1 (by decide) (by decide)
    have e0 := e j' hj' 3 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e3 e2 e1 e0
    simp only [mvG, rd, UInt64.add_zero, e3, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]

theorem mrunG_eq (S : MemoSch) (m m' : Mem) (h : nG S m' = nG S m) (k1 k2 : Word) (e : Nat) :
    mrunG S m' k1 k2 e = mrunG S m k1 k2 e := by
  simp only [mrunG, h]

theorem mrunG_lt (S : MemoSch) (m : Mem) (k1 k2 : Word) (e : Nat) (hn : 0 < nG S m) :
    mrunG S m k1 k2 e < nG S m :=
  walkW_lt _ _ _ (homeW_lt _ _ hn)

section setClear
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (hS : S.WF) (K : MemoKey κ) (dv : Word → ν)

include hS in
/-- **`find; put` is `insert`.** -/
theorem memoRG_set (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) (k1 k2 v : Word)
    (hk : K.ok k1 k2) (m' : Mem) (h : msetG S m k1 k2 v = some m') :
    MemoRG S K dv m' (mp.insert (K.dk k1 k2) (dv v)) := by
  have hok := mfindG_ok S m k1 k2
  simp only [msetG, mputG] at h
  split at h
  · simp at h
  rename_i hne
  split at h
  · simp at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hctl, hep, hst, hlive, huniq, hrun⟩ := hR
  have hmiss := fun hh => memoRG_miss S K dv m mp ⟨hctl, hep, hst, hlive, huniq, hrun⟩ k1 k2 hk hne hh
  have hok' := hok hne
  generalize hrs : mfindG S m k1 k2 = rs at *
  obtain ⟨hhit', hmiss'⟩ := hok'
  have hj : rs.tail.headD 0 < nG S m := by
    by_cases hh : rs.headD 0 = 0
    · exact (hmiss' hh).2.1
    · exact (hhit' hh).2.2.2
  obtain ⟨r1, r2, r3, r4, r4', r5⟩ := mputMem_reads S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 v hj
  have hdk := K.ek_dk k1 k2 hk
  refine ⟨?_, by rw [r1]; exact hep, ?_, ?_, ?_, ?_⟩
  · have := (mputMem_frame S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 v).2.2.1 CTL; omega
  · intro j hj'; rw [r2] at hj'; rw [r3 j hj', r1]; have := hst j hj'; split <;> grind
  · intro j hj' hl
    rw [r2] at hj'
    rw [r3 j hj', r1] at hl
    rw [r4 j hj', r4' j hj', r5 j hj']
    by_cases hjj : j = rs.tail.headD 0
    · subst hjj
      by_cases hh : rs.headD 0 = 0
      · simp only [hh, and_self, ↓reduceIte, Std.HashMap.getElem?_insert_self]
        exact ⟨hk, by simp⟩
      · obtain ⟨h1, h2, h2', -⟩ := hhit' hh
        simp only [hh, and_false, ↓reduceIte, h2, h2', Std.HashMap.getElem?_insert_self]
        exact ⟨hk, by simp⟩
    · simp only [hjj, false_and, ↓reduceIte] at hl ⊢
      obtain ⟨hk', hm⟩ := hlive j hj' hl
      refine ⟨hk', ?_⟩
      rw [Std.HashMap.getElem?_insert]
      have : ¬ (K.dk k1 k2 == K.dk (mk1G S m j) (mk2G S m j)) = true := by
        intro he
        have he' : K.dk k1 k2 = K.dk (mk1G S m j) (mk2G S m j) := beq_iff_eq.mp he
        have := congrArg K.ek he'
        rw [hdk, K.ek_dk _ _ hk'] at this
        obtain ⟨e1, e2⟩ := Prod.mk.inj this
        by_cases hh : rs.headD 0 = 0
        · have h0 := hmiss hh; rw [e1, e2] at h0; rw [h0] at hm
          simp at hm
        · obtain ⟨h1, h2, h2', -⟩ := hhit' hh
          exact hjj (huniq _ _ hj' hj hl h1 (by rw [h2, e1]) (by rw [h2', e2]))
      simp only [this, Bool.false_eq_true, ↓reduceIte, hm]
  · intro j j' hj1 hj2 hl1 hl2 hkk hkk'
    rw [r2] at hj1 hj2
    rw [r3 j hj1, r1] at hl1
    rw [r3 j' hj2, r1] at hl2
    rw [r4 j hj1, r4 j' hj2] at hkk
    rw [r4' j hj1, r4' j' hj2] at hkk'
    by_cases hh : rs.headD 0 = 0
    · -- the new key is absent from the old live slots
      have habs : ∀ j'', j'' < nG S m → mstG S m j'' = epG S m →
          ¬ (mk1G S m j'' = k1 ∧ mk2G S m j'' = k2) := by
        intro j'' hj'' hl'' ⟨hk1, hk2⟩
        have := (hlive j'' hj'' hl'').2
        rw [hk1, hk2, hmiss hh] at this; simp at this
      by_cases e1 : j = rs.tail.headD 0 <;> by_cases e2 : j' = rs.tail.headD 0
      · rw [e1, e2]
      · simp only [e1, e2, hh, and_self, ↓reduceIte, false_and] at hkk hkk' hl2
        exact absurd ⟨hkk.symm, hkk'.symm⟩ (habs j' hj2 hl2)
      · simp only [e1, e2, hh, and_self, ↓reduceIte, false_and] at hkk hkk' hl1
        exact absurd ⟨hkk, hkk'⟩ (habs j hj1 hl1)
      · simp only [e1, e2, false_and, ↓reduceIte] at hkk hkk' hl1 hl2
        exact huniq j j' hj1 hj2 hl1 hl2 hkk hkk'
    · simp only [hh, and_false, ↓reduceIte] at hkk hkk' hl1 hl2
      exact huniq j j' hj1 hj2 hl1 hl2 hkk hkk'
  · intro x w hx
    rw [Std.HashMap.getElem?_insert] at hx
    have hn0 : 0 < nG S m := by grind
    have hr := fun a b e => mrunG_eq S m (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 v) r2 a b e
    by_cases hxk : (K.dk k1 k2 == x) = true
    · have hxe : x = K.dk k1 k2 := (beq_iff_eq.mp hxk).symm
      subst hxe
      rw [hdk]
      by_cases hh : rs.headD 0 = 0
      · obtain ⟨hj1, -, -, hnm⟩ := hmiss' hh
        refine ⟨(rs.tail.tail.headD 0).toNat, ?_, ?_, ?_, fun e he => ?_⟩
        · rw [hr, ← hj1, r3 _ hj, r1]; simp only [hh, and_self, ↓reduceIte]
        · rw [hr, ← hj1, r4 _ hj]; simp only [hh, and_self, ↓reduceIte]
        · rw [hr, ← hj1, r4' _ hj]; simp only [hh, and_self, ↓reduceIte]
        · have hlt := mrunG_lt S m k1 k2 e hn0
          rw [hr, r3 _ hlt, r1]
          split
          · rfl
          · exact (hnm e he).1
      · obtain ⟨hl, h2, h2', hlt⟩ := hhit' hh
        have := memoRG_hit S K dv m mp ⟨hctl, hep, hst, hlive, huniq, hrun⟩ k1 k2 (by rw [hrs]; exact hne)
          (by rw [hrs]; exact hh)
        obtain ⟨d, hd1, hd2, hd2', hd3⟩ := hrun _ _ this
        rw [hdk] at hd1 hd2 hd2' hd3
        refine ⟨d, ?_, ?_, ?_, fun e he => ?_⟩
        · rw [hr, r3 _ (mrunG_lt S m k1 k2 d hn0), r1]; simp only [hh, and_false, ↓reduceIte, hd1]
        · rw [hr, r4 _ (mrunG_lt S m k1 k2 d hn0)]; simp only [hh, and_false, ↓reduceIte, hd2]
        · rw [hr, r4' _ (mrunG_lt S m k1 k2 d hn0)]; simp only [hh, and_false, ↓reduceIte, hd2']
        · rw [hr, r3 _ (mrunG_lt S m k1 k2 e hn0), r1]
          simp only [hh, and_false, ↓reduceIte, hd3 e he]
    · simp only [hxk, Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨d, hd1, hd2, hd2', hd3⟩ := hrun _ _ hx
      have hl : ∀ e, mstG S m (mrunG S m (K.ek x).1 (K.ek x).2 e) = epG S m →
          mstG S (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 v)
            (mrunG S (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 v) (K.ek x).1 (K.ek x).2 e) =
            epG S (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 v) := by
        intro e he
        rw [hr, r3 _ (mrunG_lt S m _ _ e hn0), r1]
        split
        · rfl
        · exact he
      have hfree : ¬ (mrunG S m (K.ek x).1 (K.ek x).2 d = rs.tail.headD 0 ∧ rs.headD 0 = 0) := by
        rintro ⟨hc1, hc2⟩
        obtain ⟨-, -, hfr, -⟩ := hmiss' hc2
        exact hfr (hc1 ▸ hd1)
      refine ⟨d, hl d hd1, ?_, ?_, fun e he => hl e (hd3 e he)⟩
      · rw [hr, r4 _ (mrunG_lt S m _ _ d hn0)]
        simp only [hfree, ↓reduceIte, hd2]
      · rw [hr, r4' _ (mrunG_lt S m _ _ d hn0)]
        simp only [hfree, ↓reduceIte, hd2']

include hS in
/-- **`clear` is `∅`.** -/
theorem memoRG_clear (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp)
    (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) : MemoRG S K dv (mclearG S m) ∅ := by
  obtain ⟨hctl, hep, hst, -, -, -⟩ := hR
  have hf := mclearG_frame S m
  have hsz := hf.2.2.1
  have hb : (mclearG S m).arr64 S.arr = m.arr64 S.arr := hf.1 S.arr (by simp) hS.arr_ctl
  have hn : nG S (mclearG S m) = nG S m := by simp only [nG, len64_eq, hb]
  have hs : ∀ j, mstG S (mclearG S m) j = mstG S m j := fun j => by simp only [mstG, hb]
  have hcs : S.cs + 1 ≠ S.cs := by
    intro h; have := hS.cs; grind
  have he : epG S (mclearG S m) = epG S m + 1 := by
    simp only [epG, mclearG, rdW_set64, size_set64, hcs]; grind
  have hlt : ∀ j, j < nG S m → (mstG S m j).toNat < (epG S m + 1).toNat := by
    intro j hj
    have := hst j hj
    have : (epG S m + 1).toNat = (epG S m).toNat + 1 := by
      simp only [epG] at *; rw [UInt64.toNat_add]; grind
    omega
  refine ⟨by rw [hsz]; exact hctl, by rw [he]; simp only [epG] at *; grind, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hn] at hj; rw [hs, he]; exact Nat.le_of_lt (hlt j hj)
  · intro j hj hl; rw [hn] at hj; rw [hs, he] at hl; have := hlt j hj; rw [hl] at this; omega
  · intro j j' hj _ hl _ _ _; rw [hn] at hj; rw [hs, he] at hl; have := hlt j hj; rw [hl] at this
    omega
  · intro x v hx; simp at hx

include hS in
omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **The memo relation survives a writer of other arrays and of `CTL` words other than the
stamp.** -/
theorem memoRG_frame (A : List ArrId) (C : List Word) (hA : S.arr ∉ A) (hC : S.cs ∉ C)
    (m m' : Mem) (hf : MemFrame A C m m') (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) :
    MemoRG S K dv m' mp := by
  have hb : m'.arr64 S.arr = m.arr64 S.arr := hf.1 S.arr hA hS.arr_ctl
  have hn : nG S m' = nG S m := by simp only [nG, len64_eq, hb]
  have he : epG S m' = epG S m := by simp only [epG, hf.2.1 S.cs hC]
  have hs : ∀ j, mstG S m' j = mstG S m j := fun j => by simp only [mstG, hb]
  have hk : ∀ j, mk1G S m' j = mk1G S m j := fun j => by simp only [mk1G, hb]
  have hk' : ∀ j, mk2G S m' j = mk2G S m j := fun j => by simp only [mk2G, hb]
  have hv : ∀ j, mvG S m' j = mvG S m j := fun j => by simp only [mvG, hb]
  have hr : ∀ a b e, mrunG S m' a b e = mrunG S m a b e := fun a b e => by simp only [mrunG, hn]
  obtain ⟨hctl, hep, hst, hlive, huniq, hrun⟩ := hR
  refine ⟨by rw [hf.2.2.1]; exact hctl, by rw [he]; exact hep, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hs, he]; exact hst j (hn ▸ hj)
  · intro j hj hl; rw [hs, he] at hl; rw [hk, hk', hv]; exact hlive j (hn ▸ hj) hl
  · intro j j' hj hj' hl hl' hkk hkk'; rw [hs, he] at hl hl'; rw [hk, hk] at hkk
    rw [hk', hk'] at hkk'
    exact huniq j j' (hn ▸ hj) (hn ▸ hj') hl hl' hkk hkk'
  · intro x v hx
    obtain ⟨d, h1, h2, h2', h3⟩ := hrun x v hx
    exact ⟨d, by rw [hr, hs, he]; exact h1, by rw [hr, hk]; exact h2, by rw [hr, hk']; exact h2',
      fun e hle => by rw [hr, hs, he]; exact h3 e hle⟩

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **All-zero memory is the empty map.** -/
theorem memoRG_zero (m : Mem) (hz : ∀ b x, rdW (m.arr64 b) x = 0)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) : MemoRG S K dv m ∅ := by
  refine ⟨hctl, by simp [epG, hz], fun j _ => by simp [mstG, epG, hz],
    fun j _ h => by simp [mstG, epG, hz] at h, fun j _ _ _ h => by simp [mstG, epG, hz] at h,
    fun x v h => by simp at h⟩

end setClear

/-! ## The instances' keys -/

/-- The key word of a handle decoded from a word below `2^32`. -/
theorem word_decE (k : Word) (hk : k.toNat < 2 ^ 32) : (decE k).word.toUInt64 = k := by
  have := word_decI (decE k) k hk
  rw [decE_eq] at this ⊢
  exact this.mpr rfl

theorem bmSch_wf : bmSch.WF := ⟨by decide, by decide⟩
theorem lfSch_wf : lfSch.WF := ⟨by decide, by decide⟩
theorem imSch_wf : imSch.WF := ⟨by decide, by decide⟩

/-- `bvarBC`'s keys: a handle word, second word `0`. -/
def bmKey : MemoKey EIdx where
  dk k1 _ := decE k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by simp only [word_decE k1 h.1, h.2]

/-- `liftC`'s keys: a handle word and the cutoff. -/
def lfKey : MemoKey (EIdx × Nat) where
  dk k1 k2 := (decE k1, k2.toNat)
  ek x := (x.1.word.toUInt64, x.2.toUInt64)
  ok k1 _ := k1.toNat < 2 ^ 32
  ek_dk k1 k2 h := by simp only [word_decE k1 h, Nat.toUInt64_eq, UInt64.ofNat_toNat]

end L.Arena
