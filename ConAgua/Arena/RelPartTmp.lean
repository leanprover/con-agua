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
words `ok`; no valid key starts with the tombstone word. -/
structure MemoKey (κ : Type) where
  dk : Word → Word → κ
  ek : κ → Word × Word
  ok : Word → Word → Prop
  ek_dk : ∀ k1 k2, ok k1 k2 → ek (dk k1 k2) = (k1, k2)
  ok_tomb : ∀ k1 k2, ok k1 k2 → k1 ≠ TOMB

/-- What the generic lemmas need of a memo schema. -/
structure MemoSch.WF (S : MemoSch) : Prop where
  arr_ctl : S.arr ≠ CTL
  cs : S.cs.toNat + 2 < 2 ^ 32

/-- The stamp, key words and value of slot `j`. -/
def mstG (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4)
def mk1G (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4 + 1)
def mk2G (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4 + 2)
def mvG (S : MemoSch) (m : Mem) (j : Word) : Word := rdW (m.arr64 S.arr) (j * 4 + 3)

/-- Slot `e` of the run of key `(k1, k2)` in the region from slot `b` of `n` slots. -/
def runAt (b n k1 k2 : Word) (e : Nat) : Word := b + walkW n (homeW (kh k1 k2) n) e

/-- Slot `e` of the run from the home slot of key `(k1, k2)`, in the memo's region. -/
def mrunG (S : MemoSch) (m : Mem) (k1 k2 : Word) (e : Nat) : Word :=
  runAt (mbG S m) (nG S m) k1 k2 e

/-- Slot `j` lies in the region from slot `b` of `n` slots. -/
def InReg (b n j : Word) : Prop := b.toNat ≤ j.toNat ∧ j.toNat < b.toNat + n.toNat

/-- The map's entry `o` is a value the slot word `w` denotes in `m` (by the value relation `VR`). -/
def MemoV {ν : Type} (VR : Mem → Word → ν → Prop) (m : Mem) (w : Word) (o : Option ν) : Prop :=
  ∃ v, o = some v ∧ VR m w v

section rel
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop)

/-- **The slots of a region represent a lookup function `f`**, at live stamp `e`: the live slots
that are not tombstones hold distinct valid keys, each mapped by `f` to a value its word denotes;
every entry of `f` is the decoding of its own encoding, not a tombstone key, and sits in a live
slot on the run from its encoded key's home, after live slots. -/
def MemoAt (e b n : Word) (m : Mem) (f : κ → Option ν) : Prop :=
  (∀ j, InReg b n j → mstG S m j = e → mk1G S m j ≠ TOMB →
    K.ok (mk1G S m j) (mk2G S m j) ∧ MemoV VR m (mvG S m j) (f (K.dk (mk1G S m j) (mk2G S m j)))) ∧
  (∀ j j', InReg b n j → InReg b n j' → mstG S m j = e → mstG S m j' = e →
    mk1G S m j ≠ TOMB → mk1G S m j = mk1G S m j' → mk2G S m j = mk2G S m j' → j = j') ∧
  (∀ (x : κ) (v : ν), f x = some v → K.dk (K.ek x).1 (K.ek x).2 = x ∧ (K.ek x).1 ≠ TOMB ∧
    ∃ d : Nat, mstG S m (runAt b n (K.ek x).1 (K.ek x).2 d) = e ∧
    mk1G S m (runAt b n (K.ek x).1 (K.ek x).2 d) = (K.ek x).1 ∧
    mk2G S m (runAt b n (K.ek x).1 (K.ek x).2 d) = (K.ek x).2 ∧
    ∀ e' < d, mstG S m (runAt b n (K.ek x).1 (K.ek x).2 e') = e)

end rel

/-- The array's slot count (header slot included). -/
def slotsG (S : MemoSch) (m : Mem) : Nat := (m.len64 S.arr).toNat / 4

/-- **The region is well placed**: it is empty or lies in the array after the header slot; no
slot (nor the header's first word) holds a stamp above the live one; no slot above the region is
live (so a region grown right above it starts empty). -/
def RegOK (S : MemoSch) (m : Mem) : Prop :=
  ((nG S m).toNat = 0 ∨ (1 ≤ (mbG S m).toNat ∧ (mbG S m).toNat + (nG S m).toNat ≤ slotsG S m)) ∧
  (∀ j : Word, j.toNat < slotsG S m → (mstG S m j).toNat ≤ (epG S m).toNat) ∧
  (∀ j : Word, (mbG S m).toNat + (nG S m).toNat ≤ j.toNat → j.toNat < slotsG S m →
    mstG S m j ≠ epG S m) ∧
  (rdW (m.arr64 S.arr) 0).toNat ≤ (epG S m).toNat

section rel2
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop)

/-- **The memo relation, with a value relation that may read memory** (a value word can be a
pointer into a tree heap: `VR m w v` says `w` denotes `v` in `m`): the control words are there,
the live stamp is not `0`, the region is well placed, and its slots represent `mp`. -/
def MemoRV (m : Mem) (mp : Std.HashMap κ ν) : Prop :=
  S.cs.toNat + 2 ≤ (m.arr64 CTL).size ∧ epG S m ≠ 0 ∧ RegOK S m ∧
  MemoAt S K VR (epG S m) (mbG S m) (nG S m) m (fun x => mp[x]?)

/-- The value relation survives the memo's own writes (it reads other memory only). -/
def VStable : Prop :=
  ∀ m m', MemFrame [S.arr] [S.cs, S.cs + 1] m m' → ∀ w v, VR m w v → VR m' w v

/-- **The memo relation with word values** (`dv` decodes a value word): `MemoRV` at the value
relation `v = dv w`. -/
def MemoRG (dv : Word → ν) (m : Mem) (mp : Std.HashMap κ ν) : Prop :=
  MemoRV S K (fun _ w v => v = dv w) m mp

end rel2

/-! ## The probe -/

theorem slotsG_lt (S : MemoSch) (m : Mem) : slotsG S m < 2 ^ 62 := by
  have := (m.len64 S.arr).toNat_lt; simp only [slotsG]; omega

theorem runAt_reg (b n k1 k2 : Word) (d : Nat) (hn : 0 < n) (hb : b.toNat + n.toNat < 2 ^ 64) :
    InReg b n (runAt b n k1 k2 d) ∧
      (runAt b n k1 k2 d).toNat = b.toNat + (walkW n (homeW (kh k1 k2) n) d).toNat := by
  have hw := walkW_lt n (homeW (kh k1 k2) n) d (homeW_lt _ _ hn)
  have hw' : (walkW n (homeW (kh k1 k2) n) d).toNat < n.toNat := hw
  have e : (runAt b n k1 k2 d).toNat = b.toNat + (walkW n (homeW (kh k1 k2) n) d).toNat := by
    simp only [runAt, UInt64.toNat_add]; omega
  exact ⟨⟨by omega, by omega⟩, e⟩

/-- The first `d` slots of the run of `(k1, k2)` are live and hold other keys. -/
def MNoMatchAt (S : MemoSch) (m : Mem) (e b n k1 k2 : Word) (d : Nat) : Prop :=
  ∀ e' < d, mstG S m (runAt b n k1 k2 e') = e ∧
    ¬ (mk1G S m (runAt b n k1 k2 e') = k1 ∧ mk2G S m (runAt b n k1 k2 e') = k2)

/-- What the probe's result `rs` says: the region is not empty; a hit is a live slot `rs[1]` of the
run with key `(k1, k2)`; a miss is the non-live slot `rs[1]`, step `rs[2]` of the run, after live
slots with other keys. -/
def MProbeOKAt (S : MemoSch) (m : Mem) (e b n k1 k2 : Word) (rs : List Word) : Prop :=
  rs ≠ [] → 0 < n ∧
    (rs.headD 0 ≠ 0 → mstG S m (rs.tail.headD 0) = e ∧ mk1G S m (rs.tail.headD 0) = k1 ∧
      mk2G S m (rs.tail.headD 0) = k2 ∧ ∃ d : Nat, rs.tail.headD 0 = runAt b n k1 k2 d) ∧
    (rs.headD 0 = 0 → rs.tail.headD 0 = runAt b n k1 k2 (rs.tail.tail.headD 0).toNat ∧
      mstG S m (rs.tail.headD 0) ≠ e ∧ MNoMatchAt S m e b n k1 k2 (rs.tail.tail.headD 0).toNat)

theorem mprobeG_okAt (S : MemoSch) (m : Mem) (e b n k1 k2 : Word)
    (hx : homeW (kh k1 k2) n < n) :
    ∀ (k : Nat) (d : Word), n.toNat - d.toNat = k → MNoMatchAt S m e b n k1 k2 d.toNat →
      MProbeOKAt S m e b n k1 k2
        (mprobeG (m.arr64 S.arr) k1 k2 e b n (walkW n (homeW (kh k1 k2) n) d.toNat) d) := by
  have hn : 0 < n := by
    have : (homeW (kh k1 k2) n).toNat < n.toNat := hx
    exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
  intro k
  induction k with
  | zero =>
    intro d hk _; rw [mprobeG]; grind [MProbeOKAt]
  | succ k ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < n := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    rw [hd1, walkW_succ] at this
    rw [mprobeG]
    have hrun : b + walkW n (homeW (kh k1 k2) n) d.toNat = runAt b n k1 k2 d.toNat := rfl
    by_cases h0 : rdW (m.arr64 S.arr) ((b + walkW n (homeW (kh k1 k2) n) d.toNat) * 4) ≠ e
    · simp only [hd, h0, ↓reduceIte, ne_eq, not_false_eq_true]
      refine fun _ => ⟨hn, fun h => by simp at h, fun _ => ?_⟩
      simp only [List.tail_cons, List.headD_cons, ← hrun]
      exact ⟨trivial, h0, hnm⟩
    by_cases hm : rdW (m.arr64 S.arr) ((b + walkW n (homeW (kh k1 k2) n) d.toNat) * 4 + 1) = k1 ∧
        rdW (m.arr64 S.arr) ((b + walkW n (homeW (kh k1 k2) n) d.toNat) * 4 + 2) = k2
    · simp only [hd, h0, hm, ↓reduceIte, ne_eq, not_true_eq_false, and_self]
      refine fun _ => ⟨hn, fun _ => ?_, fun h => by simp at h⟩
      simp only [List.tail_cons, List.headD_cons]
      simp only [ne_eq, Decidable.not_not] at h0
      exact ⟨h0, hm.1, hm.2, d.toNat, hrun⟩
    · simp only [hd, h0, hm, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
      simp only [ne_eq, Decidable.not_not] at h0
      exact this (fun e' he' => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h | h
        · exact hnm e' h
        · subst h; exact ⟨h0, hm⟩)

/-- The probe from the home slot. -/
theorem mprobeG_home_ok (S : MemoSch) (m : Mem) (e b n k1 k2 : Word) :
    MProbeOKAt S m e b n k1 k2 (mprobeG (m.arr64 S.arr) k1 k2 e b n (homeW (kh k1 k2) n) 0) := by
  by_cases hn : n = 0
  · subst hn; rw [mprobeG]; simp [MProbeOKAt]
  · have := mprobeG_okAt S m e b n k1 k2 (homeW_lt _ _ (by grind)) _ 0 rfl
      (by simp [MNoMatchAt])
    simpa [walkW] using this

/-- The probe `X_find` makes. -/
theorem mfindG_ok (S : MemoSch) (m : Mem) (k1 k2 : Word) :
    MProbeOKAt S m (epG S m) (mbG S m) (nG S m) k1 k2 (mfindG S m k1 k2) :=
  mprobeG_home_ok S m _ _ _ k1 k2

/-- The free-slot probe of the growth. -/
theorem mslotG_ok (S : MemoSch) (m : Mem) (e b n k1 k2 : Word) :
    MProbeOKAt S m e b n k1 k2 (mslotG (m.arr64 S.arr) k1 k2 e b n) :=
  mprobeG_home_ok S m e b n k1 k2

/-- A non-empty region of a well-placed memo lies in the array. -/
theorem RegOK.bound {S : MemoSch} {m : Mem} (h : RegOK S m) (hn : 0 < nG S m) :
    1 ≤ (mbG S m).toNat ∧ (mbG S m).toNat + (nG S m).toNat ≤ slotsG S m := by
  rcases h.1 with h0 | h1
  · exact absurd h0 (by have : 0 < (nG S m).toNat := hn; omega)
  · exact h1

theorem RegOK.noov {S : MemoSch} {m : Mem} (h : RegOK S m) (hn : 0 < nG S m) :
    (mbG S m).toNat + (nG S m).toNat < 2 ^ 64 := by
  have := h.bound hn; have := slotsG_lt S m; omega

section relLemmas
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop)

omit [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] in
/-- **A probe hit is the entry of `f`**, a value the slot's word denotes. -/
theorem memoAt_hit (e b n : Word) (m : Mem) (f : κ → Option ν) (hA : MemoAt S K VR e b n m f)
    (hb : b.toNat + n.toNat < 2 ^ 64) (k1 k2 : Word) (rs : List Word)
    (hok : MProbeOKAt S m e b n k1 k2 rs) (hr : rs ≠ []) (hh : rs.headD 0 ≠ 0) (hk : K.ok k1 k2) :
    MemoV VR m (mvG S m (rs.tail.headD 0)) (f (K.dk k1 k2)) := by
  obtain ⟨hn, hhit, -⟩ := hok hr
  obtain ⟨h1, h2, h3, d, hd⟩ := hhit hh
  have hreg := (runAt_reg b n k1 k2 d hn hb).1
  rw [← hd] at hreg
  have := hA.1 _ hreg h1 (by rw [h2]; exact K.ok_tomb k1 k2 hk)
  rw [h2, h3] at this
  exact this.2

omit [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] in
/-- **A probe miss is the absence from `f`.** -/
theorem memoAt_miss (e b n : Word) (m : Mem) (f : κ → Option ν) (hA : MemoAt S K VR e b n m f)
    (k1 k2 : Word) (rs : List Word) (hok : MProbeOKAt S m e b n k1 k2 rs) (hk : K.ok k1 k2)
    (hr : rs ≠ []) (hh : rs.headD 0 = 0) : f (K.dk k1 k2) = none := by
  obtain ⟨-, -, hmiss⟩ := hok hr
  obtain ⟨hj, hfree, hnm⟩ := hmiss hh
  cases hc : f (K.dk k1 k2) with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨-, -, d, hd1, hd2, hd2', hd3⟩ := hA.2.2 _ _ hc
    rw [K.ek_dk k1 k2 hk] at hd1 hd2 hd2' hd3
    by_cases hlt' : d < (rs.tail.tail.headD 0).toNat
    · exact (hnm d hlt').2 ⟨hd2, hd2'⟩
    · by_cases heq : d = (rs.tail.tail.headD 0).toNat
      · subst heq; rw [← hj] at hd1; exact hfree hd1
      · have := hd3 (rs.tail.tail.headD 0).toNat (by omega)
        rw [← hj] at this; exact hfree this

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **A probe hit is the map's entry**, a value the slot's word denotes. -/
theorem memoRV_hit (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp) (k1 k2 : Word)
    (hr : mfindG S m k1 k2 ≠ []) (hh : (mfindG S m k1 k2).headD 0 ≠ 0) (hk : K.ok k1 k2) :
    MemoV VR m (mvG S m ((mfindG S m k1 k2).tail.headD 0)) mp[K.dk k1 k2]? :=
  memoAt_hit S K VR _ _ _ m _ hR.2.2.2 (hR.2.2.1.noov ((mfindG_ok S m k1 k2 hr).1)) k1 k2 _
    (mfindG_ok S m k1 k2) hr hh hk

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **A probe miss is the map's absence.** -/
theorem memoRV_miss (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp) (k1 k2 : Word)
    (hk : K.ok k1 k2) (hr : mfindG S m k1 k2 ≠ []) (hh : (mfindG S m k1 k2).headD 0 = 0) :
    mp[K.dk k1 k2]? = none :=
  memoAt_miss S K VR _ _ _ m (fun x => mp[x]?) hR.2.2.2 k1 k2 _ (mfindG_ok S m k1 k2) hk hr hh

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- A probe hit of `MemoRG` is the map's entry. -/
theorem memoRG_hit (dv : Word → ν) (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp)
    (k1 k2 : Word) (hr : mfindG S m k1 k2 ≠ []) (hh : (mfindG S m k1 k2).headD 0 ≠ 0)
    (hk : K.ok k1 k2) :
    mp[K.dk k1 k2]? = some (dv (mvG S m ((mfindG S m k1 k2).tail.headD 0))) := by
  obtain ⟨v, h1, h2⟩ := memoRV_hit S K _ m mp hR k1 k2 hr hh hk
  rw [h1, h2]

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- A probe miss of `MemoRG` is the map's absence. -/
theorem memoRG_miss (dv : Word → ν) (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp)
    (k1 k2 : Word) (hk : K.ok k1 k2) (hr : mfindG S m k1 k2 ≠ [])
    (hh : (mfindG S m k1 k2).headD 0 = 0) : mp[K.dk k1 k2]? = none :=
  memoRV_miss S K _ m mp hR k1 k2 hk hr hh

end relLemmas

/-! ## Slot reads -/

theorem slotsG_toNat (S : MemoSch) (m : Mem) : slotsG S m = (m.arr64 S.arr).size % 2 ^ 64 / 4 := by
  simp only [slotsG, len64_eq, UInt64.toNat_ofNat']

/-- Word `f < 4` of slot `x`. -/
theorem adS (S : MemoSch) (m : Mem) (x : Word) (hx : x.toNat < slotsG S m) (f : Word)
    (hf : f.toNat < 4) :
    (x * 4 + f).toNat = x.toNat * 4 + f.toNat ∧ (x * 4 + f).toNat < (m.arr64 S.arr).size := by
  have := slotsG_lt S m
  rw [slotsG_toNat] at hx
  have := (m.arr64 S.arr).size.mod_le (2 ^ 64)
  have e : (x * 4 + f).toNat = x.toNat * 4 + f.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    rw [show (4 : Word).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨e, by omega⟩

theorem adS_eq (S : MemoSch) (m : Mem) (x y : Word) (hx : x.toNat < slotsG S m)
    (hy : y.toNat < slotsG S m) (f g : Word) (hf : f.toNat < 4) (hg : g.toNat < 4) :
    (x * 4 + f = y * 4 + g) ↔ (x = y ∧ f = g) := by
  constructor
  · intro h
    have h' := congrArg UInt64.toNat h
    rw [(adS S m x hx f hf).1, (adS S m y hy g hg).1] at h'
    exact ⟨UInt64.toNat_inj.mp (by omega), UInt64.toNat_inj.mp (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem slotsG_set64 (S : MemoSch) (m : Mem) (a : ArrId) (k v : Word) :
    slotsG S (m.set64 a k v) = slotsG S m := by
  simp only [slotsG, len64_eq, size_set64]

/-- Word `f` of slot `j` after a write to word `g` of slot `s`. -/
theorem rdS_set (S : MemoSch) (m : Mem) (s j f g v : Word) (hs : s.toNat < slotsG S m)
    (hj : j.toNat < slotsG S m) (hf : f.toNat < 4) (hg : g.toNat < 4) :
    rdW ((m.set64 S.arr (s * 4 + g) v).arr64 S.arr) (j * 4 + f) =
      if s = j ∧ g = f then v else rdW (m.arr64 S.arr) (j * 4 + f) := by
  rw [rdW_set64]
  have := (adS S m s hs g hg).2
  by_cases h : s = j ∧ g = f
  · obtain ⟨rfl, rfl⟩ := h; simp only [and_self, this, ↓reduceIte]
  · have : ¬ (s * 4 + g = j * 4 + f) := fun e => h ((adS_eq S m s j hs hj g f hg hf).mp e)
    simp [h, this]

/-- The four words of slot `j` after a write to word `g` of slot `s`. -/
theorem slot_set (S : MemoSch) (m : Mem) (s g v : Word) (hs : s.toNat < slotsG S m)
    (hg : g.toNat < 4) (j : Word) (hj : j.toNat < slotsG S m) :
    mstG S (m.set64 S.arr (s * 4 + g) v) j = (if s = j ∧ g = 0 then v else mstG S m j) ∧
    mk1G S (m.set64 S.arr (s * 4 + g) v) j = (if s = j ∧ g = 1 then v else mk1G S m j) ∧
    mk2G S (m.set64 S.arr (s * 4 + g) v) j = (if s = j ∧ g = 2 then v else mk2G S m j) ∧
    mvG S (m.set64 S.arr (s * 4 + g) v) j = (if s = j ∧ g = 3 then v else mvG S m j) := by
  have r := fun f hf => rdS_set S m s j f g v hs hj hf hg
  have r0 := r 0 (by decide)
  simp only [UInt64.add_zero] at r0
  exact ⟨r0, r 1 (by decide), r 2 (by decide), r 3 (by decide)⟩

theorem slot_set0 (S : MemoSch) (m : Mem) (s v : Word) (hs : s.toNat < slotsG S m)
    (j : Word) (hj : j.toNat < slotsG S m) :
    mstG S (m.set64 S.arr (s * 4) v) j = (if s = j then v else mstG S m j) ∧
    mk1G S (m.set64 S.arr (s * 4) v) j = mk1G S m j ∧
    mk2G S (m.set64 S.arr (s * 4) v) j = mk2G S m j ∧
    mvG S (m.set64 S.arr (s * 4) v) j = mvG S m j := by
  have := slot_set S m s 0 v hs (by decide) j hj
  simpa using this

/-- Slot reads through a write to another array. -/
theorem slot_other (S : MemoSch) (m : Mem) (a : ArrId) (ha : a ≠ S.arr) (k v j : Word) :
    mstG S (m.set64 a k v) j = mstG S m j ∧ mk1G S (m.set64 a k v) j = mk1G S m j ∧
    mk2G S (m.set64 a k v) j = mk2G S m j ∧ mvG S (m.set64 a k v) j = mvG S m j := by
  simp only [mstG, mk1G, mk2G, mvG, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm ha), and_self]

/-- The header words (0, 1, 2 of slot 0) through a write to a slot `s ≥ 1`. -/
theorem hdr_set (S : MemoSch) (m : Mem) (s g v : Word) (hs : s.toNat < slotsG S m)
    (hs1 : 1 ≤ s.toNat) (hg : g.toNat < 4) (f : Word) (hf : f.toNat < 3) :
    rdW ((m.set64 S.arr (s * 4 + g) v).arr64 S.arr) f = rdW (m.arr64 S.arr) f := by
  have h0 : (0 : Word).toNat < slotsG S m := by simp; omega
  have := rdS_set S m s 0 f g v hs h0 (by omega) hg
  simp only [UInt64.zero_mul, UInt64.zero_add] at this
  rw [this]
  have : ¬ s = 0 := fun e => by subst e; simp at hs1
  simp [this]

/-- The region, the stamp and the slot count are those of the header and `CTL`: a memory that
agrees on the three header words, on `CTL[cs]` and on the array's size has the same region. -/
theorem reg_congr (S : MemoSch) (m m' : Mem)
    (hh : ∀ f : Word, f.toNat < 3 → rdW (m'.arr64 S.arr) f = rdW (m.arr64 S.arr) f)
    (hc : rdW (m'.arr64 CTL) S.cs = rdW (m.arr64 CTL) S.cs)
    (hz : (m'.arr64 S.arr).size = (m.arr64 S.arr).size) :
    epG S m' = epG S m ∧ mbG S m' = mbG S m ∧ nG S m' = nG S m ∧ slotsG S m' = slotsG S m ∧
      (hdG S m' ↔ hdG S m) := by
  have he : epG S m' = epG S m := by simp only [epG, hc]
  have hd : hdG S m' ↔ hdG S m := by
    simp only [hdG, he, hh 0 (by decide)]
  have hl : m'.len64 S.arr = m.len64 S.arr := by simp only [len64_eq, hz]
  refine ⟨he, ?_, ?_, by simp only [slotsG, hl], hd⟩
  · simp only [mbG, hh 1 (by decide)]
    by_cases h : hdG S m <;> simp [h, hd]
  · simp only [nG, hh 2 (by decide), hl]
    by_cases h : hdG S m <;> simp [h, hd]

/-! ## Writes: reads after `put`, the growth's header, frames -/

/-- The four words of slot `j` after `put`'s writes at slot `s`. -/
theorem mputMemE_reads (S : MemoSch) (hS : S.WF) (m : Mem) (fd s k1 k2 w e c : Word)
    (hs : s.toNat < slotsG S m) (j : Word) (hj : j.toNat < slotsG S m) :
    mstG S (mputMemE S m fd s k1 k2 w e c) j = (if j = s ∧ fd = 0 then e else mstG S m j) ∧
    mk1G S (mputMemE S m fd s k1 k2 w e c) j = (if j = s ∧ fd = 0 then k1 else mk1G S m j) ∧
    mk2G S (mputMemE S m fd s k1 k2 w e c) j = (if j = s ∧ fd = 0 then k2 else mk2G S m j) ∧
    mvG S (mputMemE S m fd s k1 k2 w e c) j = (if j = s then w else mvG S m j) := by
  have hac := hS.arr_ctl
  unfold mputMemE
  by_cases hfd : fd = 0
  · simp only [hfd, ↓reduceIte, and_true]
    have h1 := slot_set0 S m s e hs j hj
    have hs1 : s.toNat < slotsG S (m.set64 S.arr (s * 4) e) := by rw [slotsG_set64]; exact hs
    have hj1 : j.toNat < slotsG S (m.set64 S.arr (s * 4) e) := by rw [slotsG_set64]; exact hj
    have h2 := slot_set S _ s 1 k1 hs1 (by decide) j hj1
    have hs2 : s.toNat < slotsG S ((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1) := by
      rw [slotsG_set64]; exact hs1
    have hj2 : j.toNat < slotsG S ((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1) := by
      rw [slotsG_set64]; exact hj1
    have h3 := slot_set S _ s 2 k2 hs2 (by decide) j hj2
    have h4 := slot_other S (((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1).set64 S.arr
      (s * 4 + 2) k2) CTL (Ne.symm hac) (S.cs + 1) (c + 1) j
    have hs4 : s.toNat < slotsG S ((((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1).set64
        S.arr (s * 4 + 2) k2).set64 CTL (S.cs + 1) (c + 1)) := by
      simp only [slotsG_set64]; exact hs
    have hj4 : j.toNat < slotsG S ((((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1).set64
        S.arr (s * 4 + 2) k2).set64 CTL (S.cs + 1) (c + 1)) := by
      simp only [slotsG_set64]; exact hj
    have h5 := slot_set S _ s 3 w hs4 (by decide) j hj4
    rw [h5.1, h5.2.1, h5.2.2.1, h5.2.2.2, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2, h3.1, h3.2.1, h3.2.2.1,
      h3.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
    by_cases h : j = s
    · subst h; simp
    · have h' : ¬ s = j := fun e => h e.symm
      simp [h, h']
  · simp only [hfd, ↓reduceIte, and_false]
    have h5 := slot_set S m s 3 w hs (by decide) j hj
    rw [h5.1, h5.2.1, h5.2.2.1, h5.2.2.2]
    by_cases h : j = s
    · subst h; simp
    · have h' : ¬ s = j := fun e => h e.symm
      simp [h, h']

theorem mputMemE_frame (S : MemoSch) (hS : S.WF) (m : Mem) (fd j k1 k2 v e c : Word) :
    MemFrame [S.arr] [S.cs + 1] m (mputMemE S m fd j k1 k2 v e c) := by
  have hac := hS.arr_ctl
  have fa : ∀ (m : Mem) k v, MemFrame [S.arr] [S.cs + 1] m (m.set64 S.arr k v) :=
    fun m k v => (MemFrame.set64 m S.arr hac k v).mono (by simp) (by simp)
  have fc : ∀ (m : Mem) v, MemFrame [S.arr] [S.cs + 1] m (m.set64 CTL (S.cs + 1) v) :=
    fun m v => (MemFrame.setCtl m (S.cs + 1) v).mono (by simp) (by simp)
  unfold mputMemE
  split
  · exact ((((fa _ _ _).trans (fa _ _ _)).trans (fa _ _ _)).trans (fc _ _)).trans (fa _ _ _)
  · exact fa _ _ _

/-- The header and `CTL[cs]` after `put`'s writes at a slot `s ≥ 1`: the region stays. -/
theorem mputMemE_reg (S : MemoSch) (hS : S.WF) (m : Mem) (fd s k1 k2 w e c : Word)
    (hs : s.toNat < slotsG S m) (hs1 : 1 ≤ s.toNat) :
    epG S (mputMemE S m fd s k1 k2 w e c) = epG S m ∧ mbG S (mputMemE S m fd s k1 k2 w e c) = mbG S m ∧
      nG S (mputMemE S m fd s k1 k2 w e c) = nG S m ∧
      slotsG S (mputMemE S m fd s k1 k2 w e c) = slotsG S m ∧
      rdW ((mputMemE S m fd s k1 k2 w e c).arr64 S.arr) 0 = rdW (m.arr64 S.arr) 0 := by
  have hac := hS.arr_ctl
  have hf := mputMemE_frame S hS m fd s k1 k2 w e c
  have hcs : S.cs ≠ S.cs + 1 := by intro h; have := hS.cs; grind
  have hh : ∀ f : Word, f.toNat < 3 →
      rdW ((mputMemE S m fd s k1 k2 w e c).arr64 S.arr) f = rdW (m.arr64 S.arr) f := by
    intro f hf3
    have hz := fun (m : Mem) (g v : Word) (hs' : s.toNat < slotsG S m) (hg : g.toNat < 4) =>
      hdr_set S m s g v hs' hs1 hg f hf3
    unfold mputMemE
    split
    · rw [hz _ 3 _ (by simp only [slotsG_set64]; exact hs) (by decide)]
      rw [show rdW ((((((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1).set64 S.arr
          (s * 4 + 2) k2).set64 CTL (S.cs + 1) (c + 1))).arr64 S.arr) f =
          rdW ((((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) k1).set64 S.arr
          (s * 4 + 2) k2).arr64 S.arr) f by rw [Mem.arr64_set64_ne _ _ _ _ _ hac]]
      rw [hz _ 2 _ (by simp only [slotsG_set64]; exact hs) (by decide),
        hz _ 1 _ (by simp only [slotsG_set64]; exact hs) (by decide)]
      have := hz m 0 e hs (by decide)
      simpa using this
    · exact hz m 3 w hs (by decide)
  obtain ⟨h1, h2, h3, h4, -⟩ := reg_congr S m _ hh (hf.2.1 S.cs (by simp [hcs])) (hf.2.2.1 S.arr)
  exact ⟨h1, h2, h3, h4, hh 0 (by decide)⟩

theorem mputMem_frame (S : MemoSch) (hS : S.WF) (m : Mem) (fd j k1 k2 v : Word) :
    MemFrame [S.arr] [S.cs + 1] m (mputMem S m fd j k1 k2 v) :=
  mputMemE_frame S hS m fd j k1 k2 v _ _

theorem mrehashG_frame (S : MemoSch) (hS : S.WF) (e nb nn : Word) :
    ∀ (k : Nat) (i c : Word) (m m' : Mem) (c' : Word), nb.toNat - i.toNat = k →
      mrehashG S e nb nn i c m = some (m', c') → MemFrame [S.arr] [] m m' := by
  intro k
  induction k with
  | zero =>
    intro i c m m' c' hk h
    rw [mrehashG] at h
    have hi : ¬ i < nb := fun h' => by have : i.toNat < nb.toNat := h'; omega
    simp only [hi, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact MemFrame.refl _ _ _
  | succ k ih =>
    intro i c m m' c' hk h
    rw [mrehashG] at h
    by_cases hi : i < nb
    · have hi' : i.toNat < nb.toNat := hi
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := nb.toNat_lt; omega
      simp only [hi, ↓reduceIte] at h
      split at h
      · split at h
        · have := ih _ _ _ _ _ (by omega) h
          refine (MemFrame.trans ?_ this)
          have fa := fun (m : Mem) k v => MemFrame.set64 m S.arr hS.arr_ctl k v
          exact ((fa _ _ _).trans (fa _ _ _)).trans (fa _ _ _) |>.trans (fa _ _ _)
        · simp at h
      · exact ih _ _ _ _ _ (by omega) h
    · have : ¬ i.toNat < nb.toNat := fun h' => hi (UInt64.lt_iff_toNat_lt.mpr h')
      omega

theorem mgrowAt_frame (S : MemoSch) (hS : S.WF) (e b n : Word) (m m₁ : Mem) (c : Word)
    (h : mgrowAt S e b n m = some (m₁, c)) : MemFrame [S.arr] [S.cs + 1] m m₁ := by
  simp only [mgrowAt] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i m' c' hr
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]
  have f0 : MemFrame [S.arr] [S.cs + 1] m m' :=
    (mrehashG_frame S hS e _ _ _ _ _ _ _ _ rfl hr).mono (by simp) (by simp)
  have fa : ∀ (m : Mem) k v, MemFrame [S.arr] [S.cs + 1] m (m.set64 S.arr k v) :=
    fun m k v => (MemFrame.set64 m S.arr hS.arr_ctl k v).mono (by simp) (by simp)
  have fc : ∀ (m : Mem) v, MemFrame [S.arr] [S.cs + 1] m (m.set64 CTL (S.cs + 1) v) :=
    fun m v => (MemFrame.setCtl m (S.cs + 1) v).mono (by simp) (by simp)
  exact (((f0.trans (fa _ _ _)).trans (fa _ _ _)).trans (fa _ _ _)).trans (fc _ _)

theorem mputG_frame (S : MemoSch) (hS : S.WF) (m m' : Mem) (k1 k2 v fd j : Word)
    (h : mputG S m k1 k2 v fd j = some m') : MemFrame [S.arr] [S.cs + 1] m m' := by
  simp only [mputG] at h
  split at h
  · split at h
    · simp at h
    · rename_i m₁ c hg
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact (mgrowAt_frame S hS _ _ _ m m₁ c hg).trans (mputMemE_frame S hS _ _ _ _ _ _ _ _)
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

/-! ## The relation lemmas -/

section setClear
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (hS : S.WF) (K : MemoKey κ) (VR : Mem → Word → ν → Prop)

theorem getElem?_insert_fun (mp : Std.HashMap κ ν) (k : κ) (x : ν) :
    (fun z => (mp.insert k x)[z]?) = fun z => if (k == z) = true then some x else mp[z]? := by
  funext z; rw [Std.HashMap.getElem?_insert]

omit [Hashable κ] [LawfulHashable κ] in
/-- **Writing a probed slot is an update of `f`**: at a miss, the stamp, the key and the value;
at a hit, the value. -/
theorem memoAt_write (e b n : Word) (hb : b.toNat + n.toNat < 2 ^ 64) (m m' : Mem)
    (f : κ → Option ν) (hA : MemoAt S K VR e b n m f) (hV : ∀ w v, VR m w v → VR m' w v)
    (k1 k2 w : Word) (hk : K.ok k1 k2) (x : ν) (hx : VR m w x)
    (rs : List Word) (hr : rs ≠ []) (hok : MProbeOKAt S m e b n k1 k2 rs)
    (r3 : ∀ j, InReg b n j → mstG S m' j =
      if j = rs.tail.headD 0 ∧ rs.headD 0 = 0 then e else mstG S m j)
    (r4 : ∀ j, InReg b n j → mk1G S m' j =
      if j = rs.tail.headD 0 ∧ rs.headD 0 = 0 then k1 else mk1G S m j)
    (r4' : ∀ j, InReg b n j → mk2G S m' j =
      if j = rs.tail.headD 0 ∧ rs.headD 0 = 0 then k2 else mk2G S m j)
    (r5 : ∀ j, InReg b n j → mvG S m' j = if j = rs.tail.headD 0 then w else mvG S m j) :
    MemoAt S K VR e b n m' (fun z => if (K.dk k1 k2 == z) = true then some x else f z) := by
  obtain ⟨hn0, hhit', hmiss'⟩ := hok hr
  have hmiss := fun hh => memoAt_miss S K VR e b n m f hA k1 k2 rs hok hk hr hh
  have htk := K.ok_tomb k1 k2 hk
  have hdk := K.ek_dk k1 k2 hk
  have hreg := fun d => (runAt_reg b n k1 k2 d hn0 hb).1
  have hj : InReg b n (rs.tail.headD 0) := by
    by_cases hh : rs.headD 0 = 0
    · rw [(hmiss' hh).1]; exact hreg _
    · obtain ⟨-, -, -, d, hd⟩ := hhit' hh; rw [hd]; exact hreg d
  obtain ⟨hlive, huniq, hrun⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro j hj' hl htomb
    rw [r3 j hj'] at hl
    rw [r4 j hj'] at htomb
    rw [r4 j hj', r4' j hj', r5 j hj']
    by_cases hjj : j = rs.tail.headD 0
    · subst hjj
      by_cases hh : rs.headD 0 = 0
      · simp only [hh, and_self, ↓reduceIte, beq_self_eq_true]
        exact ⟨hk, x, rfl, hV _ _ hx⟩
      · obtain ⟨h1, h2, h2', -⟩ := hhit' hh
        simp only [hh, and_false, ↓reduceIte, h2, h2', beq_self_eq_true]
        exact ⟨hk, x, rfl, hV _ _ hx⟩
    · simp only [hjj, false_and, ↓reduceIte] at hl htomb ⊢
      obtain ⟨hk', v, hm, hv⟩ := hlive j hj' hl htomb
      refine ⟨hk', v, ?_, hV _ _ hv⟩
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
          exact hjj (huniq _ _ hj' hj hl h1 htomb (by rw [h2, e1]) (by rw [h2', e2]))
      simp only [this, Bool.false_eq_true, ↓reduceIte, hm]
  · intro j j' hj1 hj2 hl1 hl2 htomb hkk hkk'
    rw [r3 j hj1] at hl1
    rw [r3 j' hj2] at hl2
    rw [r4 j hj1] at htomb
    rw [r4 j hj1, r4 j' hj2] at hkk
    rw [r4' j hj1, r4' j' hj2] at hkk'
    by_cases hh : rs.headD 0 = 0
    · have habs : ∀ j'', InReg b n j'' → mstG S m j'' = e →
          ¬ (mk1G S m j'' = k1 ∧ mk2G S m j'' = k2) := by
        intro j'' hj'' hl'' ⟨hk1, hk2⟩
        obtain ⟨-, v, hm, -⟩ := hlive j'' hj'' hl'' (by rw [hk1]; exact htk)
        rw [hk1, hk2, hmiss hh] at hm; simp at hm
      by_cases e1 : j = rs.tail.headD 0 <;> by_cases e2 : j' = rs.tail.headD 0
      · rw [e1, e2]
      · simp only [e1, e2, hh, and_self, ↓reduceIte, false_and] at hkk hkk' hl2
        exact absurd ⟨hkk.symm, hkk'.symm⟩ (habs j' hj2 hl2)
      · simp only [e1, e2, hh, and_self, ↓reduceIte, false_and] at hkk hkk' hl1
        exact absurd ⟨hkk, hkk'⟩ (habs j hj1 hl1)
      · simp only [e1, e2, false_and, ↓reduceIte] at hkk hkk' hl1 hl2 htomb
        exact huniq j j' hj1 hj2 hl1 hl2 htomb hkk hkk'
    · simp only [hh, and_false, ↓reduceIte] at hkk hkk' hl1 hl2 htomb
      exact huniq j j' hj1 hj2 hl1 hl2 htomb hkk hkk'
  · intro y u hy
    by_cases hxk : (K.dk k1 k2 == y) = true
    · have hxe : y = K.dk k1 k2 := (beq_iff_eq.mp hxk).symm
      subst hxe
      rw [hdk]
      refine ⟨rfl, htk, ?_⟩
      by_cases hh : rs.headD 0 = 0
      · obtain ⟨hj1, -, hnm⟩ := hmiss' hh
        refine ⟨(rs.tail.tail.headD 0).toNat, ?_, ?_, ?_, fun e' he => ?_⟩
        · rw [← hj1, r3 _ hj]; simp only [hh, and_self, ↓reduceIte]
        · rw [← hj1, r4 _ hj]; simp only [hh, and_self, ↓reduceIte]
        · rw [← hj1, r4' _ hj]; simp only [hh, and_self, ↓reduceIte]
        · rw [r3 _ (hreg e')]
          split
          · rfl
          · exact (hnm e' he).1
      · obtain ⟨hl, h2, h2', -⟩ := hhit' hh
        obtain ⟨v, hv, -⟩ := memoAt_hit S K VR e b n m f ⟨hlive, huniq, hrun⟩ hb k1 k2 rs hok hr hh hk
        obtain ⟨-, -, d, hd1, hd2, hd2', hd3⟩ := hrun _ _ hv
        rw [hdk] at hd1 hd2 hd2' hd3
        refine ⟨d, ?_, ?_, ?_, fun e' he => ?_⟩
        · rw [r3 _ (hreg d)]; simp only [hh, and_false, ↓reduceIte, hd1]
        · rw [r4 _ (hreg d)]; simp only [hh, and_false, ↓reduceIte, hd2]
        · rw [r4' _ (hreg d)]; simp only [hh, and_false, ↓reduceIte, hd2']
        · rw [r3 _ (hreg e')]
          simp only [hh, and_false, ↓reduceIte, hd3 e' he]
    · simp only [hxk, Bool.false_eq_true, ↓reduceIte] at hy
      obtain ⟨hdy, hty, d, hd1, hd2, hd2', hd3⟩ := hrun _ _ hy
      refine ⟨hdy, hty, ?_⟩
      have hreg' := fun d => (runAt_reg b n (K.ek y).1 (K.ek y).2 d hn0 hb).1
      have hl : ∀ e', mstG S m (runAt b n (K.ek y).1 (K.ek y).2 e') = e →
          mstG S m' (runAt b n (K.ek y).1 (K.ek y).2 e') = e := by
        intro e' he
        rw [r3 _ (hreg' e')]
        split
        · rfl
        · exact he
      have hfree : ¬ (runAt b n (K.ek y).1 (K.ek y).2 d = rs.tail.headD 0 ∧ rs.headD 0 = 0) := by
        rintro ⟨hc1, hc2⟩
        obtain ⟨-, hfr, -⟩ := hmiss' hc2
        exact hfr (hc1 ▸ hd1)
      refine ⟨d, hl d hd1, ?_, ?_, fun e' he => hl e' (hd3 e' he)⟩
      · rw [r4 _ (hreg' d)]
        simp only [hfree, ↓reduceIte, hd2]
      · rw [r4' _ (hreg' d)]
        simp only [hfree, ↓reduceIte, hd2']

omit [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] in
/-- `MemoAt` reads only the region's slots (when the region is not empty). -/
theorem memoAt_congr (e b n : Word) (hn : 0 < n) (hb : b.toNat + n.toNat < 2 ^ 64) (m m' : Mem)
    (f : κ → Option ν) (hA : MemoAt S K VR e b n m f) (hV : ∀ w v, VR m w v → VR m' w v)
    (hs : ∀ j, InReg b n j → mstG S m' j = mstG S m j ∧ mk1G S m' j = mk1G S m j ∧
      mk2G S m' j = mk2G S m j ∧ mvG S m' j = mvG S m j) :
    MemoAt S K VR e b n m' f := by
  obtain ⟨hlive, huniq, hrun⟩ := hA
  refine ⟨fun j hj hl ht => ?_, fun j j' hj hj' hl hl' ht hkk hkk' => ?_, fun x v hx => ?_⟩
  · obtain ⟨s1, s2, s3, s4⟩ := hs j hj
    rw [s1] at hl; rw [s2] at ht; rw [s2, s3, s4]
    obtain ⟨h1, u, h2, h3⟩ := hlive j hj hl ht
    exact ⟨h1, u, h2, hV _ _ h3⟩
  · obtain ⟨s1, s2, s3, -⟩ := hs j hj
    obtain ⟨t1, t2, t3, -⟩ := hs j' hj'
    rw [s1] at hl; rw [t1] at hl'; rw [s2] at ht; rw [s2, t2] at hkk; rw [s3, t3] at hkk'
    exact huniq j j' hj hj' hl hl' ht hkk hkk'
  · obtain ⟨hdx, htx, d, h1, h2, h2', h3⟩ := hrun x v hx
    have hreg := fun d => (runAt_reg b n (K.ek x).1 (K.ek x).2 d hn hb).1
    refine ⟨hdx, htx, d, ?_, ?_, ?_, fun e' he => ?_⟩
    · rw [(hs _ (hreg d)).1]; exact h1
    · rw [(hs _ (hreg d)).2.1]; exact h2
    · rw [(hs _ (hreg d)).2.2.1]; exact h2'
    · rw [(hs _ (hreg e')).1]; exact h3 e' he

/-- A region of `dfltN l` slots after slot `1` fits in an array of `l` words. -/
theorem dfltN_fits (l : Word) : (dfltN l).toNat = 0 ∨ (dfltN l).toNat + 1 ≤ l.toNat / 4 := by
  have hl : (l >>> 2).toNat = l.toNat / 4 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have hM : MN0.toNat = 16384 := rfl
  unfold dfltN
  by_cases h0 : (0 : Word) < l >>> 2
  · have h0' : 0 < l.toNat / 4 := by
      have := UInt64.lt_iff_toNat_lt.mp h0; simp at this; omega
    have hs : ((l >>> 2) - 1).toNat = l.toNat / 4 - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]; simp; omega), hl]; rfl
    simp only [h0, ↓reduceIte]
    split
    · rename_i h; have := UInt64.lt_iff_toNat_lt.mp h; rw [hs] at this; right; omega
    · right; omega
  · have : l.toNat / 4 = 0 := by
      rcases Nat.eq_zero_or_pos (l.toNat / 4) with h | h
      · exact h
      · exact absurd (UInt64.lt_iff_toNat_lt.mpr (by simp; omega)) h0
    simp only [h0, ↓reduceIte]
    have hz : (l >>> 2) - (0 : Word) = l >>> 2 := by simp
    rw [hz]
    split
    · rename_i h; have := UInt64.lt_iff_toNat_lt.mp h; rw [hl] at this; omega
    · left; rw [hl]; exact this

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **A memo whose stamps are all below the live one is the empty map** (after a `clear`, and on
zeroed memory): the header names no region, so the region is the default one, and no slot is
live. -/
theorem memoRV_fresh (m : Mem) (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) (he : epG S m ≠ 0)
    (h0 : (rdW (m.arr64 S.arr) 0).toNat < (epG S m).toNat)
    (hst : ∀ j : Word, j.toNat < slotsG S m → (mstG S m j).toNat < (epG S m).toNat) :
    MemoRV S K VR m ∅ := by
  have hd : ¬ hdG S m := fun h => by
    simp only [hdG] at h; rw [h] at h0; omega
  have hb : mbG S m = 1 := by simp [mbG, hd]
  have hn : nG S m = dfltN (m.len64 S.arr) := by simp [nG, hd]
  have hne : ∀ j : Word, j.toNat < slotsG S m → mstG S m j ≠ epG S m := fun j hj h => by
    have := hst j hj; rw [h] at this; omega
  refine ⟨hctl, he, ⟨?_, fun j hj => Nat.le_of_lt (hst j hj), fun j _ hj => hne j hj,
    Nat.le_of_lt h0⟩, ?_, ?_, fun x v h => by simp at h⟩
  · rw [hb, hn]
    rcases dfltN_fits (m.len64 S.arr) with h | h
    · left; exact h
    · right; simp only [slotsG]; refine ⟨by decide, ?_⟩
      have : (1 : Word).toNat = 1 := rfl
      omega
  · intro j hj hl
    exfalso
    rcases dfltN_fits (m.len64 S.arr) with h | h
    · rw [hn] at hj; have := hj.2; rw [h] at this; have := hj.1; omega
    · rw [hb, hn] at hj
      have : (1 : Word).toNat = 1 := rfl
      exact hne j (by simp only [slotsG]; have := hj.2; omega) hl
  · intro j _ hj _ hl
    exfalso
    rcases dfltN_fits (m.len64 S.arr) with h | h
    · rw [hn] at hj; have := hj.2; rw [h] at this; have := hj.1; omega
    · rw [hb, hn] at hj
      have : (1 : Word).toNat = 1 := rfl
      exact hne j (by simp only [slotsG]; have := hj.2; omega) hl

include hS in
/-- **`put` without a growth is `insert`.** -/
theorem memoRV_putNG (hVS : VStable S VR) (m : Mem) (mp : Std.HashMap κ ν)
    (hR : MemoRV S K VR m mp) (k1 k2 w : Word) (hk : K.ok k1 k2) (x : ν) (hx : VR m w x)
    (hr : mfindG S m k1 k2 ≠ []) :
    MemoRV S K VR (mputMem S m ((mfindG S m k1 k2).headD 0) ((mfindG S m k1 k2).tail.headD 0)
      k1 k2 w) (mp.insert (K.dk k1 k2) x) := by
  obtain ⟨hctl, hep, hreg, hA⟩ := hR
  have hok := mfindG_ok S m k1 k2
  generalize hrs : mfindG S m k1 k2 = rs at *
  obtain ⟨hn0, hhit', hmiss'⟩ := hok hr
  obtain ⟨hb1, hbn⟩ := hreg.bound hn0
  have hnov := hreg.noov hn0
  have hj : InReg (mbG S m) (nG S m) (rs.tail.headD 0) := by
    by_cases hh : rs.headD 0 = 0
    · rw [(hmiss' hh).1]; exact (runAt_reg _ _ k1 k2 _ hn0 hnov).1
    · obtain ⟨-, -, -, d, hd⟩ := hhit' hh; rw [hd]; exact (runAt_reg _ _ k1 k2 d hn0 hnov).1
  have hs : (rs.tail.headD 0).toNat < slotsG S m := by have := hj.2; omega
  have hs1 : 1 ≤ (rs.tail.headD 0).toNat := by have := hj.1; omega
  unfold mputMem
  generalize hm' : mputMemE S m (rs.headD 0) (rs.tail.headD 0) k1 k2 w (epG S m) (cntG S m) = m'
  have rd := fun j hj => mputMemE_reads S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 w (epG S m)
    (cntG S m) hs j hj
  obtain ⟨g1, g2, g3, g4, g5⟩ := mputMemE_reg S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 w
    (epG S m) (cntG S m) hs hs1
  rw [hm'] at rd g1 g2 g3 g4 g5
  have hf := mputMemE_frame S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 w (epG S m) (cntG S m)
  rw [hm'] at hf
  have hV : ∀ w v, VR m w v → VR m' w v :=
    hVS m m' (hf.mono (by simp) (fun y hy => by simp at hy; simp [hy]))
  have hsl : ∀ j, InReg (mbG S m) (nG S m) j → j.toNat < slotsG S m := fun j hj => by
    have := hj.2; omega
  refine ⟨by rw [hf.2.2.1]; exact hctl, by rw [g1]; exact hep, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g2, g3, g4]; right; exact ⟨hb1, hbn⟩
  · intro j hj'; rw [g4] at hj'; rw [(rd j hj').1, g1]
    split
    · exact Nat.le_refl _
    · exact hreg.2.1 j hj'
  · intro j hj1 hj2; rw [g2, g3] at hj1; rw [g4] at hj2; rw [(rd j hj2).1, g1]
    have : ¬ (j = rs.tail.headD 0 ∧ rs.headD 0 = 0) := fun ⟨e, _⟩ => by
      subst e; have := hj.2; omega
    simp only [this, ↓reduceIte]
    exact hreg.2.2.1 j hj1 hj2
  · rw [g5, g1]; exact hreg.2.2.2
  · rw [g1, g2, g3, getElem?_insert_fun]
    rw [← hrs] at hr
    exact memoAt_write S K VR _ _ _ hnov m m' _ hA hV k1 k2 w hk x hx rs (hrs ▸ hr)
      (hrs ▸ mfindG_ok S m k1 k2) (fun j hj => (rd j (hsl j hj)).1)
      (fun j hj => (rd j (hsl j hj)).2.1) (fun j hj => (rd j (hsl j hj)).2.2.1)
      (fun j hj => (rd j (hsl j hj)).2.2.2)

end setClear
end L.Arena
