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
slot holds a stamp above the live one; no slot above the region is live (so a region grown right
above it starts empty). -/
def RegOK (S : MemoSch) (m : Mem) : Prop :=
  ((nG S m).toNat = 0 ∨ (1 ≤ (mbG S m).toNat ∧ (mbG S m).toNat + (nG S m).toNat ≤ slotsG S m)) ∧
  (∀ j : Word, j.toNat < slotsG S m → (mstG S m j).toNat ≤ (epG S m).toNat) ∧
  (∀ j : Word, (mbG S m).toNat + (nG S m).toNat ≤ j.toNat → j.toNat < slotsG S m →
    mstG S m j ≠ epG S m)

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
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
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
      simp only [List.tail_cons, List.headD_cons, hrun]
      exact ⟨rfl, by rw [← hrun]; exact h0, hnm⟩
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

omit [LawfulBEq κ] [LawfulHashable κ] in
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

omit [LawfulBEq κ] [LawfulHashable κ] in
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
  · simp [h, this]
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

section setClear
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (hS : S.WF) (K : MemoKey κ) (VR : Mem → Word → ν → Prop)

include hS in
/-- **`find; put` is `insert`**, of a value the written word denotes. -/
theorem memoRV_set (hVS : VStable S VR) (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp)
    (k1 k2 w : Word) (hk : K.ok k1 k2) (x : ν) (hx : VR m w x) (m' : Mem)
    (h : msetG S m k1 k2 w = some m') :
    MemoRV S K VR m' (mp.insert (K.dk k1 k2) x) := by
  have hok := mfindG_ok S m k1 k2
  have hfr := msetG_frame S hS m m' k1 k2 w h
  have hV : ∀ w v, VR m w v → VR m' w v :=
    hVS m m' (hfr.mono (by simp) (fun y hy => by simp at hy; simp [hy]))
  simp only [msetG, mputG] at h
  split at h
  · simp at h
  rename_i hne
  split at h
  · simp at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hctl, hep, hst, hlive, huniq, hrun⟩ := hR
  have hmiss := fun hh => memoRV_miss S K VR m mp ⟨hctl, hep, hst, hlive, huniq, hrun⟩ k1 k2 hk hne hh
  have hok' := hok hne
  have htk := K.ok_tomb k1 k2 hk
  generalize hrs : mfindG S m k1 k2 = rs at *
  obtain ⟨hhit', hmiss'⟩ := hok'
  have hj : rs.tail.headD 0 < nG S m := by
    by_cases hh : rs.headD 0 = 0
    · exact (hmiss' hh).2.1
    · exact (hhit' hh).2.2.2
  obtain ⟨r1, r2, r3, r4, r4', r5⟩ := mputMem_reads S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 w hj
  have hdk := K.ek_dk k1 k2 hk
  refine ⟨?_, by rw [r1]; exact hep, ?_, ?_, ?_, ?_⟩
  · have := (mputMem_frame S hS m (rs.headD 0) (rs.tail.headD 0) k1 k2 w).2.2.1 CTL; omega
  · intro j hj'; rw [r2] at hj'; rw [r3 j hj', r1]; have := hst j hj'; split <;> grind
  · intro j hj' hl htomb
    rw [r2] at hj'
    rw [r3 j hj', r1] at hl
    rw [r4 j hj'] at htomb
    rw [r4 j hj', r4' j hj', r5 j hj']
    have hx' := hV _ _ hx
    by_cases hjj : j = rs.tail.headD 0
    · subst hjj
      by_cases hh : rs.headD 0 = 0
      · simp only [hh, and_self, ↓reduceIte, Std.HashMap.getElem?_insert_self] at hx' ⊢
        exact ⟨hk, x, rfl, hx'⟩
      · obtain ⟨h1, h2, h2', -⟩ := hhit' hh
        simp only [hh, and_false, ↓reduceIte, h2, h2', Std.HashMap.getElem?_insert_self]
        exact ⟨hk, x, rfl, hV _ _ hx⟩
    · simp only [hjj, false_and, ↓reduceIte] at hl htomb ⊢
      obtain ⟨hk', v, hm, hv⟩ := hlive j hj' hl htomb
      refine ⟨hk', v, ?_, hV _ _ hv⟩
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
          exact hjj (huniq _ _ hj' hj hl h1 htomb (by rw [h2, e1]) (by rw [h2', e2]))
      simp only [this, Bool.false_eq_true, ↓reduceIte, hm]
  · intro j j' hj1 hj2 hl1 hl2 htomb hkk hkk'
    rw [r2] at hj1 hj2
    rw [r3 j hj1, r1] at hl1
    rw [r3 j' hj2, r1] at hl2
    rw [r4 j hj1] at htomb
    rw [r4 j hj1, r4 j' hj2] at hkk
    rw [r4' j hj1, r4' j' hj2] at hkk'
    by_cases hh : rs.headD 0 = 0
    · -- the new key is absent from the old live slots
      have habs : ∀ j'', j'' < nG S m → mstG S m j'' = epG S m →
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
    rw [Std.HashMap.getElem?_insert] at hy
    have hn0 : 0 < nG S m := by grind
    have hr := fun a b e => mrunG_eq S m (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 w) r2 a b e
    by_cases hxk : (K.dk k1 k2 == y) = true
    · have hxe : y = K.dk k1 k2 := (beq_iff_eq.mp hxk).symm
      subst hxe
      rw [hdk]
      refine ⟨rfl, ?_⟩
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
        obtain ⟨v, hv, -⟩ := memoRV_hit S K VR m mp ⟨hctl, hep, hst, hlive, huniq, hrun⟩ k1 k2
          (by rw [hrs]; exact hne) (by rw [hrs]; exact hh) hk
        obtain ⟨-, d, hd1, hd2, hd2', hd3⟩ := hrun _ _ hv
        rw [hdk] at hd1 hd2 hd2' hd3
        refine ⟨d, ?_, ?_, ?_, fun e he => ?_⟩
        · rw [hr, r3 _ (mrunG_lt S m k1 k2 d hn0), r1]; simp only [hh, and_false, ↓reduceIte, hd1]
        · rw [hr, r4 _ (mrunG_lt S m k1 k2 d hn0)]; simp only [hh, and_false, ↓reduceIte, hd2]
        · rw [hr, r4' _ (mrunG_lt S m k1 k2 d hn0)]; simp only [hh, and_false, ↓reduceIte, hd2']
        · rw [hr, r3 _ (mrunG_lt S m k1 k2 e hn0), r1]
          simp only [hh, and_false, ↓reduceIte, hd3 e he]
    · simp only [hxk, Bool.false_eq_true, ↓reduceIte] at hy
      obtain ⟨hdy, d, hd1, hd2, hd2', hd3⟩ := hrun _ _ hy
      refine ⟨hdy, ?_⟩
      have hl : ∀ e, mstG S m (mrunG S m (K.ek y).1 (K.ek y).2 e) = epG S m →
          mstG S (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 w)
            (mrunG S (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 w) (K.ek y).1 (K.ek y).2 e) =
            epG S (mputMem S m (rs.headD 0) (rs.tail.headD 0) k1 k2 w) := by
        intro e he
        rw [hr, r3 _ (mrunG_lt S m _ _ e hn0), r1]
        split
        · rfl
        · exact he
      have hfree : ¬ (mrunG S m (K.ek y).1 (K.ek y).2 d = rs.tail.headD 0 ∧ rs.headD 0 = 0) := by
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
theorem memoRV_clear (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp)
    (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) : MemoRV S K VR (mclearG S m) ∅ := by
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
stamp**, when the values' denotations do (a heap that only grows, say). -/
theorem memoRV_frame (A : List ArrId) (C : List Word) (hA : S.arr ∉ A) (hC : S.cs ∉ C)
    (m m' : Mem) (hf : MemFrame A C m m') (hV : ∀ w v, VR m w v → VR m' w v)
    (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp) : MemoRV S K VR m' mp := by
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
  · intro j hj hl ht; rw [hs, he] at hl; rw [hk] at ht; rw [hk, hk', hv]
    obtain ⟨h1, u, h2, h3⟩ := hlive j (hn ▸ hj) hl ht
    exact ⟨h1, u, h2, hV _ _ h3⟩
  · intro j j' hj hj' hl hl' ht hkk hkk'; rw [hs, he] at hl hl'; rw [hk] at ht; rw [hk, hk] at hkk
    rw [hk', hk'] at hkk'
    exact huniq j j' (hn ▸ hj) (hn ▸ hj') hl hl' ht hkk hkk'
  · intro x v hx
    obtain ⟨hdx, d, h1, h2, h2', h3⟩ := hrun x v hx
    exact ⟨hdx, d, by rw [hr, hs, he]; exact h1, by rw [hr, hk]; exact h2,
      by rw [hr, hk']; exact h2', fun e hle => by rw [hr, hs, he]; exact h3 e hle⟩

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **All-zero memory is the empty map.** -/
theorem memoRV_zero (m : Mem) (hz : ∀ b x, rdW (m.arr64 b) x = 0)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) : MemoRV S K VR m ∅ := by
  refine ⟨hctl, by simp [epG, hz], fun j _ => by simp [mstG, epG, hz],
    fun j _ h => by simp [mstG, epG, hz] at h, fun j _ _ _ h => by simp [mstG, epG, hz] at h,
    fun x v h => by simp at h⟩

/-! ### Erase -/

include hS in
/-- Reads after `X_erase(s)`: only the first key word of slot `s` changed. -/
theorem meraseG_reads (m : Mem) (s : Word) (hs : s < nG S m) :
    epG S (meraseG S m s) = epG S m ∧ nG S (meraseG S m s) = nG S m ∧
    (∀ j, j < nG S m → mstG S (meraseG S m s) j = mstG S m j) ∧
    (∀ j, j < nG S m → mk1G S (meraseG S m s) j = if j = s then TOMB else mk1G S m j) ∧
    (∀ j, j < nG S m → mk2G S (meraseG S m s) j = mk2G S m j) ∧
    (∀ j, j < nG S m → mvG S (meraseG S m s) j = mvG S m j) := by
  have hac := hS.arr_ctl
  have l1 := adG_lt S m s hs 1 (by decide)
  have e := fun j (hj : j < nG S m) f (hf : f.toNat < 4) => adG_eq S m j s hj hs f 1 hf (by decide)
  refine ⟨by simp only [epG, meraseG, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hac)],
    by simp only [nG, meraseG, len64_eq, size_set64], fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_⟩
  · have := e j hj 0 (by decide); simp only [UInt64.add_zero] at this
    simp only [mstG, meraseG, rdW_set64, l1, and_true, true_and]
    split
    · rename_i h; exact absurd (this.mp h.symm).2 (by decide)
    · rfl
  · have := e j hj 1 (by decide)
    simp only [mk1G, meraseG, rdW_set64, l1, and_true, true_and]
    by_cases h : j = s
    · subst h; simp
    · simp only [h, ↓reduceIte]; split
      · rename_i h'; exact absurd (this.mp h'.symm).1 h
      · rfl
  · have := e j hj 2 (by decide)
    simp only [mk2G, meraseG, rdW_set64, l1, and_true, true_and]
    split
    · rename_i h; exact absurd (this.mp h.symm).2 (by decide)
    · rfl
  · have := e j hj 3 (by decide)
    simp only [mvG, meraseG, rdW_set64, l1, and_true, true_and]
    split
    · rename_i h; exact absurd (this.mp h.symm).2 (by decide)
    · rfl

include hS in
theorem meraseG_frame (m : Mem) (s : Word) : MemFrame [S.arr] [] m (meraseG S m s) :=
  MemFrame.set64 m S.arr hS.arr_ctl _ _

include hS in
/-- **`find` (a hit), then `X_erase` at the found slot, is `erase`.** -/
theorem memoRV_erase (hVS : VStable S VR) (m : Mem) (mp : Std.HashMap κ ν)
    (hR : MemoRV S K VR m mp) (k1 k2 : Word) (hk : K.ok k1 k2) (hr : mfindG S m k1 k2 ≠ [])
    (hh : (mfindG S m k1 k2).headD 0 ≠ 0) :
    MemoRV S K VR (meraseG S m ((mfindG S m k1 k2).tail.headD 0)) (mp.erase (K.dk k1 k2)) := by
  obtain ⟨hl0, hs1, hs2, hsn⟩ := (mfindG_ok S m k1 k2 hr).1 hh
  generalize hsd : (mfindG S m k1 k2).tail.headD 0 = s at *
  have hV : ∀ w v, VR m w v → VR (meraseG S m s) w v :=
    hVS m _ ((meraseG_frame S hS m s).mono (by simp) (by simp))
  obtain ⟨r1, r2, r3, r4, r4', r5⟩ := meraseG_reads S hS m s hsn
  have hdk := K.ek_dk k1 k2 hk
  obtain ⟨hctl, hep, hst, hlive, huniq, hrun⟩ := hR
  -- the only live slot with key `(k1, k2)` is `s`
  have honly : ∀ j, j < nG S m → mstG S m j = epG S m → mk1G S m j = k1 → mk2G S m j = k2 →
      j = s := fun j hj hl e1 e2 =>
    huniq j s hj hsn hl hl0 (by rw [e1]; exact K.ok_tomb k1 k2 hk) (by rw [e1, hs1]) (by rw [e2, hs2])
  refine ⟨by rw [(meraseG_frame S hS m s).2.2.1]; exact hctl, by rw [r1]; exact hep, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [r2] at hj; rw [r3 j hj, r1]; exact hst j hj
  · intro j hj hl ht
    rw [r2] at hj; rw [r3 j hj, r1] at hl; rw [r4 j hj] at ht ⊢; rw [r4' j hj, r5 j hj]
    by_cases hjs : j = s
    · simp [hjs] at ht
    simp only [hjs, ↓reduceIte] at ht ⊢
    obtain ⟨hk', u, hu, hvu⟩ := hlive j hj hl ht
    refine ⟨hk', u, ?_, hV _ _ hvu⟩
    rw [Std.HashMap.getElem?_erase]
    have : ¬ (K.dk k1 k2 == K.dk (mk1G S m j) (mk2G S m j)) = true := by
      intro he
      have := congrArg K.ek (beq_iff_eq.mp he)
      rw [hdk, K.ek_dk _ _ hk'] at this
      obtain ⟨e1, e2⟩ := Prod.mk.inj this
      exact hjs (honly j hj hl e1.symm e2.symm)
    simp only [this, Bool.false_eq_true, ↓reduceIte, hu]
  · intro j j' hj hj' hl hl' ht hkk hkk'
    rw [r2] at hj hj'
    rw [r3 j hj, r1] at hl; rw [r3 j' hj', r1] at hl'
    rw [r4 j hj] at ht; rw [r4 j hj, r4 j' hj'] at hkk; rw [r4' j hj, r4' j' hj'] at hkk'
    by_cases hjs : j = s
    · simp [hjs] at ht
    simp only [hjs, ↓reduceIte] at ht hkk
    by_cases hjs' : j' = s
    · simp only [hjs', ↓reduceIte] at hkk; exact absurd hkk ht
    simp only [hjs', ↓reduceIte] at hkk
    exact huniq j j' hj hj' hl hl' ht hkk hkk'
  · intro x v hx
    rw [Std.HashMap.getElem?_erase] at hx
    by_cases hxk : (K.dk k1 k2 == x) = true
    · simp [hxk] at hx
    simp only [hxk, Bool.false_eq_true, ↓reduceIte] at hx
    obtain ⟨hdx, d, h1, h2, h2', h3⟩ := hrun x v hx
    have hn0 : 0 < nG S m := by grind
    have hr : ∀ e, mrunG S (meraseG S m s) (K.ek x).1 (K.ek x).2 e = mrunG S m (K.ek x).1 (K.ek x).2 e :=
      fun e => mrunG_eq S m _ r2 _ _ e
    have hlt := mrunG_lt S m (K.ek x).1 (K.ek x).2 d hn0
    have hds : mrunG S m (K.ek x).1 (K.ek x).2 d ≠ s := by
      intro hds
      rw [hds, hs1] at h2; rw [hds, hs2] at h2'
      apply hxk
      rw [← hdx, ← h2, ← h2']
      simp
    refine ⟨hdx, d, ?_, ?_, ?_, fun e he => ?_⟩
    · rw [hr, r3 _ hlt, r1]; exact h1
    · rw [hr, r4 _ hlt]; simp only [hds, ↓reduceIte]; exact h2
    · rw [hr, r4' _ hlt]; exact h2'
    · rw [hr, r3 _ (mrunG_lt S m _ _ e hn0), r1]; exact h3 e he

/-! ### The word-valued memos (`MemoRG`) -/

variable (dv : Word → ν)

theorem vstable_eq : VStable S (fun (_ : Mem) w (v : ν) => v = dv w) := fun _ _ _ _ _ h => h

include hS in
theorem memoRG_set (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) (k1 k2 v : Word)
    (hk : K.ok k1 k2) (m' : Mem) (h : msetG S m k1 k2 v = some m') :
    MemoRG S K dv m' (mp.insert (K.dk k1 k2) (dv v)) :=
  memoRV_set S hS K _ (vstable_eq S dv) m mp hR k1 k2 v hk _ rfl m' h

include hS in
theorem memoRG_clear (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp)
    (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) : MemoRG S K dv (mclearG S m) ∅ :=
  memoRV_clear S hS K _ m mp hR hw

include hS in
omit [LawfulBEq κ] [LawfulHashable κ] in
theorem memoRG_frame (A : List ArrId) (C : List Word) (hA : S.arr ∉ A) (hC : S.cs ∉ C)
    (m m' : Mem) (hf : MemFrame A C m m') (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) :
    MemoRG S K dv m' mp :=
  memoRV_frame S hS K _ A C hA hC m m' hf (fun _ _ h => h) mp hR

omit [LawfulBEq κ] [LawfulHashable κ] in
theorem memoRG_zero (m : Mem) (hz : ∀ b x, rdW (m.arr64 b) x = 0)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) : MemoRG S K dv m ∅ :=
  memoRV_zero S K _ m hz hctl

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
theorem frSch_wf : frSch.WF := ⟨by decide, by decide⟩

/-- `bvarBC`'s keys: a handle word, second word `0`. -/
def bmKey : MemoKey EIdx where
  dk k1 _ := decE k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by simp only [word_decE k1 h.1, h.2]
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- `liftC`'s keys: a handle word and the cutoff. -/
def lfKey : MemoKey (EIdx × Nat) where
  dk k1 k2 := (decE k1, k2.toNat)
  ek x := (x.1.word.toUInt64, x.2.toUInt64)
  ok k1 _ := k1.toNat < 2 ^ 32
  ek_dk k1 k2 h := by simp only [word_decE k1 h, Nat.toUInt64_eq, UInt64.ofNat_toNat]
  ok_tomb k1 k2 h e := by subst e; exact absurd h (by decide)

end L.Arena
