import ConAgua.Arena.Frame
import ConAgua.Arena.MemoLib
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The memo library's relation: an L memo represents a `Std.HashMap κ ν`

The live slots of memo `S` lie in its **region** (`mbG`, `nG`: named by the header slot `0`, or the
default region after `clear`). `MemoAt S K VR e b n m f`: the live slots (stamp `e`) of the region
from slot `b` of `n` slots hold distinct keys, each a valid key (`K.ok`) whose decoding `K.dk` is
mapped by `f` to a value the slot's word denotes (`VR`), and every entry of `f` sits in a live slot
on the run from its encoded key's home, after live slots (linear probing; a stale stamp is free
space). `MemoRV S K VR m mp` is `MemoAt` of the memo's own region and stamp at `mp`'s lookup, plus
`RegOK`: the region lies in the array, no stamp is above the live one, and no slot above the region
is live. Generic in the schema, the key codec `K` (two words per key) and the value relation.

The lemmas: a probe hit is `mp`'s entry (`memoRG_hit`), a miss is its absence (`memoRG_miss`),
`put` after a probe is `insert` (`memoRV_set`; a `put` that grows the table moves the live slots into
a fresh region of twice the size and keeps the map, `memoRV_grow`), `clear` is `∅`
(`memoRG_clear`), other writers leave it alone (`memoRG_frame`), and all-zero memory is the empty
map (`memoRG_zero`). An instance supplies the codec and its one law `ek_dk`; nothing else.
-/

open ConRon.Arena


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
    · simp only [hd, h0, hm, ↓reduceIte, and_self]
      refine fun _ => ⟨hn, fun _ => ?_, fun h => by simp at h⟩
      simp only [List.tail_cons, List.headD_cons]
      simp only [ne_eq, Decidable.not_not] at h0
      exact ⟨h0, hm.1, hm.2, d.toNat, hrun⟩
    · simp only [hd, h0, hm, ↓reduceIte]
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
  · simp only [mbG, hh 0 (by decide), hh 1 (by decide), he]
  · simp only [nG, hh 0 (by decide), hh 2 (by decide), hl, he]

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
  have hd : ¬ rdW (m.arr64 S.arr) 0 = epG S m := fun h => by
    rw [h] at h0; omega
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
/-! ## The growth keeps the map -/

/-- The four words of slot `j` after the four writes of slot `s`. -/
theorem mput4_reads (S : MemoSch) (m : Mem) (s e x y w : Word) (hs : s.toNat < slotsG S m)
    (j : Word) (hj : j.toNat < slotsG S m) :
    mstG S (mput4 S m s e x y w) j = (if j = s then e else mstG S m j) ∧
    mk1G S (mput4 S m s e x y w) j = (if j = s then x else mk1G S m j) ∧
    mk2G S (mput4 S m s e x y w) j = (if j = s then y else mk2G S m j) ∧
    mvG S (mput4 S m s e x y w) j = (if j = s then w else mvG S m j) := by
  unfold mput4
  have h1 := slot_set0 S m s e hs j hj
  have hs1 : s.toNat < slotsG S (m.set64 S.arr (s * 4) e) := by rw [slotsG_set64]; exact hs
  have hj1 : j.toNat < slotsG S (m.set64 S.arr (s * 4) e) := by rw [slotsG_set64]; exact hj
  have h2 := slot_set S _ s 1 x hs1 (by decide) j hj1
  have hs2 : s.toNat < slotsG S ((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) x) := by
    rw [slotsG_set64]; exact hs1
  have hj2 : j.toNat < slotsG S ((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) x) := by
    rw [slotsG_set64]; exact hj1
  have h3 := slot_set S _ s 2 y hs2 (by decide) j hj2
  have hs3 : s.toNat < slotsG S (((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) x).set64 S.arr
      (s * 4 + 2) y) := by simp only [slotsG_set64]; exact hs
  have hj3 : j.toNat < slotsG S (((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) x).set64 S.arr
      (s * 4 + 2) y) := by simp only [slotsG_set64]; exact hj
  have h4 := slot_set S _ s 3 w hs3 (by decide) j hj3
  rw [h4.1, h4.2.1, h4.2.2.1, h4.2.2.2, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, h2.1, h2.2.1, h2.2.2.1,
    h2.2.2.2, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  by_cases h : j = s
  · subst h; simp
  · have h' : ¬ s = j := fun e => h e.symm
    simp [h, h']

/-- Slot `j ≥ 1` after a write to a header word `g < 4` (slot `0`). -/
theorem hdr_slot (S : MemoSch) (m : Mem) (g v : Word) (hg : g.toNat < 4) (j : Word)
    (hj : j.toNat < slotsG S m) (hj1 : 1 ≤ j.toNat) :
    mstG S (m.set64 S.arr g v) j = mstG S m j ∧ mk1G S (m.set64 S.arr g v) j = mk1G S m j ∧
    mk2G S (m.set64 S.arr g v) j = mk2G S m j ∧ mvG S (m.set64 S.arr g v) j = mvG S m j := by
  have h := slot_set S m 0 g v (by simp; omega) hg j hj
  rw [show (0 : Word) * 4 + g = g by simp] at h
  have : ¬ (0 : Word) = j := fun e => by subst e; simp at hj1
  simpa [this] using h

/-- The rehash's slots of the old region so far: valid keys of live non-tombstone slots below
`i`. -/
def RPres {κ : Type} (S : MemoSch) (K : MemoKey κ) (m₀ : Mem) (e b i : Word) (z : κ) : Prop :=
  ∃ j : Word, b.toNat ≤ j.toNat ∧ j.toNat < i.toNat ∧ mstG S m₀ j = e ∧ mk1G S m₀ j ≠ TOMB ∧
    K.dk (mk1G S m₀ j) (mk2G S m₀ j) = z

open Classical in
/-- The map the new region represents after moving the old slots below `i`. -/
noncomputable def rfun {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (m₀ : Mem)
    (mp : Std.HashMap κ ν) (e b i : Word) : κ → Option ν :=
  fun z => if RPres S K m₀ e b i z then mp[z]? else none

/-- The rehash's invariant at old slot `i`, memory `m`: only the new region changed, no stamp
above the live one, and the new region represents `rfun … i`. -/
def RInv {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
    (VR : Mem → Word → ν → Prop) (m₀ : Mem) (mp : Std.HashMap κ ν) (e b nb nn i : Word)
    (m : Mem) : Prop :=
  MemFrame [S.arr] [] m₀ m ∧
  (∀ j : Word, j.toNat < slotsG S m₀ → (j.toNat < nb.toNat ∨ nb.toNat + nn.toNat ≤ j.toNat) →
    mstG S m j = mstG S m₀ j ∧ mk1G S m j = mk1G S m₀ j ∧ mk2G S m j = mk2G S m₀ j ∧
    mvG S m j = mvG S m₀ j) ∧
  (∀ j : Word, j.toNat < slotsG S m₀ → (mstG S m j).toNat ≤ e.toNat) ∧
  MemoAt S K VR e nb nn m (rfun S K m₀ mp e b i)

theorem slotsG_frame (S : MemoSch) {A : List ArrId} {C : List Word} {m m' : Mem}
    (h : MemFrame A C m m') : slotsG S m' = slotsG S m := by
  simp only [slotsG, len64_eq, h.2.2.1]

section grow
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
variable (S : MemoSch) (hS : S.WF) (K : MemoKey κ) (VR : Mem → Word → ν → Prop)

include hS in
omit [LawfulHashable κ] in
theorem mrehash_inv (hVS : VStable S VR) (m₀ : Mem) (mp : Std.HashMap κ ν)
    (hR : MemoRV S K VR m₀ mp) (hn0 : 0 < nG S m₀) (nb nn : Word)
    (hnb : nb.toNat = (mbG S m₀).toNat + (nG S m₀).toNat) (hnn : nn.toNat = 2 * (nG S m₀).toNat)
    (hfit : nb.toNat + nn.toNat ≤ slotsG S m₀) :
    ∀ (k : Nat) (i c : Word) (m m' : Mem) (c' : Word), nb.toNat - i.toNat = k →
      (mbG S m₀).toNat ≤ i.toNat → i.toNat ≤ nb.toNat →
      RInv S K VR m₀ mp (epG S m₀) (mbG S m₀) nb nn i m →
      mrehashG S (epG S m₀) nb nn i c m = some (m', c') →
      RInv S K VR m₀ mp (epG S m₀) (mbG S m₀) nb nn nb m' := by
  obtain ⟨hctl, hep, hreg, hA⟩ := hR
  obtain ⟨hb1, hbn⟩ := hreg.bound hn0
  have hnn0 : 0 < nn := UInt64.lt_iff_toNat_lt.mpr (by simp; have : 0 < (nG S m₀).toNat := hn0; omega)
  have hnbov : nb.toNat + nn.toNat < 2 ^ 64 := by have := slotsG_lt S m₀; omega
  intro k
  induction k with
  | zero =>
    intro i c m m' c' hk hbi hin hI h
    rw [mrehashG] at h
    have hi : ¬ i < nb := fun h' => by have : i.toNat < nb.toNat := h'; omega
    simp only [hi, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    have : i = nb := UInt64.toNat_inj.mp (by omega)
    subst this; rw [← h.1]; exact hI
  | succ k ih =>
    intro i c m m' c' hk hbi hin hI h
    have hi' : i.toNat < nb.toNat := by omega
    have hi : i < nb := UInt64.lt_iff_toNat_lt.mpr hi'
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := nb.toNat_lt; omega
    obtain ⟨hIf, hIo, hIs, hIA⟩ := hI
    have hisl : i.toNat < slotsG S m₀ := by omega
    obtain ⟨o1, o2, o3, o4⟩ := hIo i hisl (.inl hi')
    have hreg_i : InReg (mbG S m₀) (nG S m₀) i := ⟨hbi, by omega⟩
    rw [mrehashG] at h
    simp only [hi, ↓reduceIte] at h
    have hV₀ : ∀ w v, VR m₀ w v → VR m w v :=
      hVS m₀ m (hIf.mono (by simp) (by simp))
    split at h
    · rename_i hlv
      change mstG S m i = epG S m₀ ∧ mk1G S m i ≠ TOMB at hlv
      rw [o1, o2] at hlv
      obtain ⟨hk, v, hv, hvr⟩ := hA.1 i hreg_i hlv.1 hlv.2
      split at h
      · rename_i hsl
        change mslotG (m.arr64 S.arr) (mk1G S m i) (mk2G S m i) (epG S m₀) nb nn ≠ [] ∧
          (mslotG (m.arr64 S.arr) (mk1G S m i) (mk2G S m i) (epG S m₀) nb nn).headD 0 = 0 at hsl
        have hok := mslotG_ok S m (epG S m₀) nb nn (mk1G S m i) (mk2G S m i)
        generalize hrs : mslotG (m.arr64 S.arr) (mk1G S m i) (mk2G S m i) (epG S m₀) nb nn = rs
          at hsl hok
        change mrehashG S (epG S m₀) nb nn (i + 1) (c + 1)
          (mput4 S m ((mslotG (m.arr64 S.arr) (mk1G S m i) (mk2G S m i) (epG S m₀) nb nn).tail.headD 0)
            (epG S m₀) (mk1G S m i) (mk2G S m i) (mvG S m i)) = some (m', c') at h
        rw [hrs] at h
        obtain ⟨hn', -, hmiss'⟩ := hok hsl.1
        obtain ⟨hsr, -, -⟩ := hmiss' hsl.2
        have hsreg : InReg nb nn (rs.tail.headD 0) := by
          rw [hsr]; exact (runAt_reg nb nn _ _ _ hnn0 hnbov).1
        have hsm : slotsG S m = slotsG S m₀ := slotsG_frame S hIf
        have hss : (rs.tail.headD 0).toNat < slotsG S m := by rw [hsm]; have := hsreg.2; omega
        have rd := fun j (hj : j.toNat < slotsG S m) =>
          mput4_reads S m (rs.tail.headD 0) (epG S m₀) (mk1G S m i) (mk2G S m i) (mvG S m i) hss j hj
        have hf4 : MemFrame [S.arr] [] m (mput4 S m (rs.tail.headD 0) (epG S m₀) (mk1G S m i)
            (mk2G S m i) (mvG S m i)) := by
          have fa := fun (m : Mem) k v => MemFrame.set64 m S.arr hS.arr_ctl k v
          unfold mput4
          exact ((fa _ _ _).trans (fa _ _ _)).trans (fa _ _ _) |>.trans (fa _ _ _)
        have hV₁ : ∀ w v, VR m w v → VR (mput4 S m (rs.tail.headD 0) (epG S m₀) (mk1G S m i)
            (mk2G S m i) (mvG S m i)) w v := hVS _ _ (hf4.mono (by simp) (by simp))
        have hsl' : ∀ j, InReg nb nn j → j.toNat < slotsG S m := fun j hj => by
          rw [hsm]; have := hj.2; omega
        have hW := memoAt_write S K VR (epG S m₀) nb nn hnbov m _ _ hIA hV₁ (mk1G S m i)
          (mk2G S m i) (mvG S m i) (by rw [o2, o3]; exact hk) v (by rw [o4]; exact hV₀ _ _ hvr)
          rs hsl.1 hok
          (fun j hj => by rw [(rd j (hsl' j hj)).1]; simp only [hsl.2, and_true])
          (fun j hj => by rw [(rd j (hsl' j hj)).2.1]; simp only [hsl.2, and_true])
          (fun j hj => by rw [(rd j (hsl' j hj)).2.2.1]; simp only [hsl.2, and_true])
          (fun j hj => by rw [(rd j (hsl' j hj)).2.2.2])
        refine ih (i + 1) (c + 1) _ m' c' (by omega) (by omega) (by omega) ⟨hIf.trans hf4,
          fun j hj ho => ?_, fun j hj => ?_, ?_⟩ h
        · have hne : ¬ j = rs.tail.headD 0 := fun e => by
            subst e; have := hsreg.1; have := hsreg.2; omega
          rw [hsm] at rd
          obtain ⟨r1, r2, r3, r4⟩ := rd j hj
          simp only [hne, ↓reduceIte] at r1 r2 r3 r4
          rw [r1, r2, r3, r4]; exact hIo j hj ho
        · rw [hsm] at rd
          rw [(rd j hj).1]
          split
          · exact Nat.le_refl _
          · exact hIs j hj
        · have hfe : (fun z => if (K.dk (mk1G S m i) (mk2G S m i) == z) = true then some v
              else rfun S K m₀ mp (epG S m₀) (mbG S m₀) i z) =
              rfun S K m₀ mp (epG S m₀) (mbG S m₀) (i + 1) := by
            funext z
            simp only [rfun]
            by_cases hz : (K.dk (mk1G S m i) (mk2G S m i) == z) = true
            · have hz' : K.dk (mk1G S m i) (mk2G S m i) = z := beq_iff_eq.mp hz
              have hp : RPres S K m₀ (epG S m₀) (mbG S m₀) (i + 1) z :=
                ⟨i, hbi, by omega, hlv.1, hlv.2, by rw [← o2, ← o3]; exact hz'⟩
              simp only [hz, ↓reduceIte, hp]
              simp only at hv
              rw [← hz', o2, o3]; exact hv.symm
            · simp only [hz, Bool.false_eq_true, ↓reduceIte]
              have : RPres S K m₀ (epG S m₀) (mbG S m₀) (i + 1) z ↔
                  RPres S K m₀ (epG S m₀) (mbG S m₀) i z := by
                constructor
                · rintro ⟨j, h1, h2, h3, h4, h5⟩
                  refine ⟨j, h1, ?_, h3, h4, h5⟩
                  rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ h2) with h2 | h2
                  · exact h2
                  · have : j = i := UInt64.toNat_inj.mp h2
                    subst this; rw [o2, o3] at hz; exact absurd (beq_iff_eq.mpr h5) hz
                · rintro ⟨j, h1, h2, h3, h4, h5⟩; exact ⟨j, h1, by omega, h3, h4, h5⟩
              by_cases hp : RPres S K m₀ (epG S m₀) (mbG S m₀) i z
              · have hp' := this.mpr hp
                simp only [hp, hp', ↓reduceIte]
              · have hp' : ¬ RPres S K m₀ (epG S m₀) (mbG S m₀) (i + 1) z := fun h => hp (this.mp h)
                simp only [hp, hp', ↓reduceIte]
          rw [← hfe]; exact hW
      · simp at h
    · rename_i hlv
      change ¬ (mstG S m i = epG S m₀ ∧ mk1G S m i ≠ TOMB) at hlv
      rw [o1, o2] at hlv
      have hfe : rfun S K m₀ mp (epG S m₀) (mbG S m₀) i = rfun S K m₀ mp (epG S m₀) (mbG S m₀) (i + 1) := by
        funext z
        simp only [rfun]
        have : RPres S K m₀ (epG S m₀) (mbG S m₀) (i + 1) z ↔ RPres S K m₀ (epG S m₀) (mbG S m₀) i z := by
          constructor
          · rintro ⟨j, h1, h2, h3, h4, h5⟩
            refine ⟨j, h1, ?_, h3, h4, h5⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ h2) with h2 | h2
            · exact h2
            · have : j = i := UInt64.toNat_inj.mp h2
              subst this; exact absurd ⟨h3, h4⟩ hlv
          · rintro ⟨j, h1, h2, h3, h4, h5⟩; exact ⟨j, h1, by omega, h3, h4, h5⟩
        by_cases hp : RPres S K m₀ (epG S m₀) (mbG S m₀) i z
        · have hp' := this.mpr hp
          simp only [hp, hp', ↓reduceIte]
        · have hp' : ¬ RPres S K m₀ (epG S m₀) (mbG S m₀) (i + 1) z := fun h => hp (this.mp h)
          simp only [hp, hp', ↓reduceIte]
      refine ih (i + 1) c m m' c' (by omega) (by omega) (by omega) ⟨hIf, hIo, hIs, ?_⟩ h
      rw [← hfe]; exact hIA

omit [LawfulHashable κ] in
include hS in
/-- **The growth keeps the map**: the new region, twice the size, right above the old one, named
by the header, represents the same map. -/
theorem memoRV_grow (hVS : VStable S VR) (m : Mem) (mp : Std.HashMap κ ν)
    (hR : MemoRV S K VR m mp) (m₁ : Mem) (c : Word)
    (h : mgrowAt S (epG S m) (mbG S m) (nG S m) m = some (m₁, c)) :
    MemoRV S K VR m₁ mp ∧ epG S m₁ = epG S m ∧ mbG S m₁ = mbG S m + nG S m ∧
      nG S m₁ = nG S m * 2 ∧ cntG S m₁ = c := by
  have hf₁ := mgrowAt_frame S hS _ _ _ m m₁ c h
  simp only [mgrowAt] at h
  split at h
  · simp at h
  rename_i hn2
  split at h
  · simp at h
  rename_i hlen
  split at h
  · simp at h
  rename_i m' c' hr
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hctl, hep, hreg, hA⟩ := hR
  have hn0 : 0 < nG S m := by
    rcases Nat.eq_zero_or_pos (nG S m).toNat with h0 | h0
    · exact absurd (by rw [UInt64.toNat_inj.mp (by rw [h0]; rfl : (nG S m).toNat = (0 : Word).toNat)]; simp) hn2
    · exact UInt64.lt_iff_toNat_lt.mpr (by simpa using h0)
  obtain ⟨hb1, hbn⟩ := hreg.bound hn0
  have hsl := slotsG_lt S m
  have hnb : (mbG S m + nG S m).toNat = (mbG S m).toNat + (nG S m).toNat := by
    rw [UInt64.toNat_add]; omega
  have hnn : (nG S m * 2).toNat = 2 * (nG S m).toNat := by
    rw [UInt64.toNat_mul]; simp; omega
  have hfit : (mbG S m + nG S m).toNat + (nG S m * 2).toNat ≤ slotsG S m := by
    have hl : (m.len64 S.arr >>> 2).toNat = slotsG S m := by
      simp only [slotsG, UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have : ¬ (m.len64 S.arr >>> 2).toNat < (mbG S m + nG S m + nG S m * 2).toNat :=
      fun h' => hlen (UInt64.lt_iff_toNat_lt.mpr h')
    have e3 : (mbG S m + nG S m + nG S m * 2).toNat =
        (mbG S m + nG S m).toNat + (nG S m * 2).toNat := by
      rw [UInt64.toNat_add (mbG S m + nG S m)]; omega
    omega
  have hbase : RInv S K VR m mp (epG S m) (mbG S m) (mbG S m + nG S m) (nG S m * 2) (mbG S m) m := by
    refine ⟨MemFrame.refl _ _ _, fun j _ _ => ⟨rfl, rfl, rfl, rfl⟩, hreg.2.1, ?_, ?_, ?_⟩
    · intro j hj hl
      exact absurd hl (hreg.2.2.1 j (by have := hj.1; omega) (by have := hj.2; omega))
    · intro j _ hj _ hl
      exact absurd hl (hreg.2.2.1 j (by have := hj.1; omega) (by have := hj.2; omega))
    · intro x v hx
      simp only [rfun] at hx
      split at hx
      · rename_i hp; obtain ⟨j, h1, h2, -⟩ := hp; omega
      · simp at hx
  have hI := mrehash_inv S hS K VR hVS m mp ⟨hctl, hep, hreg, hA⟩ hn0 _ _ hnb hnn hfit _
    (mbG S m) 0 m m' c' rfl (Nat.le_refl _) (by omega) hbase hr
  obtain ⟨hIf, hIo, hIs, hIA⟩ := hI
  -- the map of the new region is `mp`
  have hmp : rfun S K m mp (epG S m) (mbG S m) (mbG S m + nG S m) = fun z => mp[z]? := by
    funext z
    simp only [rfun]
    split
    · rfl
    · rename_i hp
      cases hz : mp[z]? with
      | none => rfl
      | some v =>
        exfalso; apply hp
        obtain ⟨hdz, htz, d, h1, h2, h2', -⟩ := hA.2.2 z v hz
        have hrg := runAt_reg (mbG S m) (nG S m) (K.ek z).1 (K.ek z).2 d hn0 (by omega)
        refine ⟨_, hrg.1.1, by rw [hnb]; exact hrg.1.2, h1, by rw [h2]; exact htz, ?_⟩
        rw [h2, h2', hdz]
  rw [hmp] at hIA
  -- the header writes
  have hac := hS.arr_ctl
  have hm's : slotsG S m' = slotsG S m := slotsG_frame S hIf
  have hz0 : 0 < (m'.arr64 S.arr).size := by
    have : 1 ≤ slotsG S m' := by rw [hm's]; omega
    rw [slotsG_toNat] at this; have := (m'.arr64 S.arr).size.mod_le (2 ^ 64); omega
  have hz2 : 2 < (m'.arr64 S.arr).size := by
    have : 1 ≤ slotsG S m' := by rw [hm's]; omega
    rw [slotsG_toNat] at this; have := (m'.arr64 S.arr).size.mod_le (2 ^ 64); omega
  have hctl' : S.cs.toNat + 2 ≤ (m'.arr64 CTL).size := by rw [hIf.2.2.1]; exact hctl
  have hcs1 : (S.cs + 1).toNat < (m'.arr64 CTL).size := by
    have := hS.cs; rw [UInt64.toNat_add]; simp; omega
  have hcs : S.cs ≠ S.cs + 1 := by intro h; have := hS.cs; grind
  generalize hM : (((m'.set64 S.arr 0 (epG S m)).set64 S.arr 1 (mbG S m + nG S m)).set64 S.arr 2
    (nG S m * 2)).set64 CTL (S.cs + 1) c' = m₁ at hf₁ ⊢
  have harr : m₁.arr64 S.arr = (((m'.set64 S.arr 0 (epG S m)).set64 S.arr 1 (mbG S m + nG S m)).set64
      S.arr 2 (nG S m * 2)).arr64 S.arr := by rw [← hM, Mem.arr64_set64_ne _ _ _ _ _ hac]
  have hh : ∀ f : Word, rdW (m₁.arr64 S.arr) f =
      if f = 2 then nG S m * 2 else if f = 1 then mbG S m + nG S m else if f = 0 then epG S m
      else rdW (m'.arr64 S.arr) f := by
    intro f
    rw [harr]
    simp only [rdW_set64, size_set64, true_and]
    by_cases f2 : f = 2
    · subst f2; simp [hz2]
    by_cases f1 : f = 1
    · subst f1; simp [show 1 < (m'.arr64 S.arr).size by omega]
    by_cases f0 : f = 0
    · subst f0; simp [hz0]
    simp [Ne.symm f2, Ne.symm f1, Ne.symm f0, f2, f1, f0]
  have hep₁ : epG S m₁ = epG S m := by
    simp only [epG]; rw [← hM, rdW_set64]; simp only [Ne.symm hcs, false_and, and_false, ↓reduceIte]
    simp only [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hac)]
    rw [hIf.2.1 S.cs (by simp)]
  have hd₁ : rdW (m₁.arr64 S.arr) 0 = epG S m₁ := by simp only [hep₁, hh]; simp
  have hb₁ : mbG S m₁ = mbG S m + nG S m := by simp only [mbG, hd₁, ↓reduceIte, hh]; simp
  have hn₁ : nG S m₁ = nG S m * 2 := by simp only [nG, hd₁, ↓reduceIte, hh]
  have hs₁ : slotsG S m₁ = slotsG S m := by
    rw [← hm's, ← hM]; simp only [slotsG_set64]
  have hc₁ : cntG S m₁ = c' := by
    simp only [cntG]; rw [← hM, rdW_set64]
    simp only [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hac)]; simp
    intro h; have := hS.cs; omega
  -- slots `j ≥ 1` of `m₁` are those of `m'`
  have hsj : ∀ j : Word, j.toNat < slotsG S m → 1 ≤ j.toNat →
      mstG S m₁ j = mstG S m' j ∧ mk1G S m₁ j = mk1G S m' j ∧ mk2G S m₁ j = mk2G S m' j ∧
      mvG S m₁ j = mvG S m' j := by
    intro j hj hj1
    have hjs : j.toNat < slotsG S m' := by rw [hm's]; exact hj
    have a1 := hdr_slot S m' 0 (epG S m) (by decide) j hjs hj1
    have a2 := hdr_slot S (m'.set64 S.arr 0 (epG S m)) 1 (mbG S m + nG S m) (by decide) j
      (by rw [slotsG_set64]; exact hjs) hj1
    have a3 := hdr_slot S ((m'.set64 S.arr 0 (epG S m)).set64 S.arr 1 (mbG S m + nG S m)) 2
      (nG S m * 2) (by decide) j (by simp only [slotsG_set64]; exact hjs) hj1
    have a4 := slot_other S (((m'.set64 S.arr 0 (epG S m)).set64 S.arr 1 (mbG S m + nG S m)).set64
      S.arr 2 (nG S m * 2)) CTL (Ne.symm hac) (S.cs + 1) c' j
    rw [hM] at a4
    rw [a4.1, a4.2.1, a4.2.2.1, a4.2.2.2, a3.1, a3.2.1, a3.2.2.1, a3.2.2.2, a2.1, a2.2.1, a2.2.2.1,
      a2.2.2.2, a1.1, a1.2.1, a1.2.2.1, a1.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hf' : MemFrame [S.arr] [S.cs + 1] m' m₁ := by
    rw [← hM]
    have fa : ∀ (m : Mem) k v, MemFrame [S.arr] [S.cs + 1] m (m.set64 S.arr k v) :=
      fun m k v => (MemFrame.set64 m S.arr hac k v).mono (by simp) (by simp)
    exact (((fa _ _ _).trans (fa _ _ _)).trans (fa _ _ _)).trans
      ((MemFrame.setCtl _ (S.cs + 1) c').mono (by simp) (by simp))
  have hV' : ∀ w v, VR m' w v → VR m₁ w v := hVS m' m₁ (hf'.mono (by simp) (by simp))
  refine ⟨⟨by rw [hf₁.2.2.1]; exact hctl, by rw [hep₁]; exact hep, ⟨?_, ?_, ?_, ?_⟩, ?_⟩,
    hep₁, hb₁, hn₁, hc₁⟩
  · right; rw [hb₁, hn₁, hs₁, hnb, hnn]; rw [hnb, hnn] at hfit; omega
  · intro j hj
    rw [hs₁] at hj
    rw [hep₁]
    rcases Nat.eq_zero_or_pos j.toNat with h0 | h0
    · have : j = 0 := UInt64.toNat_inj.mp (by simp [h0])
      subst this; simp only [mstG, UInt64.zero_mul, hh]; simp
    · rw [(hsj j hj h0).1]; exact hIs j hj
  · intro j hj1 hj2
    rw [hb₁, hn₁, hnb, hnn] at hj1
    rw [hs₁] at hj2
    rw [(hsj j hj2 (by omega)).1, (hIo j hj2 (.inr (by rw [hnb, hnn]; omega))).1, hep₁]
    exact hreg.2.2.1 j (by omega) hj2
  · rw [hh]; simp [hep₁]
  · rw [hep₁, hb₁, hn₁]
    have := UInt64.lt_iff_toNat_lt.mp hn0
    exact memoAt_congr S K VR _ _ _ (UInt64.lt_iff_toNat_lt.mpr (by rw [hnn]; simp at this ⊢; omega))
      (by rw [hnb, hnn]; omega) m' m₁ _ hIA hV' (fun j hj =>
        hsj j (by have := hj.2; omega) (by have := hj.1; omega))

include hS in
/-- **`find; put` is `insert`**, of a value the written word denotes. -/
theorem memoRV_set (hVS : VStable S VR) (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp)
    (k1 k2 w : Word) (hk : K.ok k1 k2) (x : ν) (hx : VR m w x) (m' : Mem)
    (h : msetG S m k1 k2 w = some m') :
    MemoRV S K VR m' (mp.insert (K.dk k1 k2) x) := by
  simp only [msetG] at h
  split at h
  · simp at h
  rename_i hne
  simp only [mputG] at h
  split at h
  · split at h
    · simp at h
    rename_i m₁ c hg
    split at h
    · rename_i hsl
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hR₁, he, hb, hn, hc⟩ := memoRV_grow S hS K VR hVS m mp hR m₁ c hg
      have hf := mgrowAt_frame S hS _ _ _ m m₁ c hg
      have hx₁ : VR m₁ w x := hVS m m₁ (hf.mono (by simp) (by simp)) w x hx
      have hfind : mfindG S m₁ k1 k2 =
          mslotG (m₁.arr64 S.arr) k1 k2 (epG S m) (mbG S m + nG S m) (nG S m * 2) := by
        simp only [mfindG, mslotG, he, hb, hn]
      have := memoRV_putNG S hS K VR hVS m₁ mp hR₁ k1 k2 w hk x hx₁ (by rw [hfind]; exact hsl.1)
      rw [hfind, hsl.2] at this
      simpa only [mputMem, he, hc] using this
    · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact memoRV_putNG S hS K VR hVS m mp hR k1 k2 w hk x hx hne

include hS in
omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **`clear` is `∅`.** -/
theorem memoRV_clear (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp)
    (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) : MemoRV S K VR (mclearG S m) ∅ := by
  obtain ⟨hctl, hep, hreg, -⟩ := hR
  have hf := mclearG_frame S m
  have hsz := hf.2.2.1
  have hb : (mclearG S m).arr64 S.arr = m.arr64 S.arr := hf.1 S.arr (by simp) hS.arr_ctl
  have hsl : slotsG S (mclearG S m) = slotsG S m := slotsG_frame S hf
  have hs : ∀ j, mstG S (mclearG S m) j = mstG S m j := fun j => by simp only [mstG, hb]
  have hcs : S.cs + 1 ≠ S.cs := by
    intro h; have := hS.cs; grind
  have he : epG S (mclearG S m) = epG S m + 1 := by
    simp only [epG, mclearG, rdW_set64, size_set64, hcs]; grind
  have he1 : (epG S m + 1).toNat = (epG S m).toNat + 1 := by
    simp only [epG] at *; rw [UInt64.toNat_add]; grind
  apply memoRV_fresh S K VR _ (by rw [hsz]; exact hctl)
  · rw [he]; simp only [epG] at *; grind
  · rw [hb, he, he1]; have := hreg.2.2.2; omega
  · intro j hj; rw [hsl] at hj; rw [hs, he, he1]; have := hreg.2.1 j hj; omega

include hS in
omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **The memo relation survives a writer of other arrays and of `CTL` words other than the
stamp**, when the values' denotations do (a heap that only grows, say). -/
theorem memoRV_frame (A : List ArrId) (C : List Word) (hA : S.arr ∉ A) (hC : S.cs ∉ C)
    (m m' : Mem) (hf : MemFrame A C m m') (hV : ∀ w v, VR m w v → VR m' w v)
    (mp : Std.HashMap κ ν) (hR : MemoRV S K VR m mp) : MemoRV S K VR m' mp := by
  have hb : m'.arr64 S.arr = m.arr64 S.arr := hf.1 S.arr hA hS.arr_ctl
  obtain ⟨g1, g2, g3, g4, -⟩ := reg_congr S m m' (fun f _ => by rw [hb]) (hf.2.1 S.cs hC)
    (by rw [hb])
  have hs : ∀ j, mstG S m' j = mstG S m j := fun j => by simp only [mstG, hb]
  have hk : ∀ j, mk1G S m' j = mk1G S m j := fun j => by simp only [mk1G, hb]
  have hk' : ∀ j, mk2G S m' j = mk2G S m j := fun j => by simp only [mk2G, hb]
  have hv : ∀ j, mvG S m' j = mvG S m j := fun j => by simp only [mvG, hb]
  obtain ⟨hctl, hep, ⟨r1, r2, r3, r4⟩, hlive, huniq, hrun⟩ := hR
  refine ⟨by rw [hf.2.2.1]; exact hctl, by rw [g1]; exact hep,
    ⟨by rw [g2, g3, g4]; exact r1, fun j hj => by rw [hs, g1]; exact r2 j (g4 ▸ hj),
      fun j h1 h2 => by rw [hs, g1]; exact r3 j (by rw [← g2, ← g3]; exact h1) (g4 ▸ h2),
      by rw [hb, g1]; exact r4⟩, ?_, ?_, ?_⟩
  · intro j hj hl ht; rw [g2, g3] at hj; rw [hs, g1] at hl; rw [hk] at ht; rw [hk, hk', hv]
    obtain ⟨h1, u, h2, h3⟩ := hlive j hj hl ht
    exact ⟨h1, u, h2, hV _ _ h3⟩
  · intro j j' hj hj' hl hl' ht hkk hkk'; rw [g2, g3] at hj hj'; rw [hs, g1] at hl hl'
    rw [hk] at ht; rw [hk, hk] at hkk; rw [hk', hk'] at hkk'
    exact huniq j j' hj hj' hl hl' ht hkk hkk'
  · intro x v hx
    obtain ⟨hdx, htx, d, h1, h2, h2', h3⟩ := hrun x v hx
    refine ⟨hdx, htx, d, ?_, ?_, ?_, fun e he => ?_⟩
    · rw [g2, g3, hs, g1]; exact h1
    · rw [g2, g3, hk]; exact h2
    · rw [g2, g3, hk']; exact h2'
    · rw [g2, g3, hs, g1]; exact h3 e he

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- **All-zero memory is the empty map.** -/
theorem memoRV_zero (m : Mem) (hz : ∀ b x, rdW (m.arr64 b) x = 0)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) : MemoRV S K VR m ∅ := by
  have he : epG S m = 1 := by simp [epG, hz]
  apply memoRV_fresh S K VR m hctl (by rw [he]; decide)
  · rw [he, hz]; decide
  · intro j _; rw [he]; simp [mstG, hz]

/-! ### Erase -/

/-! ### The word-valued memos (`MemoRG`) -/

variable (dv : Word → ν)

theorem vstable_eq : VStable S (fun (_ : Mem) w (v : ν) => v = dv w) := fun _ _ _ _ _ h => h

include hS in
theorem memoRG_set (m : Mem) (mp : Std.HashMap κ ν) (hR : MemoRG S K dv m mp) (k1 k2 v : Word)
    (hk : K.ok k1 k2) (m' : Mem) (h : msetG S m k1 k2 v = some m') :
    MemoRG S K dv m' (mp.insert (K.dk k1 k2) (dv v)) :=
  memoRV_set S hS K _ (vstable_eq S dv) m mp hR k1 k2 v hk _ rfl m' h

include hS in
omit [LawfulBEq κ] [LawfulHashable κ] in
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

end grow

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
