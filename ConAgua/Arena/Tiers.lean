module

import ConAgua.Arena.DerRel
public import ConAgua.Arena.Keeps
public import ConAgua.Arena.EnvRec
public import ConRon.Arena.CheckDecl
public import ConAgua.Arena.MemoBank
public import ConAgua.Arena.CoreCaches
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Arena.DerRelBase

@[expose] public section

/-!
# The relation by tier, over projections of the state

Lane `scale` found that one flat bundle over `AState` costs more per writer the more fields it
has (faster than linearly), and that a group stated over `AState` gets no twin-side frame by
unfolding. So the relation is a few groups, each over the **projection** of the state it reads,
each owning a disjoint range of arrays and `CTL` words, each with **one** group frame lemma:

| group | over | arrays | `CTL` words | status |
|---|---|---|---|---|
| `ArenaR` (store tier, `ArenaRel.lean`) | `a.store` (19 tables, pool) | `storeArrs` ⊆ 0‥40 | `storeCtl` ⊆ 0‥41 | done |
| `MemosR` (walk memos, nested in `ArenaR`) | `a.memos` | 24, 41, 47, 48; 49‥55 reserved | 24, 25, 42‥47; 48‥61 reserved | 4 of 10 memos |
| `DerR` (derived columns, `DerRel.lean`) | `a.store` | 42‥46 | – | 5 compound tables |
| `StateDR` (front, `Front/StateDR.lean`) | the parse state | 64‥66; 67‥95 reserved | 64‥95 reserved | lane `front2` |
| `CoreR` | `a.caches` | 96‥106; 107‥127 reserved | 96‥113, 116‥119; others reserved | 11 of 14 tables, both mode-memo sets (lane `whnf`) |
| `PinsR` | `a.pins` | 128 (`PINS`) | – | filled (lane `pinsenv`) |
| `EnvR` | a view `vis` of `fe : IFEnv` (an argument) | 129‥136, 140‥143, tier 1 of 129‥131 | 128 (129: the record top), 133 | filled (lane `pinsenv`; tables: lane `consync`) |
| `PendR` (`Checker.lean`) | `pend` (an argument) | 137 | 130 | lane `pinsenv` |
| argument relations (`PMemo`, `pend`, saved `ModeMemos`, walk-local memos) | arguments | 144‥191 | 136‥191 | not yet |

`ArenaD = ArenaR ∧ DerR` stays the walks' tier. `CheckR` is the whole relation. A walk changes
only arrays below 64 (`WriteSets.lean`) and only `store`/`memos` (`Keeps cp`, `Keeps.lean`), so
`CheckR.of_walk` carries the upper tiers across it with no lemma about the walk.
-/

namespace L.Arena

open ConRon.Arena

/-- The arrays of a range, `lo ≤ b < hi` (both tiers), apart from a writer. -/
def AvoidA (lo hi : Nat) (A : List TieredArray) : Prop := ∀ b ∈ A, b.arr < lo ∨ hi ≤ b.arr
def AvoidC (lo hi : Nat) (C : List Word) : Prop := ∀ x ∈ C, x.toNat < lo ∨ hi ≤ x.toNat

instance (lo hi : Nat) (A : List TieredArray) : Decidable (AvoidA lo hi A) := by unfold AvoidA; infer_instance

/-- A writer of arrays and words below `k` avoids every range starting at `k` or above. -/
theorem AvoidA.of_lt {k lo hi : Nat} {A : List TieredArray} (hA : ∀ b ∈ A, b.arr < k) (hk : k ≤ lo) :
    AvoidA lo hi A := fun b hb => .inl (Nat.lt_of_lt_of_le (hA b hb) hk)
theorem AvoidC.of_lt {k lo hi : Nat} {C : List Word} (hC : ∀ x ∈ C, x.toNat < k) (hk : k ≤ lo) :
    AvoidC lo hi C := fun x hx => .inl (Nat.lt_of_lt_of_le (hC x hx) hk)
/-- A writer of the store tier (arrays below `64`, both tiers) avoids every range from `64` on. -/
theorem AvoidA.of_low {lo hi : Nat} {A : List TieredArray} (hA : ∀ b ∈ A, InStoreTier b)
    (hlo : 64 ≤ lo) : AvoidA lo hi A := fun b hb =>
  .inl (Nat.lt_of_lt_of_le (hA b hb) hlo)

/-! ## The per-declaration caches: arrays 96‥127, `CTL` 96‥127

Eleven of con-ron's fourteen `Caches` tables are memos in L (`CoreCaches.lean`: arrays 96‥106,
stamps and counts `CTL` 96‥113 and 116‥119). The six **mode memos** hold both of the twin's sets
(the plain tower's six fields, the eager tower's `eagerMemos`), told apart by the eager bit `eb`
in the key's second word (`MemoBank.lean`'s `genKey`): L keeps one map `M` per table over
`(key, eb)`. At eager bit `eb` the twin's six fields are bank `eb`; outside the eager tower
(`eb = 0`) `eagerMemos` is bank `1`, inside it (`eb = 1`) `eagerMemos` is empty (`enterEager` moved
it into the fields) and the plain set is the eager slot's local, bank `0`, which an eager run
keeps (`KeptAll`, `WhnfBase.lean`). The three constant caches and the two level-verdict caches
are plain memos. `readLC`, `readNC`, `readLsC` have no L table (L makes no readbacks; see
`CoreCaches.lean`). -/

/-- The key of a one-handle mode memo: the handle and its generation. -/
def eKeyG : MemoKey (EIdx × Word) := genKey bmKey (fun _ _ h => by rw [h.2]; decide)

/-- Two handle words, one per key word (both below `2^32`). -/
def pairKey {k₁ k₂ : IdxKind} : MemoKey (Idx k₁ × Idx k₂) where
  dk k1 k2 := (decI k1, decI k2)
  ek x := (x.1.word.toUInt64, x.2.word.toUInt64)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2.toNat < 2 ^ 32
  ek_dk k1 k2 h := by
    simp only [Prod.mk.injEq]
    exact ⟨(word_decI _ k1 h.1).mpr rfl, (word_decI _ k2 h.2).mpr rfl⟩
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- `defeqC`'s key: the ordered pair and the generation. -/
def dKeyG : MemoKey ((EIdx × EIdx) × Word) := genKey pairKey (fun _ _ h => h.2)

/-- `ruleRhsC`'s key: the recursor in the first word, the constructor and the levels packed in
the second (`ctor ∣ us << 32`). -/
def rrKey : MemoKey (NIdx × NIdx × LsIdx) where
  dk k1 k2 := (decI k1, decI (k2 &&& 0xFFFFFFFF), decI (k2 >>> 32))
  ek x := (x.1.word.toUInt64, x.2.1.word.toUInt64 ||| (x.2.2.word.toUInt64 <<< 32))
  ok k1 _ := k1.toNat < 2 ^ 32
  ek_dk k1 k2 h := by
    have h1 : (k2 &&& 0xFFFFFFFF).toNat < 2 ^ 32 := by
      rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have h2 : (k2 >>> 32).toNat < 2 ^ 32 := by
      have := k2.toNat_lt
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
    simp only [Prod.mk.injEq, (word_decI _ k1 h).mpr rfl, (word_decI _ _ h1).mpr rfl,
      (word_decI _ _ h2).mpr rfl, true_and]
    exact lo_hi k2
  ok_tomb k1 k2 h e := by subst e; exact absurd h (by decide)

/-- A handle-valued memo's value relation: the word is a handle word (below `2^32`, so the L
code may compute with it) and denotes the entry. Independent of the memory. -/
def VH (_ : Mem) (w : Word) (v : EIdx) : Prop := v = decE w ∧ w.toNat < 2 ^ 32

/-- A `defeqC` value word: the verdict. -/
def decB (w : Word) : Bool := w != 0

/-- A `Bool`-valued memo's value relation. -/
def VB (_ : Mem) (w : Word) (v : Bool) : Prop := v = decB w

/-- The six mode memos' maps over `(key, generation)`. -/
structure ModeMaps where
  wc : Std.HashMap (EIdx × Word) EIdx
  wk : Std.HashMap (EIdx × Word) EIdx
  wh : Std.HashMap (EIdx × Word) EIdx
  inf : Std.HashMap (EIdx × Word) EIdx
  io : Std.HashMap (EIdx × Word) EIdx
  de : Std.HashMap ((EIdx × EIdx) × Word) Bool

/-- The maps with nothing in them. -/
def ModeMaps.empty : ModeMaps := ⟨∅, ∅, ∅, ∅, ∅, ∅⟩

/-- **One mode memo** at eager bit `eb`: its map `M` over `(key, eager bit)` is in memory, the
twin's field `t` is bank `eb`, and its stored eager table `te` is bank `1` outside the eager
tower and empty inside it. -/
structure ModeR {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey (κ × Word))
    (VR : Mem → Word → ν → Prop) (m : Mem) (M : Std.HashMap (κ × Word) ν) (eb : Word)
    (t te : Std.HashMap κ ν) : Prop where
  memo : MemoRV S K VR m M
  cur : Bank M eb t
  stored : eb = 0 → Bank M 1 te
  empty : eb ≠ 0 → te = ∅

/-- A value relation that does not read the memory. -/
def VConst {ν : Type} (VR : Mem → Word → ν → Prop) : Prop := ∀ m m' w v, VR m w v → VR m' w v

theorem vh_const : VConst VH := fun _ _ _ _ h => h
theorem vb_const : VConst VB := fun _ _ _ _ h => h

theorem ModeR.frame {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {VR : Mem → Word → ν → Prop} {m m' : Mem} {M : Std.HashMap (κ × Word) ν} {eb : Word}
    {t te : Std.HashMap κ ν} {A : List TieredArray} {C : List Word} (hS : S.WF) (hV : VConst VR)
    (hA : (S.arr : TieredArray) ∉ A) (hC : S.cs ∉ C) (hf : MemFrame A C m m') (h : ModeR S K VR m M eb t te) :
    ModeR S K VR m' M eb t te :=
  ⟨memoRV_frame S hS K VR A C hA hC m m' hf (hV m m') M h.memo, h.cur, h.stored, h.empty⟩

/-- **The core tier at explicit maps and eager bit.** -/
structure CoreRM (m : Mem) (c : Caches) (M : ModeMaps) (eb : Word) : Prop where
  wc : ModeR wcSch eKeyG VH m M.wc eb c.whnfCoreC c.eagerMemos.whnfCoreC
  wk : ModeR wkSch eKeyG VH m M.wk eb c.whnfCoreCheapC c.eagerMemos.whnfCoreCheapC
  wh : ModeR whSch eKeyG VH m M.wh eb c.whnfC c.eagerMemos.whnfC
  inf : ModeR inSch eKeyG VH m M.inf eb c.inferC c.eagerMemos.inferC
  io : ModeR ioSch eKeyG VH m M.io eb c.inferIOC c.eagerMemos.inferIOC
  de : ModeR deSch dKeyG VB m M.de eb c.defeqC c.eagerMemos.defeqC
  eb1 : eb ≤ 1
  ct : MemoRV ctSch pairKey VH m c.constTyC
  cv : MemoRV cvSch pairKey VH m c.constValC
  rr : MemoRV rrSch rrKey VH m c.ruleRhsC
  lq : MemoRG lqSch pairKey decB m c.lvlEqC
  lsq : MemoRG lsqSch pairKey decB m c.lvlsEqC

/-- **The core tier** (tier D: `flushCaches` per declaration), over `a.caches`, outside the eager
tower. -/
def CoreR (m : Mem) (c : Caches) : Prop := ∃ M, CoreRM m c M 0

theorem coreSch_wf (a : ArrId) (c : Word) (h1 : a ≠ CTL) (h2 : c.toNat + 2 < 2 ^ 32) :
    MemoSch.WF ⟨a, c⟩ := ⟨h1, h2⟩

theorem CoreRM.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {c : Caches} {M : ModeMaps}
    {eb : Word} (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m')
    (h : CoreRM m c M eb) : CoreRM m' c M eb := by
  have nA : ∀ b : ArrId, 96 ≤ b → b < 128 → (b : TieredArray) ∉ A := fun b h1 h2 hb => by
    have := hA _ hb; simp only [ArrId] at *; omega
  have nC : ∀ x : Word, 96 ≤ x.toNat → x.toNat < 128 → x ∉ C := fun x h1 h2 hx => by
    have := hC x hx; omega
  have wf := coreSch_wf
  exact ⟨h.wc.frame (wf _ _ (by decide) (by decide)) vh_const (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.wk.frame (wf _ _ (by decide) (by decide)) vh_const (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.wh.frame (wf _ _ (by decide) (by decide)) vh_const (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.inf.frame (wf _ _ (by decide) (by decide)) vh_const (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.io.frame (wf _ _ (by decide) (by decide)) vh_const (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.de.frame (wf _ _ (by decide) (by decide)) vb_const (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.eb1,
    memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf (vh_const m m') _ h.ct,
    memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf (vh_const m m') _ h.cv,
    memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf (vh_const m m') _ h.rr,
    memoRG_frame _ (wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.lq,
    memoRG_frame _ (wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.lsq⟩

theorem CoreR.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {c : Caches}
    (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m') (h : CoreR m c) :
    CoreR m' c := by
  obtain ⟨M, h⟩ := h
  exact ⟨M, h.frame hA hC hf⟩

/-! ### `flush_caches()` is `Caches.empty` -/

/-- A run of memo clears, in order. -/
def clearsL : List MemoSch → Mem → Mem
  | [], m => m
  | S :: l, m => clearsL l (mclearG S m)

/-- No stamp of the run is about to wrap, at the moment it is cleared. -/
def ClearsOK : List MemoSch → Mem → Prop
  | [], _ => True
  | S :: l, m => rdW (m.arr64 CTL) S.cs + 2 ≠ 0 ∧ ClearsOK l (mclearG S m)

theorem clearsL_frame : ∀ (l : List MemoSch) (m : Mem),
    MemFrame [] (l.flatMap fun S => [S.cs, S.cs + 1]) m (clearsL l m)
  | [], m => MemFrame.refl _ _ _
  | S :: l, m => ((mclearG_frame S m).mono (by simp)
      (fun x h => by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl h)).trans
      ((clearsL_frame l _).mono (by simp) (fun x h => List.mem_append_right _ h))

/-- A memo outside a run of clears keeps its relation across it. -/
theorem memoRV_clearsL_other {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (hS : S.WF)
    (K : MemoKey κ) (VR : Mem → Word → ν → Prop) (hV : VConst VR) (l : List MemoSch)
    (hl : ∀ S' ∈ l, S.cs ≠ S'.cs ∧ S.cs ≠ S'.cs + 1)
    (m : Mem) (mp : Std.HashMap κ ν) (h : MemoRV S K VR m mp) : MemoRV S K VR (clearsL l m) mp :=
  memoRV_frame S hS K VR [] _ (by simp) (fun hm => by
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨S', h1, h2⟩ := hm
    rcases h2 with e | e
    · exact (hl S' h1).1 e
    · exact (hl S' h1).2 e) m _ (clearsL_frame l m) (hV m _) mp h

/-- **A memo cleared in a run is empty after it**, if no other clear of the run touches its
stamp. -/
theorem memoRV_clearsL {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    (S : MemoSch) (hS : S.WF) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) (hV : VConst VR) :
    ∀ (pre post : List MemoSch) (m : Mem) (mp : Std.HashMap κ ν),
    (∀ S' ∈ pre ++ post, S.cs ≠ S'.cs ∧ S.cs ≠ S'.cs + 1) → ClearsOK (pre ++ S :: post) m →
    MemoRV S K VR m mp → MemoRV S K VR (clearsL (pre ++ S :: post) m) ∅
  | [], post, m, mp, hl, hok, h => by
    simp only [List.nil_append, clearsL] at hok ⊢
    exact memoRV_clearsL_other S hS K VR hV post (fun S' h' => hl S' (by simpa using h')) _ _
      (memoRV_clear S hS K VR m mp h hok.1)
  | S₀ :: pre, post, m, mp, hl, hok, h => by
    simp only [List.cons_append, clearsL] at hok ⊢
    have h0 := hl S₀ (by simp)
    refine memoRV_clearsL S hS K VR hV pre post _ mp (fun S' h' => hl S' (by simp [h'])) hok.2 ?_
    exact memoRV_frame S hS K VR [] _ (by simp) (by simp [h0.1, h0.2]) m _ (mclearG_frame S₀ m)
      (hV m _) mp h

/-- The eleven core memos, in `flush_caches()`' order. -/
def coreSchs : List MemoSch :=
  [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch, rrSch, lqSch, lsqSch]

theorem flushOK_eq (m : Mem) : FlushOK m ↔ ClearsOK coreSchs m := by
  simp only [FlushOK, ClearsOK, coreSchs, and_true]

theorem bank_empty {κ ν : Type} [BEq κ] [Hashable κ] (g : Word) :
    Bank (∅ : Std.HashMap (κ × Word) ν) g ∅ := fun _ => by simp

/-- **The flush**: after `flush_caches()` the core tier relates the empty caches. -/
theorem CoreR.flush {m : Mem} {c : Caches} (h : CoreR m c) (hok : FlushOK m) :
    CoreR (flushMem m) Caches.empty := by
  obtain ⟨M, h⟩ := h
  rw [flushOK_eq] at hok
  have hc : ∀ {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (S : MemoSch)
      (K : MemoKey κ) (VR : Mem → Word → ν → Prop) (mp : Std.HashMap κ ν) (pre post : List MemoSch),
      VConst VR → S.WF → pre ++ S :: post = coreSchs →
      (∀ S' ∈ pre ++ post, S.cs ≠ S'.cs ∧ S.cs ≠ S'.cs + 1) →
      MemoRV S K VR m mp → MemoRV S K VR (flushMem m) ∅ :=
    fun S K VR mp pre post hV hS he hl hR => by
      have := memoRV_clearsL S hS K VR hV pre post m mp hl (he ▸ hok) hR
      rw [he] at this
      exact this
  have md : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop}, MemoRV S K VR (flushMem m) ∅ →
      ModeR S K VR (flushMem m) ∅ 0 ∅ ∅ :=
    fun hR => ⟨hR, bank_empty 0, fun _ => bank_empty 1, fun h => absurd rfl h⟩
  refine ⟨ModeMaps.empty, ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact md (hc wcSch _ _ _ [] _ vh_const (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide)
      h.wc.memo)
  · exact md (hc wkSch _ _ _ [wcSch] _ vh_const (coreSch_wf _ _ (by decide) (by decide)) rfl
      (by decide) h.wk.memo)
  · exact md (hc whSch _ _ _ [wcSch, wkSch] _ vh_const (coreSch_wf _ _ (by decide) (by decide)) rfl
      (by decide) h.wh.memo)
  · exact md (hc inSch _ _ _ [wcSch, wkSch, whSch] _ vh_const (coreSch_wf _ _ (by decide) (by decide))
      rfl (by decide) h.inf.memo)
  · exact md (hc ioSch _ _ _ [wcSch, wkSch, whSch, inSch] _ vh_const
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.io.memo)
  · exact md (hc deSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch] _ vb_const
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.de.memo)
  · exact hc ctSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch] _ vh_const
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.ct
  · exact hc cvSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch] _ vh_const
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.cv
  · exact hc rrSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch] _ vh_const
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.rr
  · exact hc lqSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch, rrSch] _
      (fun _ _ _ _ h => h) (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.lq
  · exact hc lsqSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch, rrSch, lqSch] _
      (fun _ _ _ _ h => h) (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) h.lsq

/-! ## The pin table: array 128 (`PINS`)

The twin's `Pins` (`CoreState.lean:137`): 51 name handles, the 16 reserved names, and three
interned values. In L one word array, filled once by the driver:

| word | contents |
|---:|---|
| 0 | the ready flag (`≠ 0`: filled; the twin's `pinsReady`, `names.size = 51`) |
| 1‥51 | `names[0‥50]` (slot `PIN_*` at word `1 + PIN_*`) |
| 52, 53, 54 | `emptyLevels`, `zeroLevel`, `sortOne` |
| 55‥70 | `reserved` (16 names) |

A reader checks the flag and aborts on `0`, where the twin raises `.internal` (an unfilled table
is empty in the twin, so every read fails there too). So the relation claims nothing while the
flag is `0`, and all-zero memory is related to every `Pins` (in particular `Pins.empty`).
-/

/-- Word `i` of the pin array (`0` out of bounds). -/
def pinW (m : Mem) (i : Nat) : Word := (m.arr64 PINS)[i]?.getD 0

/-- The filled table: what the flag promises. -/
structure PinsFull (m : Mem) (p : Pins) : Prop where
  size : 72 ≤ (m.arr64 PINS).size
  names_size : p.names.size = 52
  names_lt : ∀ i, i < 51 → (pinW m (1 + i)).toNat < 2 ^ 32
  names : ∀ i (h : i < 51), p.names[i]'(by omega) = decI (pinW m (1 + i))
  /-- Slot `51` (`quotMkName`) is word `71`, past the reserved names. -/
  quotMk_lt : (pinW m 71).toNat < 2 ^ 32
  quotMk : p.names[51]'(by omega) = decI (pinW m 71)
  lv_lt : (pinW m 52).toNat < 2 ^ 32 ∧ (pinW m 53).toNat < 2 ^ 32 ∧ (pinW m 54).toNat < 2 ^ 32
  emptyLevels : p.emptyLevels = decI (pinW m 52)
  zeroLevel : p.zeroLevel = decI (pinW m 53)
  sortOne : p.sortOne = decI (pinW m 54)
  reserved_lt : ∀ i, i < 16 → (pinW m (55 + i)).toNat < 2 ^ 32
  reserved : p.reserved = (List.range 16).map fun i => decI (pinW m (55 + i))

/-- **The pins** (global, filled once by `internReservedPins`), over `a.pins`: when the flag is
set, the table is the twin's. -/
structure PinsR (m : Mem) (p : Pins) : Prop where
  full : pinW m 0 ≠ 0 → PinsFull m p

theorem PinsFull.congr {m m' : Mem} {p : Pins} (he : m'.arr64 PINS = m.arr64 PINS)
    (h : PinsFull m p) : PinsFull m' p := by
  have hw : ∀ i, pinW m' i = pinW m i := fun i => by simp only [pinW, he]
  exact { size := he ▸ h.size, names_size := h.names_size,
            names_lt := fun i hi => hw _ ▸ h.names_lt i hi, names := fun i hi => hw _ ▸ h.names i hi,
            quotMk_lt := hw _ ▸ h.quotMk_lt, quotMk := hw _ ▸ h.quotMk,
            lv_lt := by simpa only [hw] using h.lv_lt, emptyLevels := hw _ ▸ h.emptyLevels,
            zeroLevel := hw _ ▸ h.zeroLevel, sortOne := hw _ ▸ h.sortOne,
            reserved_lt := fun i hi => hw _ ▸ h.reserved_lt i hi,
            reserved := by simpa only [hw] using h.reserved }

theorem PinsR.congr {m m' : Mem} {p : Pins} (he : m'.arr64 PINS = m.arr64 PINS)
    (h : PinsR m p) : PinsR m' p :=
  ⟨fun h0 => (h.full (by simpa only [pinW, he] using h0)).congr he⟩

theorem PinsR.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {p : Pins}
    (hA : AvoidA 128 129 A) (hf : MemFrame A C m m') (h : PinsR m p) : PinsR m' p :=
  h.congr (hf.arr PINS (fun hm => by have := hA _ hm; revert this; decide) (by decide))

/-- All-zero pins (the flag `0`) are related to every table. -/
theorem PinsR.of_flag {m : Mem} {p : Pins} (h : pinW m 0 = 0) : PinsR m p :=
  ⟨fun h0 => absurd h h0⟩

/-! ## The environment: arrays 129‥137, 140‥142, 146‥148, `CTL` 128‥130, 133‥135

The twin's `IFEnv` (`ConRon/Arena/Env.lean`) is a job's own layer over the frozen stream index
(`Env.lean`'s module doc has the L layout). `EnvR m vis fe` relates one view `vis` of the own
layer and the stream index, **extensionally** (through what the twin's lookups read, so the
layout of `Std.HashMap` is free):

* the own layer: `fe.idx[n]?` is the own row of `n` when it carries the job's stamp and a
  counter below `vis`, decoded; `fe.tbls[n]?` the own table row of `n` with the stamp, decoded;
* the stream index: `fe.base.below = EBELOW`, `fe.base.belowRec = EBELOWR`, every entry of
  `fe.base.idx` is the base row of its name (counter and record, decoded), every entry of
  `fe.base.tbls` the base table row (position and record, decoded).
-/

/-- The constructor tag of a name handle word (`⟦w⟧.tag`). -/
def rowTag (w : Word) : Nat := (tagW w).toNat
/-- The tier bit of a name handle word (`⟦w⟧.tier`). -/
def rowTier (w : Word) : Nat := w.toNat / 2 ^ 31 % 2

theorem tagW_toNat_row (w : Word) : (tagW w).toNat = rowTag w := rfl

theorem tierW_toNat_row (w : Word) : (tierW w).toNat = rowTier w := tierW_toNat' w

/-- A name handle word (tag at most `2`) is narrow. -/
theorem rowTag_narrow {w : Word} (h : rowTag w ≤ 2) : w.toNat / 2 ^ 30 % 2 = 0 :=
  narrow_of_tagW w fun e => by simp only [rowTag, e] at h; revert h; decide

/-- The tag of a narrow word as a number. -/
theorem rowTag_eq {w : Word} (h : rowTag w ≤ 2) : rowTag w = w.toNat / 2 ^ 26 % 16 := by
  have hn := rowTag_narrow h
  have := tagW_toNat w; rw [ite_eq_right (by omega)] at this; exact this

theorem rowTag_lt (w : Word) : rowTag w < 16 := by
  have := tagW_toNat w; simp only [rowTag]; split at this <;> omega

/-- The first word of a name handle's row in its array. -/
def rowIx (w : Word) : Nat := 2 * (idxW w).toNat

/-- The stream index's constant-row array of name tag `g`: `EIXA`, `EIXS`, `EIXN`. -/
def eixArr (g : Nat) : ArrId := if g = 0 then EIXA else if g = 1 then EIXS else EIXN

/-- The own layer's constant-row array of name tag `g`: `OIXA`, `OIXS`, `OIXN`. -/
def oixArr (g : Nat) : ArrId := if g = 0 then OIXA else if g = 1 then OIXS else OIXN

/-- The stream index's table-row array of name tag `g`: `TIXA`, `TIXS`, `TIXN`. -/
def tixArr (g : Nat) : ArrId := if g = 0 then TIXA else if g = 1 then TIXS else TIXN

/-- The own layer's table-row array of name tag `g`: `OTXA`, `OTXS`, `OTXN`. -/
def otxArr (g : Nat) : ArrId := if g = 0 then OTXA else if g = 1 then OTXS else OTXN

/-- Word `k` of an array, `0` out of bounds. -/
def rdN (a : Array Word) (k : Nat) : Word := a[k]?.getD 0

/-- The job's stamp. -/
def stampW (m : Mem) : Word := rdW (m.arr64 CTL) 133

/-- The own layer's row of name handle `w` (tag at most `2`): its two words. -/
def ownRow (m : Mem) (w : Word) : Word × Word :=
  let a := m.arr64 (tierA (oixArr (rowTag w)) (tierW w))
  (rdN a (rowIx w), rdN a (rowIx w + 1))

/-- The own layer's raw row (`fe.idx[n]?`'s counter plus one and record): `(0, 0)` unless it
carries the stamp. -/
def ownRaw (m : Mem) (w : Word) : Word × Word :=
  if rowTag w ≤ 2 ∧ (ownRow m w).1 >>> 32 = stampW m then
    ((ownRow m w).1 &&& 4294967295, (ownRow m w).2) else (0, 0)

/-- The stream index's row of name handle `w`: counter plus one and record, `(0, 0)` for a
scratch name or another tag. -/
def baseRow (m : Mem) (w : Word) : Word × Word :=
  if rowTag w ≤ 2 ∧ rowTier w = 0 then
    (rdN (m.arr64 (eixArr (rowTag w))) (rowIx w), rdN (m.arr64 (eixArr (rowTag w))) (rowIx w + 1))
  else (0, 0)

/-- The own layer's table row: the record's address plus one, `0` for none. -/
def ownTbl (m : Mem) (w : Word) : Word :=
  let a := m.arr64 (tierA (otxArr (rowTag w)) (tierW w))
  if rowTag w ≤ 2 ∧ rdN a (rowIx w) = stampW m then rdN a (rowIx w + 1) else 0

/-- The stream index's table row: position plus one and record. -/
def baseTbl (m : Mem) (w : Word) : Word × Word :=
  if rowTag w ≤ 2 ∧ rowTier w = 0 then
    (rdN (m.arr64 (tixArr (rowTag w))) (rowIx w), rdN (m.arr64 (tixArr (rowTag w))) (rowIx w + 1))
  else (0, 0)

/-- The record pool's tier-0 top, `CTL[129]`. -/
def erTop (m : Mem) : Nat := (rdW (m.arr64 CTL) 129).toNat

/-- The record pool's tier-1 top, `CTL[130]`. -/
def erecTop1 (m : Mem) : Nat := (rdW (m.arr64 CTL) 130).toNat

/-- **L's tagged read `EREC⦃a⦄`**, as a function of the address (and as a model reads it). -/
def erRd (m : Mem) (a : Word) : Word := rdW (m.arr64 (tierA EREC (a >>> 40))) (a &&& 0xFFFFFFFFFF)

theorem ctl_t0 : TieredArray.t0 1 = (CTL : TieredArray) := rfl

/-- **The record pool in use**, both tiers as one address space, read exactly as L's tagged
read `EREC⦃a⦄` reads the word address `a < 2^64`: tier bit 40, offset the low 40 bits (so tier 1
is at `2^40 + o`), each tier below its top. Every record the relations decode is decoded here, so
a writer above a top (an allocation, `erec_alloc`) keeps them all (`ArrExt`), and a decoded word
is the word L reads (`erecP_tagRead`). -/
def erecP (m : Mem) : Nat → Option Word := fun i =>
  if i < 2 ^ 64 then
    (if i / 2 ^ 40 % 2 = 0 then (if i % 2 ^ 40 < erTop m then (m.arr64 EREC)[i % 2 ^ 40]? else none)
     else if i % 2 ^ 40 < erecTop1 m then (m.arr64 (tier1 EREC))[i % 2 ^ 40]? else none)
  else none

/-- `m'`'s record pool extends `m`'s: both tops only moved up, nothing below them changed. -/
structure ErecGrow (m m' : Mem) : Prop where
  top : erTop m ≤ erTop m'
  get : ∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?
  top1 : erecTop1 m ≤ erecTop1 m'
  get1 : ∀ i < erecTop1 m, (m'.arr64 (tier1 EREC))[i]? = (m.arr64 (tier1 EREC))[i]?

theorem ErecGrow.ext {m m' : Mem} (h : ErecGrow m m') : ArrExt (erecP m) (erecP m') := by
  intro i v hv
  unfold erecP at hv ⊢
  by_cases h64 : i < 2 ^ 64
  · simp only [h64, ite_true] at hv ⊢
    by_cases hi : i / 2 ^ 40 % 2 = 0
    · simp only [hi, ite_true] at hv ⊢
      by_cases ht : i % 2 ^ 40 < erTop m
      · simp only [ht, ite_true] at hv
        rw [ite_eq_left (Nat.lt_of_lt_of_le ht h.top), h.get _ ht]; exact hv
      · simp [ht] at hv
    · simp only [hi, ite_false] at hv ⊢
      by_cases ht : i % 2 ^ 40 < erecTop1 m
      · simp only [ht, ite_true] at hv
        rw [ite_eq_left (Nat.lt_of_lt_of_le ht h.top1), h.get1 _ ht]; exact hv
      · simp [ht] at hv
  · simp [h64] at hv

/-- **A decoded word is the word L's tagged read `EREC⦃a⦄` reads** (`ld64t EREC (a >>> 40)
(a &&& (2^40 - 1))`), in bounds. -/
theorem erecP_tagRead {m : Mem} {a v : Word} (h : erecP m a.toNat = some v) :
    (a &&& 0xFFFFFFFFFF).toNat < (m.arr64 (tierA EREC (a >>> 40))).size ∧
      (m.arr64 (tierA EREC (a >>> 40)))[(a &&& 0xFFFFFFFFFF).toNat]? = some v := by
  have hmask : (a &&& 0xFFFFFFFFFF).toNat = a.toNat % 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 40
  have hbit : ((a >>> 40) &&& 1).toNat = a.toNat / 2 ^ 40 % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat]
    exact Nat.and_one_is_mod _
  have ht : tierA EREC (a >>> 40) = if a.toNat / 2 ^ 40 % 2 = 0 then (EREC : TieredArray) else tier1 EREC := by
    unfold tierA
    by_cases e : a.toNat / 2 ^ 40 % 2 = 0
    · have : (a >>> 40) &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [hbit, e]; rfl)
      simp [e, this]
    · have : (a >>> 40) &&& 1 ≠ 0 := fun h' => e (by rw [← hbit, h']; rfl)
      simp [e, this]
  rw [hmask, ht]
  unfold erecP at h
  simp only [a.toNat_lt, ite_true] at h
  split at h
  · rename_i e; simp only [e, ite_true]; split at h
    · exact ⟨(Array.getElem?_eq_some_iff.mp h).1, h⟩
    · simp at h
  · rename_i e; simp only [e, ite_false]; split at h
    · exact ⟨(Array.getElem?_eq_some_iff.mp h).1, h⟩
    · simp at h

theorem ErecGrow.refl (m : Mem) : ErecGrow m m :=
  ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem ErecGrow.trans {m₁ m₂ m₃ : Mem} (h₁ : ErecGrow m₁ m₂) (h₂ : ErecGrow m₂ m₃) :
    ErecGrow m₁ m₃ :=
  ⟨Nat.le_trans h₁.top h₂.top, fun i hi => (h₂.get i (Nat.lt_of_lt_of_le hi h₁.top)).trans (h₁.get i hi),
   Nat.le_trans h₁.top1 h₂.top1,
   fun i hi => (h₂.get1 i (Nat.lt_of_lt_of_le hi h₁.top1)).trans (h₁.get1 i hi)⟩

/-- The relation's view of an own row: the decoded constant when the row is the job's and
below `vis`. -/
def ownFind (m : Mem) (vis : Word) (w : Word) : Option IConstantInfo :=
  let r := ownRaw m w
  if r.1 ≠ 0 ∧ r.1.toNat - 1 < vis.toNat then decCI (erecP m) r.2.toNat else none

/-- Every own row and own table row carries a stamp at most the current one (what lets a stamp
bump empty the own layer without clearing it: `record_job`). Every own-row writer stores the
current stamp (`env_push`, `env_pop_temp`, `tbl_own_set`), so the clause rides along `EnvR`. -/
def OwnBelow (m : Mem) : Prop :=
  ∀ w, rowTag w ≤ 2 → ((ownRow m w).1 >>> 32).toNat ≤ (stampW m).toNat ∧
    (rdN (m.arr64 (tierA (otxArr (rowTag w)) (tierW w))) (rowIx w)).toNat ≤ (stampW m).toNat

/-- **The environment relation** (one view). Every clause is over all names (a row of a word
of another tag reads as absent: `ownRaw`, `baseRow`, `ownTbl`, `baseTbl`):

* the own layer is the twin's `idx` (`own`), its rows decode (`own_dec`), every row is in the
  view (`fresh`: the view is the newest, so a push at `vis` sees no stale row) and the rows'
  counters are distinct (`uniq`: `popTemp` lowers the view past exactly one row);
* the own table rows are the twin's `tbls` and decode (`otbl`, `otbl_dec`);
* the stream index is the twin's `base` (`below`, `belowRec`, `base`, `btbl`);
* the stamp is below `2^32` (`stamp`: a row word is `stamp · 2^32 + c + 1`), and no row carries
  a later one (`ownBelow`). -/
structure EnvR (m : Mem) (vis : Word) (fe : IFEnv) : Prop where
  own : ∀ n : NIdx, fe.idx[n]? = ownFind m vis n.word.toUInt64
  own_dec : ∀ n : NIdx, (ownRaw m n.word.toUInt64).1 ≠ 0 →
    ∃ ci, decCI (erecP m) (ownRaw m n.word.toUInt64).2.toNat = some ci
  fresh : ∀ n : NIdx, (ownRaw m n.word.toUInt64).1 ≠ 0 →
    (ownRaw m n.word.toUInt64).1.toNat - 1 < vis.toNat
  uniq : ∀ n n' : NIdx, (ownRaw m n.word.toUInt64).1 ≠ 0 →
    (ownRaw m n.word.toUInt64).1 = (ownRaw m n'.word.toUInt64).1 → n = n'
  otbl : ∀ n : NIdx,
    fe.tbls[n]? = (if ownTbl m n.word.toUInt64 = 0 then none
      else decTbl (erecP m) ((ownTbl m n.word.toUInt64).toNat - 1))
  otbl_dec : ∀ n : NIdx, ownTbl m n.word.toUInt64 ≠ 0 →
    ∃ t, decTbl (erecP m) ((ownTbl m n.word.toUInt64).toNat - 1) = some t
  below : fe.base.below = (rdW (m.arr64 CTL) 134).toNat
  belowRec : fe.base.belowRec = (rdW (m.arr64 CTL) 135).toNat
  base : ∀ n : NIdx,
    (fe.base.idx[n]?).map (fun e => (e.1, some e.2)) =
      (if (baseRow m n.word.toUInt64).1 = 0 then none
       else some ((baseRow m n.word.toUInt64).1.toNat - 1,
         decCI (erecP m) (baseRow m n.word.toUInt64).2.toNat))
  btbl : ∀ n : NIdx,
    (fe.base.tbls[n]?).map (fun e => (e.1, some e.2)) =
      (if (baseTbl m n.word.toUInt64).1 = 0 then none
       else some ((baseTbl m n.word.toUInt64).1.toNat - 1,
         decTbl (erecP m) (baseTbl m n.word.toUInt64).2.toNat))
  stamp : (stampW m).toNat < 2 ^ 32
  ownBelow : OwnBelow m

/-- The arrays and globals `EnvR` reads. -/
def envArrs : List TieredArray :=
  [EIXA, EIXS, EIXN, TIXA, TIXS, TIXN, EREC, tier1 EREC, OIXA, OIXS, OIXN, tier1 OIXA,
   tier1 OIXS, tier1 OIXN, OTXA, OTXS, OTXN, tier1 OTXA, tier1 OTXS, tier1 OTXN]

/-- The control words `EnvR` reads. -/
def envCtl : List Word := [129, 130, 133, 134, 135]

/-- The own layer's row arrays of every tag and tier are `EnvR`'s. -/
theorem tierA_oix_mem (g : Nat) (t : UInt64) : tierA (oixArr g) t ∈ envArrs := by
  unfold tierA oixArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

theorem tierA_otx_mem (g : Nat) (t : UInt64) : tierA (otxArr g) t ∈ envArrs := by
  unfold tierA otxArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

theorem eix_mem (g : Nat) : (eixArr g : TieredArray) ∈ envArrs := by
  unfold eixArr; split <;> (try split) <;> decide

theorem tix_mem (g : Nat) : (tixArr g : TieredArray) ∈ envArrs := by
  unfold tixArr; split <;> (try split) <;> decide

/-- **`EnvR` reads only `envArrs` and `envCtl`.** -/
theorem EnvR.congr {m m' : Mem} {vis : Word} {fe : IFEnv}
    (he : ∀ b ∈ envArrs, m'.arr64 b = m.arr64 b)
    (hc : ∀ x ∈ envCtl, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (h : EnvR m vis fe) : EnvR m' vis fe := by
  have hP : erecP m' = erecP m := by
    funext i
    simp only [erecP, erTop, erecTop1, he EREC (by decide), he (tier1 EREC) (by decide),
      hc 129 (by decide), hc 130 (by decide)]
    rfl
  have hs : stampW m' = stampW m := hc 133 (by decide)
  have hor : ∀ w, ownRow m' w = ownRow m w := fun w => by
    simp only [ownRow, he _ (tierA_oix_mem _ _)]
  have hraw : ∀ w, ownRaw m' w = ownRaw m w := fun w => by simp only [ownRaw, hor, hs]
  have hfind : ∀ w, ownFind m' vis w = ownFind m vis w := fun w => by
    simp only [ownFind, hraw, hP]
  have hot : ∀ w, ownTbl m' w = ownTbl m w := fun w => by
    simp only [ownTbl, he _ (tierA_otx_mem _ _), hs]
  have hb : ∀ w, baseRow m' w = baseRow m w := fun w => by
    simp only [baseRow, he _ (eix_mem _)]
  have hbt : ∀ w, baseTbl m' w = baseTbl m w := fun w => by
    simp only [baseTbl, he _ (tix_mem _)]
  exact ⟨fun n => by rw [hfind]; exact h.own n, fun n => by rw [hraw, hP]; exact h.own_dec n,
    fun n => by rw [hraw]; exact h.fresh n, fun n n' => by rw [hraw, hraw]; exact h.uniq n n',
    fun n => by rw [hot, hP]; exact h.otbl n, fun n => by rw [hot, hP]; exact h.otbl_dec n,
    by rw [hc 134 (by decide)]; exact h.below, by rw [hc 135 (by decide)]; exact h.belowRec,
    fun n => by rw [hb, hP]; exact h.base n, fun n => by rw [hbt, hP]; exact h.btbl n,
    by rw [hs]; exact h.stamp, fun w hw => by
      rw [hor, hs, he _ (tierA_otx_mem _ _)]; exact h.ownBelow w hw⟩

/-- **`EnvR` across a frame** that avoids its arrays and control words. -/
theorem EnvR.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hA : ∀ b ∈ A, b ∉ envArrs) (hC : ∀ x ∈ C, x ∉ envCtl) (hf : MemFrame A C m m')
    (h : EnvR m vis fe) : EnvR m' vis fe :=
  h.congr (fun b hb => hf.arr b (fun hm => hA b hm hb) (fun e => by subst e; revert hb; decide))
    (fun x hx => hf.ctl x (fun hm => hC x hm hx))

/-- `EnvR`'s arrays are at 129‥148. -/
theorem envArrs_arr {b : TieredArray} (h : b ∈ envArrs) :
    129 ≤ b.arr ∧ b.arr < 149 ∧ b.arr ≠ 135 ∧ (b.arr < 137 ∨ 140 ≤ b.arr) ∧ (b.arr < 143 ∨ 146 ≤ b.arr) := by
  simp only [envArrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> decide

theorem not_mem_envArrs {b : TieredArray}
    (h : b.arr < 129 ∨ 149 ≤ b.arr ∨ b.arr = 135 ∨ (137 ≤ b.arr ∧ b.arr < 140) ∨ (143 ≤ b.arr ∧ b.arr < 146)) :
    b ∉ envArrs := fun hm => by have := envArrs_arr hm; omega

theorem not_mem_envCtl {x : Word}
    (h : x.toNat < 129 ∨ 136 ≤ x.toNat ∨ x.toNat = 131 ∨ x.toNat = 132) : x ∉ envCtl := fun hm => by
  simp only [envCtl, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e <;> subst e <;> simp at h

/-- **`EnvR` across a growth of the record pool** (allocations and writes above the tops):
the rows are untouched and every decoding they name decodes in the bigger pool too. -/
theorem EnvR.growC {m m' : Mem} {vis : Word} {fe : IFEnv}
    (he : ∀ b : TieredArray, b.arr ≠ 136 → b.arr ≠ 1 → b ∈ envArrs → m'.arr64 b = m.arr64 b)
    (hc : ∀ x ∈ envCtl, x ≠ 129 → x ≠ 130 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (hg : ErecGrow m m') (h : EnvR m vis fe) : EnvR m' vis fe := by
  have hx := hg.ext
  have he : ∀ b : TieredArray, b.arr ≠ 136 → b.arr ≠ 1 → b ∈ envArrs → m'.arr64 b = m.arr64 b := he
  have hc : ∀ x, x ≠ 129 → x ≠ 130 → x ∈ envCtl → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x :=
    fun x h1 h2 hm => hc x hm h1 h2
  have hs : stampW m' = stampW m := hc 133 (by decide) (by decide) (by decide)
  have o1 : ∀ g t, (tierA (oixArr g) t).arr ≠ 136 ∧ (tierA (oixArr g) t).arr ≠ 1 := fun g t => by
    unfold tierA oixArr; split <;> (try split) <;> simp [OIXA, OIXS, OIXN]
  have o2 : ∀ g t, (tierA (otxArr g) t).arr ≠ 136 ∧ (tierA (otxArr g) t).arr ≠ 1 := fun g t => by
    unfold tierA otxArr; split <;> (try split) <;> simp [OTXA, OTXS, OTXN]
  have o3 : ∀ g, (eixArr g : TieredArray).arr ≠ 136 ∧ (eixArr g : TieredArray).arr ≠ 1 := fun g => by
    unfold eixArr; split <;> (try split) <;> decide
  have o4 : ∀ g, (tixArr g : TieredArray).arr ≠ 136 ∧ (tixArr g : TieredArray).arr ≠ 1 := fun g => by
    unfold tixArr; split <;> (try split) <;> decide
  have hor : ∀ w, ownRow m' w = ownRow m w := fun w => by
    simp only [ownRow, he _ (o1 _ _).1 (o1 _ _).2 (tierA_oix_mem _ _)]
  have hraw : ∀ w, ownRaw m' w = ownRaw m w := fun w => by simp only [ownRaw, hor, hs]
  have hot : ∀ w, ownTbl m' w = ownTbl m w := fun w => by
    simp only [ownTbl, he _ (o2 _ _).1 (o2 _ _).2 (tierA_otx_mem _ _), hs]
  have hb : ∀ w, baseRow m' w = baseRow m w := fun w => by
    simp only [baseRow, he _ (o3 _).1 (o3 _).2 (eix_mem _)]
  have hbt : ∀ w, baseTbl m' w = baseTbl m w := fun w => by
    simp only [baseTbl, he _ (o4 _).1 (o4 _).2 (tix_mem _)]
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun n n' hn hq => ?_, fun n => ?_, fun n hn => ?_,
    by rw [hc 134 (by decide) (by decide) (by decide)]; exact h.below, by rw [hc 135 (by decide) (by decide) (by decide)]; exact h.belowRec,
    fun n => ?_, fun n => ?_, by rw [hs]; exact h.stamp, fun w hw => by
      rw [hor, hs, he _ (o2 _ _).1 (o2 _ _).2 (tierA_otx_mem _ _)]; exact h.ownBelow w hw⟩
  · rw [h.own n]; simp only [ownFind, hraw]
    split
    · rename_i c; obtain ⟨ci, hci⟩ := h.own_dec n c.1; rw [hci, hx.decCI hci]
    · rfl
  · rw [hraw] at hn ⊢; obtain ⟨ci, hci⟩ := h.own_dec n hn; exact ⟨ci, hx.decCI hci⟩
  · rw [hraw] at hn ⊢; exact h.fresh n hn
  · rw [hraw, hraw] at hq; rw [hraw] at hn; exact h.uniq n n' hn hq
  · rw [h.otbl n, hot]
    split
    · rfl
    · rename_i c; obtain ⟨t, ht⟩ := h.otbl_dec n c; rw [ht, hx.decTbl ht]
  · rw [hot] at hn ⊢; obtain ⟨t, ht⟩ := h.otbl_dec n hn; exact ⟨t, hx.decTbl ht⟩
  · have := h.base n; rw [hb]
    rw [this]; split
    · rfl
    · cases e : fe.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [hbt]
    rw [this]; split
    · rfl
    · cases e : fe.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]

/-! ## The whole relation -/

theorem EnvR.grow {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hf : MemFrame [EREC, tier1 EREC] [129, 130] m m') (hg : ErecGrow m m') (h : EnvR m vis fe) :
    EnvR m' vis fe :=
  h.growC (fun b h1 h2 _ => hf.arr b (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (e | e) <;> subst e <;> exact h1 rfl) (fun e => by subst e; exact h2 rfl))
    (fun x _ h1 h2 => hf.ctl x (by simp [h1, h2])) hg

/-- **`EnvR` across a frame that grows the record pool**: every array the frame names is a record
tier or not `EnvR`'s, every control word `129`, `130` or not `EnvR`'s. -/
theorem EnvR.growF {A : List TieredArray} {C : List Word} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b.arr = 136 ∨ b ∉ envArrs)
    (hC : ∀ x ∈ C, x = 129 ∨ x = 130 ∨ x ∉ envCtl) (hg : ErecGrow m m') (h : EnvR m vis fe) :
    EnvR m' vis fe :=
  h.growC (fun b h1 _ hb => hf.arr b (fun hm => by
      rcases hA b hm with e | e
      · exact h1 e
      · exact e hb) (fun e => by subst e; revert hb; decide))
    (fun x hx h1 h2 => hf.ctl x (fun hm => by
      rcases hC x hm with e | e | e
      · exact h1 e
      · exact h2 e
      · exact e hx)) hg

theorem MemFrame.top_eq {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    (hC : (0 : Word) ∉ C) : m'.top = m.top := by
  have := hf.ctl 0 hC
  simp only [rdW] at this
  simpa [Mem.top] using this

/-- **The mode across a frame** that keeps `CTL[0]` and `CTL[1]`. -/
theorem ModeOK.frame {m m' : Mem} {A : List TieredArray} {C : List Word} (h : ModeOK m)
    (hf : MemFrame A C m m') (h0 : (0 : Word) ∉ C) (h1 : (1 : Word) ∉ C) : ModeOK m' := by
  have ht : m'.top = m.top := hf.top_eq h0
  have hfl : m'.flag = m.flag := hf.ctl 1 h1
  unfold ModeOK; rw [ht, hfl]; exact h

/-- **The relation, by tier.** -/
structure CheckR (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) : Prop where
  arena : ArenaD m a
  core : CoreR m a.caches
  pins : PinsR m a.pins
  env : EnvR m vis fe
  /-- The pool's mode (lane tierpool; `ModeOK`). -/
  mode : ModeOK m

/-- **The upper tiers across a walk**: a run whose L write set is below 64 (every walk,
`WriteSets.lean`) and whose twin side keeps `cp` (every walk, `Keeps.lean`) keeps `CoreR`,
`PinsR` and `EnvR`; the walk's own theorem gives `ArenaD`. -/
theorem CheckR.of_walkM {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {A : List TieredArray} {C : List Word} (hR : CheckR m a vis fe) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, InStoreTier b) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a)
    (hmode : ModeOK m') : CheckR m' a' vis fe := by
  have hc : a'.caches = a.caches := congrArg Prod.fst hk
  have hp : a'.pins = a.pins := congrArg Prod.snd hk
  refine ⟨hD, ?_, ?_, hR.env.frame (fun b hb => not_mem_envArrs (.inl (by have := hA b hb; omega)))
    (fun x hx => not_mem_envCtl (.inl (by have := hC x hx; omega))) hf, hmode⟩
  · rw [hc]; exact hR.core.frame (.of_low hA (by decide)) (.of_lt hC (by decide)) hf
  · rw [hp]; exact hR.pins.frame (.of_low hA (by decide)) hf

/-- `CheckR.of_walkM` for a walk that keeps `CTL[0]` and `CTL[1]` (an interning): the mode by the
frame. -/
theorem CheckR.of_walk {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {A : List TieredArray} {C : List Word} (hR : CheckR m a vis fe) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, InStoreTier b) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a)
    (h01 : (0 : Word) ∉ C ∧ (1 : Word) ∉ C := by decide) : CheckR m' a' vis fe :=
  hR.of_walkM hD hf hA hC hk (hR.mode.frame hf h01.1 h01.2)

/-- **Every tier but the arena's above a writer**: tier-0 arrays from 137 but the own layer's
(140‥142, 146‥148), and `CTL` words from 131 up but the stamp and the base view (133‥135)
(the argument relations: pending checks, `PMemo`, the level heap) keep `CheckR`. -/
theorem CheckR.frame_hi {A : List TieredArray} {C : List Word}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    (hA : ∀ b ∈ A, b.hi = false ∧ 137 ≤ b.arr ∧ (b.arr < 140 ∨ 144 ≤ b.arr) ∧ (b.arr < 146 ∨ 149 ≤ b.arr))
    (hC : ∀ x ∈ C, 131 ≤ x.toNat ∧ x.toNat ≠ 133 ∧ x.toNat ≠ 134 ∧ x.toNat ≠ 135)
    (hf : MemFrame A C m m') (h : CheckR m a vis fe) :
    CheckR m' a vis fe := by
  have hA' : ∀ lo hi, hi ≤ 137 → AvoidA lo hi A := fun lo hi hh b hb => .inr (by
    have := (hA b hb).2.1; omega)
  have hC' : ∀ lo hi, hi ≤ 131 → AvoidC lo hi C := fun lo hi hh x hx => .inr (by
    have := (hC x hx).1; omega)
  refine ⟨⟨?_, ?_⟩, h.core.frame (hA' _ _ (by decide)) (hC' _ _ (by decide)) hf,
    h.pins.frame (hA' _ _ (by decide)) hf,
    h.env.frame (fun b hb => not_mem_envArrs (by have := hA b hb; omega))
      (fun x hx => not_mem_envCtl (by have := hC x hx; omega)) hf,
    h.mode.frame hf (fun h => by have := (hC _ h).1; simp at this)
      (fun h => by have := (hC _ h).1; simp at this)⟩
  · exact ArenaR.frame_ext A C (fun b hb => by
      have := hA b hb; exact ⟨this.1, by omega⟩)
      (fun x hx => by have := (hC x hx).1; omega) m m' hf a h.arena.base
  · exact DerR.frameM A C m m' hf (fun b hb => by
      have := hA b hb; omega) a h.arena.der

/-- **The relation across a growth of the record pool** (`erec_alloc`, `erec_put` above the
tops): only `EREC` (both tiers) and its tops change. -/
theorem CheckR.erGrow {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} (h : CheckR m a vis fe)
    (hf : MemFrame [EREC, tier1 EREC] [129, 130] m m') (hg : ErecGrow m m') : CheckR m' a vis fe := by
  have hA : ∀ b ∈ [(EREC : TieredArray), tier1 EREC], 136 ≤ b.arr ∧ b.arr < 137 := by
    simp [EREC, tier1]
  have hC : ∀ x ∈ ([129, 130] : List Word), 129 ≤ x.toNat ∧ x.toNat < 131 := by simp
  have hlow : ∀ y ∈ arenaArrs, y.arr < 64 := by decide
  refine ⟨⟨?_, ?_⟩, h.core.frame (fun b hb => .inr (by have := hA b hb; omega)) (fun x hx => .inr (by have := hC x hx; omega)) hf,
    h.pins.frame (fun b hb => .inr (by have := hA b hb; omega)) hf, h.env.grow hf hg,
    h.mode.frame hf (by decide) (by decide)⟩
  · exact ArenaR.frame (fun b hb hm => by have := hlow b hm; have := hA b hb; omega) (fun x hx => not_mem_arenaCtl x (by have := hC x hx; omega)) hf h.arena.base
  · exact DerR.frameM _ _ m m' hf (fun b hb => by have := hA b hb; omega) a h.arena.der

end L.Arena
