import ConAgua.Arena.DerRel
import ConAgua.Arena.Keeps
import ConAgua.Arena.EnvRec
import ConAgua.Arena.MemoBank
import ConAgua.Arena.CoreCaches
import Std.Tactic.BVDecide.Normalize.Prop

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
| `EnvR` | a view `vis` of `fe : IFEnv` (an argument) | 129‥136, 140‥143, 385‥387 | 128 (129: the record top), 133 | filled (lane `pinsenv`; tables: lane `consync`) |
| `PendR` (`Checker.lean`) | `pend` (an argument) | 137 | 130 | lane `pinsenv` |
| argument relations (`PMemo`, `pend`, saved `ModeMemos`, walk-local memos) | arguments | 144‥191 | 136‥191 | not yet |

`ArenaD = ArenaR ∧ DerR` stays the walks' tier. `CheckR` is the whole relation. A walk changes
only arrays below 64 (`WriteSets.lean`) and only `store`/`memos` (`Keeps cp`, `Keeps.lean`), so
`CheckR.of_walk` carries the upper tiers across it with no lemma about the walk.
-/

namespace L.Arena

open ConRon.Arena

/-- The words of a range, `lo ≤ x < hi`, apart from a writer. -/
def AvoidA (lo hi : Nat) (A : List ArrId) : Prop := ∀ b ∈ A, b < lo ∨ hi ≤ b
def AvoidC (lo hi : Nat) (C : List Word) : Prop := ∀ x ∈ C, x.toNat < lo ∨ hi ≤ x.toNat

instance (lo hi : Nat) (A : List ArrId) : Decidable (AvoidA lo hi A) := by unfold AvoidA; infer_instance

/-- A writer of arrays and words below `k` avoids every range starting at `k` or above. -/
theorem AvoidA.of_lt {k lo hi : Nat} {A : List ArrId} (hA : ∀ b ∈ A, b < k) (hk : k ≤ lo) :
    AvoidA lo hi A := fun b hb => .inl (Nat.lt_of_lt_of_le (hA b hb) hk)
theorem AvoidC.of_lt {k lo hi : Nat} {C : List Word} (hC : ∀ x ∈ C, x.toNat < k) (hk : k ≤ lo) :
    AvoidC lo hi C := fun x hx => .inl (Nat.lt_of_lt_of_le (hC x hx) hk)
/-- A writer of the store tier (arrays below `64` and their tier-1 twins `256‥319`) avoids every
range inside `[64, 256)`. -/
theorem AvoidA.of_low {lo hi : Nat} {A : List ArrId} (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320))
    (hlo : 64 ≤ lo) (hhi : hi ≤ 256) : AvoidA lo hi A := fun b hb =>
  (hA b hb).elim (fun h => .inl (Nat.lt_of_lt_of_le h hlo)) (fun h => .inr (Nat.le_trans hhi h.1))


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
    {t te : Std.HashMap κ ν} {A : List ArrId} {C : List Word} (hS : S.WF) (hV : VConst VR)
    (hA : S.arr ∉ A) (hC : S.cs ∉ C) (hf : MemFrame A C m m') (h : ModeR S K VR m M eb t te) :
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

theorem CoreRM.frame {A : List ArrId} {C : List Word} {m m' : Mem} {c : Caches} {M : ModeMaps}
    {eb : Word} (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m')
    (h : CoreRM m c M eb) : CoreRM m' c M eb := by
  have nA : ∀ b : ArrId, 96 ≤ b → b < 128 → b ∉ A := fun b h1 h2 hb => by
    have := hA b hb; simp only [ArrId] at this h1 h2; omega
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

theorem CoreR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {c : Caches}
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

/-- The pin array. -/
abbrev PINS : ArrId := 128

/-- Word `i` of the pin array (`0` out of bounds). -/
def pinW (m : Mem) (i : Nat) : Word := (m.arr64 PINS)[i]?.getD 0

/-- The filled table: what the flag promises. -/
structure PinsFull (m : Mem) (p : Pins) : Prop where
  size : 71 ≤ (m.arr64 PINS).size
  names_size : p.names.size = 51
  names_lt : ∀ i, i < 51 → (pinW m (1 + i)).toNat < 2 ^ 32
  names : ∀ i (h : i < 51), p.names[i]'(by omega) = decI (pinW m (1 + i))
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
  exact ⟨he ▸ h.size, h.names_size, fun i hi => hw _ ▸ h.names_lt i hi,
    fun i hi => hw _ ▸ h.names i hi, by simpa only [hw] using h.lv_lt,
    hw _ ▸ h.emptyLevels, hw _ ▸ h.zeroLevel, hw _ ▸ h.sortOne,
    fun i hi => hw _ ▸ h.reserved_lt i hi, by simpa only [hw] using h.reserved⟩

theorem PinsR.congr {m m' : Mem} {p : Pins} (he : m'.arr64 PINS = m.arr64 PINS)
    (h : PinsR m p) : PinsR m' p :=
  ⟨fun h0 => (h.full (by simpa only [pinW, he] using h0)).congr he⟩

theorem PinsR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {p : Pins}
    (hA : AvoidA 128 129 A) (hf : MemFrame A C m m') (h : PinsR m p) : PinsR m' p :=
  h.congr (hf.1 PINS (fun hm => by have := hA _ hm; revert this; decide) (by decide))

/-- All-zero pins (the flag `0`) are related to every table. -/
theorem PinsR.of_flag {m : Mem} {p : Pins} (h : pinW m 0 = 0) : PinsR m p :=
  ⟨fun h0 => absurd h h0⟩

/-! ## The environment: arrays 129‥136, 140‥143, 385‥387, `CTL` 128, 129, 133

The twin's `IFEnv` (`Env.lean:276`) is an argument of the checker, not part of `AState`, and
several views of one index are live at once (`restrictTo`: the same index, a smaller
`visibleBelow`). In L there is **one destructive index** and a view is a word `vis`:

* **The index, directly addressed by the name handle** (no hashing, no tombstones): a name
  handle is `tag · 2^28 + tier · 2^27 + i` with `tag` 0 (`anonymous`), 1 (`str`), 2 (`num`), so
  its row is words `2 i`, `2 i + 1` of array `EIXA`/`EIXS`/`EIXN` (132 + `tag`) for tier 0 and
  `EIXA1`/`EIXS1`/`EIXN1` (140 + `tag`) for tier 1 (`rowArr`): the counter plus one (`0`: no row)
  and the record pointer. `erase` writes `0`. The arrays are sized like the name tables (an index
  past the end aborts, a capacity). One array per tier (lane parmode, docs/design/parmode.md), as
  the stores have: the parallel mode freezes tier 0 and gives each worker its own tier 1.
* `ECON` (135): the record pointer of every constant by counter position, oldest first;
  `CTL[128]` is their number. The twin's `env.consts` (newest first) is its reverse.
* `EREC` (136): the record pool (`EnvRec.lean`'s layouts); `CTL[129]` its top.

`EnvR dn m vis fe` relates one view, **extensionally** (through the rows the twin's
`idx[n]?` reads, so the layout of `Std.HashMap` is free): the view's bound is `vis`, every row's
presence and counter is the twin's, every present row's record decodes to the twin's constant,
and the constants list decodes in order. `find?` follows (`EnvR.find?`); a raw row
(`idx[n]?`, `GenRec`'s `prev`) is the same clause without the bound. `dn` reads `PropWhen`'s
name handles back (`EnvRec.lean`).
-/

abbrev EIXA : ArrId := 132
abbrev EIXS : ArrId := 133
abbrev EIXN : ArrId := 134
abbrev ECON : ArrId := 135
abbrev EREC : ArrId := 136
abbrev EIXA1 : ArrId := 140
abbrev EIXS1 : ArrId := 141
abbrev EIXN1 : ArrId := 142

/-- The constructor tag of a name handle word. -/
def rowTag (w : Word) : Nat := w.toNat / 2 ^ 28
/-- The tier bit of a name handle word. -/
def rowTier (w : Word) : Nat := w.toNat / 2 ^ 27 % 2
/-- The row's array: `132 + tag` for tier 0, `140 + tag` for tier 1. -/
def rowArr (w : Word) : ArrId := 132 + rowTag w + 8 * rowTier w
/-- The first word of a name handle's row in its array. -/
def rowIx (w : Word) : Nat := 2 * (w.toNat % 2 ^ 27)

/-- The row's first word: the counter plus one, `0` for no row. -/
def rowC (m : Mem) (w : Word) : Word :=
  if rowTag w ≤ 2 then (m.arr64 (rowArr w))[rowIx w]?.getD 0 else 0
/-- The row's record pointer. -/
def rowP (m : Mem) (w : Word) : Word :=
  if rowTag w ≤ 2 then (m.arr64 (rowArr w))[rowIx w + 1]?.getD 0 else 0

/-- The row of a name handle, decoded: counter and record pointer. -/
def rowW (m : Mem) (w : Word) : Option (Nat × Word) :=
  if rowC m w = 0 then none else some ((rowC m w).toNat - 1, rowP m w)

/-- The number of constants, `CTL[128]`. -/
def envLen (m : Mem) : Nat := (rdW (m.arr64 CTL) 128).toNat

/-- The record pool's top, `CTL[129]`. -/
def erecTop (m : Mem) : Nat := (rdW (m.arr64 CTL) 129).toNat

/-- **The record pool in use**: `EREC` below its top. Every record the relations decode is
decoded here, so a writer above the top (an allocation, `erec_alloc`) keeps them all
(`decCI_mono`). -/
def erecP (m : Mem) : Array Word := (m.arr64 EREC).extract 0 (erecTop m)

/-- The constants, newest first, decoded. -/
def envConsts (dn : NIdx → Option ConLeche.Name) (m : Mem) : Option (List IConstantInfo) :=
  (List.range (envLen m)).reverse.mapM fun c => do
    decCI (erecP m) dn (← nat? (m.arr64 ECON) c)

theorem erecP_get {m : Mem} {i : Nat} {v : Word} (h : (erecP m)[i]? = some v) :
    (m.arr64 EREC)[i]? = some v := by
  simp only [erecP, Array.getElem?_extract] at h
  split at h
  · simpa using h
  · simp at h

theorem erecP_congr {m m' : Mem} (he : m'.arr64 EREC = m.arr64 EREC)
    (hc : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129) : erecP m' = erecP m := by
  simp only [erecP, erecTop, he, hc]

/-! ### The table component

The twin's projection tables (`IEnv.tables`, `IFEnv.tbls`: keyed on the structure's name, no
counter) have their own arrays, as con-ron keeps them (`env.tables`, a `Vec`, and the table map):

* **The table rows** `TIXA`/`TIXS`/`TIXN` (129‥131, one per name tag, as `EIX*`; tier 1 at
  `+ 256`, `tierA`): the row of name handle `w` is word `i` (the handle's index) of `tblArr w`,
  the table record's pointer plus one, `0` for no table (`IFEnv.rawTable?`).
* **The tables list** `ETAB` (143): the record pointer of every table by slot, oldest first (the
  twin's `env.tables` is its reverse), `CTL[133]` of them.

All of it is zero in zero memory (`mkIFEnv IEnv.empty`). -/

abbrev TIXA : ArrId := 129
abbrev TIXS : ArrId := 130
abbrev TIXN : ArrId := 131
abbrev ETAB : ArrId := 143

/-- The table row's array: `129 + tag`, tier 1 at `+ 256`. -/
def tblArr (w : Word) : ArrId := 129 + rowTag w + 256 * rowTier w

/-- The table row's index: the handle's index. -/
def tblIx (w : Word) : Nat := w.toNat % 2 ^ 27

/-- The table row of a name handle: the table record's pointer plus one, `0` for none. -/
def tblRow (m : Mem) (w : Word) : Word :=
  if rowTag w ≤ 2 then (m.arr64 (tblArr w))[tblIx w]?.getD 0 else 0

/-- The number of tables, `CTL[133]`. -/
def tblCnt (m : Mem) : Nat := (rdW (m.arr64 CTL) 133).toNat

/-- The tables, newest first, decoded. -/
def envTables (m : Mem) : Option (List IProjTable) :=
  (List.range (tblCnt m)).reverse.mapM fun j => do
    decTbl (erecP m) (← nat? (m.arr64 ETAB) j)

/-- **The environment, seen through the view `vis`.** -/
structure EnvR (dn : NIdx → Option ConLeche.Name) (m : Mem) (vis : Word) (fe : IFEnv) : Prop where
  vis : fe.visibleBelow = vis.toNat
  keys : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 →
    (fe.idx[n]?).map Prod.fst = (rowW m n.word.toUInt64).map Prod.fst
  vals : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → rowC m n.word.toUInt64 ≠ 0 →
    (fe.idx[n]?).map Prod.snd = decCI (erecP m) dn (rowP m n.word.toUInt64).toNat
  consts : envConsts dn m = some fe.env.consts
  /-- The table map (`IFEnv.tbls`): a table row is present exactly where the twin's is ... -/
  tkeys : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 →
    (fe.tbls[n]?).isSome = (tblRow m n.word.toUInt64 != 0)
  /-- ... and decodes to it. -/
  tvals : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → tblRow m n.word.toUInt64 ≠ 0 →
    fe.tbls[n]? = decTbl (erecP m) ((tblRow m n.word.toUInt64).toNat - 1)
  /-- The tables list (`IEnv.tables`). -/
  tables : envTables m = some fe.env.tables

theorem tblArr_cases (w : Word) (h : rowTag w ≤ 2) :
    tblArr w = 129 ∨ tblArr w = 130 ∨ tblArr w = 131 ∨ tblArr w = 385 ∨ tblArr w = 386 ∨
      tblArr w = 387 := by
  have : rowTier w < 2 := Nat.mod_lt _ (by decide)
  simp only [tblArr, ArrId]; omega

/-- The table side of the environment: what `tkeys`, `tvals`, `tables` read besides `erecP`. -/
def TblSame (m m' : Mem) : Prop :=
  (∀ w, rowTag w ≤ 2 → m'.arr64 (tblArr w) = m.arr64 (tblArr w)) ∧
    m'.arr64 ETAB = m.arr64 ETAB ∧ rdW (m'.arr64 CTL) 133 = rdW (m.arr64 CTL) 133

theorem TblSame.refl (m : Mem) : TblSame m m := ⟨fun _ _ => rfl, rfl, rfl⟩

/-- The table side from a frame avoiding the table arrays and `CTL[133]`. -/
theorem TblSame.of_frame {A : List ArrId} {C : List Word} {m m' : Mem}
    (hA : AvoidA 129 132 A) (hA1 : AvoidA 385 388 A) (hE : ETAB ∉ A) (hC : (133 : Word) ∉ C)
    (hf : MemFrame A C m m') : TblSame m m' := by
  refine ⟨fun w hw => hf.1 _ (fun hm => ?_)
    (by rcases tblArr_cases w hw with h | h | h | h | h | h <;> rw [h] <;> decide),
    hf.1 _ hE (by decide), hf.2.1 133 hC⟩
  have h1 := hA _ hm; have h2 := hA1 _ hm; have := tblArr_cases w hw
  simp only [ArrId] at *; omega

theorem EnvR.congr {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (he : ∀ b : Nat, 132 ≤ b → b < 143 → (b < 137 ∨ 140 ≤ b) → m'.arr64 b = m.arr64 b)
    (hc : rdW (m'.arr64 CTL) 128 = rdW (m.arr64 CTL) 128)
    (hc9 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129) (ht : TblSame m m')
    (h : EnvR dn m vis fe) : EnvR dn m' vis fe := by
  have hC : ∀ w, rowC m' w = rowC m w := fun w => by
    unfold rowC; split
    · rw [he _ (by simp only [rowArr]; omega) (by simp only [rowArr, rowTier]; omega)
        (by simp only [rowArr, rowTier]; omega)]
    · rfl
  have hP : ∀ w, rowP m' w = rowP m w := fun w => by
    unfold rowP; split
    · rw [he _ (by simp only [rowArr]; omega) (by simp only [rowArr, rowTier]; omega)
        (by simp only [rowArr, rowTier]; omega)]
    · rfl
  have hW : ∀ w, rowW m' w = rowW m w := fun w => by simp only [rowW, hC, hP]
  have hR : erecP m' = erecP m := by
    simp only [erecP, erecTop, he EREC (by decide) (by decide) (by decide), hc9]
  have hN : m'.arr64 ECON = m.arr64 ECON := he _ (by decide) (by decide) (by decide)
  have hT : ∀ w, tblRow m' w = tblRow m w := fun w => by
    unfold tblRow; split
    · rename_i hw; rw [ht.1 w hw]
    · rfl
  refine ⟨h.vis, fun n hn => (hW _).symm ▸ h.keys n hn, fun n hn h0 => ?_, ?_,
    fun n hn => (hT _).symm ▸ h.tkeys n hn, fun n hn h0 => ?_, ?_⟩
  · rw [hP, hR]; exact h.vals n hn (by rwa [← hC])
  · rw [← h.consts]; simp only [envConsts, envLen, hc, hR, hN]
  · rw [hT, hR]; exact h.tvals n hn (by rwa [← hT])
  · rw [← h.tables]; simp only [envTables, tblCnt, ht.2.1, ht.2.2, hR]

/-- Every record in use is in `EREC` (a decoding in `erecP` is one in the whole array). -/
theorem erecP_ext (m : Mem) : ArrExt (erecP m) (m.arr64 EREC) := fun _ _ h => erecP_get h

/-- **The record pool grew**: its top did not go down and nothing below the old top changed. -/
def ErecGrow (m m' : Mem) : Prop :=
  erecTop m ≤ erecTop m' ∧ (∀ i, i < erecTop m → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC).size = (m.arr64 EREC).size

theorem ErecGrow.ext {m m' : Mem} (h : ErecGrow m m') : ArrExt (erecP m) (erecP m') := by
  intro i v hv
  simp only [erecP, Array.getElem?_extract] at hv ⊢
  split at hv
  · rename_i hi
    have hi' : i < erecTop m := by simp at hi; omega
    have := h.1; have := h.2.2
    rw [ite_eq_left (by simp at hi ⊢; omega)]
    simp only [Nat.zero_add] at hv ⊢
    rw [h.2.1 i hi']
    exact hv
  · simp at hv

theorem ErecGrow.refl (m : Mem) : ErecGrow m m := ⟨Nat.le_refl _, fun _ _ => rfl, rfl⟩

theorem ErecGrow.trans {m₁ m₂ m₃ : Mem} (h₁ : ErecGrow m₁ m₂) (h₂ : ErecGrow m₂ m₃) :
    ErecGrow m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hi => (h₂.2.1 i (by have := h₁.1; omega)).trans (h₁.2.1 i hi),
    h₂.2.2.trans h₁.2.2⟩

/-- **`EnvR` across a pool growth** (rows, constants and `CTL[128]` unchanged). -/
theorem EnvR.grow {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (he : ∀ b : Nat, 132 ≤ b → b < 143 → (b < 136 ∨ 140 ≤ b) → m'.arr64 b = m.arr64 b)
    (hc : rdW (m'.arr64 CTL) 128 = rdW (m.arr64 CTL) 128) (hg : ErecGrow m m') (ht : TblSame m m')
    (h : EnvR dn m vis fe) : EnvR dn m' vis fe := by
  have hC : ∀ w, rowC m' w = rowC m w := fun w => by
    unfold rowC; split
    · rw [he _ (by simp only [rowArr]; omega) (by simp only [rowArr, rowTier]; omega)
        (by simp only [rowArr, rowTier]; omega)]
    · rfl
  have hP : ∀ w, rowP m' w = rowP m w := fun w => by
    unfold rowP; split
    · rw [he _ (by simp only [rowArr]; omega) (by simp only [rowArr, rowTier]; omega)
        (by simp only [rowArr, rowTier]; omega)]
    · rfl
  have hW : ∀ w, rowW m' w = rowW m w := fun w => by simp only [rowW, hC, hP]
  have hN : m'.arr64 ECON = m.arr64 ECON := he _ (by decide) (by decide) (by decide)
  have hT : ∀ w, tblRow m' w = tblRow m w := fun w => by
    unfold tblRow; split
    · rename_i hw; rw [ht.1 w hw]
    · rfl
  have hx := hg.ext
  refine ⟨h.vis, fun n hn => (hW _).symm ▸ h.keys n hn, fun n hn h0 => ?_, ?_,
    fun n hn => (hT _).symm ▸ h.tkeys n hn, fun n hn h0 => ?_, ?_⟩
  · rw [hC] at h0
    have hv := h.vals n hn h0
    have hk := h.keys n hn
    simp only [rowW, h0, ite_false, Option.map_some] at hk
    cases e : fe.idx[n]? with
    | none => simp [e] at hk
    | some r =>
      rw [e] at hv; simp only [Option.map_some] at hv
      rw [hP]; simp only [Option.map_some]
      exact (hx.decCI hv.symm).symm
  · have hcs := h.consts
    simp only [envConsts, envLen, hc, hN] at hcs ⊢
    exact ArrExt.mapM (fun c x hcx => by
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hcx ⊢
      obtain ⟨q, hq, hd⟩ := hcx
      exact ⟨q, hq, hx.decCI hd⟩) _ _ hcs
  · rw [hT] at h0 ⊢
    have hv := h.tvals n hn h0
    have hk := h.tkeys n hn
    cases e : fe.tbls[n]? with
    | none => simp [e, h0] at hk
    | some t => rw [e] at hv; exact (hx.decTbl hv.symm).symm
  · have hts := h.tables
    simp only [envTables, tblCnt, ht.2.1, ht.2.2] at hts ⊢
    exact ArrExt.mapM (fun c x hcx => by
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hcx ⊢
      obtain ⟨q, hq, hd⟩ := hcx
      exact ⟨q, hq, hx.decTbl hd⟩) _ _ hts

/-- The frame over exactly what `EnvR` reads: arrays 129‥142 (but `PEND`‥`RMEMO`), `ETAB`, the
table rows' tier 1 (385‥387) and `CTL[128]`, `CTL[129]`, `CTL[133]`. -/
theorem EnvR.frameN {dn : NIdx → Option ConLeche.Name} {A : List ArrId} {C : List Word}
    {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hA : AvoidA 129 137 A) (hA1 : AvoidA 140 144 A) (hA2 : AvoidA 385 388 A)
    (hC : AvoidC 128 130 C) (hC3 : AvoidC 133 134 C)
    (hf : MemFrame A C m m') (h : EnvR dn m vis fe) :
    EnvR dn m' vis fe :=
  h.congr (fun b h1 h2 h3 => hf.1 b (fun hm => by
      have := hA _ hm; have := hA1 _ hm; simp only [ArrId] at *; omega)
    (by simp only [CTL, ArrId]; omega))
    (hf.2.1 128 (fun hm => by have := hC _ hm; simp at this))
    (hf.2.1 129 (fun hm => by have := hC _ hm; simp at this))
    (TblSame.of_frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) hA2
      (fun hm => by have := hA1 _ hm; simp [ETAB] at this)
      (fun hm => by have := hC3 _ hm; simp at this) hf)

/-- A writer of the store tier (arrays below `64` and `256‥319`) avoids the table rows' tier 1. -/
theorem AvoidA.of_lowT {A : List ArrId} (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) :
    AvoidA 385 388 A := fun b hb => .inl (by have := hA b hb; simp only [ArrId] at *; omega)

theorem EnvR.frame {dn : NIdx → Option ConLeche.Name} {A : List ArrId} {C : List Word}
    {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hA : AvoidA 129 144 A) (hC : AvoidC 128 136 C) (hf : MemFrame A C m m') (h : EnvR dn m vis fe)
    (hA2 : AvoidA 385 388 A := by decide) :
    EnvR dn m' vis fe :=
  h.frameN (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
    (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) hA2
    (fun x hx => by have := hC x hx; omega) (fun x hx => by have := hC x hx; omega) hf

/-! ## The whole relation -/

theorem MemFrame.top_eq {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hC : (0 : Word) ∉ C) : m'.top = m.top := by
  have := hf.2.1 0 hC
  simp only [rdW] at this
  simpa [Mem.top] using this

/-- **The mode across a frame** that keeps `CTL[0]` and `CTL[1]`. -/
theorem ModeOK.frame {m m' : Mem} {A : List ArrId} {C : List Word} (h : ModeOK m)
    (hf : MemFrame A C m m') (h0 : (0 : Word) ∉ C) (h1 : (1 : Word) ∉ C) : ModeOK m' := by
  have ht : m'.top = m.top := hf.top_eq h0
  have hfl : m'.flag = m.flag := hf.2.1 1 h1
  unfold ModeOK; rw [ht, hfl]; exact h

/-- **The relation, by tier.** -/
structure CheckR (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) : Prop where
  arena : ArenaD m a
  core : CoreR m a.caches
  pins : PinsR m a.pins
  env : EnvR dn m vis fe
  /-- The pool's mode (lane tierpool; `ModeOK`). -/
  mode : ModeOK m

/-- **The upper tiers across a walk**: a run whose L write set is below 64 (every walk,
`WriteSets.lean`) and whose twin side keeps `cp` (every walk, `Keeps.lean`) keeps `CoreR`,
`PinsR` and `EnvR`; the walk's own theorem gives `ArenaD`. -/
theorem CheckR.of_walkM {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {A : List ArrId} {C : List Word} (hR : CheckR dn m a vis fe) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a)
    (hmode : ModeOK m') : CheckR dn m' a' vis fe := by
  have hc : a'.caches = a.caches := congrArg Prod.fst hk
  have hp : a'.pins = a.pins := congrArg Prod.snd hk
  refine ⟨hD, ?_, ?_, hR.env.frame (.of_low hA (by decide) (by decide)) (.of_lt hC (by decide)) hf
    (.of_lowT hA), hmode⟩
  · rw [hc]; exact hR.core.frame (.of_low hA (by decide) (by decide)) (.of_lt hC (by decide)) hf
  · rw [hp]; exact hR.pins.frame (.of_low hA (by decide) (by decide)) hf

/-- `CheckR.of_walkM` for a walk that keeps `CTL[0]` and `CTL[1]` (an interning): the mode by the
frame. -/
theorem CheckR.of_walk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {A : List ArrId} {C : List Word} (hR : CheckR dn m a vis fe) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a)
    (h01 : (0 : Word) ∉ C ∧ (1 : Word) ∉ C := by decide) : CheckR dn m' a' vis fe :=
  hR.of_walkM hD hf hA hC hk (hR.mode.frame hf h01.1 h01.2)

/-- **Every tier but the arena's above a writer**: arrays from 137 (but the env index's tier 1,
140‥142) and `CTL` words from 130 up
(the argument relations: pending checks, `PMemo`, the level heap) keep `CheckR`. -/
theorem CheckR.frame_hi {dn : NIdx → Option ConLeche.Name} {A : List ArrId} {C : List Word}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} (hA : ∀ b ∈ A, 137 ≤ b ∧ b < 256 ∧ (b < 140 ∨ 144 ≤ b))
    (hC : ∀ x ∈ C, 130 ≤ x.toNat ∧ x.toNat ≠ 133) (hf : MemFrame A C m m') (h : CheckR dn m a vis fe) :
    CheckR dn m' a vis fe := by
  have hA' : ∀ lo hi, hi ≤ 137 → AvoidA lo hi A := fun lo hi hh b hb => .inr (by
    have := (hA b hb).1; simp only [ArrId] at this ⊢; omega)
  have hE : AvoidA 140 144 A := fun b hb => by
    have := hA b hb; simp only [ArrId] at this ⊢; omega
  have hE2 : AvoidA 385 388 A := fun b hb => by
    have := hA b hb; simp only [ArrId] at this ⊢; omega
  have hC' : ∀ lo hi, hi ≤ 130 → AvoidC lo hi C := fun lo hi hh x hx => .inr (by
    have := (hC x hx).1; omega)
  have hC3 : AvoidC 133 134 C := fun x hx => by have := hC x hx; omega
  refine ⟨⟨?_, ?_⟩, h.core.frame (hA' _ _ (by decide)) (hC' _ _ (by decide)) hf,
    h.pins.frame (hA' _ _ (by decide)) hf,
    h.env.frameN (hA' _ _ (by decide)) hE hE2 (hC' _ _ (by decide)) hC3 hf,
    h.mode.frame hf (fun h => by have := (hC _ h).1; simp at this)
      (fun h => by have := (hC _ h).1; simp at this)⟩
  · exact ArenaR.frame_ext A C (fun b hb => by
      have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => by have := (hC x hx).1; omega) m m' hf a h.arena.1
  · exact DerR.frameM A C m m' hf (fun b hb => by
      have := hA b hb; simp only [ArrId] at this ⊢; omega) a h.arena.2

end L.Arena
