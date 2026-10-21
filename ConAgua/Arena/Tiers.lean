import ConAgua.Arena.DerRel
import ConAgua.Arena.Keeps
import ConRon.Arena.Env
import ConAgua.Arena.EnvRec
import ConAgua.Arena.MemoBank
import ConAgua.Arena.CoreCaches

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
| `CoreR` | `a.caches` | 96‥106; 107‥127 reserved | 96‥119; 120‥127 reserved | 11 of 14 tables (lane `whnf`) |
| `PinsR` | `a.pins` | 128 (`PINS`); 129‥131 reserved | – | filled (lane `pinsenv`) |
| `EnvR` | a view `vis` of `fe : IFEnv` (an argument) | 132‥136 | 128 (129: the record top) | filled (lane `pinsenv`) |
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

set_option linter.unusedVariables false

/-! ## The per-declaration caches: arrays 96‥127, `CTL` 96‥127

Eleven of con-ron's fourteen `Caches` tables are memos in L (`CoreCaches.lean`: arrays 96‥106,
stamps and counts `CTL` 96‥113 and 116‥119, the mode memos' bank words `CTL` 114, 115). The six **mode memos**
are generation-tagged (`MemoBank.lean`): L keeps one map `M` per table over `(key, generation)`,
the twin's table is the bank of the current generation `g`, and no entry is above the last
allocated generation `G`. The saved tables of an enclosing eager comparison are other banks of
the same maps (stated by the knot over `CoreRM`'s explicit maps). The three constant caches and the two
level-verdict caches are plain `MemoRG`s. `readLC`, `readNC`, `readLsC` have no L table (L makes
no readbacks; see `CoreCaches.lean`). -/

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

/-- A cache value word: a handle. -/
def decEV (w : Word) : EIdx := decE w

/-- A `defeqC` value word: the verdict. -/
def decB (w : Word) : Bool := w != 0

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

/-- **One mode memo**: its map `M` over `(key, generation)` is in memory, the twin's table `t` is
the bank of the current generation `g`, and nothing lies above the last generation `G`. -/
structure ModeR {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey (κ × Word))
    (dv : Word → ν) (m : Mem) (M : Std.HashMap (κ × Word) ν) (G g : Word)
    (t : Std.HashMap κ ν) : Prop where
  memo : MemoRG S K dv m M
  bank : Bank M g t
  fresh : Fresh M G

theorem ModeR.frame {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {dv : Word → ν} {m m' : Mem} {M : Std.HashMap (κ × Word) ν} {G g : Word}
    {t : Std.HashMap κ ν} {A : List ArrId} {C : List Word} (hS : S.WF) (hA : S.arr ∉ A)
    (hC : S.cs ∉ C) (hf : MemFrame A C m m') (h : ModeR S K dv m M G g t) : ModeR S K dv m' M G g t :=
  ⟨memoRG_frame S hS K dv A C hA hC m m' hf M h.memo, h.bank, h.fresh⟩

/-- **The core tier at explicit maps and bank words.** -/
structure CoreRM (m : Mem) (c : Caches) (M : ModeMaps) (G g : Word) : Prop where
  wc : ModeR wcSch eKeyG decEV m M.wc G g c.whnfCoreC
  wk : ModeR wkSch eKeyG decEV m M.wk G g c.whnfCoreCheapC
  wh : ModeR whSch eKeyG decEV m M.wh G g c.whnfC
  inf : ModeR inSch eKeyG decEV m M.inf G g c.inferC
  io : ModeR ioSch eKeyG decEV m M.io G g c.inferIOC
  de : ModeR deSch dKeyG decB m M.de G g c.defeqC
  bank : BankW BANKC m G g
  ct : MemoRG ctSch pairKey decEV m c.constTyC
  cv : MemoRG cvSch pairKey decEV m c.constValC
  rr : MemoRG rrSch rrKey decEV m c.ruleRhsC
  lq : MemoRG lqSch pairKey decB m c.lvlEqC
  lsq : MemoRG lsqSch pairKey decB m c.lvlsEqC

/-- **The core tier** (tier D: `flushCaches` per declaration), over `a.caches`. -/
def CoreR (m : Mem) (c : Caches) : Prop := ∃ M G g, CoreRM m c M G g

theorem coreSch_wf (a : ArrId) (c : Word) (h1 : a ≠ CTL) (h2 : c.toNat + 2 < 2 ^ 32) :
    MemoSch.WF ⟨a, c⟩ := ⟨h1, h2⟩

theorem BankW.frame {c : Word} {m m' : Mem} {G g : Word} {A : List ArrId} {C : List Word}
    (h1 : c ∉ C) (h2 : c + 1 ∉ C) (hf : MemFrame A C m m') (h : BankW c m G g) : BankW c m' G g := by
  obtain ⟨hB1, hB2, hgG, hGl, hsz⟩ := h
  exact ⟨hf.2.1 _ h1 ▸ hB1, hf.2.1 _ h2 ▸ hB2, hgG, hGl, hf.2.2.1 CTL ▸ hsz⟩

theorem CoreRM.frame {A : List ArrId} {C : List Word} {m m' : Mem} {c : Caches} {M : ModeMaps}
    {G g : Word} (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m')
    (h : CoreRM m c M G g) : CoreRM m' c M G g := by
  have nA : ∀ b : ArrId, 96 ≤ b → b < 128 → b ∉ A := fun b h1 h2 hb => by
    have := hA b hb; simp only [ArrId] at this h1 h2; omega
  have nC : ∀ x : Word, 96 ≤ x.toNat → x.toNat < 128 → x ∉ C := fun x h1 h2 hx => by
    have := hC x hx; omega
  exact ⟨h.wc.frame (coreSch_wf _ _ (by decide) (by decide)) (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.wk.frame (coreSch_wf _ _ (by decide) (by decide)) (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.wh.frame (coreSch_wf _ _ (by decide) (by decide)) (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.inf.frame (coreSch_wf _ _ (by decide) (by decide)) (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.io.frame (coreSch_wf _ _ (by decide) (by decide)) (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.de.frame (coreSch_wf _ _ (by decide) (by decide)) (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) hf,
    h.bank.frame (nC _ (by decide) (by decide)) (nC _ (by decide) (by decide)) hf,
    memoRG_frame _ (coreSch_wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.ct,
    memoRG_frame _ (coreSch_wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.cv,
    memoRG_frame _ (coreSch_wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.rr,
    memoRG_frame _ (coreSch_wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.lq,
    memoRG_frame _ (coreSch_wf _ _ (by decide) (by decide)) _ _ A C (nA _ (by decide) (by decide))
      (nC _ (by decide) (by decide)) m m' hf _ h.lsq⟩

theorem CoreR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {c : Caches}
    (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m') (h : CoreR m c) :
    CoreR m' c := by
  obtain ⟨M, G, g, h⟩ := h
  exact ⟨M, G, g, h.frame hA hC hf⟩

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
theorem memoRG_clearsL_other {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (hS : S.WF)
    (K : MemoKey κ) (dv : Word → ν) (l : List MemoSch) (hl : ∀ S' ∈ l, S.cs ≠ S'.cs ∧ S.cs ≠ S'.cs + 1)
    (m : Mem) (mp : Std.HashMap κ ν) (h : MemoRG S K dv m mp) : MemoRG S K dv (clearsL l m) mp :=
  memoRG_frame S hS K dv [] _ (by simp) (fun hm => by
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨S', h1, h2⟩ := hm
    rcases h2 with e | e
    · exact (hl S' h1).1 e
    · exact (hl S' h1).2 e) m _ (clearsL_frame l m) mp h

/-- **A memo cleared in a run is empty after it**, if no other clear of the run touches its
stamp. -/
theorem memoRG_clearsL {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    (S : MemoSch) (hS : S.WF) (K : MemoKey κ) (dv : Word → ν) :
    ∀ (pre post : List MemoSch) (m : Mem) (mp : Std.HashMap κ ν),
    (∀ S' ∈ pre ++ post, S.cs ≠ S'.cs ∧ S.cs ≠ S'.cs + 1) → ClearsOK (pre ++ S :: post) m →
    MemoRG S K dv m mp → MemoRG S K dv (clearsL (pre ++ S :: post) m) ∅
  | [], post, m, mp, hl, hok, h => by
    simp only [List.nil_append, clearsL] at hok ⊢
    exact memoRG_clearsL_other S hS K dv post (fun S' h' => hl S' (by simpa using h')) _ _
      (memoRG_clear S hS K dv m mp h hok.1)
  | S₀ :: pre, post, m, mp, hl, hok, h => by
    simp only [List.cons_append, clearsL] at hok ⊢
    have h0 := hl S₀ (by simp)
    refine memoRG_clearsL S hS K dv pre post _ mp (fun S' h' => hl S' (by simp [h'])) hok.2 ?_
    exact memoRG_frame S hS K dv [] _ (by simp) (by simp [h0.1, h0.2]) m _ (mclearG_frame S₀ m) mp h

/-- The eleven core memos, in `flush_caches()`' order. -/
def coreSchs : List MemoSch :=
  [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch, rrSch, lqSch, lsqSch]

theorem flushClears_eq (m : Mem) : flushClears m = clearsL coreSchs m := rfl

theorem flushOK_eq (m : Mem) : FlushOK m ↔ ClearsOK coreSchs m := by
  simp only [FlushOK, ClearsOK, coreSchs, and_true]

theorem bank_empty {κ ν : Type} [BEq κ] [Hashable κ] (g : Word) :
    Bank (∅ : Std.HashMap (κ × Word) ν) g ∅ := fun _ => by simp

/-- **The flush**: after `flush_caches()` the core tier relates the empty caches. -/
theorem CoreR.flush {m : Mem} {c : Caches} (h : CoreR m c) (hok : FlushOK m) :
    CoreR (flushMem m) Caches.empty := by
  obtain ⟨M, G, g, h⟩ := h
  rw [flushOK_eq] at hok
  have fr : ∀ {m₁ : Mem}, MemFrame [] [114, 115] m₁ (bankReset m₁) := fun {m₁} =>
    ((MemFrame.setCtl _ 114 0).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 115 0).mono (by simp) (by simp))
  have hc : ∀ {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (S : MemoSch)
      (K : MemoKey κ) (dv : Word → ν) (mp : Std.HashMap κ ν) (pre post : List MemoSch),
      S.WF → pre ++ S :: post = coreSchs → (∀ S' ∈ pre ++ post, S.cs ≠ S'.cs ∧ S.cs ≠ S'.cs + 1) →
      S.cs ≠ 114 → S.cs ≠ 115 → MemoRG S K dv m mp → MemoRG S K dv (flushMem m) ∅ :=
    fun S K dv mp pre post hS he hl h1 h2 hR => by
      have := memoRG_clearsL S hS K dv pre post m mp hl (he ▸ hok) hR
      rw [he] at this
      exact memoRG_frame S hS K dv [] _ (by simp) (by simp [h1, h2]) _ _ fr _ this
  obtain ⟨-, -, -, -, hsz⟩ := h.bank
  have hsz' : (114 : Word).toNat + 1 < ((flushMem m).arr64 CTL).size := by
    have e1 : ((bankReset (clearsL coreSchs m)).arr64 CTL).size = (m.arr64 CTL).size := by
      rw [fr.2.2.1, (clearsL_frame coreSchs m).2.2.1]
    rw [show flushMem m = bankReset (clearsL coreSchs m) from rfl, e1]; exact hsz
  refine ⟨ModeMaps.empty, 0, 0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ⟨hc wcSch _ _ _ [] _ (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide)
      (by decide) h.wc.memo, bank_empty 0, fresh_empty 0⟩
  · exact ⟨hc wkSch _ _ _ [wcSch] _ (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide)
      (by decide) (by decide) h.wk.memo, bank_empty 0, fresh_empty 0⟩
  · exact ⟨hc whSch _ _ _ [wcSch, wkSch] _ (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide)
      (by decide) (by decide) h.wh.memo, bank_empty 0, fresh_empty 0⟩
  · exact ⟨hc inSch _ _ _ [wcSch, wkSch, whSch] _ (coreSch_wf _ _ (by decide) (by decide)) rfl
      (by decide) (by decide) (by decide) h.inf.memo, bank_empty 0, fresh_empty 0⟩
  · exact ⟨hc ioSch _ _ _ [wcSch, wkSch, whSch, inSch] _ (coreSch_wf _ _ (by decide) (by decide))
      rfl (by decide) (by decide) (by decide) h.io.memo, bank_empty 0, fresh_empty 0⟩
  · exact ⟨hc deSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch] _
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide) (by decide) h.de.memo,
      bank_empty 0, fresh_empty 0⟩
  · have e0 : ((flushClears m).arr64 CTL).size = (m.arr64 CTL).size :=
      (clearsL_frame coreSchs m).2.2.1 CTL
    simp only [BANKC] at hsz hsz' ⊢
    have h114 : (114 : Word).toNat = 114 := rfl
    rw [h114] at hsz hsz'
    refine ⟨?_, ?_, by decide, by decide, hsz'⟩
    · simp only [flushMem, bankReset, rdW_set64, size_set64, e0]; simp; omega
    · simp only [flushMem, bankReset, rdW_set64, size_set64, e0]; simp; omega
  · exact hc ctSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch] _
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide) (by decide) h.ct
  · exact hc cvSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch] _
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide) (by decide) h.cv
  · exact hc rrSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch] _
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide) (by decide) h.rr
  · exact hc lqSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch, rrSch] _
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide) (by decide) h.lq
  · exact hc lsqSch _ _ _ [wcSch, wkSch, whSch, inSch, ioSch, deSch, ctSch, cvSch, rrSch, lqSch] _
      (coreSch_wf _ _ (by decide) (by decide)) rfl (by decide) (by decide) (by decide) h.lsq

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
    (hA : AvoidA 128 132 A) (hf : MemFrame A C m m') (h : PinsR m p) : PinsR m' p :=
  h.congr (hf.1 PINS (fun hm => by have := hA _ hm; revert this; decide) (by decide))

/-- All-zero pins (the flag `0`) are related to every table. -/
theorem PinsR.of_flag {m : Mem} {p : Pins} (h : pinW m 0 = 0) : PinsR m p :=
  ⟨fun h0 => absurd h h0⟩

/-! ## The environment: arrays 132‥136, `CTL` 128

The twin's `IFEnv` (`Env.lean:276`) is an argument of the checker, not part of `AState`, and
several views of one index are live at once (`restrictTo`: the same index, a smaller
`visibleBelow`). In L there is **one destructive index** and a view is a word `vis`:

* **The index, directly addressed by the name handle** (no hashing, no tombstones): a name
  handle is `tag · 2^28 + tier · 2^27 + i` with `tag` 0 (`anonymous`), 1 (`str`), 2 (`num`), so
  its row is words `4 i + 2 tier`, `+ 1` of array `EIXA`/`EIXS`/`EIXN` (132 + `tag`): the counter
  plus one (`0`: no row) and the record pointer. `erase` writes `0`. The arrays are sized like
  the name tables (an index past the end aborts, a capacity).
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

/-- The constructor tag of a name handle word. -/
def rowTag (w : Word) : Nat := w.toNat / 2 ^ 28
/-- The first word of a name handle's row in its tag's array. -/
def rowIx (w : Word) : Nat := 4 * (w.toNat % 2 ^ 27) + 2 * (w.toNat / 2 ^ 27 % 2)

/-- The row's first word: the counter plus one, `0` for no row. -/
def rowC (m : Mem) (w : Word) : Word :=
  if rowTag w ≤ 2 then (m.arr64 (132 + rowTag w))[rowIx w]?.getD 0 else 0
/-- The row's record pointer. -/
def rowP (m : Mem) (w : Word) : Word :=
  if rowTag w ≤ 2 then (m.arr64 (132 + rowTag w))[rowIx w + 1]?.getD 0 else 0

/-- The row of a name handle, decoded: counter and record pointer. -/
def rowW (m : Mem) (w : Word) : Option (Nat × Word) :=
  if rowC m w = 0 then none else some ((rowC m w).toNat - 1, rowP m w)

/-- The number of constants, `CTL[128]`. -/
def envLen (m : Mem) : Nat := (rdW (m.arr64 CTL) 128).toNat

/-- The constants, newest first, decoded. -/
def envConsts (dn : NIdx → Option ConLeche.Name) (m : Mem) : Option (List IConstantInfo) :=
  (List.range (envLen m)).reverse.mapM fun c => do
    decCI (m.arr64 EREC) dn (← nat? (m.arr64 ECON) c)

/-- **The environment, seen through the view `vis`.** -/
structure EnvR (dn : NIdx → Option ConLeche.Name) (m : Mem) (vis : Word) (fe : IFEnv) : Prop where
  vis : fe.visibleBelow = vis.toNat
  keys : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 →
    (fe.idx[n]?).map Prod.fst = (rowW m n.word.toUInt64).map Prod.fst
  vals : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → rowC m n.word.toUInt64 ≠ 0 →
    (fe.idx[n]?).map Prod.snd = decCI (m.arr64 EREC) dn (rowP m n.word.toUInt64).toNat
  consts : envConsts dn m = some fe.env.consts

theorem EnvR.congr {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (he : ∀ b : Nat, 132 ≤ b → b < 137 → m'.arr64 b = m.arr64 b)
    (hc : rdW (m'.arr64 CTL) 128 = rdW (m.arr64 CTL) 128) (h : EnvR dn m vis fe) :
    EnvR dn m' vis fe := by
  have hC : ∀ w, rowC m' w = rowC m w := fun w => by
    unfold rowC; split
    · rw [he _ (by omega) (by omega)]
    · rfl
  have hP : ∀ w, rowP m' w = rowP m w := fun w => by
    unfold rowP; split
    · rw [he _ (by omega) (by omega)]
    · rfl
  have hW : ∀ w, rowW m' w = rowW m w := fun w => by simp only [rowW, hC, hP]
  have hR : m'.arr64 EREC = m.arr64 EREC := he _ (by decide) (by decide)
  have hN : m'.arr64 ECON = m.arr64 ECON := he _ (by decide) (by decide)
  refine ⟨h.vis, fun n hn => (hW _).symm ▸ h.keys n hn, fun n hn h0 => ?_, ?_⟩
  · rw [hP, hR]; exact h.vals n hn (by rwa [← hC])
  · rw [← h.consts]; simp only [envConsts, envLen, hc, hR, hN]

theorem EnvR.frame {dn : NIdx → Option ConLeche.Name} {A : List ArrId} {C : List Word}
    {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hA : AvoidA 132 137 A) (hC : AvoidC 128 129 C) (hf : MemFrame A C m m') (h : EnvR dn m vis fe) :
    EnvR dn m' vis fe :=
  h.congr (fun b h1 h2 => hf.1 b (fun hm => by have := hA _ hm; simp only [ArrId] at this; omega)
    (by simp only [CTL, ArrId]; omega))
    (hf.2.1 128 (fun hm => by have := hC _ hm; simp at this))



/-! ## The whole relation -/

/-- **The relation, by tier.** -/
structure CheckR (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) : Prop where
  arena : ArenaD m a
  core : CoreR m a.caches
  pins : PinsR m a.pins
  env : EnvR dn m vis fe

/-- **The upper tiers across a walk**: a run whose L write set is below 64 (every walk,
`WriteSets.lean`) and whose twin side keeps `cp` (every walk, `Keeps.lean`) keeps `CoreR`,
`PinsR` and `EnvR`; the walk's own theorem gives `ArenaD`. -/
theorem CheckR.of_walk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {A : List ArrId} {C : List Word} (hR : CheckR dn m a vis fe) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a) :
    CheckR dn m' a' vis fe := by
  have hc : a'.caches = a.caches := congrArg Prod.fst hk
  have hp : a'.pins = a.pins := congrArg Prod.snd hk
  refine ⟨hD, ?_, ?_, hR.env.frame (.of_lt hA (by decide)) (.of_lt hC (by decide)) hf⟩
  · rw [hc]; exact hR.core.frame (.of_lt hA (by decide)) (.of_lt hC (by decide)) hf
  · rw [hp]; exact hR.pins.frame (.of_lt hA (by decide)) hf

/-- **Every tier but the arena's above a writer**: arrays from 137 and `CTL` words from 130 up
(the argument relations: pending checks, `PMemo`, the level heap) keep `CheckR`. -/
theorem CheckR.frame_hi {dn : NIdx → Option ConLeche.Name} {A : List ArrId} {C : List Word}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} (hA : ∀ b ∈ A, 137 ≤ b)
    (hC : ∀ x ∈ C, 130 ≤ x.toNat) (hf : MemFrame A C m m') (h : CheckR dn m a vis fe) :
    CheckR dn m' a vis fe := by
  have hA' : ∀ lo hi, hi ≤ 137 → AvoidA lo hi A := fun lo hi hh b hb => .inr (by
    have := hA b hb; simp only [ArrId] at this ⊢; omega)
  have hC' : ∀ lo hi, hi ≤ 130 → AvoidC lo hi C := fun lo hi hh x hx => .inr (by
    have := hC x hx; omega)
  refine ⟨⟨?_, ?_⟩, h.core.frame (hA' _ _ (by decide)) (hC' _ _ (by decide)) hf,
    h.pins.frame (hA' _ _ (by decide)) hf,
    h.env.frame (hA' _ _ (by decide)) (hC' _ _ (by decide)) hf⟩
  · exact ArenaR.frame_ext A C (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => by have := hC x hx; omega) m m' hf a h.arena.1
  · exact DerR.frame m m' a h.arena.2 (fun B hB => hf.1 B (fun hm => by
      have := hA B hm; rcases hB with rfl | rfl | rfl | rfl | rfl <;> revert this <;> decide)
      (by rcases hB with rfl | rfl | rfl | rfl | rfl <;> decide))

end L.Arena
