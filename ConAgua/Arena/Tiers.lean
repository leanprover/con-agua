import ConAgua.Arena.DerRel
import ConAgua.Arena.Keeps
import ConRon.Arena.Env
import ConAgua.Arena.EnvRec

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
| `CoreR` | `a.caches` | 96‥127 | 96‥127 | stub |
| `PinsR` | `a.pins` | 128 (`PINS`); 129‥131 reserved | – | filled (lane `pinsenv`) |
| `EnvR` | a view `vis` of `fe : IFEnv` (an argument) | 132‥136 | 128 (129: the record top) | filled (lane `pinsenv`) |
| `PendR` (`Checker.lean`) | `pend` (an argument) | 137 | 130 | lane `pinsenv` |
| argument relations (`PMemo`, `pend`, saved `ModeMemos`, walk-local memos) | arguments | 144‥191 | 136‥191 | not yet |

`ArenaD = ArenaR ∧ DerR` stays the walks' tier. `CheckR` is the whole relation. A walk changes
only arrays below 64 (`WriteSets.lean`) and only `store`/`memos` (`Keeps cp`, `Keeps.lean`), so
`CheckR.of_walk` carries the upper tiers across it with no lemma about the walk. `CoreR` is still a
stub with no fields (it claims nothing); its frame lemma is already the one a real relation over
the reserved range will have.
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

/-! ## The per-declaration caches: arrays 96‥127, `CTL` 96‥127 -/

/-- **The core tier** (tier D: `flushCaches` per declaration): the 14 caches of `Caches` as
`MemoRG`s (and the eager-depth banks), over `a.caches`. Stub. -/
structure CoreR (m : Mem) (c : Caches) : Prop

theorem CoreR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {c : Caches}
    (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m') (h : CoreR m c) :
    CoreR m' c := ⟨⟩

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
