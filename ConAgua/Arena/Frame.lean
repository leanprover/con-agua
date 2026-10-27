import ConAgua.Arena.StoreLib
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Frames between tables

Each table relation (`ConsR` of one cons table, `ConsLibRel.lean`) reads its own two arrays, its two counts in `CTL`, the
scratch flag `CTL[1]` and (for `lit`) the pool and its top `CTL[0]`. Each writer (an `intern_*`
function, the pool's `nat_add`, the memo's `memo_set`) changes a known list of word arrays and of
`CTL` words. `MemFrame A C m m'` says exactly that, and `ConsR.frame` is the one lemma that moves
a table's relation across a writer it is apart from (`Apart`, decided by `decide` for concrete
schemas). The arena side needs the same frame for the state: `protoRun_st` says an interning
changes at most one of the two tables behind its lens.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `m'` is `m` except in the word arrays `A` and in the `CTL` words `C`; every array keeps its
size. -/
def MemFrame (A : List ArrId) (C : List Word) (m m' : Mem) : Prop :=
  (∀ b, b ∉ A → b ≠ CTL → m'.arr64 b = m.arr64 b) ∧
  (∀ x, x ∉ C → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) ∧
  (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size

theorem MemFrame.refl (A : List ArrId) (C : List Word) (m : Mem) : MemFrame A C m m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem MemFrame.trans {A : List ArrId} {C : List Word} {m₁ m₂ m₃ : Mem} (h₁ : MemFrame A C m₁ m₂)
    (h₂ : MemFrame A C m₂ m₃) : MemFrame A C m₁ m₃ :=
  ⟨fun b hb hc => (h₂.1 b hb hc).trans (h₁.1 b hb hc), fun x hx => (h₂.2.1 x hx).trans (h₁.2.1 x hx),
    fun b => (h₂.2.2.1 b).trans (h₁.2.2.1 b), h₂.2.2.2.trans h₁.2.2.2⟩

/-- A frame for fewer arrays and words is one for more. -/
theorem MemFrame.mono {A A' : List ArrId} {C C' : List Word} {m m' : Mem} (h : MemFrame A C m m')
    (hA : ∀ b ∈ A, b ∈ A') (hC : ∀ x ∈ C, x ∈ C') : MemFrame A' C' m m' :=
  ⟨fun b hb hc => h.1 b (fun h' => hb (hA b h')) hc, fun x hx => h.2.1 x (fun h' => hx (hC x h')),
    h.2.2.1, h.2.2.2⟩

/-- Both tiers of an array outside a frame's arrays are unchanged. -/
theorem MemFrame.tier {A : List ArrId} {C : List Word} {m m' : Mem} (h : MemFrame A C m m')
    (B : ArrId) (hB : B ∉ A) (hB' : tier1 B ∉ A) (hc : B ≠ CTL) (t : Word) :
    m'.arr64 (tierA B t) = m.arr64 (tierA B t) := by
  rcases tierA_cases' B t with e | e <;> rw [e]
  · exact h.1 B hB hc
  · exact h.1 _ hB' (tier1_ne (by decide))

/-- The arrays below `64` and their tier-1 twins `256‥319` (the store tier's), as a list. -/
def lowTierArrs : List ArrId := List.range 64 ++ (List.range 64).map tier1

theorem low_tier_mem (b : Nat) (h : b < 64 ∨ (256 ≤ b ∧ b < 320)) : b ∈ lowTierArrs := by
  rcases h with h | ⟨h1, h2⟩
  · exact List.mem_append_left _ (List.mem_range.mpr h)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨b - 256, List.mem_range.mpr (by omega),
      by simp only [tier1, tierOff]; omega⟩)

/-- A word write to array `a ≠ CTL` is a frame of `[a]`. -/
theorem MemFrame.set64 (m : Mem) (a : ArrId) (ha : a ≠ CTL) (k v : Word) :
    MemFrame [a] [] m (m.set64 a k v) := by
  refine ⟨fun b hb _ => Mem.arr64_set64_ne _ _ _ _ _ (by simpa using hb), fun x _ => ?_,
    fun b => size_set64 _ _ _ _ _, Mem.words_size_set64 _ _ _ _⟩
  rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm ha)]

/-- A write to `CTL[c]` is a frame of `[c]`. -/
theorem MemFrame.setCtl (m : Mem) (c v : Word) : MemFrame [] [c] m (m.set64 CTL c v) := by
  refine ⟨fun b _ hc => Mem.arr64_set64_ne _ _ _ _ _ hc, fun x hx => ?_,
    fun b => size_set64 _ _ _ _ _, Mem.words_size_set64 _ _ _ _⟩
  rw [rdW_set64]
  simp only [List.mem_singleton] at hx
  simp [Ne.symm hx]

theorem word_le_one (t : Word) (h : t ≤ 1) : t = 0 ∨ t = 1 := by
  have : t.toNat ≤ 1 := h
  rcases (show t.toNat = 0 ∨ t.toNat = 1 by omega) with h | h
  · exact .inl (UInt64.toNat_inj.mp h)
  · exact .inr (UInt64.toNat_inj.mp h)

/-! ## Frames from the program text (`L/WriteSet.lean`)

A program whose functions `fs` pass `closedA p A C fs` (by `decide +kernel` on the concrete
program) changes only the arrays `A` and the `CTL` words `C`, on every run: `run_memFrame`,
`invoke_memFrame`. A relation that is `Stable` under such frames (`ConsR` by `ConsR.frame`,
`StateDR.frame`, a tier group's `frame`) then survives every run with no lemma about the program:
`run_keeps`. -/

/-- The write set of `fs` in `p` at the arena's control array `CTL`. -/
abbrev closedA (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName) : Bool :=
  closedW CTL p A C fs

/-- The arena's frame relation for the text check: `MemFrame` and the same byte arrays. -/
def WFr (A : List ArrId) (C : List Word) (m₀ m : Mem) : Prop :=
  MemFrame A C m₀ m ∧ m.bytes = m₀.bytes

theorem wFr_wframe (A : List ArrId) (C : List Word) : WFrame CTL A C (WFr A C) where
  refl m := ⟨MemFrame.refl _ _ _, rfl⟩
  st64 m₀ m a i v h ha := by
    refine ⟨?_, h.2⟩
    rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
    · exact MemFrame.trans h.1 (MemFrame.mono (MemFrame.set64 m a hc i v) (by simpa using ha) (by simp))
    · exact MemFrame.trans h.1 (MemFrame.mono (MemFrame.setCtl m i v) (by simp) (by simpa using hi))
  setG _ _ _ _ h := h

/-- **Every run of a function of a closed set is a frame of its write set** (and keeps the byte
arrays). -/
theorem run_memFrame {p : Prog} {A : List ArrId} {C : List Word} {fs : List FnName}
    (hp : closedA p A C fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem}
    {rs : List Word} {m' : Mem} (h : run p n f vs m = .ok (rs, m')) :
    MemFrame A C m m' ∧ m'.bytes = m.bytes :=
  run_frame p hp (wFr_wframe A C) f hf n vs m rs m' h

/-- The same as a triple about a call, for use inside a caller's `vcgen`. -/
theorem invoke_memFrame {p : Prog} {A : List ArrId} {C : List Word} {fs : List FnName}
    (hp : closedA p A C fs = true) (n : Nat) {f : FnName} (hf : f ∈ fs) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun _ s => MemFrame A C s₀.mem s.mem ∧ s.mem.bytes = s₀.mem.bytes; ⊤⦄ :=
  invoke_frame p hp (wFr_wframe A C) n f hf vs s₀

/-- A memory predicate that every frame of `(A, C)` keeps: it reads nothing in the write set. -/
def Stable (A : List ArrId) (C : List Word) (X : Mem → Prop) : Prop :=
  ∀ m m', MemFrame A C m m' → X m → X m'

/-- **Frames for free**: a predicate stable under `(A, C)` survives every run of a function of a
set closed in `(A, C)`. -/
theorem run_keeps {p : Prog} {A : List ArrId} {C : List Word} {fs : List FnName}
    (hp : closedA p A C fs = true) {f : FnName} (hf : f ∈ fs) {X : Mem → Prop} (hX : Stable A C X)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n f vs m = .ok (rs, m')) (hx : X m) : X m' :=
  hX m m' (run_memFrame hp hf h).1 hx

/-- `Stable` by array bounds: a predicate that a frame of arrays and words outside `[lo, hi)`
keeps is stable under every write set that avoids `[lo, hi)`. -/
theorem Stable.of_range {lo hi clo chi : Nat} {X : Mem → Prop}
    (hX : ∀ A C m m', (∀ b ∈ A, b < lo ∨ hi ≤ b) → (∀ x ∈ C, x.toNat < clo ∨ chi ≤ x.toNat) →
      MemFrame A C m m' → X m → X m')
    {A : List ArrId} {C : List Word} (hA : ∀ b ∈ A, b < lo ∨ hi ≤ b)
    (hC : ∀ x ∈ C, x.toNat < clo ∨ chi ≤ x.toNat) : Stable A C X :=
  fun m m' hf hx => hX A C m m' hA hC hf hx

/-! ## Table relations across a frame -/

section frame
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- **The instance's locality**: a node's relation and hash depend only on the record array, the
arrays `A₀` and the `CTL` words `C₀` (for `lit`: the pool and its top `CTL[0]`). (`RFrame` is the
same fact for the table's own appends; this one is for every other writer.) -/
def RLocal (A₀ : List ArrId) (C₀ : List Word) : Prop :=
  ∀ m m', (∀ t, m'.arr64 (tierA S.ra t) = m.arr64 (tierA S.ra t)) → (∀ b ∈ A₀, m'.arr64 b = m.arr64 b) →
    (∀ x ∈ C₀, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) →
    (∀ t i a, R m t i a → R m' t i a) ∧ ∀ t i, hs m' t i = hs m t i

/-- A table (and the arrays `A₀` and words `C₀` its records refer to) is apart from a writer of
`A` and `C` (the table's arrays in both tiers: `a` and `tier1 a`). -/
def Apart (A₀ : List ArrId) (C₀ : List Word) (A : List ArrId) (C : List Word) : Prop :=
  S.ra ∉ A ∧ tier1 S.ra ∉ A ∧ S.sa ∉ A ∧ tier1 S.sa ∉ A ∧ (∀ b ∈ A₀, b ∉ A ∧ b ≠ CTL) ∧
    S.ca ∉ C ∧ S.ca + 1 ∉ C ∧ (1 : Word) ∉ C ∧ SCB ∉ C ∧ ∀ x ∈ C₀, x ∉ C

instance (A₀ : List ArrId) (C₀ : List Word) (A : List ArrId) (C : List Word) :
    Decidable (Apart S A₀ C₀ A C) := by
  unfold Apart
  exact instDecidableAnd (dq := instDecidableAnd (dq := instDecidableAnd (dq := instDecidableAnd (dq := instDecidableAnd))))

/-- **`Apart` by bounds**: a table below array `ka` and below `CTL` word `kc` is apart from any
writer of arrays `≥ ka` (and not the tier-1 twins `256 + b` of arrays `b < ka`) and `CTL` words
`≥ kc` (`ArenaR.frame_above`, `ArenaR.frame_ext`). -/
theorem apart_hi (ka kc : Nat) (A₀ : List ArrId) (C₀ : List Word) (A : List ArrId) (C : List Word)
    (hlo : S.ra < ka ∧ S.sa < ka ∧ S.ca.toNat + 1 < kc ∧ (∀ b ∈ A₀, b < ka ∧ b ≠ CTL) ∧
      ∀ x ∈ C₀, x.toNat < kc) (hk : 62 < kc) (hkc : kc < 2 ^ 64)
    (hA : ∀ b ∈ A, ka ≤ b ∧ (b < 256 ∨ 256 + ka ≤ b)) (hC : ∀ x ∈ C, kc ≤ x.toNat) :
    Apart S A₀ C₀ A C := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hlo
  have tw : ∀ r : ArrId, r < ka → tier1 r ∉ A := fun r hr h => by
    rcases (hA _ h).2 with h' | h'
    · exact absurd h' (Nat.not_lt.mpr (Nat.le_add_left 256 r))
    · exact absurd hr (Nat.not_lt.mpr
        (Nat.le_of_add_le_add_right (by rwa [Nat.add_comm 256 ka] at h')))
  refine ⟨fun h => Nat.not_le_of_lt h1 (hA _ h).1, tw _ h1,
    fun h => Nat.not_le_of_lt h2 (hA _ h).1, tw _ h2,
    fun b hb => ⟨fun h => Nat.not_le_of_lt (h4 b hb).1 (hA _ h).1, (h4 b hb).2⟩,
    fun h => by have := hC _ h; omega, fun h => ?_,
    fun h => by have := hC _ h; simp at this; omega,
    fun h => by have := hC _ h; simp [SCB] at this; omega,
    fun x hx h => by have := hC _ h; have := h5 x hx; omega⟩
  have := hC _ h
  have : (S.ca + 1).toNat = S.ca.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

end frame

/-! ## The arena side: an interning changes one table -/

section proto
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- The state after `protoRun` is the old one, or one of the lens's two tables replaced. -/
theorem protoRun_st (L : Lens α δ k) (key : α) (tag : UInt32) (pf : Option (Idx k)) (d : δ)
    (err : CheckError) (a a' : AState) (y : Idx k) (h : protoRun L key tag pf d err a = .ok (y, a')) :
    a' = a ∨ (∃ t, a' = L.setP a t) ∨ (∃ t, a' = L.setS a t) := by
  unfold protoRun at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inr (.inr ⟨_, h.2.symm⟩)
        · simp at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inr (.inl ⟨_, h.2.symm⟩)
      · simp at h

/-- The same for the final state of an arena operation that runs as `protoRun`. -/
theorem AM.st_proto (L : Lens α δ k) (op : AM (Idx k)) (key : α) (tag : UInt32)
    (pf : Option (Idx k)) (d : δ) (err : CheckError) (a : AState)
    (hrun : op.run a = protoRun L key tag pf d err a) (hok : AM.ok op a) :
    AM.st op a = a ∨ (∃ t, AM.st op a = L.setP a t) ∨ (∃ t, AM.st op a = L.setS a t) :=
  protoRun_st L key tag pf d err a _ _ (hrun.symm.trans (AM.run_of_ok op a hok))

end proto

end L.Arena
