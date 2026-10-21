import ConAgua.Arena.StoreLib

/-!
# Frames between tables

Each table relation (`StoreR` of one schema) reads its own two arrays, its two counts in `CTL`, the
scratch flag `CTL[1]` and (for `lit`) the pool and its top `CTL[0]`. Each writer (an `intern_*`
function, the pool's `nat_add`, the memo's `memo_set`) changes a known list of word arrays and of
`CTL` words. `MemFrame A C m m'` says exactly that, and `storeR_frame` is the one lemma that moves
a table's relation across a writer it is apart from (`Apart`, decided by `decide` for concrete
schemas). The arena side needs the same frame for the state: `protoRun_st` says an interning
changes at most one of the two tables behind its lens.
-/

open ConRon.Arena

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

/-! ## Table relations across a frame -/

section frame
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- **The instance's locality**: a node's relation and hash depend only on the record array, the
arrays `A₀` and the `CTL` words `C₀` (for `lit`: the pool and its top `CTL[0]`). (`RFrame` is the
same fact for the table's own appends; this one is for every other writer.) -/
def RLocal (A₀ : List ArrId) (C₀ : List Word) : Prop :=
  ∀ m m', m'.arr64 S.ra = m.arr64 S.ra → (∀ b ∈ A₀, m'.arr64 b = m.arr64 b) →
    (∀ x ∈ C₀, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) →
    (∀ t i a, R m t i a → R m' t i a) ∧ ∀ t i, hs m' t i = hs m t i

/-- A table (and the arrays `A₀` and words `C₀` its records refer to) is apart from a writer of
`A` and `C`. -/
def Apart (A₀ : List ArrId) (C₀ : List Word) (A : List ArrId) (C : List Word) : Prop :=
  S.ra ∉ A ∧ S.sa ∉ A ∧ (∀ b ∈ A₀, b ∉ A ∧ b ≠ CTL) ∧ S.ca ∉ C ∧ S.ca + 1 ∉ C ∧
    (1 : Word) ∉ C ∧ ∀ x ∈ C₀, x ∉ C

instance (A₀ : List ArrId) (C₀ : List Word) (A : List ArrId) (C : List Word) :
    Decidable (Apart S A₀ C₀ A C) := by
  unfold Apart; infer_instance

/-- **`Apart` by bounds**: a table below array `ka` and below `CTL` word `kc` is apart from any
writer of arrays `≥ ka` and `CTL` words `≥ kc` (`ArenaR.frame_above`, `ArenaR.frame_ext`). -/
theorem apart_hi (ka kc : Nat) (A₀ : List ArrId) (C₀ : List Word) (A : List ArrId) (C : List Word)
    (hlo : S.ra < ka ∧ S.sa < ka ∧ S.ca.toNat + 1 < kc ∧ (∀ b ∈ A₀, b < ka ∧ b ≠ CTL) ∧
      ∀ x ∈ C₀, x.toNat < kc) (hk : 1 < kc) (hkc : kc < 2 ^ 64)
    (hA : ∀ b ∈ A, ka ≤ b) (hC : ∀ x ∈ C, kc ≤ x.toNat) : Apart S A₀ C₀ A C := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hlo
  refine ⟨fun h => Nat.not_le_of_lt h1 (hA _ h), fun h => Nat.not_le_of_lt h2 (hA _ h),
    fun b hb => ⟨fun h => Nat.not_le_of_lt (h4 b hb).1 (hA _ h), (h4 b hb).2⟩,
    fun h => by have := hC _ h; omega, fun h => ?_,
    fun h => by have := hC _ h; simp at this; omega,
    fun x hx h => by have := hC _ h; have := h5 x hx; omega⟩
  have := hC _ h
  have : (S.ca + 1).toNat = S.ca.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

/-- **A table's relation survives a writer it is apart from.** -/
theorem storeR_frame (hS : S.WF) (A₀ : List ArrId) (C₀ : List Word) (hl : RLocal S R hs A₀ C₀)
    (A : List ArrId) (C : List Word) (hap : Apart S A₀ C₀ A C) (m m' : Mem) (hf : MemFrame A C m m') (on : Bool)
    (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs m on tbP tbS) :
    StoreR S R hs m' on tbP tbS := by
  obtain ⟨hra, hsa, hA₀, hc0, hc1, h1, h0⟩ := hap
  obtain ⟨hfa, hfc, hfs, -⟩ := hf
  obtain ⟨hctl, hfl, hT0, hT1⟩ := hR
  have era := hfa S.ra hra hS.ra_ctl
  have esa := hfa S.sa hsa hS.sa_ctl
  have hloc := hl m m' era (fun b hb => hfa b (hA₀ b hb).1 (hA₀ b hb).2) (fun x hx => hfc x (h0 x hx))
  have ec : ∀ t : Word, t ≤ 1 → cntW S m' t = cntW S m t := by
    intro t ht
    simp only [cntW]
    apply hfc
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · exact hc1
  refine ⟨by rw [hfs]; exact hctl, by rw [hfc 1 h1]; exact hfl, ?_, ?_⟩
  · exact tierR_mono S R hs m m' 0 tbP era esa (ec 0 (by decide)) (hloc.1 0) (hloc.2 0) hT0
  · exact tierR_mono S R hs m m' 1 tbS era esa (ec 1 (by decide)) (hloc.1 1) (hloc.2 1) hT1

end frame

/-! ## The frame of an append and of an `intern_*` model -/

theorem pushG_frame (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (vs : List Word)
    (j c : Word) : MemFrame [S.ra, S.sa] [S.ca, S.ca + 1] m (pushG S m t vs j c) := by
  refine ⟨fun b hb hc => ?_, fun x hx => ?_, fun b => pushG_size S m t vs j c b,
    pushG_words S m t vs j c⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    exact pushG_arr S m t vs j c b hb.1 hb.2 hc
  · rw [pushG_ctl S hS]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    have : x ≠ S.ca + t := by
      rcases word_le_one t ht with rfl | rfl
      · simpa using hx.1
      · exact hx.2
    simp [this]

/-- **What an `intern_*` model changes**: the table's two arrays and its two counts. -/
theorem internM_frame (S : Schema) (hS : S.WF) (m : Mem) (sk : Word) (pk : Word → Bool)
    (vs rs₀ rs₁ : List Word) (w : Word) (m' : Mem) (h : internM S m sk pk vs rs₀ rs₁ = some (w, m')) :
    MemFrame [S.ra, S.sa] [S.ca, S.ca + 1] m m' := by
  have h0 := pushG_frame S hS m 0 (by decide) vs
  have h1 := pushG_frame S hS m 1 (by decide) vs
  simp only [internM] at h
  split at h <;> try split at h <;> try split at h <;> try split at h <;> try split at h <;>
    try split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
       first | with_reducible exact MemFrame.refl _ _ _ | with_reducible exact h0 _ _ |
         with_reducible exact h1 _ _)
    | simp at h

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
