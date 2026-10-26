import ConAgua.Arena.PromoteCIRef6

/-!
# Decoding a rule record is stable when the pool is extended on the words it reads

A rule record at `d` reads its 11 words and, if it fires nested, two slices that lie at or above
`T`. `ExtP P a b`: `b` extends `a` at the positions satisfying `P`.
-/

open ConRon.Arena

namespace L.Arena

/-- Firing slices lie at or above `T`. -/
def FireHi (A : Array Word) (d T : Nat) : Prop :=
  nat? A (d + 3) = some 1 → ∃ q b r y : Nat, nat? A (d + 4) = some q ∧ nat? A (d + 5) = some b ∧
    nat? A (d + 6) = some r ∧ nat? A (d + 7) = some y ∧ T ≤ q ∧ T ≤ r

/-- `b` extends `a` at the positions satisfying `P`. -/
def ExtP (P : Nat → Prop) (a b : Array Word) : Prop :=
  ∀ i v, P i → a[i]? = some v → b[i]? = some v

theorem mapM_mono {α : Type} (f g : Nat → Option α) :
    ∀ (l : List Nat) (xs : List α), (∀ j ∈ l, ∀ x, f j = some x → g j = some x) →
    l.mapM f = some xs → l.mapM g = some xs
  | [], xs, _, hx => by simpa using hx
  | j :: js, xs, hfg, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := hx
    exact ⟨y, hfg j (List.mem_cons_self ..) y hy, ys,
      mapM_mono f g js ys (fun j' hj' => hfg j' (List.mem_cons_of_mem _ hj')) hys, rfl⟩

section ext
variable {P : Nat → Prop} {a b : Array Word} (h : ExtP P a b)
include h

theorem ExtP.rn {i x : Nat} (hi : P i) (hx : nat? a i = some x) : nat? b i = some x := by
  obtain ⟨w, hw, rfl⟩ := nat?_get hx
  simp [L.Arena.nat?, h i w hi hw]

theorem ExtP.rb {i : Nat} {x : Bool} (hi : P i) (hx : bool? a i = some x) :
    bool? b i = some x := by
  obtain ⟨w, hw, rfl⟩ := bool?_get hx
  simp [L.Arena.bool?, h i w hi hw]

theorem ExtP.rd {k : IdxKind} {i : Nat} {x : Idx k} (hi : P i) (hx : hd? a i = some x) :
    hd? b i = some x := by
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some hx
  simp [L.Arena.hd?, h i w hi hw, hl]

theorem ExtP.rs {k : IdxKind} {o c : Nat} {xs : List (Idx k)} (hr : ∀ j < c, P (o + j))
    (hx : hslice? a o c = some xs) : hslice? b o c = some xs :=
  mapM_mono (fun j => L.Arena.hd? a (o + j)) (fun j => L.Arena.hd? b (o + j)) _ _
    (fun j hj _y hy => h.rd (hr j (List.mem_range.mp hj)) hy) hx

theorem ExtP.rl {k : IdxKind} {i : Nat} {xs : List (Idx k)} (hi : P i) (hi1 : P (i + 1))
    (hr : ∀ x _y : Nat, nat? a i = some x → nat? a (i + 1) = some _y → ∀ j < _y, P (x + j))
    (hx : hlist? a i = some xs) : hlist? b i = some xs := by
  simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨o, ho, c, hc, hs⟩ := hx
  exact ⟨o, h.rn hi ho, c, h.rn hi1 hc, h.rs (hr o c ho hc) hs⟩

end ext

/-- The positions a rule record at `d` reads. -/
def RuleP (d T : Nat) : Nat → Prop := fun i => (d ≤ i ∧ i < d + 11) ∨ T ≤ i

theorem decFire_ext {a b : Array Word} {d T : Nat} {fire : IRecRuleFire}
    (h : ExtP (RuleP d T) a b) (hf : decFire a d = some fire) (hhi : FireHi a d T) :
    decFire b d = some fire := by
  unfold decFire at hf ⊢
  cases hk : nat? a (d + 3) with
  | none => simp [hk] at hf
  | some t =>
    have hk' : nat? b (d + 3) = some t := h.rn (Or.inl (by omega)) hk
    simp only [hk, hk', Option.bind_eq_bind, Option.bind_some] at hf ⊢
    rcases t with _ | _ | t
    · exact hf
    · obtain ⟨q, bb, r, y, hq, hb, hr, hy, hTq, hTr⟩ := hhi hk
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hf ⊢
      obtain ⟨l1, hl1, l2, hl2, rfl⟩ := hf
      refine ⟨l1, h.rl (Or.inl (by omega)) (Or.inl (by omega)) ?_ hl1, l2,
        h.rl (Or.inl (by omega)) (Or.inl (by omega)) ?_ hl2, rfl⟩
      · intro x z hx hz j hj
        rw [hq] at hx; rw [hb] at hz; cases hx; cases hz
        exact Or.inr (by omega)
      · intro x z hx hz j hj
        rw [hr] at hx; rw [hy] at hz; cases hx; cases hz
        exact Or.inr (by omega)
    · simp at hf

theorem decRule_ext {a b : Array Word} {d T : Nat} {rl : IRecRule}
    (h : ExtP (RuleP d T) a b) (hA : decRule a d = some rl) (hhi : FireHi a d T) :
    decRule b d = some rl := by
  obtain ⟨w0, w1, w2, w8, w9, w10, e0, l0, hctor, e1, hnf, e2, hcpr, e8, l8, hrhs, e9, hk, e10,
    he⟩ := pmDecRule_words hA
  have P' : ∀ i, d ≤ i → i < d + 11 → RuleP d T i := fun i h1 h2 => Or.inl ⟨h1, h2⟩
  have b0 := h d w0 (P' _ (by omega) (by omega)) e0
  have b1 := h (d + 1) w1 (P' _ (by omega) (by omega)) e1
  have b2 := h (d + 2) w2 (P' _ (by omega) (by omega)) e2
  have b8 := h (d + 8) w8 (P' _ (by omega) (by omega)) e8
  have b9 := h (d + 9) w9 (P' _ (by omega) (by omega)) e9
  have b10 := h (d + 10) w10 (P' _ (by omega) (by omega)) e10
  have hfi := decFire_ext h (decRule_fire hA) hhi
  have := decRule_mk (a := b) (q := d) (c := rl.ctor) (nf := rl.nfields) (cpar := rl.ctorParams)
    (fire := rl.fire) (kb := rl.k) (eb := rl.eta) (rh := rl.rhs)
    (by rw [hctor]; simp [L.Arena.hd?, b0, l0]) (by rw [← hnf]; simp [L.Arena.nat?, b1])
    (by rw [← hcpr]; simp [L.Arena.nat?, b2]) hfi (by rw [hrhs]; simp [L.Arena.hd?, b8, l8])
    (by rw [← hk]; simp [L.Arena.bool?, b9]) (by rw [← he]; simp [L.Arena.bool?, b10])
  exact this

end L.Arena
