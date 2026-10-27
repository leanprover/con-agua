import ConAgua.Arena.IndLibSpec
import Std.Tactic.BVDecide.Normalize.Prop
import ConRon.Bridge.Grind

/-!
# The `And` pin's inductive arm, part 2a: relocating a front constant record

`ind_block_to_erec` (`DeclStep.lean`) copies the front's constant records (`DLP`, decoded in the
cut pool `trunc`, `IndDeclAt`) into `EREC`: each record's words, its universe-parameter slice
(relocated: word `2` points at the copy) and a recursor's rule slice (word `7`). A record's other
slices are copied as they are, so the copy decodes to the same constant only if they are empty:
the front's records are of the shape `FrontCI` (an inductive's default capabilities, plain rules),
the constants the twin's `installIndD` pushes.

`decCI_reloc`: if every word the original decoding reads reappears in the copy (`ShR`, a shifted
extension), the copy decodes to the same constant, at any name decoder.
-/

open ConRon.Arena

namespace L.Arena

/-! ## The front's constant shapes -/

/-- **The constants of a front inductive block**: an inductive with no `all`/`ctors` and a
`sortZ` with no names (the default capabilities), a constructor, a recursor with plain rules. -/
def FrontCI : IConstantInfo → Prop
  | .indInfo _ caps => caps.all = [] ∧ caps.ctors = [] ∧
      (caps.sortZ = .never ∨ caps.sortZ = .ifAllZero [])
  | .ctorInfo _ _ _ => True
  | .recInfo _ _ _ rules => ∀ r ∈ rules, r.fire = .plain
  | _ => False

/-- A front block: every constant of the front's shape. -/
def FrontBlock (block : List IConstantInfo) : Prop := ∀ c ∈ block, FrontCI c

/-! ## Shifted extensions -/

/-- The words of `T` at `s + k` reappear in `B` at `p + k`, for the offsets `K` admits. -/
def ShR (T B : Array Word) (s p : Nat) (K : Nat → Prop) : Prop :=
  ∀ k v, K k → T[s + k]? = some v → B[p + k]? = some v

section sh
variable {T B : Array Word} {s p : Nat} {K : Nat → Prop}

theorem ShR.nat (h : ShR T B s p K) {k x i j : Nat} (hk : K k) (hi : i = s + k) (hj : j = p + k)
    (hx : nat? T i = some x) : nat? B j = some x := by
  subst hi hj
  simp only [nat?, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨v, h k v hk hv, rfl⟩

theorem ShR.hd {kk : IdxKind} (h : ShR T B s p K) {k i j : Nat} {x : Idx kk} (hk : K k)
    (hi : i = s + k) (hj : j = p + k) (hx : hd? T i = some x) : hd? B j = some x := by
  subst hi hj
  simp only [hd?, bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, hx⟩ := hx
  exact ⟨v, h k v hk hv, hx⟩

theorem ShR.bool (h : ShR T B s p K) {k i j : Nat} {x : Bool} (hk : K k)
    (hi : i = s + k) (hj : j = p + k) (hx : bool? T i = some x) : bool? B j = some x := by
  subst hi hj
  simp only [bool?, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨v, h k v hk hv, rfl⟩

end sh

theorem mapM_imp {α β : Type} {f g : α → Option β} :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys →
      (∀ x ∈ l, ∀ y, f x = some y → g x = some y) → l.mapM g = some ys
  | [], ys, h, _ => by simpa using h
  | x :: xs, ys, h, hfg => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    exact ⟨y, hfg x (by simp) y hy, ys', mapM_imp xs ys' hys' (fun z hz => hfg z (by simp [hz])), rfl⟩

/-- A slice whose words reappear decodes the same. -/
theorem hslice?_sh {kk : IdxKind} {T B : Array Word} {o q c : Nat} {xs : List (Idx kk)}
    (h : hslice? T o c = some xs) (hs : ∀ j v, j < c → T[o + j]? = some v → B[q + j]? = some v) :
    hslice? B q c = some xs := by
  unfold hslice? at h ⊢
  refine mapM_imp _ _ h fun j hj y hy => ?_
  have hj' : j < c := List.mem_range.mp hj
  exact ShR.hd (K := fun j => j < c) (fun k v hk hv => hs k v hk hv) hj' rfl rfl hy

theorem hslice?_nil {kk : IdxKind} {T : Array Word} {o c : Nat}
    (h : (hslice? T o c : Option (List (Idx kk))) = some []) : c = 0 := by
  unfold hslice? at h
  have := L.Ind.mapM_opt_length _ _ _ h
  simpa using this.symm

/-- An empty list whose header words reappear decodes empty. -/
theorem hlist?_nil_sh {kk : IdxKind} {T B : Array Word} {s p : Nat} {K : Nat → Prop}
    (h : ShR T B s p K) {k i j : Nat} (hk : K k) (hk1 : K (k + 1)) (hi : i = s + k) (hj : j = p + k)
    (hx : (hlist? T i : Option (List (Idx kk))) = some []) : hlist? B j = some ([] : List (Idx kk)) := by
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨o, ho, c, hc, hs⟩ := hx
  have hc0 := hslice?_nil hs
  subst hc0
  exact ⟨o, h.nat hk hi hj ho, 0, h.nat hk1 (by omega) (by omega) hc, rfl⟩

/-! ## The relocation -/

/-- The constant value at `s + 1`, its level-parameter slice relocated to `q`. -/
theorem decCV_reloc {T B : Array Word} {s p q : Nat} {K : Nat → Prop} {cv : IConstantVal}
    (h : ShR T B s p K) (hK1 : K 1) (hK3 : K 3) (hK4 : K 4)
    (hcv : decCV T (s + 1) = some cv) (hq : nat? B (p + 2) = some q)
    (hl : ∀ off cnt, nat? T (s + 2) = some off → nat? T (s + 3) = some cnt →
      ∀ j v, j < cnt → T[off + j]? = some v → B[q + j]? = some v) :
    decCV B (p + 1) = some cv := by
  simp only [decCV, hlist?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv ⊢
  obtain ⟨nm, hnm, lps, ⟨off, hoff, cnt, hcnt, hsl⟩, ty, hty, rfl⟩ := hcv
  refine ⟨nm, h.hd hK1 rfl rfl hnm, lps, ⟨q, hq, cnt, h.nat hK3 (by omega) (by omega) hcnt,
    hslice?_sh hsl (hl off cnt hoff hcnt)⟩, ty, h.hd hK4 (by omega) (by omega) hty, rfl⟩

/-- An inductive's capabilities at `s + 5` (words `5‥19`), of the front's shape. -/
theorem decCaps_reloc {T B : Array Word} {dn0 dn : NIdx → Option ConLeche.Name} {s p : Nat}
    {K : Nat → Prop} {caps : IIndCaps} (h : ShR T B s p K) (hK : ∀ k, 5 ≤ k → k < 20 → K k)
    (hc : decCaps T dn0 (s + 5) = some caps) (hall : caps.all = []) (hct : caps.ctors = [])
    (hz : caps.sortZ = .never ∨ caps.sortZ = .ifAllZero []) :
    decCaps B dn (p + 5) = some caps := by
  simp only [decCaps, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc ⊢
  obtain ⟨eta, h0, ec, h1, ep, h2, ef, h3, ul, h4, up, h5, rk, h6, sz, h7, al, h10, np, h12, ct,
    h13, rfl⟩ := hc
  simp only at hall hct hz
  subst hall hct
  refine ⟨eta, h.bool (hK 5 (Nat.le_refl _) (by omega)) (by omega) (by omega) h0,
    ec, h.hd (hK 6 (by omega) (by omega)) (by omega) (by omega) h1,
    ep, h.nat (hK 7 (by omega) (by omega)) (by omega) (by omega) h2,
    ef, h.nat (hK 8 (by omega) (by omega)) (by omega) (by omega) h3,
    ul, h.bool (hK 9 (by omega) (by omega)) (by omega) (by omega) h4,
    up, h.nat (hK 10 (by omega) (by omega)) (by omega) (by omega) h5,
    rk, h.bool (hK 11 (by omega) (by omega)) (by omega) (by omega) h6,
    sz, ?_, [], hlist?_nil_sh h (hK 15 (by omega) (by omega)) (hK 16 (by omega) (by omega))
      (by omega) (by omega) h10,
    np, h.nat (hK 17 (by omega) (by omega)) (by omega) (by omega) h12,
    [], hlist?_nil_sh h (hK 18 (by omega) (by omega)) (hK 19 (by omega) (by omega))
      (by omega) (by omega) h13, rfl⟩
  -- `sortZ`
  simp only [decPW, bind, Option.bind_eq_some_iff] at h7 ⊢
  obtain ⟨kz, hkz, h7⟩ := h7
  refine ⟨kz, h.nat (hK 12 (by omega) (by omega)) (by omega) (by omega) hkz, ?_⟩
  rcases kz with _ | _ | kz
  · exact h7
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h7 ⊢
    obtain ⟨ns, hns, l, hl, rfl⟩ := h7
    rcases hz with hz | hz
    · cases hz
    · cases hz
      have hl0 : ns = [] := by
        have := L.Ind.mapM_opt_length _ _ _ hl; simp at this; exact List.length_eq_zero_iff.mp this.symm
      subst hl0
      exact ⟨[], hlist?_nil_sh h (hK 13 (by omega) (by omega)) (hK 14 (by omega) (by omega))
        (by omega) (by omega) hns, [], rfl, rfl⟩
  · exact h7

/-- A plain recursor rule whose 11 words reappear. -/
theorem decRule_reloc {T B : Array Word} {o q : Nat} {rr : IRecRule}
    (h : ShR T B o q (fun k => k < 11)) (hr : decRule T o = some rr) (hp : rr.fire = .plain) :
    decRule B q = some rr := by
  unfold decRule at hr ⊢
  cases hfk : nat? T (o + 3) with
  | none => simp [hfk] at hr
  | some fk =>
  rw [h.nat (k := 3) (by omega) rfl rfl hfk]
  rw [hfk] at hr
  rcases fk with _ | _ | fk
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Option.bind_some] at hr ⊢
    obtain ⟨ct, h0, nf, h1, cp, h2, rhs, h8, k, h9, eta, h10, rfl⟩ := hr
    exact ⟨ct, h.hd (k := 0) (by omega) rfl rfl h0,
      nf, h.nat (k := 1) (by omega) rfl rfl h1, cp, h.nat (k := 2) (by omega) rfl rfl h2,
      rhs, h.hd (k := 8) (by omega) rfl rfl h8, k, h.bool (k := 9) (by omega) rfl rfl h9,
      eta, h.bool (k := 10) (by omega) rfl rfl h10, rfl⟩
  · exfalso
    simp only [bind, Option.bind_some] at hr
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨fire, hfire, hr⟩ := hr
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, rfl⟩ := hr
    simp at hp
  · simp at hr

/-- A rule slice whose words reappear. -/
theorem decRules_reloc {T B : Array Word} {o q c : Nat} {rules : List IRecRule}
    (hr : decRules T o c = some rules) (hp : ∀ r ∈ rules, r.fire = .plain)
    (hs : ∀ x v, x < 11 * c → T[o + x]? = some v → B[q + x]? = some v) :
    decRules B q c = some rules := by
  unfold decRules at hr ⊢
  have hlen := L.Ind.mapM_opt_length _ _ _ hr
  refine mapM_imp _ _ hr fun j hj y hy => ?_
  have hj' : j < c := List.mem_range.mp hj
  have hmem : y ∈ rules := by
    obtain ⟨i, hi, hiy⟩ : ∃ i, ∃ hi : i < (List.range c).length, (List.range c)[i] = j :=
      List.mem_iff_getElem.mp hj
    have := L.Ind.mapM_opt_get _ _ _ hr i hi
    rw [hiy, hy] at this
    simp only [Option.some.injEq] at this
    rw [this]; exact List.getElem_mem _
  refine decRule_reloc (fun k v hk hv => ?_) hy (hp y hmem)
  have := hs (11 * j + k) v (by omega) (by rw [← Nat.add_assoc]; exact hv)
  rw [← Nat.add_assoc] at this; exact this

/-- **The relocated copy of a front constant record decodes as the record.** `T` the cut pool,
`s` the record; `B` the copy at `p`, its level parameters at `q` (word `2`), a recursor's rules at
`r` (word `7`); every other word of the record (`K kk`, by the kind `kk`) reappears. -/
def relocK (kk k : Nat) : Prop :=
  k < (if kk = 3 then 20 else if kk = 4 then 7 else 9) ∧ k ≠ 2 ∧ (kk = 5 → k ≠ 7)

theorem decCI_reloc {T B : Array Word} {dn0 dn : NIdx → Option ConLeche.Name} {s p q r : Nat}
    {c : IConstantInfo} (hc : decCI T dn0 s = some c) (hF : FrontCI c)
    (hsh : ∀ kk, nat? T s = some kk → ShR T B s p (relocK kk))
    (hq : nat? B (p + 2) = some q)
    (hl : ∀ off cnt, nat? T (s + 2) = some off → nat? T (s + 3) = some cnt →
      ∀ j v, j < cnt → T[off + j]? = some v → B[q + j]? = some v)
    (hr : nat? T s = some 5 → nat? B (p + 7) = some r ∧
      ∀ off cnt, nat? T (s + 7) = some off → nat? T (s + 8) = some cnt →
        ∀ x v, x < 11 * cnt → T[off + x]? = some v → B[r + x]? = some v) :
    decCI B dn p = some c := by
  unfold decCI at hc ⊢
  cases hk : nat? T s with
  | none => simp [hk] at hc
  | some kk =>
  have h := hsh kk hk
  have hk0 : nat? B (p + 0) = some kk := by
    refine h.nat (k := 0) ?_ rfl rfl (by simpa using hk)
    refine ⟨?_, by omega, by omega⟩
    split <;> (try split) <;> omega
  simp only [Nat.add_zero] at hk0
  rw [hk0]
  rw [hk] at hc
  simp only [bind, Option.bind_some] at hc ⊢
  rcases kk with _ | _ | _ | _ | _ | _ | kk
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨cv, -, rfl⟩ := hc; exact hF.elim
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨cv, -, _, -, _, -, rfl⟩ := hc; exact hF.elim
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨cv, -, rfl⟩ := hc; exact hF.elim
  · -- inductive
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc ⊢
    obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := hc
    obtain ⟨hall, hct, hz⟩ := hF
    have hK : ∀ k, k < 20 → k ≠ 2 → relocK 3 k := fun k h1 h2 => ⟨by simpa using h1, h2, by omega⟩
    exact ⟨cv, decCV_reloc h (hK 1 (by omega) (by omega)) (hK 3 (by omega) (by omega))
        (hK 4 (by omega) (by omega)) hcv hq hl,
      caps, decCaps_reloc h (fun k h1 h2 => hK k h2 (by omega)) hcaps hall hct hz, rfl⟩
  · -- constructor
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc ⊢
    obtain ⟨cv, hcv, a1, h1, a2, h2, rfl⟩ := hc
    have hK : ∀ k, k < 7 → k ≠ 2 → relocK 4 k := fun k h1 h2 => ⟨by simpa using h1, h2, by omega⟩
    exact ⟨cv, decCV_reloc h (hK 1 (by omega) (by omega)) (hK 3 (by omega) (by omega))
        (hK 4 (by omega) (by omega)) hcv hq hl,
      a1, h.nat (hK 5 (by omega) (by omega)) rfl rfl h1,
      a2, h.nat (hK 6 (by omega) (by omega)) rfl rfl h2, rfl⟩
  · -- recursor
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc ⊢
    obtain ⟨cv, hcv, a1, h1, a2, h2, hc⟩ := hc
    obtain ⟨ro, hro, rc, hrc, rules, hrules, rfl⟩ := hc
    have hK : ∀ k, k < 9 → k ≠ 2 → k ≠ 7 → relocK 5 k := fun k h1 h2 h3 =>
      ⟨by simpa using h1, h2, fun _ => h3⟩
    obtain ⟨hr7, hrs⟩ := hr (by simpa using hk)
    exact ⟨cv, decCV_reloc h (hK 1 (by omega) (by omega) (by omega))
        (hK 3 (by omega) (by omega) (by omega)) (hK 4 (by omega) (by omega) (by omega)) hcv hq hl,
      a1, h.nat (hK 5 (by omega) (by omega) (by omega)) rfl rfl h1,
      a2, h.nat (hK 6 (by omega) (by omega) (by omega)) rfl rfl h2,
      r, hr7, rc, h.nat (hK 8 (by omega) (by omega) (by omega)) rfl rfl hrc,
      rules, decRules_reloc hrules hF (hrs ro rc hro hrc), rfl⟩
  · simp at hc

end L.Arena
