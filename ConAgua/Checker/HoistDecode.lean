import ConAgua.Checker.HoistRefBase

/-!
# Decoding facts for the hoist's walk refinement (lane `front4`)

What `HoistWalkRef.lean` reads of the pool's records: an inductive block's member pointers
(`decCIs`), a member's kind, type and recursor rules (`decCI`, `decCV`, `decRules`), the words of
`trunc P t` as words of `P` (away from word `0`), and a `DECL` record's words (`dw`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

set_option linter.unusedSimpArgs false

namespace L.Checker

/-! ## Block decoding -/

theorem trunc_get {P : Array Word} {t j : Nat} {w : Word} (h : (trunc P t)[j]? = some w) (hj : 0 < j) :
    P[j]? = some w ∧ j ≤ t := by
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_extract,
    Array.size_extract, Nat.sub_zero, Nat.zero_add] at h
  have hj' : ¬ (0 = j) := by omega
  simp only [hj', false_and, ite_false] at h
  split at h
  · exact ⟨h, by omega⟩
  · cases h

theorem rdW_of {P : Array Word} {x : Word} {j : Nat} {w : Word} (hx : x.toNat = j)
    (h : P[j]? = some w) : rdW P x = w := by
  simp [rdW, hx, h]

theorem mapM_range_succ {β : Type} {F : Nat → Option β} {k : Nat} {cs : List β}
    (h : (List.range (k + 1)).mapM F = some cs) :
    ∃ x xs, F 0 = some x ∧ (List.range k).mapM (fun j => F (j + 1)) = some xs ∧ cs = x :: xs := by
  rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map] at h
  cases h1 : F 0 with
  | none => simp [h1] at h
  | some x =>
    cases h2 : (List.range k).mapM (fun j => F (j + 1)) with
    | none =>
      have : List.mapM (F ∘ Nat.succ) (List.range k) = none := h2
      simp [h1, this] at h
    | some xs =>
      have : List.mapM (F ∘ Nat.succ) (List.range k) = some xs := h2
      simp [h1, this] at h
      exact ⟨x, xs, rfl, rfl, h.symm⟩

theorem decCIs_succ {a : Array Word} {dn : NIdx → Option ConLeche.Name} {off k : Nat}
    {cs : List IConstantInfo} (h : decCIs a dn off (k + 1) = some cs) :
    ∃ p ci cs', nat? a off = some p ∧ decCI a dn p = some ci ∧ decCIs a dn (off + 1) k = some cs' ∧
      cs = ci :: cs' := by
  obtain ⟨ci, cs', h0, hs, rfl⟩ := mapM_range_succ h
  simp only [Nat.add_zero] at h0
  cases h1 : nat? a off with
  | none => simp [h1] at h0
  | some p =>
    simp only [h1, Option.bind_eq_bind, Option.bind_some] at h0
    refine ⟨p, ci, cs', rfl, h0, ?_, rfl⟩
    simp only [decCIs]
    rw [← hs]
    congr 1; funext j; rw [Nat.add_right_comm, Nat.add_assoc]

theorem decCIs_zero {a : Array Word} {dn : NIdx → Option ConLeche.Name} {off : Nat}
    {cs : List IConstantInfo} (h : decCIs a dn off 0 = some cs) : cs = [] := by
  simp [decCIs] at h; exact h

theorem hd?_some {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  by_cases hl : w.toNat < 2 ^ 32
  · simp [hl] at h; exact ⟨w, hw, hl, h.symm⟩
  · simp [hl] at h

theorem decCV_type {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decE w := by
  simp only [decCV, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨x, -, y, -, z, hz, he⟩ := h
  cases Option.some.inj he
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some hz
  exact ⟨w, hw, hl, rfl⟩

theorem decCI_walk {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {ci : IConstantInfo}
    (h : decCI a dn p = some ci) :
    ∃ cv kw w, ci.toConstantVal = cv ∧ a[p]? = some kw ∧ a[p + 4]? = some w ∧
      w.toNat < 2 ^ 32 ∧ cv.type = decE w ∧
      ((kw = 5 ∧ ∃ mi rp ow cw rules, ci = .recInfo cv mi rp rules ∧ a[p + 7]? = some ow ∧
          a[p + 8]? = some cw ∧ decRules a ow.toNat cw.toNat = some rules) ∨
        (kw ≠ 5 ∧ ∀ v mi rp rules, ci ≠ .recInfo v mi rp rules)) := by
  simp only [decCI] at h
  cases hk : a[p]? with
  | none => simp [nat?, hk] at h
  | some kw =>
  simp only [nat?, hk, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  have hne : ∀ n, kw.toNat = n → n ≠ 5 → kw ≠ 5 := by
    intro n hn h5 e; subst e; exact h5 hn.symm
  generalize hn : kw.toNat = n at h
  rcases n with _ | _ | _ | _ | _ | _ | n
  all_goals
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  · obtain ⟨cv, hcv, he⟩ := h; cases Option.some.inj he
    obtain ⟨w, hw, hl, ht'⟩ := decCV_type hcv
    exact ⟨cv, kw, w, rfl, rfl, hw, hl, ht', .inr ⟨hne _ hn (by decide), fun _ _ _ _ e => by cases e⟩⟩
  · obtain ⟨cv, hcv, _, _, _, _, he⟩ := h; cases Option.some.inj he
    obtain ⟨w, hw, hl, ht'⟩ := decCV_type hcv
    exact ⟨cv, kw, w, rfl, rfl, hw, hl, ht', .inr ⟨hne _ hn (by decide), fun _ _ _ _ e => by cases e⟩⟩
  · obtain ⟨cv, hcv, he⟩ := h; cases Option.some.inj he
    obtain ⟨w, hw, hl, ht'⟩ := decCV_type hcv
    exact ⟨cv, kw, w, rfl, rfl, hw, hl, ht', .inr ⟨hne _ hn (by decide), fun _ _ _ _ e => by cases e⟩⟩
  · obtain ⟨cv, hcv, _, _, he⟩ := h; cases Option.some.inj he
    obtain ⟨w, hw, hl, ht'⟩ := decCV_type hcv
    exact ⟨cv, kw, w, rfl, rfl, hw, hl, ht', .inr ⟨hne _ hn (by decide), fun _ _ _ _ e => by cases e⟩⟩
  · obtain ⟨cv, hcv, _, _, _, _, he⟩ := h; cases Option.some.inj he
    obtain ⟨w, hw, hl, ht'⟩ := decCV_type hcv
    exact ⟨cv, kw, w, rfl, rfl, hw, hl, ht', .inr ⟨hne _ hn (by decide), fun _ _ _ _ e => by cases e⟩⟩
  · obtain ⟨cv, hcv, mi, _, rp, _, off, ho, cnt, hc, rules, hr, he⟩ := h; cases Option.some.inj he
    obtain ⟨w, hw, hl, ht'⟩ := decCV_type hcv
    have h5 : kw = 5 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    cases h7 : a[p + 7]? with
    | none => rw [h7] at ho; cases ho
    | some ow =>
    cases h8 : a[p + 8]? with
    | none => rw [h8] at hc; cases hc
    | some cw =>
    rw [h7] at ho; rw [h8] at hc
    cases Option.some.inj ho; cases Option.some.inj hc
    exact ⟨cv, kw, w, rfl, rfl, hw, hl, ht', .inl ⟨h5, mi, rp, ow, cw, rules, rfl, rfl, rfl, hr⟩⟩
  · cases h

theorem decRule_rhs {a : Array Word} {q : Nat} {r : IRecRule} (h : decRule a q = some r) :
    ∃ w, a[q + 8]? = some w ∧ w.toNat < 2 ^ 32 ∧ r.rhs = decE w := by
  unfold decRule at h
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  rw [Option.bind_eq_some_iff] at h; obtain ⟨n0, -, h⟩ := h
  rcases n0 with _ | _ | n0
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, z, hz, _, _, _, _, he⟩ := h
    cases Option.some.inj he
    obtain ⟨w, hw, hl, rfl⟩ := hd?_some hz
    exact ⟨w, hw, hl, rfl⟩
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, z, hz, _, _, _, _, he⟩ := h
    cases Option.some.inj he
    obtain ⟨w, hw, hl, rfl⟩ := hd?_some hz
    exact ⟨w, hw, hl, rfl⟩
  · simp at h

theorem decRules_facts {a : Array Word} {off cnt : Nat} {rules : List IRecRule}
    (h : decRules a off cnt = some rules) :
    rules.length = cnt ∧ ∀ q (hq : q < rules.length), ∃ w, a[off + 11 * q + 8]? = some w ∧
      w.toNat < 2 ^ 32 ∧ rules[q].rhs = decE w := by
  have hl := mapM_opt_length _ _ _ h
  simp only [List.length_range] at hl
  refine ⟨hl, fun q hq => ?_⟩
  have := mapM_opt_get _ _ _ h q (by simp; omega)
  simp only [List.getElem_range] at this
  exact decRule_rhs this

theorem idx11 (ow : Word) (q : Nat) (h : ow.toNat + 11 * q + 8 < 2 ^ 64) :
    (ow + 11 * (0 + UInt64.ofNat q) + 8).toNat = ow.toNat + 11 * q + 8 := by
  have hq : (UInt64.ofNat q).toNat = q := by simp; omega
  rw [UInt64.zero_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, hq]
  have : (11 : UInt64).toNat = 11 := rfl
  have : (8 : UInt64).toNat = 8 := rfl
  simp only [*]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem toNat_rec (r : Word) (hr : r.toNat < 2 ^ 59) : (1 + 8 * r).toNat = 1 + 8 * r.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  have : (1 : UInt64).toNat = 1 := rfl
  have : (8 : UInt64).toNat = 8 := rfl
  simp only [*]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rdW_dw0 (D : Array Word) (r : Word) (hr : r.toNat < 2 ^ 59) :
    rdW D (1 + 8 * r) = dw D r.toNat 0 := by
  simp only [rdW, dw, toNat_rec r hr, Nat.add_zero]

theorem rdW_dw (D : Array Word) (r j : Word) (hr : r.toNat < 2 ^ 59) (hj : j.toNat < 8) :
    rdW D (1 + 8 * r + j) = dw D r.toNat j.toNat := by
  have : (1 + 8 * r + j).toNat = 1 + 8 * r.toNat + j.toNat := by
    rw [UInt64.toNat_add, toNat_rec r hr]; exact Nat.mod_eq_of_lt (by omega)
  simp only [rdW, dw, this]

end L.Checker
