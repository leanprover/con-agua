module

import ConAgua.Arena.IndLibSpec
public import ConAgua.Front.StateDR
import ConRon.Bridge.Grind

@[expose] public section

/-!
# Decoding facts for the hoist's walk refinement (lane `front4`)

What `HoistWalkRef.lean` reads of the pool's records: an inductive block's member pointers
(`decCIs`), a member's kind, type and recursor rules (`decCI`, `decCV`, `decRules`), the words of
`trunc P t` as words of `P` (away from word `0`), and a `DECL` record's words (`dw`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind


namespace L.Checker

/-! ## Block decoding -/

theorem trunc_get {P : Array Word} {t j : Nat} {w : Word} (h : (trunc P t)[j]? = some w) (hj : 0 < j) :
    P[j]? = some w ∧ j ≤ t := by
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_extract,
    Array.size_extract, Nat.sub_zero, Nat.zero_add] at h
  have hj' : ¬ (0 = j) := by omega
  simp only [hj', ite_false] at h
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

theorem decCIs_succ {a : Array Word} {off k : Nat}
    {cs : List IConstantInfo} (h : decCIs a off (k + 1) = some cs) :
    ∃ p ci cs', nat? (aread a) off = some p ∧ decCI (aread a) p = some ci ∧ decCIs a (off + 1) k = some cs' ∧
      cs = ci :: cs' := by
  obtain ⟨ci, cs', h0, hs, rfl⟩ := mapM_range_succ h
  simp only [Nat.add_zero] at h0
  cases h1 : nat? (aread a) off with
  | none => simp [h1] at h0
  | some p =>
    simp only [h1, Option.bind_eq_bind, Option.bind_some] at h0
    refine ⟨p, ci, cs', rfl, h0, ?_, rfl⟩
    simp only [decCIs]
    rw [← hs]
    congr 1; funext j; rw [Nat.add_right_comm, Nat.add_assoc]

theorem decCIs_zero {a : Array Word} {off : Nat}
    {cs : List IConstantInfo} (h : decCIs a off 0 = some cs) : cs = [] := by
  simp [decCIs] at h; exact h

theorem hd?_some {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? (aread a) i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  by_cases hl : w.toNat < 2 ^ 32
  · simp [hl] at h; exact ⟨w, hw, hl, h.symm⟩
  · simp [hl] at h

theorem decCV_type {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV (aread a) q = some cv) :
    ∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decE w := by
  simp only [decCV, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨x, -, y, -, z, hz, he⟩ := h
  cases Option.some.inj he
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some hz
  exact ⟨w, hw, hl, rfl⟩

theorem decCI_walk {a : Array Word} {p : Nat} {ci : IConstantInfo}
    (h : decCI (aread a) p = some ci) :
    ∃ cv kw w, ci.toConstantVal = cv ∧ a[p]? = some kw ∧ a[p + 4]? = some w ∧
      w.toNat < 2 ^ 32 ∧ cv.type = decE w ∧
      ((kw = 5 ∧ ∃ mi rp k ow cw rules, ci = .recInfo cv mi rp k rules ∧ a[p + 7]? = some ow ∧
          a[p + 8]? = some cw ∧ decRules (aread a) ow.toNat cw.toNat = some rules) ∨
        (kw ≠ 5 ∧ ∀ v mi rp k rules, ci ≠ .recInfo v mi rp k rules)) := by
  sorry

theorem decRule_rhs {a : Array Word} {q : Nat} {r : IRecRule} (h : decRule (aread a) q = some r) :
    ∃ w, a[q + 8]? = some w ∧ w.toNat < 2 ^ 32 ∧ r.rhs = decE w := by
  unfold decRule at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨n0, -, h⟩ := h
  have fin : ∀ z (hz : hd? (aread a) (q + 8) = some z), r.rhs = z →
      ∃ w, a[q + 8]? = some w ∧ w.toNat < 2 ^ 32 ∧ r.rhs = decE w := by
    intro z hz he; obtain ⟨w, hw, hl, rfl⟩ := hd?_some hz; exact ⟨w, hw, hl, he⟩
  rcases n0 with _ | _ | _ | n0 <;> simp only [Option.bind_eq_some_iff] at h
  · obtain ⟨_, -, _, -, _, -, z, hz, he⟩ := h; cases Option.some.inj he; exact fin z hz rfl
  · obtain ⟨_, -, _, -, _, -, _, -, _, -, z, hz, he⟩ := h; cases Option.some.inj he; exact fin z hz rfl
  · obtain ⟨_, -, _, -, _, -, _, -, z, hz, he⟩ := h; cases Option.some.inj he; exact fin z hz rfl
  · simp at h

theorem decRules_facts {a : Array Word} {off cnt : Nat} {rules : List IRecRule}
    (h : decRules (aread a) off cnt = some rules) :
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

end L.Checker
