import ConAgua.Arena.DefEqLeaves

/-!
# Refinements of `DefEq.lean`'s small leaves, continued

`er_slice_eq` (a loop, as `limbs_eq`'s in `Store.lean`), `nat_pred`, `lit_eq`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `er_slice_eq` -/

theorem erSliceEqLoop_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n erSliceEqLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if eqW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 4)
        then 1 else 0]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := erSliceEqLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, ih] <;> finish

theorem erSliceEqLoop_step_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) erSliceEqLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if eqW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 4)
        then 1 else 0]; ⊤⦄ :=
  Triple.step_exec (erSliceEqLoop_spec p (n + 1) s₀)

theorem erSliceEq_spec (p : Prog) (hp : p.lookup "er_slice_eq" = some erSliceEqL) (n : Nat)
    (s₀ : St) (o1 n1 o2 n2 : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "er_slice_eq" [o1, n1, o2, n2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      r = [if n1 = n2 ∧ eqW (s₀.mem.arr64 EREC) o1 o2 n1 0 = true then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erSliceEqL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, erSliceEqLoop_step_spec p n] <;> finish

theorem mapM_get {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {l : List β}, xs.mapM f = some l →
      l.length = xs.length ∧ ∀ k (hk : k < xs.length), f xs[k] = l[k]?
  | [], l, h => by simp at h; subst h; simp
  | x :: xs, l, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hg⟩ := mapM_get hys
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => simpa using hy
    | succ k => simpa using hg k (by simpa using hk)

/-- A decoded handle slice: its length, and each element a word below `2^32`. -/
theorem hslice?_get {k : IdxKind} {a : Array Word} {o n : Nat} {l : List (Idx k)}
    (h : hslice? a o n = some l) :
    l.length = n ∧ ∀ j, j < n → ∃ w, a[o + j]? = some w ∧ w.toNat < 2 ^ 32 ∧ l[j]? = some (decI w) := by
  obtain ⟨hl, hg⟩ := mapM_get h
  simp only [List.length_range] at hl
  refine ⟨hl, fun j hj => ?_⟩
  have := hg j (by simpa using hj)
  simp only [List.getElem_range] at this
  cases e : a[o + j]? with
  | none => simp [hd?, e] at this; omega
  | some w =>
    simp only [hd?, e, Option.bind_eq_bind, Option.bind_some] at this
    by_cases hw : w.toNat < 2 ^ 32
    · simp only [hw, ↓reduceIte] at this; exact ⟨w, rfl, hw, this.symm⟩
    · simp only [hw, ↓reduceIte] at this; have := List.getElem?_eq_none_iff.mp this.symm; omega

/-- **`er_slice_eq` decides the equality of two decoded handle slices of the record pool** (the
twin's `cvc.levelParams = cvT.levelParams` in `structEtaCertWith`). -/
@[refines_part ConRon.Arena.structEtaCertWith "level-parameter lists equal"]
theorem erSliceEq_refines (p : Prog) (hp : p.lookup "er_slice_eq" = some erSliceEqL) (n : Nat)
    (s₀ : St) (o1 n1 o2 n2 : Word) {k : IdxKind} (l1 l2 : List (Idx k))
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 63)
    (h1 : hslice? (erecP s₀.mem) o1.toNat n1.toNat = some l1)
    (h2 : hslice? (erecP s₀.mem) o2.toNat n2.toNat = some l2) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "er_slice_eq" [o1, n1, o2, n2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ decBool r = decide (l1 = l2) ∧ ResH r; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hm, hloc, hr⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (erSliceEq_spec p hp n s₀ o1 n1 o2 n2)
  subst hs0
  refine ⟨hm, hloc, ?_, by rw [hr]; unfold ResH; split <;> first | exact hw0 | exact hw1⟩
  rw [hr, decBool]
  simp only [List.headD_cons]
  rw [ite_bne]
  obtain ⟨hl1, hg1⟩ := hslice?_get h1
  obtain ⟨hl2, hg2⟩ := hslice?_get h2
  have hext := erecP_ext s.mem
  have hb : ∀ {o c : Nat} {l : List (Idx k)}, hslice? (erecP s.mem) o c = some l → 0 < c →
      o + c < 2 ^ 64 := by
    intro o c l h hc
    obtain ⟨-, hg⟩ := hslice?_get h
    obtain ⟨w, hw, -, -⟩ := hg (c - 1) (by omega)
    have := hext _ _ hw
    have : o + (c - 1) < (s.mem.arr64 EREC).size := by
      rcases Nat.lt_or_ge (o + (c - 1)) (s.mem.arr64 EREC).size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at this
    omega
  congr 1
  apply propext
  constructor
  · rintro ⟨rfl, he⟩
    rcases Nat.eq_zero_or_pos n1.toNat with hz | hz
    · apply List.ext_getElem?; intro j
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have hb1 := hb h1 hz
    have hb2 := hb h2 hz
    rw [eqW_iff _ _ _ _ _ hb1 hb2] at he
    apply List.ext_getElem?; intro j
    by_cases hj : j < n1.toNat
    · obtain ⟨w1, hw1, -, he1⟩ := hg1 j hj
      obtain ⟨w2, hw2, -, he2⟩ := hg2 j hj
      have := he j (by simp) hj
      rw [hext _ _ hw1, hext _ _ hw2] at this
      simp only [Option.getD_some] at this
      rw [he1, he2, this]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro heq
    subst heq
    have hn : n1 = n2 := UInt64.toNat_inj.mp (hl1.symm.trans hl2)
    subst hn
    refine ⟨rfl, ?_⟩
    rcases Nat.eq_zero_or_pos n1.toNat with hz | hz
    · exact eqW_end _ _ _ _ _ (by simp [UInt64.lt_iff_toNat_lt, hz])
    rw [eqW_iff _ _ _ _ _ (hb h1 hz) (hb h2 hz)]
    intro j _ hj
    obtain ⟨w1, hw1, hl1', he1⟩ := hg1 j hj
    obtain ⟨w2, hw2, hl2', he2⟩ := hg2 j hj
    rw [he1] at he2
    have := decI_inj hl1' hl2' (Option.some.inj he2)
    rw [hext _ _ hw1, hext _ _ hw2, this]

end L.Arena
