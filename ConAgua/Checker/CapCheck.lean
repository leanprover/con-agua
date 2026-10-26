import ConAgua.Checker.Entry

/-!
# `cap_check()` checks the capacities (lane `pipeline`)

`cap_check()`'s body is a `foldr` over the word arrays `0‥wordArrays - 1` of
`if capCond b { abort }` (`2^62 ≤ len(b.u64)`; for a slot array, wrapping,
`2^61 - consMinWords ≤ len - consMinWords`: below `consMinWords` words or from `2^61` on), then `if len(CTL.u64) < ctlMin { abort }`, the same for
`len(DECL.u64) == 0`, `len(DLP.u64) == 0`, and `return 0`
(`capCheckBody`, `Checker/Entry.lean`). A run that returns leaves the state alone, and every
word array's length *as a word* is below `2^62` (`CapsW`). `len64` is the size modulo `2^64`, so
the actual sizes are below `2^62` only for sizes below `2^64` (`WordsFit`, which every memory the
x64 layout can hold meets): then `CapsOK`. The proof is by induction over the list, on runs
(`capFold_run`), not by unrolling the 388 branches.
-/

namespace L.Checker

open L L.Arena
open Std.WP
open scoped Lean.Order

/-- **The capacities `check` needs**: every word array the checker names is shorter than `2^62`
words (a slot array at least `consMinWords` and shorter than `2^61`), `CTL` has at least `ctlMin`
words, `DECL` (67) and `DLP` (68) are not empty, and the pool's tier arrays (0, 256) have fewer
than `2^40` words. -/
def CapsOK (m : Mem) : Prop :=
  (∀ a < wordArrays, (m.arr64 a).size < 2 ^ 62 ∧
    (a ∈ slotArrs → consMinWords ≤ (m.arr64 a).size ∧ (m.arr64 a).size < 2 ^ 61)) ∧
    ctlMin ≤ (m.arr64 CTL).size ∧
    1 ≤ (m.arr64 67).size ∧ 1 ≤ (m.arr64 68).size ∧ (m.arr64 0).size < 2 ^ 40 ∧
    (m.arr64 256).size < 2 ^ 40

/-- What `cap_check` observes: the lengths as words (`len64`, the size modulo `2^64`). -/
def CapsW (m : Mem) : Prop :=
  (∀ a < wordArrays, (m.len64 a).toNat < 2 ^ 62 ∧
    (a ∈ slotArrs → consMinWords ≤ (m.len64 a).toNat ∧ (m.len64 a).toNat < 2 ^ 61)) ∧
    ctlMin ≤ (m.arr64 CTL).size ∧
    m.len64 67 ≠ 0 ∧ m.len64 68 ≠ 0 ∧ (m.len64 0).toNat < 2 ^ 40 ∧ (m.len64 256).toNat < 2 ^ 40

/-- Every word array the checker names has a size that is a word. -/
def WordsFit (m : Mem) : Prop := ∀ a < wordArrays, (m.arr64 a).size < 2 ^ 64

theorem CapsW.capsOK {m : Mem} (h : CapsW m) (hf : WordsFit m) : CapsOK m := by
  have hsz : ∀ a < wordArrays, (m.len64 a).toNat = (m.arr64 a).size := fun a ha => by
    simp only [Mem.len64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (hf a ha)
  have hne : ∀ a < wordArrays, m.len64 a ≠ 0 → 1 ≤ (m.arr64 a).size := fun a ha h => by
    rw [← hsz a ha]
    exact Nat.one_le_iff_ne_zero.2 (fun h0 => h (UInt64.toNat_inj.1 (by simpa using h0)))
  refine ⟨fun a ha => ?_, h.2.1, hne 67 (by decide) h.2.2.1, hne 68 (by decide) h.2.2.2.1, ?_, ?_⟩
  · rw [← hsz a ha]; exact h.1 a ha
  · rw [← hsz 0 (by decide)]; exact h.2.2.2.2.1
  · rw [← hsz 256 (by decide)]; exact h.2.2.2.2.2

theorem run_throw' {α : Type} (e : Err) (s : St) : StateT.run (throw e : M α) s = .error e := rfl

theorem error_bind' {α β : Type} (e : Err) (f : α → Except Err β) :
    (Except.error e >>= f) = .error e := rfl

theorem error_map' {α β : Type} (e : Err) (f : α → β) : (f <$> (Except.error e : Except Err α)) = .error e := rfl

/-- One array's check (the `foldr`'s step). -/
def capStep (b : Nat) (s : Stmt) : Stmt :=
  .seq (.ite (capCond b) (.abort (.const R_CAP_REGION)) .skip) s

/-- The `CTL`, `DECL`, `DLP` checks and the return. -/
def capTail : Stmt :=
  .seq (.ite (.cmp .ult (.len64 CTL) (.const (UInt64.ofNat ctlMin))) (.abort (.const R_CAP_REGION)) .skip)
    (.seq (.ite (.cmp .eq (.len64 67) (.const 0)) (.abort (.const R_CAP_REGION)) .skip)
      (.seq (.ite (.cmp .eq (.len64 68) (.const 0)) (.abort (.const R_CAP_REGION)) .skip)
        (.seq (.ite (.cmp .ule (.const 1099511627776) (.len64 0)) (.abort (.const R_CAP_REGION)) .skip)
          (.seq (.ite (.cmp .ule (.const 1099511627776) (.len64 256)) (.abort (.const R_CAP_REGION)) .skip)
            (.ret [.const 0])))))

/-- A run of the checks of the arrays `l`, then `t`, that returns: every array of `l` has a
length below `2^62` as a word, and the run is `t`'s. -/
theorem capFold_run {p : Prog} {k : Stmt → M Sig} (t : Stmt) :
    ∀ (l : List Nat) (s : St) (r : Sig) (s' : St), (step p k (l.foldr capStep t)).run s = .ok (r, s') →
      (∀ b ∈ l, (s.mem.len64 b).toNat < 2 ^ 62 ∧
        (b ∈ slotArrs → consMinWords ≤ (s.mem.len64 b).toNat ∧ (s.mem.len64 b).toNat < 2 ^ 61)) ∧
        (step p k t).run s = .ok (r, s') := by
  intro l
  induction l with
  | nil => intro s r s' h; exact ⟨fun _ h => absurd h List.not_mem_nil, h⟩
  | cons b l ih =>
    intro s r s' h
    by_cases hsl : b ∈ slotArrs
    · simp [List.foldr_cons, capStep, capCond, hsl, step, evalC, evalE, Cmp.eval, BinOp.eval] at h
      by_cases hb : capLo ≤ s.mem.len64 b - capMin
      · simp [hb, run_throw', error_bind'] at h
      · simp [hb] at h
        obtain ⟨h1, h2⟩ := ih s r s' h
        refine ⟨fun c hc => ?_, h2⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · simp only [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hb
          have := (s.mem.len64 c).toNat_lt
          have em : capMin.toNat = consMinWords := rfl
          have el : capLo.toNat = 2 ^ 61 - consMinWords := rfl
          have ec : consMinWords = 18 := rfl
          rw [el] at hb
          by_cases h17 : consMinWords ≤ (s.mem.len64 c).toNat
          · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, em]; exact h17), em] at hb
            exact ⟨by omega, fun _ => ⟨h17, by omega⟩⟩
          · rw [UInt64.toNat_sub, em] at hb; omega
        · exact h1 c hc
    · simp [List.foldr_cons, capStep, capCond, hsl, step, evalC, evalE, Cmp.eval] at h
      by_cases hb : (4611686018427387904 : Word) ≤ s.mem.len64 b
      · simp [hb, run_throw', error_bind'] at h
      · simp [hb] at h
        obtain ⟨h1, h2⟩ := ih s r s' h
        refine ⟨fun c hc => ?_, h2⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · simp only [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hb
          exact ⟨by simpa using hb, fun h => absurd h hsl⟩
        · exact h1 c hc

theorem capTail_run {p : Prog} {k : Stmt → M Sig} (s : St) (r : Sig) (s' : St)
    (h : (step p k capTail).run s = .ok (r, s')) :
    ctlMin ≤ (s.mem.arr64 CTL).size ∧ s.mem.len64 67 ≠ 0 ∧ s.mem.len64 68 ≠ 0 ∧
      (s.mem.len64 0).toNat < 2 ^ 40 ∧ (s.mem.len64 256).toNat < 2 ^ 40 ∧ r = .ret [0] ∧ s' = s := by
  simp [capTail, step, evalC, evalE, evalArgs, Cmp.eval] at h
  by_cases hc : s.mem.len64 CTL < UInt64.ofNat ctlMin
  · simp [hc, run_throw', error_bind'] at h
  by_cases hd : s.mem.len64 67 = 0
  · simp [hc, hd, run_throw', error_bind'] at h
  by_cases hq : s.mem.len64 68 = 0
  · simp [hc, hd, hq, run_throw', error_bind'] at h
  by_cases hp : (1099511627776 : Word) ≤ s.mem.len64 0
  · simp [hc, hd, hq, hp, run_throw', error_bind'] at h
  by_cases hp1 : (1099511627776 : Word) ≤ s.mem.len64 256
  · simp [hc, hd, hq, hp, hp1, run_throw', error_bind'] at h
  · simp [hc, hd, hq, hp, hp1] at h
    change Except.ok _ = _ at h
    cases h
    have hp' : (s.mem.len64 0).toNat < 2 ^ 40 := by
      simp only [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hp; exact hp
    have hp1' : (s.mem.len64 256).toNat < 2 ^ 40 := by
      simp only [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hp1; exact hp1
    refine ⟨?_, hd, hq, hp', hp1', rfl, rfl⟩
    simp only [UInt64.not_lt, UInt64.le_iff_toNat_le, Mem.len64, UInt64.toNat_ofNat'] at hc
    have : ctlMin % 2 ^ 64 = ctlMin := by simp [ctlMin]
    rw [this] at hc
    exact Nat.le_trans hc (Nat.mod_le _ _)

/-- **`cap_check()` observes the capacities**: a run that returns leaves the state alone, and
the lengths as words meet `CapsW`. -/
theorem capCheck_specW (p : Prog) (hp : p.lookup "cap_check" = some capCheckL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "cap_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ CapsW s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  rw [invoke_eq _ hp] at hrun
  cases n with
  | zero => simp [callFn, exec, run_throw', error_map'] at hrun
  | succ n =>
    simp only [callFn, exec, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set] at hrun
    cases hb : (step p (exec p n) capCheckL.body).run { s with loc := Locals.init [] } with
    | error e => rw [hb] at hrun; cases hrun
    | ok q =>
      obtain ⟨r₁, s₁⟩ := q
      rw [hb] at hrun
      simp at hrun
      obtain ⟨-, rfl⟩ := hrun
      have hb' : (step p (exec p n) ((List.range wordArrays).foldr capStep capTail)).run
          { s with loc := Locals.init [] } = .ok (r₁, s₁) := hb
      obtain ⟨h1, h2⟩ := capFold_run capTail _ _ _ _ hb'
      obtain ⟨h3, h4, h5, h6, h7, -, rfl⟩ := capTail_run _ _ _ h2
      exact ⟨rfl, rfl, fun a ha => h1 a (List.mem_range.2 ha), h3, h4, h5, h6, h7⟩

/-- **`cap_check()` checks the capacities**: a run that returns leaves the state alone, and on a
memory whose word arrays' sizes are words (`WordsFit`) the capacities are `CapsOK`. -/
theorem capCheck_spec (p : Prog) (hp : p.lookup "cap_check" = some capCheckL) (n : Nat) (s₀ : St)
    (hf : WordsFit s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "cap_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ CapsOK s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hrun (capCheck_specW p hp n s₀)
  exact ⟨h1, h2, h3.capsOK hf⟩

end L.Checker
