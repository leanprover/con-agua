import ConRon.Arena.Frontend.NatOpGround
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The twin's worklist closure, characterised (lane `front4`)

`hoistClosure ds idx i fuel target stack` pops a record, skips it when it is done, marks it `i` and
pushes the records its constants are first declared at after `i` (`pushOne`). Here: for any set
`N` of records that is **closed** (each successor of a member is a member or already marked in the
initial map `T₀`) and whose members' constants the twin computes (`usedConsts` succeeds, in the
same state), the twin succeeds (`closure_twin`); its result marks only members, marks every
record of the stack, and is closed; and when every member is reachable from the start `j`
through members, the result is exactly `T₀` plus `N ↦ i` (`closure_exact`). The L side
(`HoistClosureL.lean`) produces such an `N`: the records L marks.

All of `T₀`'s targets are `≤ i` (targets only ever move to the current operation, and those only
grow), so "done" is "has an entry".
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Checker.HoistTwin

variable (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (i : Nat)

/-- `m` is a successor of `k` (constants `D k`): `pushOne`'s filter. -/
def Succ (D : Nat → List NIdx) (k m : Nat) : Prop := ∃ n ∈ D k, idx[n]? = some m ∧ i < m ∧ m ≠ k

theorem mem_pushOne (k : Nat) :
    ∀ (ns : List NIdx) (stack : List Nat) (x : Nat),
      x ∈ hoistClosure.pushOne idx i k ns stack ↔ x ∈ stack ∨ ∃ n ∈ ns, idx[n]? = some x ∧ i < x ∧ x ≠ k
  | [], stack, x => by simp [hoistClosure.pushOne]
  | n :: ns, stack, x => by
    unfold hoistClosure.pushOne
    split
    · rename_i m hm
      rw [mem_pushOne k ns]
      by_cases hc : (m > i && m != k) = true
      · rw [ite_eq_left hc]
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
        constructor
        · rintro (h | ⟨n', hn', h1, h2⟩)
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr ⟨n, List.mem_cons_self, hm, hc.1, hc.2⟩
            · exact Or.inl h
          · exact Or.inr ⟨n', List.mem_cons_of_mem _ hn', h1, h2⟩
        · rintro (h | ⟨n', hn', h1, h2⟩)
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.mp hn' with rfl | hn'
            · rw [hm] at h1; cases h1; exact Or.inl List.mem_cons_self
            · exact Or.inr ⟨n', hn', h1, h2⟩
      · rw [ite_eq_right hc]
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
          Decidable.not_not] at hc
        constructor
        · rintro (h | ⟨n', hn', h1, h2⟩)
          · exact Or.inl h
          · exact Or.inr ⟨n', List.mem_cons_of_mem _ hn', h1, h2⟩
        · rintro (h | ⟨n', hn', h1, h2⟩)
          · exact Or.inl h
          · rcases List.mem_cons.mp hn' with rfl | hn'
            · rw [hm] at h1; cases h1; exact absurd (hc (by omega)) h2.2
            · exact Or.inr ⟨n', hn', h1, h2⟩
    · rename_i hm
      rw [mem_pushOne k ns]
      constructor
      · rintro (h | ⟨n', hn', h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨n', List.mem_cons_of_mem _ hn', h1, h2⟩
      · rintro (h | ⟨n', hn', h1, h2⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hn' with rfl | hn'
          · rw [hm] at h1; cases h1
          · exact Or.inr ⟨n', hn', h1, h2⟩

/-- An element of the stack is done or survives `hoistDropDone`. -/
theorem mem_dropDone (T : Std.HashMap Nat Nat) :
    ∀ (stack : List Nat) (x : Nat), x ∈ stack → hoistDone T x i = true ∨ x ∈ hoistDropDone T i stack
  | [], _, h => by simp at h
  | k :: stack, x, h => by
    unfold hoistDropDone
    by_cases hk : hoistDone T k i = true
    · rw [ite_eq_left hk]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hk
      · exact mem_dropDone T stack x h
    · rw [ite_eq_right hk]; exact Or.inr h

/-- Done is "has an entry" when every target is `≤ i`. -/
theorem hoistDone_iff (T : Std.HashMap Nat Nat) (hT : ∀ (k t : Nat), T[k]? = some t → t ≤ i) (k : Nat) :
    hoistDone T k i = true ↔ (T[k]?).isSome := by
  unfold hoistDone
  cases h : T[k]? with
  | none => simp
  | some t => simp [hT k t h]

/-- The members of `N` not yet marked in `T` (the fuel the twin needs). -/
noncomputable def pend (N : Nat → Prop) (T : Std.HashMap Nat Nat) : Nat :=
  open Classical in ((List.range ds.size).filter fun k => decide (N k) && (T[k]?).isNone).length

theorem pend_insert (N : Nat → Prop) (T : Std.HashMap Nat Nat) (k : Nat) (hk : k < ds.size)
    (hN : N k) (hT : (T[k]?).isNone) : pend ds N (T.insert k i) + 1 = pend ds N T := by
  classical
  unfold pend
  have hins : ∀ x : Nat, (T.insert k i)[x]? = if k = x then some i else T[x]? := by
    intro x; simp [Std.HashMap.getElem?_insert]
  have key : ∀ (l : List Nat), l.Nodup → k ∈ l →
      (l.filter fun x => decide (N x) && ((T.insert k i)[x]?).isNone).length + 1 =
        (l.filter fun x => decide (N x) && (T[x]?).isNone).length := by
    intro l hl hkl
    induction l with
    | nil => simp at hkl
    | cons y l ih =>
      have hrest : ∀ (l' : List Nat), k ∉ l' →
          (l'.filter fun x => decide (N x) && ((T.insert k i)[x]?).isNone) =
            (l'.filter fun x => decide (N x) && (T[x]?).isNone) := by
        intro l' hnot
        apply List.filter_congr
        intro x hx
        have : k ≠ x := fun e => hnot (e ▸ hx)
        rw [hins, ite_eq_right this]
      rcases List.mem_cons.mp hkl with rfl | hkl'
      · have hnot : k ∉ l := (List.nodup_cons.mp hl).1
        rw [List.filter_cons, List.filter_cons, hrest l hnot, hins, ite_eq_left rfl]
        simp [hN, hT]
      · have hyk : k ≠ y := fun e => (List.nodup_cons.mp hl).1 (e ▸ hkl')
        have ih' := ih (List.nodup_cons.mp hl).2 hkl'
        rw [List.filter_cons, List.filter_cons, hins y, ite_eq_right hyk]
        split <;> (try simp only [List.length_cons]) <;> omega
  exact key _ (List.nodup_range) (List.mem_range.mpr hk)

theorem pend_pos (N : Nat → Prop) (T : Std.HashMap Nat Nat) (k : Nat) (hk : k < ds.size)
    (hN : N k) (hT : (T[k]?).isNone) : 0 < pend ds N T := by
  have := pend_insert ds 0 N T k hk hN hT
  omega

/-- What the closure's run keeps: only members get marked, `i`. -/
def Ext (T₀ : Std.HashMap Nat Nat) (N : Nat → Prop) (T : Std.HashMap Nat Nat) : Prop :=
  ∀ k : Nat, T[k]? = T₀[k]? ∨ (N k ∧ T[k]? = some i)

theorem run_bind {α β : Type} (x : AM α) (f : α → AM β) (a : AState) :
    (x >>= f).run a = (match x.run a with
      | .ok (v, a') => (f v).run a'
      | .error e => .error e) := by
  simp only [StateT.run_bind]
  cases x.run a <;> rfl

/-- **The twin's closure on a closed set** `N`. -/
theorem closure_twin (a : AState) (D : Nat → List NIdx) (N : Nat → Prop) (T₀ : Std.HashMap Nat Nat)
    (hT₀ : ∀ (k t : Nat), T₀[k]? = some t → t ≤ i)
    (hN : ∀ k : Nat, N k → T₀[k]? = none ∧ ∃ h : k < ds.size,
      (IDeclaration.usedConsts ds[k]).run a = .ok ((D k).toArray, a))
    (hcl : ∀ k : Nat, N k → ∀ m : Nat, Succ idx i D k m → N m ∨ (T₀[m]?).isSome) :
    ∀ (fuel : Nat) (T : Std.HashMap Nat Nat) (S : List Nat),
      Ext i T₀ N T → (∀ x ∈ S, N x ∨ (T[x]?).isSome) →
      (∀ k : Nat, N k → (T[k]?).isSome → ∀ m : Nat, Succ idx i D k m → (T[m]?).isSome ∨ m ∈ S) →
      pend ds N T ≤ fuel →
      ∃ T', (hoistClosure ds idx i fuel T S).run a = .ok (T', a) ∧ Ext i T₀ N T' ∧
        (∀ x ∈ S, (T'[x]?).isSome) ∧
        (∀ k : Nat, N k → (T'[k]?).isSome → ∀ m : Nat, Succ idx i D k m → (T'[m]?).isSome) ∧
        (∀ k : Nat, (T[k]?).isSome → T'[k]? = T[k]?) := by
  -- every map on the way has its targets `≤ i`
  have hle : ∀ T : Std.HashMap Nat Nat, Ext i T₀ N T → ∀ (k t : Nat), T[k]? = some t → t ≤ i := by
    intro T hE k t h
    rcases hE k with e | ⟨-, e⟩
    · exact hT₀ k t (e ▸ h)
    · rw [e] at h; cases h; exact Nat.le_refl _
  -- an entry of `T₀` stays
  have hkeep : ∀ T : Std.HashMap Nat Nat, Ext i T₀ N T → ∀ x : Nat, (T₀[x]?).isSome → T[x]? = T₀[x]? := by
    intro T hE x hx
    rcases hE x with e | ⟨hn, -⟩
    · exact e
    · rw [(hN x hn).1] at hx; cases hx
  intro fuel
  induction fuel with
  | zero =>
    intro T S hE hS hC hp
    rw [hoistClosure.eq_def]
    simp only
    cases hd : hoistDropDone T i S with
    | nil =>
      refine ⟨T, rfl, hE, ?_, ?_, fun _ _ => rfl⟩
      · intro x hx
        rcases mem_dropDone i T S x hx with h | h
        · exact (hoistDone_iff i T (hle T hE) x).mp h
        · rw [hd] at h; cases h
      · intro k hk hkT m hm
        rcases hC k hk hkT m hm with h | h
        · exact h
        · rcases mem_dropDone i T S m h with h | h
          · exact (hoistDone_iff i T (hle T hE) m).mp h
          · rw [hd] at h; cases h
    | cons k rest =>
      exfalso
      have hk : k ∈ S := hoistDropDone_sub T i (by rw [hd]; exact List.mem_cons_self)
      have hnd := hoistDropDone_head T i hd
      have hnone0 : T[k]? = none := by
        cases h2 : T[k]? with
        | none => rfl
        | some t =>
          have := (hoistDone_iff i T (hle T hE) k).mpr (by rw [h2]; rfl)
          rw [hnd] at this; cases this
      have hnone : (T[k]?).isNone := by rw [hnone0]; rfl
      have hNk : N k := by
        rcases hS k hk with h | h
        · exact h
        · rw [hnone0] at h; cases h
      have := pend_pos ds N T k (hN k hNk).2.1 hNk hnone
      omega
  | succ f ih =>
    intro T S hE hS hC hp
    rw [hoistClosure.eq_def]
    simp only
    cases hd : hoistDropDone T i S with
    | nil =>
      refine ⟨T, rfl, hE, ?_, ?_, fun _ _ => rfl⟩
      · intro x hx
        rcases mem_dropDone i T S x hx with h | h
        · exact (hoistDone_iff i T (hle T hE) x).mp h
        · rw [hd] at h; cases h
      · intro k hk hkT m hm
        rcases hC k hk hkT m hm with h | h
        · exact h
        · rcases mem_dropDone i T S m h with h | h
          · exact (hoistDone_iff i T (hle T hE) m).mp h
          · rw [hd] at h; cases h
    | cons k rest =>
      have hk : k ∈ S := hoistDropDone_sub T i (by rw [hd]; exact List.mem_cons_self)
      have hnd := hoistDropDone_head T i hd
      have hnone0 : T[k]? = none := by
        cases h2 : T[k]? with
        | none => rfl
        | some t =>
          have := (hoistDone_iff i T (hle T hE) k).mpr (by rw [h2]; rfl)
          rw [hnd] at this; cases this
      have hnone : (T[k]?).isNone := by rw [hnone0]; rfl
      have hNk : N k := by
        rcases hS k hk with h | h
        · exact h
        · rw [hnone0] at h; cases h
      obtain ⟨-, hks, hrun⟩ := hN k hNk
      have hrest : ∀ x ∈ rest, x ∈ S := fun x hx =>
        hoistDropDone_sub T i (by rw [hd]; exact List.mem_cons_of_mem _ hx)
      have hpush : (hoistClosure.pushDeps ds idx i k rest).run a =
          .ok (hoistClosure.pushOne idx i k (D k) rest, a) := by
        unfold hoistClosure.pushDeps
        rw [dite_eq_left hks, run_bind, hrun]
        simp only
        rfl
      rw [run_bind, hpush]
      simp only
      have hT₁ : ∀ x : Nat, (T.insert k i)[x]? = if k = x then some i else T[x]? := by
        intro x; simp [Std.HashMap.getElem?_insert]
      have hpi := pend_insert ds i N T k hks hNk hnone
      generalize T.insert k i = T₁ at hT₁ hpi ⊢
      have hmono : ∀ x : Nat, (T[x]?).isSome → T₁[x]? = T[x]? := by
        intro x hx
        rw [hT₁]
        split
        · rename_i e; rw [← e, hnone0] at hx; cases hx
        · rfl
      have hE₁ : Ext i T₀ N T₁ := by
        intro x
        rw [hT₁]
        split
        · subst_vars; exact Or.inr ⟨hNk, rfl⟩
        · exact hE x
      have hS₁ : ∀ x ∈ (hoistClosure.pushOne idx i k (D k) rest), N x ∨ (T₁[x]?).isSome := by
        intro x hx
        rcases (mem_pushOne idx i k (D k) rest x).mp hx with h | ⟨n, hn, h1, h2⟩
        · rcases hS x (hrest x h) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by rw [hmono x h']; exact h')
        · rcases hcl k hNk x ⟨n, hn, h1, h2⟩ with h' | h'
          · exact Or.inl h'
          · right
            have := hkeep T hE x h'
            rw [hmono x (by rw [this]; exact h'), this]; exact h'
      have hC₁ : ∀ k', N k' → (T₁[k']?).isSome → ∀ m : Nat, Succ idx i D k' m →
          (T₁[m]?).isSome ∨ m ∈ (hoistClosure.pushOne idx i k (D k) rest) := by
        intro k' hk' hkT m hm
        by_cases e : k = k'
        · subst e
          obtain ⟨n, hn, h1, h2⟩ := hm
          exact Or.inr ((mem_pushOne idx i k (D k) rest m).mpr (Or.inr ⟨n, hn, h1, h2⟩))
        · have hkT' : (T[k']?).isSome := by rw [hT₁, ite_eq_right e] at hkT; exact hkT
          rcases hC k' hk' hkT' m hm with h | h
          · exact Or.inl (by rw [hmono m h]; exact h)
          · rcases mem_dropDone i T S m h with h' | h'
            · have h'' := (hoistDone_iff i T (hle T hE) m).mp h'
              exact Or.inl (by rw [hmono m h'']; exact h'')
            · rw [hd] at h'
              rcases List.mem_cons.mp h' with rfl | h'
              · exact Or.inl (by rw [hT₁, ite_eq_left rfl]; rfl)
              · exact Or.inr ((mem_pushOne idx i k (D k) rest m).mpr (Or.inl h'))
      have hp₁ : pend ds N T₁ ≤ f := by omega
      obtain ⟨T', hrun', hE', hS', hC', hM'⟩ := ih T₁ _ hE₁ hS₁ hC₁ hp₁
      refine ⟨T', hrun', hE', ?_, hC', ?_⟩
      · intro x hx
        rcases mem_dropDone i T S x hx with h | h
        · have h' := (hoistDone_iff i T (hle T hE) x).mp h
          rw [hM' x (by rw [hmono x h']; exact h'), hmono x h']; exact h'
        · rw [hd] at h
          rcases List.mem_cons.mp h with rfl | h
          · rw [hM' x (by rw [hT₁, ite_eq_left rfl]; rfl), hT₁, ite_eq_left rfl]; rfl
          · exact hS' x ((mem_pushOne idx i k (D k) rest x).mpr (Or.inl h))
      · intro x hx
        rw [hM' x (by rw [hmono x hx]; exact hx), hmono x hx]

/-- Reachable from `j` through members of `N` (`j` itself a member). -/
inductive ReachIn (D : Nat → List NIdx) (N : Nat → Prop) (j : Nat) : Nat → Prop
  | base : N j → ReachIn D N j j
  | step {k m : Nat} : ReachIn D N j k → Succ idx i D k m → N m → ReachIn D N j m

theorem ReachIn.mem {D : Nat → List NIdx} {N : Nat → Prop} {j k : Nat}
    (h : ReachIn idx i D N j k) : N k := by
  cases h with
  | base h => exact h
  | step _ _ h => exact h

open Classical in
/-- **The closure of `j` is exactly `T₀` plus `N ↦ i`**, when every member is reachable from `j`
through members. -/
theorem closure_exact (a : AState) (D : Nat → List NIdx) (N : Nat → Prop) (T₀ : Std.HashMap Nat Nat)
    (j : Nat) (hT₀ : ∀ (k t : Nat), T₀[k]? = some t → t ≤ i)
    (hN : ∀ k : Nat, N k → T₀[k]? = none ∧ ∃ h : k < ds.size,
      (IDeclaration.usedConsts ds[k]).run a = .ok ((D k).toArray, a))
    (hcl : ∀ k : Nat, N k → ∀ m : Nat, Succ idx i D k m → N m ∨ (T₀[m]?).isSome)
    (hj : N j ∨ (T₀[j]?).isSome) (hR : ∀ k : Nat, N k → ReachIn idx i D N j k) :
    ∃ T', (hoistClosure ds idx i ds.size T₀ [j]).run a = .ok (T', a) ∧
      ∀ k : Nat, T'[k]? = if N k then some i else T₀[k]? := by
  classical
  have hp : pend ds N T₀ ≤ ds.size := by
    unfold pend
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  obtain ⟨T', hrun, hE, hS, hC, -⟩ := closure_twin ds idx i a D N T₀ hT₀ hN hcl ds.size T₀ [j]
    (fun k => Or.inl rfl)
    (by intro x hx; simp at hx; subst hx; exact hj)
    (by
      intro k hk hkT
      rw [(hN k hk).1] at hkT; cases hkT)
    hp
  refine ⟨T', hrun, ?_⟩
  -- every member reached is marked `i`
  have key : ∀ x : Nat, ReachIn idx i D N j x → T'[x]? = some i := by
    intro x hx
    induction hx with
    | base hNj =>
      have hs := hS j (by simp)
      rcases hE j with e | ⟨-, e⟩
      · rw [e, (hN j hNj).1] at hs; cases hs
      · exact e
    | @step k' m hk' hs hm ih =>
      have hmS : (T'[m]?).isSome := hC k' (hk'.mem idx i) (by rw [ih]; rfl) m hs
      rcases hE m with e | ⟨-, e⟩
      · rw [e, (hN m hm).1] at hmS; cases hmS
      · exact e
  intro k
  by_cases hk : N k
  · rw [ite_eq_left hk]; exact key k (hR k hk)
  · rw [ite_eq_right hk]
    rcases hE k with e | ⟨h, -⟩
    · exact e
    · exact absurd h hk

end L.Checker.HoistTwin
