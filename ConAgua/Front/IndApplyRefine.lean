import ConAgua.Front.IndApplySpec2
import ConAgua.Front.StateDR

/-!
# The apply step of an `inductive` line against the twin, I: the leaves

The models of `IndApplySpec.lean` against con-ron's `validateIndD` helpers: the telescope walks
(`piResW_ok`, `teleW_ok`, `sortTeleW_ok`: `piResultD`, `indPiTeleLen`, `piSortTeleLen?` at the
fuel word's value, every step a `view`, `eViewW_ok`), `name_rec_pre` (`nrpW_ok`: `viewN`), the
store's fuel (`storeFuelW_eq`: `nodeCount + 1`), the table lookups (`lkW_name`, `lkW_expr`).
Every twin run is read-only: it ends in the state it starts from.
-/

open L.Arena
open L.Ind (eViewW eViewW_ok ViewR)
open ConRon.Arena
open ConRon.Arena.Frontend

set_option linter.unusedSimpArgs false

namespace L.Front.Ind

/-! ## Runs -/

theorem run_pure {α : Type} (x : α) (a : AState) : (pure x : AM α).run a = .ok (x, a) := rfl

theorem run_bind {α β : Type} (x : AM α) (f : α → AM β) (a : AState) (y : α)
    (h : x.run a = .ok (y, a)) : (x >>= f).run a = (f y).run a := by
  simp only [StateT.run_bind, h]; rfl

/-- A read-only `mapM`: every element's run returns its image and keeps the state. -/
theorem mapM_run {α β : Type} (f : α → AM β) (g : α → β) (a : AState) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).run a = .ok (g x, a)) →
      (xs.mapM f).run a = .ok (xs.map g, a)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, List.map_cons]
    rw [run_bind _ _ a _ (h x (by simp)), run_bind _ _ a _ (mapM_run f g a xs fun y hy => h y (by simp [hy]))]
    rfl

/-- A read-only `forIn` that yields at every element: the states `S i`. -/
theorem forIn_yield {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (S : Nat → β) (h : ∀ i (hi : i < xs.length), (f xs[i] (S i)).run a = .ok (.yield (S (i + 1)), a)) :
    (forIn xs (S 0) f).run a = .ok (S xs.length, a) := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [run_bind _ _ a _ h0]
    have := ih (fun i => S (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa using this)
    simpa using this

/-! ## Views -/

theorem getD2 (l : List Word) : l.getD 2 0 = l.tail.tail.headD 0 := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

theorem getD1 (l : List Word) : l.getD 1 0 = l.tail.headD 0 := by
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

/-- The view of a handle the L code views. -/
theorem view_ok' (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hne : eViewW m h ≠ []) :
    ∃ v, (view (decE h)).run a = .ok (v, a) ∧ ViewR (eViewW m h) v := by
  obtain ⟨v, hv, hr⟩ := eViewW_ok m a hR h hne
  exact ⟨v, view_run _ a v hv, hr⟩

/-- The tag word of a view. -/
def tagOf : ENodeView → Word
  | .bvar _ => 0 | .fvar _ _ => 1 | .sort _ => 2 | .const _ _ => 3 | .app _ _ => 4
  | .lam _ _ => 5 | .forallE _ _ => 6 | .letE _ _ _ => 7 | .lit _ => 8 | .proj _ _ _ => 9

theorem viewR_head {r : List Word} {v : ENodeView} (h : ViewR r v) : r.headD 0 = tagOf v := by
  cases v <;> simp only [ViewR] at h <;> first | exact h.1 | exact h

theorem viewR_forall {r : List Word} {v : ENodeView} (h : ViewR r v) (h6 : r.headD 0 = 6) :
    ∃ ty, v = .forallE ty (decE (r.tail.tail.headD 0)) := by
  have ht := viewR_head h
  rw [h6] at ht
  cases v <;> simp only [tagOf] at ht <;> (try exact absurd ht (by decide))
  simp only [ViewR] at h
  exact ⟨_, by rw [← getD2, h.2.2.2.2]⟩

theorem viewR_sort {r : List Word} {v : ENodeView} (h : ViewR r v) (h2 : r.headD 0 = 2) :
    v = .sort (decI (r.tail.headD 0)) ∧ (r.tail.headD 0).toNat < 2 ^ 32 := by
  have ht := viewR_head h
  rw [h2] at ht
  cases v <;> simp only [tagOf] at ht <;> (try exact absurd ht (by decide))
  simp only [ViewR] at h
  exact ⟨by rw [← getD1, h.2.2], by rw [← getD1]; exact h.2.1⟩

theorem fuel_pred {f : Word} (hf : ¬ f = 0) : f.toNat = (f - 1).toNat + 1 := by
  have : f.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-! ## The telescope walks -/

section tele
variable (m : Mem) (a : AState) (hR : ArenaR m a)
include hR

theorem piResW_ok : ∀ (n : Nat) (f h r : Word), piResW n m f h = some r →
    (ConRon.Arena.Frontend.piResultD f.toNat (decE h)).run a = .ok (decE r, a) := by
  intro n
  induction n with
  | zero => intro f h r hw; simp [piResW] at hw
  | succ n ih =>
    intro f h r hw
    simp only [piResW] at hw
    split at hw
    · cases hw
    rename_i hf
    split at hw
    · cases hw
    rename_i hne
    obtain ⟨v, hv, hr⟩ := view_ok' m a hR h hne
    rw [fuel_pred hf, ConRon.Arena.Frontend.piResultD, run_bind _ _ a _ hv]
    split at hw
    · rename_i h6
      obtain ⟨ty, rfl⟩ := viewR_forall hr h6
      exact ih _ _ _ hw
    · rename_i h6
      cases hw
      cases v <;> (try rfl)
      exact absurd (viewR_head hr) h6

theorem teleW_ok : ∀ (n : Nat) (f h r : Word), teleW n m f h = some r →
    (ConRon.Arena.Frontend.indPiTeleLen f.toNat (decE h)).run a = .ok (r.toNat, a) ∧
      r.toNat < f.toNat := by
  intro n
  induction n with
  | zero => intro f h r hw; simp [teleW] at hw
  | succ n ih =>
    intro f h r hw
    simp only [teleW] at hw
    split at hw
    · cases hw
    rename_i hf
    split at hw
    · cases hw
    rename_i hne
    obtain ⟨v, hv, hr⟩ := view_ok' m a hR h hne
    have hf1 := fuel_pred hf
    rw [hf1, ConRon.Arena.Frontend.indPiTeleLen, run_bind _ _ a _ hv]
    split at hw
    · rename_i h6
      obtain ⟨ty, rfl⟩ := viewR_forall hr h6
      cases hrec : teleW n m (f - 1) ((eViewW m h).tail.tail.headD 0) with
      | none => rw [hrec] at hw; cases hw
      | some r' =>
        rw [hrec, teleK_some] at hw
        cases hw
        obtain ⟨h1, h2⟩ := ih _ _ _ hrec
        simp only
        rw [run_bind _ _ a _ h1]
        have hlt : (f - 1).toNat < 2 ^ 64 := UInt64.toNat_lt _
        have : (r' + 1).toNat = r'.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        exact ⟨by rw [this]; rfl, by omega⟩
    · rename_i h6
      cases hw
      refine ⟨?_, by simp only [UInt64.toNat_zero]; omega⟩
      cases v <;> (try rfl)
      exact absurd (viewR_head hr) h6

theorem sortTeleW_ok : ∀ (n : Nat) (f h ok r : Word), sortTeleW n m f h = some (ok, r) →
    (piSortTeleLen? f.toNat (decE h)).run a =
      .ok ((if ok = 0 then none else some r.toNat), a) ∧ r.toNat < f.toNat := by
  intro n
  induction n with
  | zero => intro f h ok r hw; simp [sortTeleW] at hw
  | succ n ih =>
    intro f h ok r hw
    simp only [sortTeleW] at hw
    split at hw
    · cases hw
    rename_i hf
    split at hw
    · cases hw
    rename_i hne
    obtain ⟨v, hv, hr⟩ := view_ok' m a hR h hne
    have hf1 := fuel_pred hf
    rw [hf1, piSortTeleLen?, run_bind _ _ a _ hv]
    split at hw
    · rename_i h6
      obtain ⟨ty, rfl⟩ := viewR_forall hr h6
      cases hrec : sortTeleW n m (f - 1) ((eViewW m h).tail.tail.headD 0) with
      | none => rw [hrec] at hw; cases hw
      | some q =>
        obtain ⟨ok', r'⟩ := q
        rw [hrec, stK_some] at hw
        obtain ⟨h1, h2⟩ := ih _ _ _ _ hrec
        simp only
        rw [run_bind _ _ a _ h1]
        by_cases hok : ok' = 0
        · rw [if_pos hok] at hw
          cases hw
          simp only [hok, if_true, Option.map_none]
          exact ⟨rfl, by simp⟩
        · rw [if_neg hok] at hw
          cases hw
          have : (r' + 1).toNat = r'.toNat + 1 := by
            rw [UInt64.toNat_add]; simp; have := UInt64.toNat_lt (f - 1); omega
          simp only [hok, if_false, Option.map_some, this, show (1 : Word) ≠ 0 by decide]
          exact ⟨rfl, by omega⟩
    · rename_i h6
      split at hw
      · rename_i h2
        cases hw
        refine ⟨?_, by simp only [UInt64.toNat_zero]; omega⟩
        rw [(viewR_sort hr h2).1]
        rfl
      · rename_i h2
        cases hw
        refine ⟨?_, by simp only [UInt64.toNat_zero]; omega⟩
        cases v <;> (try rfl)
        · exact absurd (viewR_head hr) h2
        · exact absurd (viewR_head hr) h6

end tele


/-! ## The store's fuel -/

/-- The sum of `c` words of `CTL` from `k`. -/
def csum (m : Mem) (k : Word) : Nat → Word
  | 0 => 0
  | c + 1 => rdW (m.arr64 CTL) k + csum m (k + 1) c

theorem ctlSumW_eq : ∀ (n : Nat) (m : Mem) (k c s : Word), ctlSumW n m k c = some s → s = csum m k c.toNat := by
  intro n
  induction n with
  | zero => intro m k c s h; simp [ctlSumW] at h
  | succ n ih =>
    intro m k c s h
    simp only [ctlSumW] at h
    split at h
    · cases h; rename_i hc; subst hc; rfl
    · rename_i hc
      cases hr : ctlSumW n m (k + 1) (c - 1) with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr, addK_some] at h
        cases h
        rw [ih _ _ _ _ hr, fuel_pred hc]
        rfl

/-- Both tiers' counts of a table: the sizes, below `2^27`. -/
theorem storeR_cnt {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {S : Schema}
    {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word} {m : Mem} {on : Bool}
    {P Q : Tbl α (Idx k) δ} (hT : StoreR S R hs m on P Q) :
    (rdW (m.arr64 CTL) (S.ca + 0)).toNat = P.size ∧ P.size ≤ 134217728 ∧
      (rdW (m.arr64 CTL) (S.ca + 1)).toNat = Q.size ∧ Q.size ≤ 134217728 :=
  ⟨hT.2.2.1.1, hT.2.2.1.2.1, hT.2.2.2.1, hT.2.2.2.2.1⟩

/-- **`store_fuel` is the twin's `storeFuel`**: the store's node count `+ 1`. -/
theorem storeFuelW_ok {m : Mem} {a : AState} (hR : ArenaR m a) {n : Nat} {f : Word}
    (h : storeFuelW n m = some f) : f.toNat = a.store.nodeCount + 1 := by
  cases n with
  | zero => simp [storeFuelW] at h
  | succ n =>
  simp only [storeFuelW] at h
  cases h1 : ctlSumW n m 2 4 with
  | none => rw [h1] at h; cases h
  | some x =>
  cases h2 : ctlSumW n m 16 8 with
  | none => rw [h1, h2] at h; cases h
  | some y =>
  cases h3 : ctlSumW n m 26 8 with
  | none => rw [h1, h2, h3] at h; cases h
  | some z =>
  rw [h1, h2, h3] at h
  simp only [sfK, Option.some.injEq] at h
  subst h
  rw [ctlSumW_eq _ _ _ _ _ h1, ctlSumW_eq _ _ _ _ _ h2, ctlSumW_eq _ _ _ _ _ h3]
  obtain ⟨a1, a2, a3, a4⟩ := storeR_cnt hR.lit.2
  obtain ⟨b1, b2, b3, b4⟩ := storeR_cnt hR.app
  obtain ⟨c1, c2, c3, c4⟩ := storeR_cnt hR.sort
  obtain ⟨d1, d2, d3, d4⟩ := storeR_cnt hR.const
  obtain ⟨e1, e2, e3, e4⟩ := storeR_cnt hR.letE
  obtain ⟨f1, f2, f3, f4⟩ := storeR_cnt hR.bvar
  obtain ⟨g1, g2, g3, g4⟩ := storeR_cnt hR.fvar
  obtain ⟨h1', h2', h3', h4'⟩ := storeR_cnt hR.lam
  obtain ⟨i1, i2, i3, i4⟩ := storeR_cnt hR.forallE
  obtain ⟨j1, j2, j3, j4⟩ := storeR_cnt hR.proj
  simp only [litSch, appSch, sortSch, constSch, letSch, bvarSch, fvarSch, lamSch, forallSch,
    projSch] at a1 a3 b1 b3 c1 c3 d1 d3 e1 e3 f1 f3 g1 g3 h1' h3' i1 i3 j1 j3
  simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count, Tbl.size] at *
  simp only [csum, show (4 : Word).toNat = 4 from rfl, show (8 : Word).toNat = 8 from rfl]
  simp only [UInt64.reduceAdd] at a1 a3 b1 b3 c1 c3 d1 d3 e1 e3 f1 f3 g1 g3 h1' h3' i1 i3 j1 j3 ⊢
  simp only [UInt64.toNat_add, UInt64.toNat_zero, UInt64.toNat_one] at *
  omega

end L.Front.Ind
