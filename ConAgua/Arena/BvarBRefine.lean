import ConAgua.Arena.BvarB
import ConAgua.Arena.Abs1Refine
import ConAgua.Arena.WalkRefine
import ConAgua.Census.Attr

/-!
# `bvar_b` refines `bvarB`, `loose_bvars_bounded_fast` refines `looseBVarsBoundedFast`

`fvbW_ok`'s proof (`Abs1Refine.lean`) for the bvar range: `derBW_ok`, `bbMemoW_correct`
(`WalkRefine.lean`, `ArenaR`), and `DerR` across `bb_memo` by the model's frame (`bbW_frame`, the
`frW_frame` induction with `bb` names: only `BMEMO` and `CTL[24‥25]`) and the twin's
`keeps_bvarBoundMemo` (the store).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The write set of `bb_go`/`bb_node`/`bb_memo`'s models. -/
abbrev BbFrame (m m' : Mem) : Prop := MemFrame [BMEMO] [24, 25] m m'

theorem bbSet_frame (m m' : Mem) (h r r' : Word) (hb : bbSet m h r = some (r', m')) :
    BbFrame m m' := by
  unfold bbSet at hb
  split at hb
  · cases hb
  rename_i m₁ hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, rfl⟩ := hb
  exact (msetG_frame bmSch bmSch_wf _ _ _ _ _ hs).mono (by simp) (by simp)

/-- A model result whose memory, if any, is a `BbFrame` of `m`. -/
def BbOK (m : Mem) (o : Option (Word × Mem)) : Prop := ∀ r m', o = some (r, m') → BbFrame m m'

theorem BbOK.app {n : Nat} {m : Mem} {c y : Word} {o : Option (Word × Mem)} (ho : BbOK m o)
    (hw : ∀ m₁, BbOK m₁ (bbW n m₁ y c)) : BbOK m (bbAppK₁ n c y o) :=
  MPost.bindK rfl (fun _ _ => rfl) ho fun _ m₁ h1 =>
    MPost.bindK (K := bbAppK₁.bbAppK₂ _) rfl (fun _ _ => rfl) (hw m₁)
      fun _ _ h2 => MPost.ret (h1.trans h2)

theorem BbOK.bind {n : Nat} {m : Mem} {c y : Word} {o : Option (Word × Mem)} (ho : BbOK m o)
    (hw : ∀ m₁, BbOK m₁ (bbW n m₁ y c)) : BbOK m (bbBindK₁ n c y o) :=
  MPost.bindK rfl (fun _ _ => rfl) ho fun _ m₁ h1 =>
    MPost.bindK (K := bbBindK₁.bbBindK₂ _) rfl (fun _ _ => rfl) (hw m₁)
      fun _ _ h2 => MPost.ret (h1.trans h2)

theorem BbOK.letE {n : Nat} {m : Mem} {c y z : Word} {o : Option (Word × Mem)} (ho : BbOK m o)
    (hw : ∀ m₁ w, BbOK m₁ (bbW n m₁ w c)) : BbOK m (bbLetK₁ n c y z o) :=
  MPost.bindK rfl (fun _ _ => rfl) ho fun _ m₁ h1 =>
    MPost.bindK (K := bbLetK₁.bbLetK₂ _ _ _ _) rfl (fun _ _ => rfl) (hw m₁ _) fun _ m₂ h2 =>
    MPost.bindK (K := bbLetK₁.bbLetK₃ _ _) rfl (fun _ _ => rfl) (hw m₂ _) fun _ _ h3 =>
    MPost.ret ((h1.trans h2).trans h3)

theorem bbW_frame (n : Nat) :
    (∀ m h c, BbOK m (bbW n m h c)) ∧ (∀ m h c, BbOK m (bbNodeW n m h c)) := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ hb => by simp [bbW] at hb, fun _ _ _ _ _ hb => by simp [bbNodeW] at hb⟩
  | succ n ih =>
    refine ⟨fun m h c r m' hb => ?_, fun m h c r m' hb => ?_⟩
    · rw [bbW] at hb
      split at hb
      · cases hb
      split at hb
      · cases hb
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact MemFrame.refl _ _ _
      split at hb
      · cases hb
      rename_i r₁ m₁ hn
      exact (ih.2 _ _ _ _ _ hn).trans (bbSet_frame _ _ _ _ _ hb)
    · have dead : ∀ S : TRec, ¬ viewOK m h S → tcnt m S (tierW h) ≤ idxW h ∨
          (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro S hv
        by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
        · exact .inr hs
        · exact .inl (UInt64.not_lt.mp fun hl => hv ⟨hs, hl⟩)
      have leaf : ∀ S, viewOK m h S → bbNodeW (n + 1) m h c = some (0, m) → BbFrame m m' →
          BbFrame m m' := fun _ _ _ h => h
      clear leaf
      by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
      · rw [bbNodeW, ite_eq_left hs] at hb; cases hb
      have tagCase : ∀ (S : TRec), (viewOK m h S → BbFrame m m') →
          (tcnt m S (tierW h) ≤ idxW h → BbFrame m m') → BbFrame m m' := by
        intro S h1 h2
        by_cases hc : tcnt m S (tierW h) ≤ idxW h
        · exact h2 hc
        · exact h1 ⟨hs, UInt64.not_le.mp hc⟩
      have none_of : ∀ (hn : bbNodeW (n + 1) m h c = none), False := fun hn => by
        rw [hn] at hb; cases hb
      have done0 : bbNodeW (n + 1) m h c = some (0, m) → BbFrame m m' := fun e => by
        rw [e] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb; exact MemFrame.refl _ _ _
      by_cases g0 : h >>> 28 = 0
      · refine tagCase BVAR (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · by_cases h1 : tfld m BVAR (tierW h) (idxW h) 0 + 1 = 0
          · exact (none_of (by rw [bbNodeW]; simp [hs, g0, h1, UInt64.not_le.mpr hv.2])).elim
          · rw [bbNodeW_bvar n m h c hv g0 h1] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨-, rfl⟩ := hb; exact MemFrame.refl _ _ _
        · rw [bbNodeW]; simp [hs, g0, hc]
      by_cases g1 : h >>> 28 = 1
      · refine tagCase FVAR (fun hv => done0 (bbNodeW_fvar n m h c g1 hv)) (fun hc => (none_of ?_).elim)
        rw [bbNodeW]; simp [hs, g1, hc]
      by_cases g4 : h >>> 28 = 4
      · refine tagCase APP (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [bbNodeW_app n m h c hv g4] at hb
          exact BbOK.app (ih.1 _ _ _) (fun m₁ => ih.1 m₁ _ _) _ _ hb
        · rw [bbNodeW]; simp [hs, g4, hc]
      by_cases g5 : h >>> 28 = 5
      · refine tagCase LAM (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [bbNodeW_lam n m h c hv g5] at hb
          exact BbOK.bind (ih.1 _ _ _) (fun m₁ => ih.1 m₁ _ _) _ _ hb
        · rw [bbNodeW]; simp [hs, g5, hc]
      by_cases g6 : h >>> 28 = 6
      · refine tagCase FORALL (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [bbNodeW_forall n m h c hv g6] at hb
          exact BbOK.bind (ih.1 _ _ _) (fun m₁ => ih.1 m₁ _ _) _ _ hb
        · rw [bbNodeW]; simp [hs, g6, hc]
      by_cases g9 : h >>> 28 = 9
      · refine tagCase PROJ (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [bbNodeW_proj n m h c hv g9] at hb
          exact ih.1 _ _ _ _ _ hb
        · rw [bbNodeW]; simp [hs, g9, hc]
      by_cases g7 : h >>> 28 = 7
      · refine tagCase LET (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [bbNodeW_let n m h c hv g7] at hb
          exact BbOK.letE (ih.1 _ _ _) (fun m₁ w => ih.1 m₁ w _) _ _ hb
        · rw [bbNodeW]; simp [hs, g7, hc]
      by_cases g2 : h >>> 28 = 2
      · refine tagCase SORT (fun hv => done0 (bbNodeW_sort n m h c g2 hv)) (fun hc => (none_of ?_).elim)
        rw [bbNodeW]; simp [hs, g2, hc]
      by_cases g3 : h >>> 28 = 3
      · refine tagCase CONST (fun hv => done0 (bbNodeW_const n m h c g3 hv)) (fun hc => (none_of ?_).elim)
        rw [bbNodeW]; simp [hs, g3, hc]
      by_cases g8 : h >>> 28 = 8
      · refine tagCase LIT (fun hv => done0 (bbNodeW_lit n m h c g8 hv)) (fun hc => (none_of ?_).elim)
        rw [bbNodeW]; simp [hs, g8, hc]
      exact (none_of (by rw [bbNodeW]; simp [hs, g0, g1, g4, g5, g6, g9, g7, g2, g3, g8])).elim

theorem bbMemoW_frame (n : Nat) (m m' : Mem) (h c r : Word) (hb : bbMemoW n m h c = some (r, m')) :
    BbFrame m m' := by
  unfold bbMemoW at hb
  split at hb
  · cases hb
  cases hw : bbW n (mclearG bmSch m) h c with
  | none => simp [hw, clrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hw, clrK] at hb
    split at hb
    · cases hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact (((mclearG_frame bmSch m).mono (by simp) (by simp)).trans
      ((bbW_frame n).1 _ _ _ _ _ hw)).trans ((mclearG_frame bmSch m₁).mono (by simp) (by simp))


theorem bvarB_run (F : Nat) (e : EIdx) (a : AState) :
    (bvarB F e).run a =
      (if (bvarOfData (a.store.derived e)).toNat == satRange then (bvarBoundMemo F e).run a
       else .ok ((bvarOfData (a.store.derived e)).toNat, a)) := by
  simp only [bvarB, StateT.run_bind, derivedE_run, except_ok_bind]
  split <;> rfl

/-- **`bvar_b`'s model refines `bvarB` at any twin fuel `F`** with `f.toNat ≤ F` (the counter) or
`n ≤ F + 1` (the L fuel), under `ArenaD`. -/
theorem bvbW_okF (n F : Nat) (m m' : Mem) (a : AState) (hA : ArenaD m a)
    (h f x : Word) (hh : h.toNat < 2 ^ 32) (hF : f.toNat ≤ F ∨ n ≤ F + 1)
    (hb : bvbW n m h f = some (x, m')) :
    ∃ a', (bvarB F (decE h)).run a = .ok (x.toNat, a') ∧ ArenaD m' a' := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [bvbW]⟩
  have hd := derBW_ok m a hA.1 hA.2 h hh
  rw [bvarB_run, ← hd]
  by_cases hs : derBW m h = 32767
  · rw [bvbW_sat n m h f hs] at hb
    have hs' : ((derBW m h).toNat == satRange) = true := by rw [hs]; rfl
    rw [ite_eq_left hs']
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [bbN]⟩
    rw [bbN_succ] at hb
    obtain ⟨a', ha', hR'⟩ := bbMemoW_correctF n F m m' a hA.1 h f x hh (by omega) hb
    have hk := (keeps_bvarBoundMemo F (decE h)).run ha'
    simp only [sp, Prod.mk.injEq] at hk
    have hf := bbMemoW_frame n m m' h f x hb
    exact ⟨a', ha', hR', DerR.of_store m' a a' (DerR.frameM _ _ m m' hf (by decide) a hA.2) hk.1⟩
  · rw [bvbW_pk n m h f hs] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hs' : ((derBW m h).toNat == satRange) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; apply hs; apply UInt64.toNat_inj.mp; rw [e]; rfl
    rw [ite_eq_right (by simp [hs'])]
    exact ⟨a, rfl, hA⟩

/-- **`bvar_b`'s model refines `bvarB`** at the counter's fuel `f.toNat`, under `ArenaD`. -/
theorem bvbW_ok (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaD m a)
    (h f x : Word) (hh : h.toNat < 2 ^ 32) (hb : bvbW n m h f = some (x, m')) :
    ∃ a', (bvarB f.toNat (decE h)).run a = .ok (x.toNat, a') ∧ ArenaD m' a' :=
  bvbW_okF n _ m m' a hA h f x hh (.inl (Nat.le_refl _)) hb

/-- **`bvar_b(f, e)` refines `bvarB f.toNat e`** under `ArenaD`, at every L fuel (`f` is the walk's
depth counter, the twin's fuel exactly). -/
@[refines ConRon.Arena.bvarB]
theorem bvarB_refines (p : Prog) (hp : BvbProg p) (n : Nat) (s₀ : St)
    (a₀ : AState) (hA : ArenaD s₀.mem a₀) (f h : Word) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bvar_b" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (bvarB f.toNat (decE h)) a₀ ∧
      ArenaD s'.mem (AM.st (bvarB f.toNat (decE h)) a₀) ∧
      AM.res (bvarB f.toNat (decE h)) a₀ = (r.headD 0).toNat; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (bvarBL_spec p hp n s₀ f h)
  subst hs
  obtain ⟨a', ha', hA'⟩ := bvbW_ok n _ _ a₀ hA h f _ hh hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres⟩

/-- **`loose_bvars_bounded_fast(f, k, e)` refines `looseBVarsBoundedFast f.toNat k e`** under
`ArenaD`: the L word is `1` exactly when the twin answers `true`. -/
@[refines ConRon.Arena.looseBVarsBoundedFast]
theorem lbbFast_refines (p : Prog) (hp : BvbProg p) (n : Nat) (s₀ : St)
    (a₀ : AState) (hA : ArenaD s₀.mem a₀) (f k h : Word) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "loose_bvars_bounded_fast" [f, k, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (looseBVarsBoundedFast f.toNat k.toNat (decE h)) a₀ ∧
      ArenaD s'.mem (AM.st (looseBVarsBoundedFast f.toNat k.toNat (decE h)) a₀) ∧
      AM.res (looseBVarsBoundedFast f.toNat k.toNat (decE h)) a₀ = (r.headD 0 != 0) ∧
      r.headD 0 ≤ 1; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (lbbFastL_spec p hp n s₀ f k h)
  subst hs
  cases hw : bvbW n s.mem h f with
  | none => rw [hw] at hI; cases hI
  | some q =>
    obtain ⟨x, m₁⟩ := q
    rw [hw, lbbK_some] at hI
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hI)
    obtain ⟨a', ha', hA'⟩ := bvbW_ok n _ _ a₀ hA h f x hh hw
    have hrun' : (looseBVarsBoundedFast f.toNat k.toNat (decE h)).run a₀ =
        .ok (decide (x.toNat ≤ k.toNat), a') := by
      simp only [looseBVarsBoundedFast, StateT.run_bind, ha']; rfl
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hloc, hok, hst ▸ hA', ?_, by rw [← hr]; split <;> decide⟩
    rw [hres, ← hr]
    by_cases hx : x ≤ k
    · simp [hx, UInt64.le_iff_toNat_le.mp hx]
    · have hx' : ¬ x.toNat ≤ k.toNat := fun e => hx (UInt64.le_iff_toNat_le.mpr e)
      simp [hx, hx']

end L.Arena
