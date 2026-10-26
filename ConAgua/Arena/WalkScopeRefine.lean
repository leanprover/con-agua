import ConAgua.Arena.WalkScope
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.View
import ConRon.Arena.ExprOps
import ConAgua.Census.Attr

/-!
# `ws_go` refines `wscopedBGo`, `wscoped_bfast` refines `wscopedBFast` (lane `whnf3`)

The twin threads its walk-local memo as an argument and a result; L keeps it in the memo table
`WSM` (array 151). The relation is `MemoRG wsSch lfKey decBW` at the twin's map (keys `(h, d)`,
values `w ≠ 0`); the walk writes that table alone (`MemFrame [WSM] [152, 153]`), so `ArenaD` is
framed, and the twin's state is unchanged (the walk only reads `derivedE` and `view`). The counter
`c` is the twin's fuel exactly (`c.toNat`), as in `FVarRangeRefine.lean`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- A memo value word as a `Bool`. -/
def decBW (w : Word) : Bool := w != 0

/-- `ArenaD` across a writer at or above array/`CTL` word 64. -/
theorem ArenaD.frame64 {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, 64 ≤ b ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat)
    (h : ArenaD m a) : ArenaD m' a :=
  ⟨ArenaR.frame_ext A C hA hC m m' hf a h.1,
   DerR.frameM A C m m' hf (fun b hb => by
     have := hA b hb; simp only [ArrId] at this ⊢; omega) a h.2⟩

theorem wsSch_wf : wsSch.WF := ⟨by decide, by decide⟩

/-- The scope walk's frame. -/
abbrev WsFrame (m m' : Mem) : Prop := MemFrame [WSM] [152, 153] m m'

theorem WsFrame.arenaD {m m' : Mem} {a : AState} (hf : WsFrame m m') (h : ArenaD m a) : ArenaD m' a :=
  ArenaD.frame64 hf (fun b hb => by simp at hb; subst hb; decide)
    (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide) h

/-! ## The twin, unfolded -/

/-- The arms of `wscopedBGo` on a view (its inner `match`), named. -/
def wsArm (memo : Std.HashMap (EIdx × Nat) Bool) (F d : Nat) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
  | .fvar idx ty => if idx < d then wscopedBGo memo F idx ty else pure (false, memo)
  | .app f a => wscopedBGoArmApp memo F d f a
  | .lam ty body | .forallE ty body => wscopedBGoArmBind memo F d ty body
  | .letE ty val body => wscopedBGoArmLet memo F d ty val body
  | .proj _ _ sub => wscopedBGo memo F d sub

/-- The node half of `wscopedBGo`: view, then the arm. -/
def wsNodeA (memo : Std.HashMap (EIdx × Nat) Bool) (F d : Nat) (h : EIdx) :
    AM (Bool × Std.HashMap (EIdx × Nat) Bool) := do
  let v ← view h
  wsArm memo F d v

theorem wscopedBGo_succ' (memo : Std.HashMap (EIdx × Nat) Bool) (F d : Nat) (h : EIdx) :
    wscopedBGo memo (F + 1) d h = (do
      if (fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
      else
        match memo[(h, d)]? with
        | some r => pure (r, memo)
        | none => do
          let (r, memo') ← wsNodeA memo F d h
          pure (r, memo'.insert (h, d) r)) := by
  rw [wscopedBGo_succ]
  congr 1; funext x
  by_cases hx : ((fvarOfData x).toNat == 0) = true
  · simp only [hx, ↓reduceIte]
  · simp only [hx, Bool.false_eq_true, ↓reduceIte]
    cases memo[(h, d)]? with
    | some r => rfl
    | none =>
      simp only [wsNodeA, bind_assoc]
      congr 1; funext v
      cases v <;> simp only [wsArm, pure_bind] <;> (try split) <;> simp only [pure_bind]

theorem wsNodeA_run (memo : Std.HashMap (EIdx × Nat) Bool) (F d : Nat) (h : EIdx) (a : AState)
    (v : ENodeView) (hv : a.store.view h = some v) :
    (wsNodeA memo F d h).run a = (wsArm memo F d v).run a := by
  simp only [wsNodeA, StateT.run_bind, view_run h a v hv]; rfl

/-! ## The refinement, by induction on the L fuel -/

/-- What `ws_go`'s model says about the twin walk at the counter's fuel. -/
def WsGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (memo : Std.HashMap (EIdx × Nat) Bool) (h d c r : Word),
    ArenaD m a → MemoRG wsSch lfKey decBW m memo → h.toNat < 2 ^ 32 →
    wscW n m h d c = some (r, m') →
    ∃ memo', (wscopedBGo memo c.toNat d.toNat (decE h)).run a = .ok ((r != 0, memo'), a) ∧
      MemoRG wsSch lfKey decBW m' memo' ∧ r ≤ 1 ∧ WsFrame m m'

/-- The same for `ws_node` and the twin's view-and-arm. -/
def WsNodeOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (memo : Std.HashMap (EIdx × Nat) Bool) (h d c r : Word),
    ArenaD m a → MemoRG wsSch lfKey decBW m memo → h.toNat < 2 ^ 32 →
    wsNodeW n m h d c = some (r, m') →
    ∃ memo', (wsNodeA memo c.toNat d.toNat (decE h)).run a = .ok ((r != 0, memo'), a) ∧
      MemoRG wsSch lfKey decBW m' memo' ∧ r ≤ 1 ∧ WsFrame m m'

theorem wsGoOK_succ (n : Nat) (ih : WsNodeOK n) : WsGoOK (n + 1) := by
  intro m m' a memo h d c r hD hM hh hb
  have hc : ¬ c = 0 := fun hc => by rw [wscW] at hb; simp [hc] at hb
  rw [ctrW_toNat c hc, wscopedBGo_succ', StateT.run_bind, derivedE_run, except_ok_bind]
  rw [← derFW_ok m a hD.1 hD.2 h hh]
  by_cases hf : derFW m h = 0
  · rw [wscW_cut n m h d c hc hf] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    refine ⟨memo, by rw [hf]; rfl, hM, by decide, MemFrame.refl _ _ _⟩
  have hf' : ((derFW m h).toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; exact hf (UInt64.toNat_inj.mp (by simpa using e))
  rw [hf']
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hr : ¬ mfindG wsSch m h d = [] := fun hr => by rw [wscW] at hb; simp [hc, hf, hr] at hb
  have hk : lfKey.ok h d := hh
  by_cases hh0 : (mfindG wsSch m h d).headD 0 ≠ 0
  · rw [wscW_hit n m h d c hc hf hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have e := memoRG_hit wsSch lfKey decBW m memo hM h d hr hh0 hk
    simp only [lfKey] at e
    rw [e]
    refine ⟨memo, ?_, hM, by split <;> decide, MemFrame.refl _ _ _⟩
    simp only [decBW, mvG]
    split <;> rename_i hv
    · have : (rdW (m.arr64 WSM) ((mfindG wsSch m h d).tail.headD 0 * 4 + 3) != 0) = true := by
        simpa using hv
      simp only [this]; rfl
    · have : rdW (m.arr64 WSM) ((mfindG wsSch m h d).tail.headD 0 * 4 + 3) = 0 := by simpa using hv
      simp only [this]; rfl
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [wscW_miss n m h d c hc hf hr hh0] at hb
    have e := memoRG_miss wsSch lfKey decBW m memo hM h d hk hr hh0
    simp only [lfKey] at e
    rw [e]
    rcases hn : wsNodeW n m h d (c - 1) with _ | ⟨r₁, m₁⟩ <;> simp only [hn, wsK, wsSet_eq, reduceCtorEq] at hb
    cases hs : msetG wsSch m₁ h d r₁ with
    | none => simp [hs, wsSetK] at hb
    | some m₂ =>
      simp only [hs, wsSetK, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨memo₁, ha₁, hM₁, hle, hf₁⟩ := ih m m₁ a memo h d (c - 1) r₁ hD hM hh hn
      refine ⟨memo₁.insert (decE h, d.toNat) (r₁ != 0), ?_, ?_, hle, ?_⟩
      · simp only [StateT.run_bind, ha₁, except_ok_bind]; rfl
      · have := memoRG_set wsSch wsSch_wf lfKey decBW m₁ memo₁ hM₁ h d r₁ hk m₂ hs
        simpa [lfKey, decBW] using this
      · exact hf₁.trans ((msetG_frame wsSch wsSch_wf m₁ m₂ h d r₁ hs).mono (by simp) (by simp))

/-- A short-circuiting pair of children (the `app` and binder arms). -/
theorem wsAnd_ok (n : Nat) (ih : WsGoOK n) (m m' : Mem) (a : AState)
    (memo : Std.HashMap (EIdx × Nat) Bool) (hD : ArenaD m a) (hM : MemoRG wsSch lfKey decBW m memo)
    (fw bw d c r : Word) (hf : fw.toNat < 2 ^ 32) (hb' : bw.toNat < 2 ^ 32)
    (hb : wsAndK n bw d c (wscW n m fw d c) = some (r, m')) :
    ∃ memo', (do
        let (rf, memo) ← wscopedBGo memo c.toNat d.toNat (decE fw)
        if rf then wscopedBGo memo c.toNat d.toNat (decE bw) else pure (false, memo) :
          AM (Bool × Std.HashMap (EIdx × Nat) Bool)).run a = .ok ((r != 0, memo'), a) ∧
      MemoRG wsSch lfKey decBW m' memo' ∧ r ≤ 1 ∧ WsFrame m m' := by
  cases h1 : wscW n m fw d c with
  | none => simp only [h1, wsAndK, reduceCtorEq] at hb
  | some q =>
    obtain ⟨x, m₁⟩ := q
    obtain ⟨memo₁, ha₁, hM₁, hx, hf₁⟩ := ih m m₁ a memo fw d c x hD hM hf h1
    rw [h1] at hb
    by_cases hx0 : x = 0
    · subst hx0
      rw [wsAndK_zero] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨memo₁, by simp only [StateT.run_bind, ha₁, except_ok_bind]; rfl, hM₁, by decide, hf₁⟩
    · rw [wsAndK_ne n m₁ x d c bw hx0] at hb
      obtain ⟨memo₂, ha₂, hM₂, hle, hf₂⟩ := ih m₁ m' a memo₁ bw d c r (hf₁.arenaD hD) hM₁ hb' hb
      refine ⟨memo₂, ?_, hM₂, hle, hf₁.trans hf₂⟩
      have : (x != 0) = true := by simpa using hx0
      simp only [StateT.run_bind, ha₁, except_ok_bind, this, ↓reduceIte]
      exact ha₂

theorem wsNodeOK_succ (n : Nat) (ih : WsGoOK n) : WsNodeOK (n + 1) := by
  intro m m' a memo h d c r hD hM hh hb
  have hR := hD.1
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [wsNodeW] at hb; simp only [ite_eq_left hs, reduceCtorEq] at hb
  have vok : ∀ c, ¬ tcnt m c (tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, UInt64.not_le.mp hc⟩
  have one : ∀ v, a.store.view (decE h) = some v → wsArm memo c.toNat d.toNat v = pure (true, memo) →
      wsNodeW (n + 1) m h d c = some (1, m) →
      ∃ memo', (wsNodeA memo c.toNat d.toNat (decE h)).run a = .ok ((r != 0, memo'), a) ∧
        MemoRG wsSch lfKey decBW m' memo' ∧ r ≤ 1 ∧ WsFrame m m' := by
    intro v hv hx e; rw [e] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact ⟨memo, by rw [wsNodeA_run _ _ _ _ a _ hv, hx]; rfl, hM, by decide, MemFrame.refl _ _ _⟩
  by_cases g0 : h >>> 28 = 0
  · have hvo := vok BVAR fun hc => by rw [wsNodeW] at hb; simp [hs, g0, hc] at hb
    exact one _ (view_bvar m a hR h hh hvo g0) rfl (wsNodeW_bvar n m h d c g0 hvo)
  by_cases g1 : h >>> 28 = 1
  · have hvo := vok FVAR fun hc => by rw [wsNodeW] at hb; simp [hs, g1, hc] at hb
    obtain ⟨hv, hty⟩ := view_fvar_idx m a hR h hh hvo g1
    by_cases hl : tfld m FVAR (tierW h) (idxW h) 0 < d
    · rw [wsNodeW_fvar_lt n m h d c g1 hvo hl] at hb
      obtain ⟨memo', ha, hM', hle, hf⟩ := ih m m' a memo _ _ c r hD hM hty hb
      refine ⟨memo', ?_, hM', hle, hf⟩
      rw [wsNodeA_run _ _ _ _ a _ hv]
      have : (tfld m FVAR (tierW h) (idxW h) 0).toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp hl
      simp only [wsArm, this, ↓reduceIte]
      exact ha
    · rw [wsNodeW_fvar_ge n m h d c g1 hvo hl] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      refine ⟨memo, ?_, hM, by decide, MemFrame.refl _ _ _⟩
      rw [wsNodeA_run _ _ _ _ a _ hv]
      have : ¬ (tfld m FVAR (tierW h) (idxW h) 0).toNat < d.toNat :=
        fun e => hl (UInt64.lt_iff_toNat_lt.mpr e)
      simp only [wsArm, this, ↓reduceIte]; rfl
  by_cases g4 : h >>> 28 = 4
  · have hvo := vok APP fun hc => by rw [wsNodeW] at hb; simp [hs, g4, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_app m a hR h hh hvo g4
    rw [wsNodeW_app n m h d c hvo g4] at hb
    obtain ⟨memo', h1, h2⟩ := wsAnd_ok n ih m m' a memo hD hM _ _ d c r hf ha hb
    exact ⟨memo', (wsNodeA_run _ _ _ _ a _ hv).trans (by simp only [wsArm, wscopedBGoArmApp]; exact h1), h2⟩
  by_cases g5 : h >>> 28 = 5
  · have hvo := vok LAM fun hc => by rw [wsNodeW] at hb; simp [hs, g5, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_lam m a hR h hh hvo g5
    rw [wsNodeW_lam n m h d c hvo g5] at hb
    obtain ⟨memo', h1, h2⟩ := wsAnd_ok n ih m m' a memo hD hM _ _ d c r hf ha hb
    exact ⟨memo', (wsNodeA_run _ _ _ _ a _ hv).trans (by simp only [wsArm, wscopedBGoArmBind]; exact h1), h2⟩
  by_cases g6 : h >>> 28 = 6
  · have hvo := vok FORALL fun hc => by rw [wsNodeW] at hb; simp [hs, g6, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_forall m a hR h hh hvo g6
    rw [wsNodeW_forall n m h d c hvo g6] at hb
    obtain ⟨memo', h1, h2⟩ := wsAnd_ok n ih m m' a memo hD hM _ _ d c r hf ha hb
    exact ⟨memo', (wsNodeA_run _ _ _ _ a _ hv).trans (by simp only [wsArm, wscopedBGoArmBind]; exact h1), h2⟩
  by_cases g7 : h >>> 28 = 7
  · have hvo := vok LET fun hc => by rw [wsNodeW] at hb; simp [hs, g7, hc] at hb
    obtain ⟨hv, ht, hv', hb'⟩ := view_let m a hR h hh hvo g7
    rw [wsNodeW_let n m h d c hvo g7] at hb
    rw [wsNodeA_run _ _ _ _ a _ hv]
    simp only [wsArm, wscopedBGoArmLet]
    cases h1 : wscW n m (tfld m LET (tierW h) (idxW h) 0) d c with
    | none => simp only [h1, wsLetK, reduceCtorEq] at hb
    | some q =>
      obtain ⟨x, m₁⟩ := q
      obtain ⟨memo₁, ha₁, hM₁, hx, hf₁⟩ := ih m m₁ a memo _ d c x hD hM ht h1
      rw [h1] at hb
      by_cases hx0 : x = 0
      · subst hx0
        rw [wsLetK_zero] at hb
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        exact ⟨memo₁, by simp only [StateT.run_bind, ha₁, except_ok_bind]; rfl, hM₁, by decide, hf₁⟩
      · rw [wsLetK_ne n m₁ x d c _ _ hx0] at hb
        obtain ⟨memo₂, ha₂, hM₂, hle, hf₂⟩ := wsAnd_ok n ih m₁ m' a memo₁ (hf₁.arenaD hD) hM₁ _ _ d c r hv' hb' hb
        refine ⟨memo₂, ?_, hM₂, hle, hf₁.trans hf₂⟩
        have : (x != 0) = true := by simpa using hx0
        simp only [StateT.run_bind, ha₁, except_ok_bind, this, ↓reduceIte]
        exact ha₂
  by_cases g9 : h >>> 28 = 9
  · have hvo := vok PROJ fun hc => by rw [wsNodeW] at hb; simp [hs, g9, hc] at hb
    obtain ⟨hv, -, he⟩ := view_proj m a hR h hh hvo g9
    rw [wsNodeW_proj n m h d c hvo g9] at hb
    obtain ⟨memo', h1, h2⟩ := ih m m' a memo _ d c r hD hM he hb
    exact ⟨memo', (wsNodeA_run _ _ _ _ a _ hv).trans h1, h2⟩
  by_cases g2 : h >>> 28 = 2
  · have hvo := vok SORT fun hc => by rw [wsNodeW] at hb; simp [hs, g2, hc] at hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh hvo g2
    exact one _ hv rfl (wsNodeW_sort n m h d c g2 hvo)
  by_cases g3 : h >>> 28 = 3
  · have hvo := vok CONST fun hc => by rw [wsNodeW] at hb; simp [hs, g3, hc] at hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh hvo g3
    exact one _ hv rfl (wsNodeW_const n m h d c g3 hvo)
  by_cases g8 : h >>> 28 = 8
  · have hvo := vok LIT fun hc => by rw [wsNodeW] at hb; simp [hs, g8, hc] at hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh hvo g8
    exact one _ hv rfl (wsNodeW_lit n m h d c g8 hvo)
  rw [wsNodeW] at hb; simp [hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-- **The model of `ws_go` refines `wscopedBGo`** at every L fuel. -/
theorem wsGoOK (n : Nat) : WsGoOK n ∧ WsNodeOK n := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ hb => by simp [wscW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ hb => by simp [wsNodeW] at hb⟩
  | succ n ih => exact ⟨wsGoOK_succ n ih.2, wsNodeOK_succ n ih.1⟩

/-! ## The entry -/

/-- The scope walk's memo is well formed (at some map): what the entry's epoch clear needs. -/
def WsMemoOK (m : Mem) : Prop := ∃ mp : Std.HashMap (EIdx × Nat) Bool, MemoRG wsSch lfKey decBW m mp

/-- **The model of `wscoped_bfast` refines `wscopedBFast coreWalkFuel`**: the twin state is
unchanged, the memo stays well formed, and the walk wrote its memo alone. -/
theorem wsFastW_ok (n : Nat) (m m' : Mem) (a : AState) (hD : ArenaD m a) (hM : WsMemoOK m)
    (d e r : Word) (he : e.toNat < 2 ^ 32) (hb : wsFastW n m d e = some (r, m')) :
    (wscopedBFast coreWalkFuel d.toNat (decE e)).run a = .ok (r != 0, a) ∧ WsMemoOK m' ∧ r ≤ 1 ∧
      MemFrame [WSM] [152, 153] m m' := by
  obtain ⟨mp, hmp⟩ := hM
  simp only [wsFastW] at hb
  have h0 : ¬ rdW (m.arr64 CTL) 152 + 2 = 0 := fun h0 => by simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hc := mclearG_frame wsSch m
  have hM₀ := memoRG_clear wsSch wsSch_wf lfKey decBW m mp hmp h0
  obtain ⟨memo', ha, hM', hle, hf⟩ :=
    (wsGoOK n).1 _ _ a ∅ e d 4000000000 r (ArenaD.frame64 hc (by simp)
      (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide) hD) hM₀ he hb
  rw [coreWalkFuel_toNat] at ha
  refine ⟨?_, ⟨_, hM'⟩, hle, (hc.mono (by simp) (by simp)).trans hf⟩
  simp only [wscopedBFast, StateT.run_bind, ha, except_ok_bind]; rfl

end L.Arena
