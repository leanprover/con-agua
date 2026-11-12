module

public import ConAgua.Arena.IndSumSpec.McGoStep
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndSum
import ConAgua.Arena.IndRealFvt

@[expose] public section

/-!
# HlbiWalk: `has_loose_bvar_in_go`, `has_loose_bvar_in` (the projection guard's window query)

The generated models `hlbiW` (the walk) and `hlbiFW` (the entry), and their refinements of
con-ron's `hasLooseBVarInGo`/`hasLooseBVarIn` under the stage relation, the walk's memo the `hb`
array (`hbMR`, the twin's per-call `memo`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`has_loose_bvar_in_go` is its model `hlbiW`** (generated). -/
l_model hlbiGo_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
    (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
    (hgo : p.lookup "has_loose_bvar_in_go" = some hasLooseBVarInGoL) (hbp : BvbProg p)
  fns [hgo ↦ hlbiW]
  specs [bvarBL_spec p hbp n, eView_spec p hv n, memoFindG_spec hbSch p _ hf n,
    hbIns_spec p hf hput hins n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] gen 20

/-! ## The twin's walk, named -/

/-- The twin's arms of a node view, the memo insertion in the branches. -/
def hlbiArm (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) (fuel : Nat) (h : EIdx) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .app f a => do
    match ← ConRon.Arena.hasLooseBVarInGo memo w d fuel f with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h d (true, memo))
    | (false, memo) => do
      let r ← ConRon.Arena.hasLooseBVarInGo memo w d fuel a
      pure (ConRon.Arena.hasLooseBVarBIns h d r)
  | .lam ty b => do
    match ← ConRon.Arena.hasLooseBVarInGo memo w d fuel ty with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h d (true, memo))
    | (false, memo) => do
      let r ← ConRon.Arena.hasLooseBVarInGo memo w (d + 1) fuel b
      pure (ConRon.Arena.hasLooseBVarBIns h d r)
  | .forallE ty b => do
    match ← ConRon.Arena.hasLooseBVarInGo memo w d fuel ty with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h d (true, memo))
    | (false, memo) => do
      let r ← ConRon.Arena.hasLooseBVarInGo memo w (d + 1) fuel b
      pure (ConRon.Arena.hasLooseBVarBIns h d r)
  | .letE t v b => do
    match ← ConRon.Arena.hasLooseBVarInGo memo w d fuel t with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h d (true, memo))
    | (false, memo) => do
      match ← ConRon.Arena.hasLooseBVarInGo memo w d fuel v with
      | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h d (true, memo))
      | (false, memo) => do
        let r ← ConRon.Arena.hasLooseBVarInGo memo w (d + 1) fuel b
        pure (ConRon.Arena.hasLooseBVarBIns h d r)
  | .proj _ _ sub => do
    let r ← ConRon.Arena.hasLooseBVarInGo memo w d fuel sub
    pure (ConRon.Arena.hasLooseBVarBIns h d r)
  | _ => pure (ConRon.Arena.hasLooseBVarBIns h d (false, memo))

/-- The twin's walk after the `bvarB` cutoff. -/
def hlbiRestT (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) (fuel : Nat) (h : EIdx) :
    AM (Bool × Std.HashMap (EIdx × Nat) Bool) := do
  let v ← view h
  match v with
  | .bvar j => pure (decide (d ≤ j) && decide (j - d < w), memo)
  | .fvar _ _ => pure (false, memo)
  | .sort _ => pure (false, memo)
  | .const _ _ => pure (false, memo)
  | .lit _ => pure (false, memo)
  | v =>
    match memo[(h, d)]? with
    | some r => pure (r, memo)
    | none => hlbiArm memo w d fuel h v

theorem hasLooseBVarInGo_succ' (memo : Std.HashMap (EIdx × Nat) Bool) (w d fuel : Nat) (h : EIdx) :
    ConRon.Arena.hasLooseBVarInGo memo w d (fuel + 1) h = (do
      let bb ← bvarB fuel h
      if bb ≤ d then pure (false, memo) else hlbiRestT memo w d fuel h) := by
  rw [ConRon.Arena.hasLooseBVarInGo.eq_2]
  rfl

theorem hlbiTwin_node (memo : Std.HashMap (EIdx × Nat) Bool) (w d fuel : Nat) (h : EIdx) (a : AState)
    (v : ENodeView) (hv : a.store.view h = some v) (hnv : HNodeV v) :
    (hlbiRestT memo w d fuel h).run a =
      ((match memo[(h, d)]? with
        | some r => pure (r, memo)
        | none => hlbiArm memo w d fuel h v : AM (Bool × Std.HashMap (EIdx × Nat) Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (simp only [hlbiRestT, StateT.run_bind]; rw [view_run _ a _ hv, except_ok_bind])

/-- `HlbiOK n`: the word model at depth `n` and fuel word `f` refines the twin at fuel `f.toNat`. -/
def HlbiOK (vis : Word) (fe : IFEnv) (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (f w d h : Word) (mp : Std.HashMap (EIdx × Nat) Bool),
    StageR vis fe m a → H h → hbMR m mp →
    Sim (hlbiW n m f w d h) (ConRon.Arena.hasLooseBVarInGo mp w.toNat d.toNat f.toNat (decE h)) a
      (HbQ vis fe m)

/-- The memo insertion closing every arm. -/
theorem hlbiIns_sim {vis : Word} {fe : IFEnv} {m m1 : Mem} {a1 : AState} {h d r : Word}
    {x : Bool × Std.HashMap (EIdx × Nat) Bool} (hh : H h) (hQ : HbQ vis fe m r x m1 a1) :
    Sim (hbInsW m1 h d r) (pure (ConRon.Arena.hasLooseBVarBIns (decE h) d.toNat x) :
      AM (Bool × Std.HashMap (EIdx × Nat) Bool)) a1 (HbQ vis fe m) := by
  intro r' m' hb
  obtain ⟨rfl, hM1, hS1, hg1⟩ := hQ
  obtain ⟨hr', hM2, hfr2⟩ := hbIns_ok hh rfl hM1 hb
  obtain ⟨hS2, hg2⟩ := L.Ind.StageR.frame_hi hS1 hfr2 (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  exact ⟨_, a1, rfl, by rw [hr']; rfl, hM2, hS2, hg1.trans hg2⟩

/-- The second call of an `or` arm and the insertion (`k_has_loose_bvar_in_go_2`). -/
theorem hlbiSecond_ok {vis : Word} {fe : IFEnv} (n : Nat) (ih : HlbiOK vis fe n) (m m1 : Mem) (a1 : AState)
    (f w d2 d h y : Word) (mp1 : Std.HashMap (EIdx × Nat) Bool) (hh : H h) (hy : H y)
    (hS1 : StageR vis fe m1 a1) (hM1 : hbMR m1 mp1) (hg1 : IWGrow m m1) :
    Sim (hlbiW.k_has_loose_bvar_in_go_2 d h (hlbiW n m1 (f - 1) w d2 y)) (do
        let r ← ConRon.Arena.hasLooseBVarInGo mp1 w.toNat d2.toNat (f - 1).toNat (decE y)
        pure (ConRon.Arena.hasLooseBVarBIns (decE h) d.toNat r) : AM (Bool × Std.HashMap (EIdx × Nat) Bool))
      a1 (HbQ vis fe m) := by
  refine Sim.bindK (hlbiW.k_has_loose_bvar_in_go_2.none ..) (fun _ _ => rfl) (ih m1 a1 _ w d2 y mp1 hS1 hy hM1) ?_
  intro r x m2 a2 ⟨h1, h2, h3, h4⟩
  rw [hlbiW.k_has_loose_bvar_in_go_2.arm1, hlbiW.j1.arm1]
  exact hlbiIns_sim hh ⟨h1, h2, h3, hg1.trans h4⟩

theorem hlbi_bvar_word (d x w : Word) :
    ((if d ≤ x then (1 : Word) else 0) &&& if x - d < w then 1 else 0) =
      if (decide (d.toNat ≤ x.toNat) && decide (x.toNat - d.toNat < w.toNat)) = true then 1 else 0 := by
  by_cases h1 : d ≤ x
  · have h1' : d.toNat ≤ x.toNat := UInt64.le_iff_toNat_le.mp h1
    have e : (x - d).toNat = x.toNat - d.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ h1]
    by_cases h2 : x - d < w
    · have h2' : x.toNat - d.toNat < w.toNat := by rw [← e]; exact UInt64.lt_iff_toNat_lt.mp h2
      simp [h1, h2, h1', h2']
    · have h2' : ¬ x.toNat - d.toNat < w.toNat := fun c => h2 (UInt64.lt_iff_toNat_lt.mpr (by rw [e]; exact c))
      simp [h1, h2, h1', h2']
  · have h1' : ¬ d.toNat ≤ x.toNat := fun c => h1 (UInt64.le_iff_toNat_le.mpr c)
    simp [h1, h1']

theorem hlbiGo_step_ok {vis : Word} {fe : IFEnv} (j : Nat)
    (ih : HlbiOK vis fe j) : HlbiOK vis fe (j + 1) := by
  intro m a f w d h mp hS hh hM
  by_cases hf0 : f = 0
  · rw [hlbiW.abort1 (hc1 := hf0)]; exact Sim.of_none
  have hF : f.toNat = (f - 1).toNat + 1 := by
    have : f.toNat ≠ 0 := fun e => hf0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [hlbiW.arm1 j m f w d h hf0, hF, hasLooseBVarInGo_succ']
  refine Sim.bindD (hlbiW.k_bvar_b.none ..) (fun _ _ => rfl) (Sim.ofD fun bb m1 hst =>
    bvbW_stageW vis fe hS j _ (f - 1) (.inl (Nat.le_refl _)) h bb hh hst) ?_
  rintro bb m1 a1 ⟨hS1, hg1, hfr⟩
  have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR _ _ (by simp [hbSch, HBM, BMEMO])
    (by simp [hbSch]) m m1 hfr (fun _ _ h => h) mp hM
  by_cases hle : bb ≤ d
  · rw [hlbiW.k_bvar_b.arm1 (hc1 := hle), ite_eq_left (UInt64.le_iff_toNat_le.mp hle)]
    exact Sim.ret ⟨rfl, hM1, hS1, hg1⟩
  rw [ite_eq_right fun c => hle (UInt64.le_iff_toNat_le.mpr c)]
  by_cases hvn : eViewW m1 h = []
  · rw [hlbiW.k_bvar_b.abort1 (hc1 := hle) (hc2 := hvn)]; exact Sim.of_none
  obtain ⟨v, hv, hvr⟩ := eViewW_ok m1 a1 hS1.check.arena.base h hvn
  obtain ⟨g, vt, hvl⟩ : ∃ g vt, eViewW m1 h = g :: vt := by
    cases e : eViewW m1 h with
    | nil => exact absurd e hvn
    | cons g vt => exact ⟨g, vt, rfl⟩
  rw [hvl] at hvr
  cases v with
  | bvar i' =>
    have hg0 : g = 0 := by simpa [ViewR] using hvr.1
    have hi' : ((g :: vt).tail.headD 0).toNat = i' := by rw [← L.getD_one]; exact hvr.2
    rw [hlbiW.k_bvar_b.arm2 (hc1 := hle) (hc2 := hvn) (hc3 := by rw [hvl]; exact hg0)]
    unfold hlbiRestT
    refine Sim.bind_twin (view_run _ a1 _ hv) (Sim.ret ⟨?_, hM1, hS1, hg1⟩)
    rw [hvl]
    generalize (g :: vt).tail.headD 0 = xx at hi' ⊢
    subst hi'
    exact hlbi_bvar_word d xx w
  | fvar _ _ | sort _ | const _ _ | lit _ =>
    have hg0 : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 8 := by
      simp only [ViewR, List.headD_cons] at hvr; first | simp [hvr.1] | simp [hvr]
    rw [hlbiW.k_bvar_b.arm3 (hc1 := hle) (hc2 := hvn)
      (hc3 := by rw [hvl]; rcases hg0 with e | e | e | e <;> simp [e])
      (hc4 := by rw [hvl]; simpa using hg0)]
    unfold hlbiRestT
    exact Sim.bind_twin (view_run _ a1 _ hv) (Sim.ret ⟨rfl, hM1, hS1, hg1⟩)
  | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | proj _ _ _ =>
    have hgs : g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 9 := by
      have := hvr.1; simp only [List.headD_cons] at this; simp [this]
    have hc3 : (eViewW m1 h).headD 0 ≠ 0 := by rw [hvl]; rcases hgs with e | e | e | e | e <;> simp [e]
    have hc4 : ¬ ((eViewW m1 h).headD 0 = 1 ∨ (eViewW m1 h).headD 0 = 2 ∨ (eViewW m1 h).headD 0 = 3 ∨
        (eViewW m1 h).headD 0 = 8) := by
      rw [hvl]; rcases hgs with e | e | e | e | e <;> simp [e]
    by_cases hd : 4294967296 ≤ d
    · rw [hlbiW.k_bvar_b.abort2 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd)]
      exact Sim.of_none
    refine Sim.ofRun (hlbiTwin_node _ _ _ _ _ a1 _ hv trivial) ?_
    by_cases hfr : mfindG hbSch m1 h d = []
    · rw [hlbiW.k_bvar_b.abort3 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd) (hc6 := hfr)]
      exact Sim.of_none
    have hk : lfKey.ok h d := hh
    by_cases hhit : (mfindG hbSch m1 h d).headD 0 ≠ 0
    · rw [hlbiW.k_bvar_b.arm4 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd) (hc6 := hfr)
        (hc7 := hhit)]
      obtain ⟨b, hb1, hb2⟩ := memoRV_hit hbSch lfKey hbVR m1 mp hM1 h d hfr hhit hk
      change mp[(decE h, d.toNat)]? = _ at hb1
      simp only [hb1]
      exact Sim.ret ⟨hb2, hM1, hS1, hg1⟩
    have hmiss := memoRV_miss hbSch lfKey hbVR m1 mp hM1 h d hk hfr (by simpa using hhit)
    change mp[(decE h, d.toNat)]? = _ at hmiss
    simp only [hmiss]
    have hd1 : (d + 1).toNat = d.toNat + 1 := word_toNat_add_one hd
    have hmiss' : (mfindG hbSch m1 h d).headD 0 = 0 := by simpa using hhit
    -- the arms
    have orArm : ∀ (m1' : Mem) (a1' : AState) (mp' : Std.HashMap (EIdx × Nat) Bool),
        StageR vis fe m1' a1' → hbMR m1' mp' → IWGrow m m1' →
        ∀ (d2 x y : Word) (K : Option (Word × Mem) → Option (Word × Mem)),
        H x → H y → K none = none → (∀ r1 m2, r1 = 1 → K (some (r1, m2)) = hbInsW m2 h d 1) →
        (∀ r1 m2, r1 ≠ 1 → K (some (r1, m2)) =
          hlbiW.k_has_loose_bvar_in_go_2 d h (hlbiW j m2 (f - 1) w d2 y)) →
        Sim (K (hlbiW j m1' (f - 1) w d x)) (do
          match ← ConRon.Arena.hasLooseBVarInGo mp' w.toNat d.toNat (f - 1).toNat (decE x) with
          | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns (decE h) d.toNat (true, memo))
          | (false, memo) => do
            let r ← ConRon.Arena.hasLooseBVarInGo memo w.toNat d2.toNat (f - 1).toNat (decE y)
            pure (ConRon.Arena.hasLooseBVarBIns (decE h) d.toNat r) :
            AM (Bool × Std.HashMap (EIdx × Nat) Bool)) a1' (HbQ vis fe m) := by
      intro m1' a1' mp' hS1' hM1' hg1' d2 x y K hx hy hK0 hK1 hK2
      refine Sim.bindK hK0 (fun _ _ => rfl) (ih m1' a1' _ w d x mp' hS1' hx hM1') ?_
      rintro r1 ⟨_ | _, mp2⟩ m2 a2 ⟨rfl, hM2, hS2, hg2⟩
      · rw [hK2 _ _ (by simp)]
        exact hlbiSecond_ok j ih m m2 a2 f w d2 d h y mp2 hh hy hS2 hM2 (hg1'.trans hg2)
      · rw [hK1 _ _ (by simp)]
        exact hlbiIns_sim hh ⟨rfl, hM2, hS2, hg1'.trans hg2⟩
    unfold hlbiArm
    all_goals first
      | (simp only [ViewR, L.getD_one, L.getD_two, List.headD_cons] at hvr
         obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
         rw [hlbiW.k_bvar_b.arm5 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd) (hc6 := hfr) (hc7 := hmiss') (hc8 := by rw [hvl]; exact hg), hvl]
         exact orArm m1 a1 mp hS1 hM1 hg1 d _ _ _ hx hy (hlbiW.k_has_loose_bvar_in_go.none ..)
           (fun r1 m2 e => by rw [hlbiW.k_has_loose_bvar_in_go.arm1 (hc1 := e), hlbiW.j1.arm1])
           (fun r1 m2 e => hlbiW.k_has_loose_bvar_in_go.arm2 (hc1 := e) ..))
      | (simp only [ViewR, L.getD_one, L.getD_two, List.headD_cons] at hvr
         obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
         rw [hlbiW.k_bvar_b.arm6 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd) (hc6 := hfr) (hc7 := hmiss') (hc8 := by rw [hvl]; simp [hg])
           (hc9 := by rw [hvl]; simp [hg]), hvl]
         have := orArm m1 a1 mp hS1 hM1 hg1 (d + 1) _ _ _ hx hy (hlbiW.k_has_loose_bvar_in_go_3.none ..)
           (fun r1 m2 e => by rw [hlbiW.k_has_loose_bvar_in_go_3.arm1 (hc1 := e), hlbiW.j1.arm1])
           (fun r1 m2 e => hlbiW.k_has_loose_bvar_in_go_3.arm2 (hc1 := e) ..)
         rw [hd1] at this
         exact this)
      | (simp only [ViewR, L.getD_one, L.getD_two, L.getD_three, List.headD_cons] at hvr
         obtain ⟨hg, hx, rfl, hy, rfl, hz, rfl⟩ := hvr
         rw [hlbiW.k_bvar_b.arm7 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd) (hc6 := hfr) (hc7 := hmiss') (hc8 := by rw [hvl]; simp [hg])
           (hc9 := by rw [hvl]; simp [hg]) (hc10 := by rw [hvl]; exact hg), hvl]
         refine Sim.bindK (hlbiW.k_has_loose_bvar_in_go_4.none ..) (fun _ _ => rfl)
           (ih m1 a1 _ w d _ mp hS1 hx hM1) ?_
         rintro r1 ⟨_ | _, mp2⟩ m2 a2 ⟨rfl, hM2, hS2, hg2⟩
         · rw [hlbiW.k_has_loose_bvar_in_go_4.arm2 (hc1 := by simp)]
           have := orArm m2 a2 mp2 hS2 hM2 (hg1.trans hg2) (d + 1) _ _ _ hy hz
             (hlbiW.k_has_loose_bvar_in_go_5.none ..)
             (fun r1 m3 e => by rw [hlbiW.k_has_loose_bvar_in_go_5.arm1 (hc1 := e), hlbiW.j1.arm1])
             (fun r1 m3 e => hlbiW.k_has_loose_bvar_in_go_5.arm2 (hc1 := e) ..)
           rw [hd1] at this
           exact this
         · rw [hlbiW.k_has_loose_bvar_in_go_4.arm1 (hc1 := by simp), hlbiW.j1.arm1]
           exact hlbiIns_sim hh ⟨rfl, hM2, hS2, hg1.trans hg2⟩)
      | (simp only [ViewR, L.getD_one, L.getD_two, L.getD_three, List.headD_cons] at hvr
         obtain ⟨hg, hx, hdx, -, hz, rfl⟩ := hvr
         rw [hlbiW.k_bvar_b.arm8 (hc1 := hle) (hc2 := hvn) (hc3 := hc3) (hc4 := hc4) (hc5 := hd) (hc6 := hfr) (hc7 := hmiss') (hc8 := by rw [hvl]; simp [hg])
           (hc9 := by rw [hvl]; simp [hg]) (hc10 := by rw [hvl]; simp [hg]), hvl]
         exact hlbiSecond_ok j ih m m1 a1 f w d d h _ mp hh hz hS1 hM1 hg1)

theorem hlbiGoOK {vis : Word} {fe : IFEnv} (n : Nat) : HlbiOK vis fe n := by
  induction n with
  | zero => intro m a f w d h mp _ _ _; rw [hlbiW.eq_1]; exact Sim.of_none
  | succ j ih => exact hlbiGo_step_ok j ih

/-! ## `has_loose_bvar_in` -/

/-- **`has_loose_bvar_in(d, w, e)` is its model `hlbiFW`** (generated). -/
l_model hlbiF_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
    (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
    (hgo : p.lookup "has_loose_bvar_in_go" = some hasLooseBVarInGoL) (hbp : BvbProg p)
    (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hp : p.lookup "has_loose_bvar_in" = some hasLooseBVarInL)
  fns [hp ↦ hlbiFW]
  specs [memoClearG_spec hbSch p _ hcl n, hlbiGo_spec p hv hf hput hins hgo hbp n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] pfuel

theorem hlbiFW_ok {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (d w e r : Word) (mp0 : Std.HashMap (EIdx × Nat) Bool)
    (hh : H e) (hS : StageR vis fe m a) (hM : hbMR m mp0)
    (hm : hlbiFW n m d w e = some (r, m')) :
    ∃ b a', (ConRon.Arena.hasLooseBVarIn d.toNat w.toNat (decE e)).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ (∃ mp1, hbMR m' mp1) ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  by_cases hw0 : w = 0
  · rw [hlbiFW.arm1 (hc1 := hw0)] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    have : w.toNat = 0 := by rw [hw0]; rfl
    exact ⟨false, a, by simp [ConRon.Arena.hasLooseBVarIn, this]; rfl, rfl, ⟨mp0, hM⟩, hS, IWGrow.refl m⟩
  have hw0' : (w.toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hw0 (UInt64.toNat_inj.mp e)
  by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
  · rw [hlbiFW.abort1 (hc1 := hw0) (hc2 := h0)] at hm; cases hm
  rw [hlbiFW.arm2 (hc1 := hw0) (hc2 := h0)] at hm
  have hf0 := mclearG_frame hbSch m
  have hM0 := memoRV_clear hbSch hbSch_wf lfKey hbVR m mp0 hM h0
  have key := L.Ind.StageR.frame_hi hS hf0 (by simp) (by
      intro x hx; simp [hbSch] at hx; rcases hx with rfl | rfl <;> decide) (by simp) (by simp [hbSch])
  obtain ⟨⟨b, mp1⟩, a', hrun, hb, hM1, hS1, hg⟩ := hlbiGoOK n _ a CWF w d e ∅ key.1 hh hM0 _ _ hm
  refine ⟨b, a', ?_, hb, ⟨mp1, hM1⟩, hS1, key.2.trans hg⟩
  simp only [ConRon.Arena.hasLooseBVarIn, hw0', Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
  rw [CWF_eq] at hrun
  rw [hrun]
  rfl

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_bvar_in_go" = some hasLooseBVarInGoL) (hbp : BvbProg p)
  (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
  (hp : p.lookup "has_loose_bvar_in" = some hasLooseBVarInL)

include hv hf hput hins hgo hbp in
/-- **`has_loose_bvar_in_go` refines `hasLooseBVarInGo`** from a related memo, at the twin fuel
`f.toNat` of the L fuel word `f`, at every exec depth `n`. -/
@[refines ConRon.Arena.hasLooseBVarInGo]
theorem hasLooseBVarInGo_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis f w d h : Word) (mp : Std.HashMap (EIdx × Nat) Bool) (hh : H h)
    (hS : StageR vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_bvar_in_go" [f, w, d, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.hasLooseBVarInGo mp w.toNat d.toNat f.toNat (decE h)) a₀ ∧
      r.headD 0 = (if (AM.res (ConRon.Arena.hasLooseBVarInGo mp w.toNat d.toNat f.toNat (decE h)) a₀).1
        then 1 else 0) ∧
      hbMR s'.mem (AM.res (ConRon.Arena.hasLooseBVarInGo mp w.toNat d.toNat f.toNat (decE h)) a₀).2 ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.hasLooseBVarInGo mp w.toNat d.toNat f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (hlbiGo_spec p hv hf hput hins hgo hbp n s₀ f w d h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨⟨b, mp'⟩, a', hrun, hb, hM', hS', hg⟩ := hlbiGoOK n _ a₀ f w d h mp hS hh hM _ _ hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

include hv hf hput hins hgo hbp hcl hp in
/-- **`has_loose_bvar_in` refines `hasLooseBVarIn`**: an empty window asks nothing, else the `hb`
memo cleared (any well-formed one on entry) and one memoised walk from `coreWalkFuel`. -/
@[refines ConRon.Arena.hasLooseBVarIn]
theorem hasLooseBVarIn_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis d w e : Word) (mp0 : Std.HashMap (EIdx × Nat) Bool)
    (hh : H e) (hS : StageR vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "has_loose_bvar_in" [d, w, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.hasLooseBVarIn d.toNat w.toNat (decE e)) a₀ ∧
      r.headD 0 = (if AM.res (ConRon.Arena.hasLooseBVarIn d.toNat w.toNat (decE e)) a₀ then 1 else 0) ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.hasLooseBVarIn d.toNat w.toNat (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (hlbiF_spec p hv hf hput hins hgo hbp hcl hp n s₀ d w e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun', hb, hM1, hS1, hg⟩ := hlbiFW_ok n _ _ a₀ d w e _ mp0 hh hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  exact ⟨hl, hok, by rw [hres]; exact hb, hM1, by rw [hst]; exact hS1, hg⟩

end census

end L.Ind
