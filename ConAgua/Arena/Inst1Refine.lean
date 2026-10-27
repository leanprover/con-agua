import ConAgua.Arena.Inst1Spec
import ConAgua.Arena.LiftRefine
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `inst_go` refines the arena's `instantiate1Go`

`LiftRefine.lean`'s proof for the second walk: the same libraries (the projections per tag of
`View.lean`, the cut-off `derBW_ok`, the memo, `mk*_ok`, `internBVar_D`), the dispatcher by the
tag (`decE_tag`), the arms probing the memo before the view.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The `instantiate1` memo under `ArenaD` -/

/-- The arena state with the `instantiate1` memo replaced. -/
def withIC (a : AState) (mp : Std.HashMap (EIdx × Nat) EIdx) : AState :=
  { a with memos := { a.memos with inst1C := mp } }

theorem inst1Get_run (x : EIdx × Nat) (a : AState) :
    (inst1Get x).run a = .ok (a.memos.inst1C[x]?, a) := rfl

theorem inst1Set_run (x : EIdx × Nat) (r : EIdx) (a : AState) :
    (inst1Set x r).run a = .ok ((), withIC a (a.memos.inst1C.insert x r)) := rfl

theorem inst1Clear_run (a : AState) : inst1Clear.run a = .ok ((), withIC a ∅) := rfl

theorem ArenaD.imemo_set (m m' : Mem) (a : AState) (hA : ArenaD m a) (h c v : Word)
    (hh : h.toNat < 2 ^ 32) (hs : msetG imSch m h c v = some m') :
    ArenaD m' (withIC a (a.memos.inst1C.insert (decE h, c.toNat) (decE v))) := by
  have hf := msetG_frame imSch imSch_wf m m' h c v hs
  refine ⟨?_, DerR.of_store m' a _ (DerR.frameM _ _ m m' hf (by simp [IMEMO]) _ hA.2) rfl⟩
  exact hA.1.with_memos hf (by apart) (by apart) (by
    memos_build hA.1.memos, hf with
      exact memoRG_set imSch imSch_wf lfKey decE m _ hA.1.memos.inst1 h c v hh m' hs)

theorem ArenaD.imemo_clear (m : Mem) (a : AState) (hA : ArenaD m a)
    (h0 : rdW (m.arr64 CTL) 44 + 2 ≠ 0) : ArenaD (mclearG imSch m) (withIC a ∅) := by
  have hf := mclearG_frame imSch m
  refine ⟨?_, DerR.of_store _ a _ (DerR.frameM _ _ m _ hf (by simp) _ hA.2) rfl⟩
  exact hA.1.with_memos hf (by apart) (by apart) (by
    memos_build hA.1.memos, hf with
      exact memoRG_clear imSch imSch_wf lfKey decE m _ hA.1.memos.inst1 h0)

theorem viewBVar_run (h : EIdx) (a : AState) :
    (viewBVar h).run a = .ok (a.store.viewBVar h, a) := rfl
theorem viewApp_run (h : EIdx) (a : AState) :
    (viewApp h).run a = .ok (a.store.viewApp h, a) := rfl
theorem viewBind_run (h : EIdx) (a : AState) :
    (viewBind h).run a = .ok (a.store.viewBind h, a) := rfl
theorem viewLet_run (h : EIdx) (a : AState) :
    (viewLet h).run a = .ok (a.store.viewLet h, a) := rfl
theorem viewProj_run (h : EIdx) (a : AState) :
    (viewProj h).run a = .ok (a.store.viewProj h, a) := rfl

/-! ## The arms' probe and tail -/

theorem itail_ok (op : AM EIdx) (mkr : Option (Word × Mem)) (a₂ : AState) (h c r : Word) (m' : Mem)
    (hh : h.toNat < 2 ^ 32)
    (hmk : ∀ r₃ m₃, mkr = some (r₃, m₃) →
      AM.ok op a₂ ∧ ArenaD m₃ (AM.st op a₂) ∧ AM.res op a₂ = decE r₃)
    (hb : instAppW.k_mk_app h c mkr = some (r, m')) :
    ∃ a', (do let r ← op; inst1Set (decE h, c.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaD m' a' := by
  cases h3 : mkr with
  | none => simp [h3, instAppW.k_mk_app] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    by_cases hr : mfindG imSch m₃ h c = []
    · simp [instAppW.k_mk_app, hr] at hb
    rw [instAppW.k_mk_app.arm1 h c r₃ m₃ hr] at hb
    cases h4 : mputG imSch m₃ h c r₃ ((mfindG imSch m₃ h c).headD 0)
        ((mfindG imSch m₃ h c).tail.headD 0) with
    | none => rw [h4] at hb; simp [instAppW.k_if_put] at hb
    | some m₄ =>
      rw [h4, instAppW.k_if_put.arm1, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hs : msetG imSch m₃ h c r₃ = some m₄ := by rw [msetG, ite_eq_right hr]; exact h4
      obtain ⟨hok, hA₃, hres⟩ := hmk r₃ m₃ h3
      refine ⟨_, ?_, ArenaD.imemo_set m₃ m₄ _ hA₃ h c r₃ hh hs⟩
      simp only [StateT.run_bind, AM.run_of_ok _ _ hok, hres, except_ok_bind, inst1Set_run]; rfl

theorem iprobe_ok (armW : Option (Word × Mem)) (miss : AM EIdx) (m m' : Mem) (a : AState)
    (hA : ArenaD m a) (h c r : Word) (hh : h.toNat < 2 ^ 32)
    (hhit : mfindG imSch m h c ≠ [] → (mfindG imSch m h c).headD 0 ≠ 0 →
      armW = some (rdW (m.arr64 IMEMO) ((mfindG imSch m h c).tail.headD 0 * 4 + 3), m))
    (hnone : mfindG imSch m h c = [] → armW = none)
    (hmiss : mfindG imSch m h c ≠ [] → (mfindG imSch m h c).headD 0 = 0 → armW = some (r, m') →
      ∃ a', miss.run a = .ok (decE r, a') ∧ ArenaD m' a')
    (hb : armW = some (r, m')) :
    ∃ a', (do
        match ← inst1Get (decE h, c.toNat) with
        | some r => pure r
        | none => miss : AM EIdx).run a = .ok (decE r, a') ∧ ArenaD m' a' := by
  rw [StateT.run_bind, inst1Get_run, except_ok_bind]
  by_cases hr : mfindG imSch m h c = []
  · rw [hnone hr] at hb; cases hb
  by_cases hh0 : (mfindG imSch m h c).headD 0 ≠ 0
  · rw [hhit hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.inst1C[(decE h, c.toNat)]? = _ from
      memoRG_hit imSch lfKey decE m _ hA.1.memos.inst1 h c hr hh0 hh]
    exact ⟨a, rfl, hA⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [show a.memos.inst1C[(decE h, c.toNat)]? = none from
      memoRG_miss imSch lfKey decE m _ hA.1.memos.inst1 h c hh hr hh0]
    exact hmiss hr hh0 hb

/-! ## The statements, by fuel -/

/-- What `inst_go`'s model at L fuel `n` and counter `fu` says about the arena walk at the twin
fuel `fu.toNat` (exactly: the counter is the twin's `fuel`; any L fuel). -/
def IGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d v fu r : Word), ArenaD m a →
    h.toNat < 2 ^ 32 → instW n m h d v fu = some (r, m') →
    ∃ a', (instantiate1Go (decE v) fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧
      ArenaD m' a'

/-- The arena arm `arm` refines the L arm `armW` (with its counter) at `h`, under `ArenaD`. -/
def IArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h d v fu r : Word) : Prop :=
  armW n m h d v fu = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaD m' a'

/-- The five arms, each at its tag. -/
def IArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d v fu r : Word), ArenaD m a →
    h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 →
      IArmRef n instAppW (instantiate1ArmApp (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r) ∧
    (h >>> 28 = 5 →
      IArmRef n instLamW (instantiate1ArmBind (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r) ∧
    (h >>> 28 = 6 →
      IArmRef n instForallW (instantiate1ArmBind (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r) ∧
    (h >>> 28 = 7 →
      IArmRef n instLetW (instantiate1ArmLet (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r) ∧
    (h >>> 28 = 9 →
      IArmRef n instProjW (instantiate1ArmProj (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r)

/-! ## The dispatcher -/

/-- The tag word and its `UInt32` (the twin's `h.tag`). -/
theorem tag_iff (h g : Word) (hh : h.toNat < 2 ^ 32) (hg : g.toNat < 16) :
    h >>> 28 = g ↔ (h >>> 28).toUInt32 = g.toUInt32 := by
  have hl : (h >>> 28).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]; simp only [Nat.shiftRight_eq_div_pow]; simp; omega
  constructor
  · intro e; rw [e]
  · intro e
    have e' := congrArg UInt32.toNat e
    simp only [UInt64.toNat_toUInt32] at e'
    apply UInt64.toNat_inj.mp
    omega

theorem igoOK_succ (n : Nat) (ih : IArmOK n) : IGoOK (n + 1) := by
  intro m m' a h d v fu r hA hh hb
  by_cases hfu : fu = 0
  · rw [instW] at hb; simp [hfu] at hb
  have hd := derBW_ok m a hA.1 hA.2 h hh
  rw [ctrW_toNat fu hfu, instantiate1Go_succ, StateT.run_bind, derivedE_run]
  simp only [except_ok_bind]
  by_cases hcut : derBW m h < 32767 ∧ derBW m h ≤ d
  · rw [instW.arm1 n m h d v fu hfu hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [hd, cut_iff] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA⟩
  have hcut' := hcut
  rw [hd, cut_iff] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih m m' a h d v (fu - 1) r hA hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : h >>> 28 = 0 ↔ (h >>> 28).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [instW.arm2 n m h d v fu hfu hcut g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [instW.arm3 n m h d v fu hfu hcut g4 g5] at hb
    simp only [show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [instW.arm4 n m h d v fu hfu hcut g4 g5 g6] at hb
    simp only [show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · simp only [show (h >>> 28).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
    · rw [instW] at hb; simp [hfu, hcut, g0, hs] at hb
    by_cases hc : tcnt m BVAR (tierW h) ≤ idxW h
    · rw [instW] at hb; simp [hfu, hcut, g0, hs, hc] at hb
    have hv : viewOK m h BVAR := ⟨hs, UInt64.not_le.mp hc⟩
    rw [instantiate1ArmBVar, StateT.run_bind, viewBVar_run, viewBVar_ok m a hA.1 h hh hv]
    simp only [except_ok_bind]
    by_cases he : tfld m BVAR (tierW h) (idxW h) 0 = d
    · rw [instW.arm5 n m h d v fu hfu hcut g4 g5 g6 g0 hs hc he] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      simp only [he, ↓reduceIte]; exact ⟨a, rfl, hA⟩
    have he' : ¬ (tfld m BVAR (tierW h) (idxW h) 0).toNat = d.toNat :=
      fun e => he (UInt64.toNat_inj.mp e)
    by_cases hl : d < tfld m BVAR (tierW h) (idxW h) 0
    · rw [instW.arm6 n m h d v fu hfu hcut g4 g5 g6 g0 hs hc he hl] at hb
      obtain ⟨hok, hA', hres⟩ := internBVar_D m a hA _ r m' hb
      have hl' : (tfld m BVAR (tierW h) (idxW h) 0).toNat > d.toNat := hl
      have hsub : (tfld m BVAR (tierW h) (idxW h) 0 - 1).toNat =
          (tfld m BVAR (tierW h) (idxW h) 0).toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
      simp only [he', hl', ↓reduceIte, internBVarE]
      rw [← hsub, AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, hA'⟩
    · rw [instW.arm7 n m h d v fu hfu hcut g4 g5 g6 g0 hs hc he hl] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hl' : ¬ (tfld m BVAR (tierW h) (idxW h) 0).toNat > d.toNat := fun e => hl e
      simp only [he', hl', ↓reduceIte]; exact ⟨a, rfl, hA⟩
  have g0' : ¬ (h >>> 28).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [instW.arm8 n m h d v fu hfu hcut g4 g5 g6 g0 g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [instW.arm9 n m h d v fu hfu hcut g4 g5 g6 g0 g7 g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  rw [instW.arm10 n m h d v fu hfu hcut g4 g5 g6 g0 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA⟩

/-! ## The arms -/

section arms
variable (n : Nat) (ih : IGoOK n) (m m' : Mem) (a : AState) (hA : ArenaD m a)
  (h d v fu r : Word) (hh : h.toNat < 2 ^ 32)
include ih hA hh

theorem iappArm_ok (hg : h >>> 28 = 4) :
    IArmRef (n + 1) instAppW (instantiate1ArmApp (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r := by
  intro hb
  rw [instantiate1ArmApp]
  refine iprobe_ok _ _ m m' a hA h d r hh (instAppW.arm1 n m h d v fu)
    (fun hr => by rw [instAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [instAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : tcnt m APP (tierW h) ≤ idxW h
  · rw [instAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb
  have hv : viewOK m h APP := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1 h hh hv hg
  rw [instAppW.arm2 n m h d v fu hr hh0 hs hc] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1 h hh hv, except_ok_bind]
  cases h1 : instW n m (tfld m APP (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, instAppW.k_inst_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : instW n m₁ (tfld m APP (tierW h) (idxW h) 1) d v fu with
  | none => simp [h1, h2, instAppW.k_inst_go, instAppW.k_inst_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, instAppW.k_inst_go, instAppW.k_inst_go_2] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ d v fu y hA₁ haw h2
  obtain ⟨a', h3, h4⟩ := itail_ok _ _ a₂ h d r m' hh (fun r₃ m₃ h => mkApp_ok m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem ilamArm_ok (hg : h >>> 28 = 5) :
    IArmRef (n + 1) instLamW (instantiate1ArmBind (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r := by
  intro hb
  by_cases hd1 : d + 1 = 0
  · rw [instLamW] at hb; simp [hd1] at hb
  rw [instantiate1ArmBind]
  refine iprobe_ok _ _ m m' a hA h d r hh (instLamW.arm1 n m h d v fu hd1)
    (fun hr => by rw [instLamW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [instLamW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : tcnt m LAM (tierW h) ≤ idxW h
  · rw [instLamW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1 h hh hv hg
  rw [instLamW.arm2 n m h d v fu hd1 hr hh0 hs hc] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1 h hh hv hg, except_ok_bind]
  cases h1 : instW n m (tfld m LAM (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, instLamW.k_inst_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : instW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (d + 1) v fu with
  | none => simp [h1, h2, instLamW.k_inst_go, instLamW.k_inst_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, instLamW.k_inst_go, instLamW.k_inst_go_2] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ (d + 1) v fu y hA₁ haw h2
  rw [succW_toNat d hd1] at ha₂
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  obtain ⟨a', h3, h4⟩ := itail_ok _ _ a₂ h d r m' hh
    (fun r₃ m₃ h => mkLam_ok m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind, hbind]; exact h3, h4⟩

theorem iforallArm_ok (hg : h >>> 28 = 6) :
    IArmRef (n + 1) instForallW (instantiate1ArmBind (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r := by
  intro hb
  by_cases hd1 : d + 1 = 0
  · rw [instForallW] at hb; simp [hd1] at hb
  rw [instantiate1ArmBind]
  refine iprobe_ok _ _ m m' a hA h d r hh (instForallW.arm1 n m h d v fu hd1)
    (fun hr => by rw [instForallW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [instForallW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : tcnt m FORALL (tierW h) ≤ idxW h
  · rw [instForallW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1 h hh hv hg
  rw [instForallW.arm2 n m h d v fu hd1 hr hh0 hs hc] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1 h hh hv hg, except_ok_bind]
  cases h1 : instW n m (tfld m FORALL (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, instForallW.k_inst_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : instW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (d + 1) v fu with
  | none => simp [h1, h2, instForallW.k_inst_go, instForallW.k_inst_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, instForallW.k_inst_go, instForallW.k_inst_go_2] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ (d + 1) v fu y hA₁ haw h2
  rw [succW_toNat d hd1] at ha₂
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  obtain ⟨a', h3, h4⟩ := itail_ok _ _ a₂ h d r m' hh
    (fun r₃ m₃ h => mkForall_ok m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind, hbind]; exact h3, h4⟩

theorem iletArm_ok (hg : h >>> 28 = 7) :
    IArmRef (n + 1) instLetW (instantiate1ArmLet (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r := by
  intro hb
  by_cases hd1 : d + 1 = 0
  · rw [instLetW] at hb; simp [hd1] at hb
  rw [instantiate1ArmLet]
  refine iprobe_ok _ _ m m' a hA h d r hh (instLetW.arm1 n m h d v fu hd1)
    (fun hr => by rw [instLetW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [instLetW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : tcnt m LET (tierW h) ≤ idxW h
  · rw [instLetW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1 h hh hv hg
  rw [instLetW.arm2 n m h d v fu hd1 hr hh0 hs hc] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1 h hh hv, except_ok_bind]
  cases h1 : instW n m (tfld m LET (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, instLetW.k_inst_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : instW n m₁ (tfld m LET (tierW h) (idxW h) 1) d v fu with
  | none => simp [h1, h2, instLetW.k_inst_go, instLetW.k_inst_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  cases h3 : instW n m₂ (tfld m LET (tierW h) (idxW h) 2) (d + 1) v fu with
  | none => simp [h1, h2, h3, instLetW.k_inst_go, instLetW.k_inst_go_2, instLetW.k_inst_go_3] at hb
  | some o =>
  obtain ⟨z, m₃⟩ := o
  simp only [h1, h2, h3, instLetW.k_inst_go, instLetW.k_inst_go_2, instLetW.k_inst_go_3] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA htw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ d v fu y hA₁ hvw h2
  obtain ⟨a₃, ha₃, hA₃⟩ := ih m₂ m₃ a₂ _ (d + 1) v fu z hA₂ hbw h3
  rw [succW_toNat d hd1] at ha₃
  obtain ⟨a', h4, h5⟩ := itail_ok _ _ a₃ h d r m' hh
    (fun r₄ m₄ h => mkLet_ok m₃ a₃ hA₃ x y z r₄ m₄ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, ha₃, except_ok_bind]; exact h4, h5⟩

theorem iprojArm_ok (hg : h >>> 28 = 9) :
    IArmRef (n + 1) instProjW (instantiate1ArmProj (decE v) fu.toNat (decE h) d.toNat) m m' a h d v fu r := by
  intro hb
  rw [instantiate1ArmProj]
  refine iprobe_ok _ _ m m' a hA h d r hh (instProjW.arm1 n m h d v fu)
    (fun hr => by rw [instProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [instProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : tcnt m PROJ (tierW h) ≤ idxW h
  · rw [instProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1 h hh hv hg
  rw [instProjW.arm2 n m h d v fu hr hh0 hs hc] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1 h hh hv, except_ok_bind]
  cases h1 : instW n m (tfld m PROJ (tierW h) (idxW h) 2) d v fu with
  | none => simp [h1, instProjW.k_inst_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  simp only [h1, instProjW.k_inst_go] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hew h1
  obtain ⟨a', h3, h4⟩ := itail_ok _ _ a₁ h d r m' hh
    (fun r₃ m₃ h => mkProj_ok m₁ a₁ hA₁ _ _ x r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact h3, h4⟩

end arms

theorem iarmOK_succ (n : Nat) (ih : IGoOK n) : IArmOK (n + 1) := by
  intro m m' a h d v fu r hA hh
  exact ⟨iappArm_ok n ih m m' a hA h d v fu r hh, ilamArm_ok n ih m m' a hA h d v fu r hh,
    iforallArm_ok n ih m m' a hA h d v fu r hh, iletArm_ok n ih m m' a hA h d v fu r hh,
    iprojArm_ok n ih m m' a hA h d v fu r hh⟩

/-- **The model of `inst_go` refines `instantiate1Go`** at the counter's fuel, for every counter
word and every L fuel (the go-level theorem; the entry pins the counter at `coreWalkFuel`). -/
theorem instOK (n : Nat) : IGoOK n ∧ IArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ hb => by simp [instW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [instAppW, instLamW, instForallW, instLetW, instProjW] at hb
  | succ n ih => exact ⟨igoOK_succ n ih.2, iarmOK_succ n ih.1⟩

/-! ## The entry `inst_entry` refines `instantiate1Fast` -/

theorem instFast_run (F : Nat) (e v : EIdx) (d : Nat) (a : AState) :
    (instantiate1Fast F e v d).run a =
      ((instantiate1Go v F e d).run (withIC a ∅) >>= fun p => .ok (p.1, withIC p.2 ∅)) := by
  simp only [instantiate1Fast, StateT.run_bind, inst1Clear_run, except_ok_bind]
  cases (instantiate1Go v F e d).run (withIC a ∅) <;> rfl

/-- The entries' 32-bit mask keeps the handle (`WhnfDeltaRefine3.lean`'s `decE_mask32`). -/
theorem decE_and32 (y : Word) : decE (y &&& 4294967295) = decE y := by
  have h : (y &&& 4294967295).toUInt32 = y.toUInt32 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_and]
    rw [show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod]
  simp only [decE, h]

/-- The masked word is below `2^32` (`WhnfDeltaRefine3.lean`'s `hw_mask32`). -/
theorem and32_lt (y : Word) : (y &&& 4294967295).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_and, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem instEntryW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaD m a)
    (e v d r : Word) (he : e.toNat < 2 ^ 32) (hb : instEntryW (n + 1) m e v d = some (r, m')) :
    ∃ a', (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat).run a = .ok (decE r, a') ∧
      ArenaD m' a' ∧ r.toNat < 2 ^ 32 := by
  have hcs : imSch.cs = 44 := rfl
  by_cases h0 : rdW (m.arr64 CTL) 44 + 2 = 0
  · simp [instEntryW, h0] at hb
  rw [instEntryW.arm1 n m e v d (by rw [hcs]; exact h0)] at hb
  have hA₀ := ArenaD.imemo_clear m a hA h0
  cases hw : instW n (mclearG imSch m) e d v 4000000000 with
  | none => simp [hw, instEntryW.k_inst_go] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    by_cases h1 : rdW (m₁.arr64 CTL) 44 + 2 = 0
    · simp [hw, instEntryW.k_inst_go, h1] at hb
    rw [hw, instEntryW.k_inst_go.arm1 r₁ m₁ (by rw [hcs]; exact h1), Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁⟩ := (instOK n).1 _ _ _ e d v 4000000000 r₁ hA₀ he hw
    rw [coreWalkFuel_toNat] at ha₁
    exact ⟨_, by rw [instFast_run, ha₁, decE_and32]; rfl, ArenaD.imemo_clear m₁ a₁ hA₁ h1,
      and32_lt r₁⟩

/-- **`inst_entry` refines the arena's `instantiate1Fast coreWalkFuel` under `ArenaD`**, at every
L fuel (the walk's counter starts at `coreWalkFuel`). -/
@[refines ConRon.Arena.instantiate1Fast]
theorem instEntry_refines (p : Prog) (hp : InstProg p) (hpe : p.lookup "inst_entry" = some instEntry)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaD s₀.mem a₀) (e v d : Word)
    (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "inst_entry" [e, v, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) a₀ ∧
      ArenaD s'.mem (AM.st (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) a₀) ∧
      AM.res (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) a₀ = decE (r.headD 0) ∧
      (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (instEntry_spec p hp hpe (n + 1) s₀ e v d)
  subst hs
  obtain ⟨a', ha', hA', hlt⟩ := instEntryW_correct n _ _ a₀ hA e v d _ he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hlt⟩

end L.Arena
