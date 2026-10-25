import ConAgua.Arena.LiftSpec
import ConAgua.Arena.DerRel
import ConAgua.Arena.FVarRangeRefine
import ConRon.Arena.ExprOps
import ConAgua.Census.Attr

/-!
# `lift_go` refines the arena's `liftLooseBVarsGo`

By induction on L's fuel, as `WalkRefine.lean`: if the model `liftW n m h c k fu` returns `r` and
`m'` from `m` related to `a` by `ArenaD` (`ArenaR` and the derived ranges `DerR`), then
`liftLooseBVarsGo k.toNat fu.toNat (decE h) c.toNat` from `a` returns `decE r` in a state related
to `m'`: the counter word `fu` is the twin's fuel exactly, at any L fuel. The pieces come from the libraries: the view
per tag (`View.lean`), the cutoff (`derBW_ok`), the memo (`MemoLibRel.lean`), the interning of
the rebuilt nodes (`mk*_ok`, `internBVar_D`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The lift memo under `ArenaD` -/

/-- The arena state with the lift memo replaced. -/
def withLC (a : AState) (mp : Std.HashMap (EIdx × Nat) EIdx) : AState :=
  { a with memos := { a.memos with liftC := mp } }

theorem liftGet_run (x : EIdx × Nat) (a : AState) :
    (liftGet x).run a = .ok (a.memos.liftC[x]?, a) := rfl

theorem liftSet_run (x : EIdx × Nat) (r : EIdx) (a : AState) :
    (liftSet x r).run a = .ok ((), withLC a (a.memos.liftC.insert x r)) := rfl

theorem liftClear_run (a : AState) : liftClear.run a = .ok ((), withLC a ∅) := rfl

theorem derivedE_run (h : EIdx) (a : AState) : (derivedE h).run a = .ok (a.store.derived h, a) :=
  rfl

/-- **`find; put` on the lift memo is `liftSet`.** -/
theorem ArenaD.lmemo_set (m m' : Mem) (a : AState) (hA : ArenaD m a) (h c v : Word)
    (hh : h.toNat < 2 ^ 32) (hs : msetG lfSch m h c v = some m') :
    ArenaD m' (withLC a (a.memos.liftC.insert (decE h, c.toNat) (decE v))) := by
  have hf := msetG_frame lfSch lfSch_wf m m' h c v hs
  refine ⟨?_, DerR.of_store m' a _ (DerR.frameM _ _ m m' hf (by simp [LMEMO]) _ hA.2) rfl⟩
  exact hA.1.with_memos hf (by apart) (by apart) (by
    memos_build hA.1.memos, hf with
      exact memoRG_set lfSch lfSch_wf lfKey decE m _ hA.1.memos.lift h c v hh m' hs)

/-- **`lf_clear` is `liftClear`.** -/
theorem ArenaD.lmemo_clear (m : Mem) (a : AState) (hA : ArenaD m a)
    (h0 : rdW (m.arr64 CTL) 42 + 2 ≠ 0) : ArenaD (mclearG lfSch m) (withLC a ∅) := by
  have hf := mclearG_frame lfSch m
  refine ⟨?_, DerR.of_store _ a _ (DerR.frameM _ _ m _ hf (by simp) _ hA.2) rfl⟩
  exact hA.1.with_memos hf (by apart) (by apart) (by
    memos_build hA.1.memos, hf with
      exact memoRG_clear lfSch lfSch_wf lfKey decE m _ hA.1.memos.lift h0)

/-! ## The statements, by fuel -/

/-- What `lift_go`'s model at L fuel `n` and counter `fu` says about the arena walk at the twin
fuel `fu.toNat`. -/
def LGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h c k fu r : Word), ArenaD m a →
    h.toNat < 2 ^ 32 → liftW n m h c k fu = some (r, m') →
    ∃ a', (liftLooseBVarsGo k.toNat fu.toNat (decE h) c.toNat).run a = .ok (decE r, a') ∧
      ArenaD m' a'

/-- The arena arm `arm` refines the L arm `armW` (with its counter) at `h` (both read the memo
first). -/
def ArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h c k fu r : Word) : Prop :=
  armW n m h c k fu = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaD m' a'

/-- The same for the five arms, given the view checks of each. -/
def LArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h c k fu r : Word), ArenaD m a →
    h.toNat < 2 ^ 32 →
    (viewOK m h APP → h >>> 28 = 4 → ArmRef n liftAppW
      (liftArmApp k.toNat fu.toNat (decE h) c.toNat (decE (tfld m APP (tierW h) (idxW h) 0))
        (decE (tfld m APP (tierW h) (idxW h) 1))) m m' a h c k fu r) ∧
    (viewOK m h LAM → h >>> 28 = 5 → ArmRef n liftLamW
      (liftArmLam k.toNat fu.toNat (decE h) c.toNat
        (decE (tfld m LAM (tierW h) (idxW h) 0))
        (decE (tfld m LAM (tierW h) (idxW h) 1))) m m' a h c k fu r) ∧
    (viewOK m h FORALL → h >>> 28 = 6 → ArmRef n liftForallW
      (liftArmForallE k.toNat fu.toNat (decE h) c.toNat
        (decE (tfld m FORALL (tierW h) (idxW h) 0))
        (decE (tfld m FORALL (tierW h) (idxW h) 1))) m m' a h c k fu r) ∧
    (viewOK m h LET → h >>> 28 = 7 → ArmRef n liftLetW
      (liftArmLet k.toNat fu.toNat (decE h) c.toNat
        (decE (tfld m LET (tierW h) (idxW h) 0))
        (decE (tfld m LET (tierW h) (idxW h) 1))
        (decE (tfld m LET (tierW h) (idxW h) 2))) m m' a h c k fu r) ∧
    (viewOK m h PROJ → h >>> 28 = 9 → ArmRef n liftProjW
      (liftArmProj k.toNat fu.toNat (decE h) c.toNat
        (decI (tfld m PROJ (tierW h) (idxW h) 0))
        (tfld m PROJ (tierW h) (idxW h) 1).toNat
        (decE (tfld m PROJ (tierW h) (idxW h) 2))) m m' a h c k fu r)

/-! ## The dispatcher -/

/-- The arena dispatcher's arms on a view (`liftLooseBVarsGo`'s inner `match`), named. -/
def liftV (k F : Nat) (h : EIdx) (c : Nat) : ENodeView → AM EIdx
  | .bvar i => if i ≥ c then internE (.bvar (i + k)) else pure h
  | .fvar _ _ => pure h
  | .sort _ => pure h
  | .const _ _ => pure h
  | .lit _ => pure h
  | .app a b => liftArmApp k F h c a b
  | .lam ty body => liftArmLam k F h c ty body
  | .forallE ty body => liftArmForallE k F h c ty body
  | .letE ty val body => liftArmLet k F h c ty val body
  | .proj n i sub => liftArmProj k F h c n i sub

/-- The cutoff in words is the arena's in `Nat`. -/
theorem cut_iff (x c : Word) :
    (x < 32767 ∧ x ≤ c) ↔ (decide (x.toNat < satRange) && decide (x.toNat ≤ c.toNat)) = true := by
  have e1 : x < 32767 ↔ x.toNat < 32767 := UInt64.lt_iff_toNat_lt
  have e2 : x ≤ c ↔ x.toNat ≤ c.toNat := UInt64.le_iff_toNat_le
  rw [e1, e2, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]; rfl

/-- No wrap: `x + y` is not below `x`. -/
theorem add_noovf (x y : Word) (h : ¬ x + y < x) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add]
  have := x.toNat_lt; have := y.toNat_lt
  rcases Nat.lt_or_ge (x.toNat + y.toNat) (2 ^ 64) with hl | hl
  · exact Nat.mod_eq_of_lt hl
  · exfalso; apply h; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)]; omega

theorem lgoOK_succ (n : Nat) (ih : LArmOK n) : LGoOK (n + 1) := by
  intro m m' a h c k fu r hA hh hb
  by_cases hfu : fu = 0
  · rw [liftW] at hb; simp [hfu] at hb
  have hd := derBW_ok m a hA.1 hA.2 h hh
  rw [ctrW_toNat fu hfu, liftLooseBVarsGo_succ, StateT.run_bind, derivedE_run]
  simp only [except_ok_bind]
  by_cases hcut : derBW m h < 32767 ∧ derBW m h ≤ c
  · rw [liftW.arm1 n m h c k fu hfu hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [hd, cut_iff] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA⟩
  have hcut' := hcut
  rw [hd, cut_iff] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
  have hR := hA.1
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [liftW] at hb; simp [hfu, hcut, hs] at hb
  have vok : ∀ c0, ¬ tcnt m c0 (tierW h) ≤ idxW h → viewOK m h c0 :=
    fun c0 hc => ⟨hs, UInt64.not_le.mp hc⟩
  by_cases g0 : h >>> 28 = 0
  · by_cases hc : tcnt m BVAR (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g0, hc] at hb
    rw [view_run _ a _ (view_bvar m a hR h hh (vok BVAR hc) g0)]
    simp only [except_ok_bind]
    by_cases hl : tfld m BVAR (tierW h) (idxW h) 0 < c
    · rw [liftW.arm2 n m h c k fu hfu hcut hs g0 hc hl] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have : ¬ (tfld m BVAR (tierW h) (idxW h) 0).toNat ≥ c.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hl; omega
      simp only [this, ↓reduceIte]; exact ⟨a, rfl, hA⟩
    by_cases ho : tfld m BVAR (tierW h) (idxW h) 0 + k <
        tfld m BVAR (tierW h) (idxW h) 0
    · rw [liftW] at hb; simp [hfu, hcut, hs, g0, hc, hl, ho] at hb
    rw [liftW.arm3 n m h c k fu hfu hcut hs g0 hc hl ho] at hb
    obtain ⟨hok, hA', hres⟩ := internBVar_D m a hA _ r m' hb
    have hge : (tfld m BVAR (tierW h) (idxW h) 0).toNat ≥ c.toNat := by
      have := UInt64.not_lt.mp hl; exact UInt64.le_iff_toNat_le.mp this
    simp only [hge, ↓reduceIte]
    rw [← add_noovf _ _ ho, AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, hA'⟩
  have arm := fun c0 (hc : ¬ tcnt m c0 (tierW h) ≤ idxW h) =>
    ih m m' a h c k (fu - 1) r hA hh
  by_cases g4 : h >>> 28 = 4
  · by_cases hc : tcnt m APP (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g4, hc] at hb
    rw [view_run _ a _ (view_app m a hR h hh (vok APP hc) g4).1]
    rw [liftW.arm4 n m h c k fu hfu hcut hs g0 g4 hc] at hb
    exact (arm APP hc).1 (vok APP hc) g4 hb
  by_cases g5 : h >>> 28 = 5
  · by_cases hc : tcnt m LAM (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g5, hc] at hb
    rw [view_run _ a _ (view_lam m a hR h hh (vok LAM hc) g5).1]
    rw [liftW.arm5 n m h c k fu hfu hcut hs g0 g4 g5 hc] at hb
    exact (arm LAM hc).2.1 (vok LAM hc) g5 hb
  by_cases g6 : h >>> 28 = 6
  · by_cases hc : tcnt m FORALL (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g6, hc] at hb
    rw [view_run _ a _ (view_forall m a hR h hh (vok FORALL hc) g6).1]
    rw [liftW.arm6 n m h c k fu hfu hcut hs g0 g4 g5 g6 hc] at hb
    exact (arm FORALL hc).2.2.1 (vok FORALL hc) g6 hb
  by_cases g7 : h >>> 28 = 7
  · by_cases hc : tcnt m LET (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g7, hc] at hb
    rw [view_run _ a _ (view_let m a hR h hh (vok LET hc) g7).1]
    rw [liftW.arm7 n m h c k fu hfu hcut hs g0 g4 g5 g6 g7 hc] at hb
    exact (arm LET hc).2.2.2.1 (vok LET hc) g7 hb
  by_cases g9 : h >>> 28 = 9
  · by_cases hc : tcnt m PROJ (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g9, hc] at hb
    rw [view_run _ a _ (view_proj m a hR h hh (vok PROJ hc) g9).1]
    rw [liftW.arm8 n m h c k fu hfu hcut hs g0 g4 g5 g6 g7 g9 hc] at hb
    exact (arm PROJ hc).2.2.2.2 (vok PROJ hc) g9 hb
  have pure_h : ∀ v, a.store.view (decE h) = some v → liftW (n + 1) m h c k fu = some (h, m) →
      (∀ x : AState, (liftV k.toNat (fu - 1).toNat (decE h) c.toNat v).run x = .ok (decE h, x)) →
      ∃ a', ((view (decE h)).run a >>= fun p => (liftV k.toNat (fu - 1).toNat (decE h) c.toNat p.1).run p.2) =
        Except.ok (decE r, a') ∧ ArenaD m' a' := by
    intro v hv hl hx
    rw [hl] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [view_run _ a v hv]
    exact ⟨a, hx a, hA⟩
  by_cases g1 : h >>> 28 = 1
  · by_cases hc : tcnt m FVAR (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g1, hc] at hb
    obtain ⟨_, _, hv⟩ := view_fvar m a hR h hh (vok FVAR hc) g1
    exact pure_h _ hv (liftW.arm9 n m h c k fu hfu hcut hs g0 g4 g5 g6 g7 g9 g1 hc) (fun _ => rfl)
  by_cases g2 : h >>> 28 = 2
  · by_cases hc : tcnt m SORT (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g2, hc] at hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh (vok SORT hc) g2
    exact pure_h _ hv (liftW.arm10 n m h c k fu hfu hcut hs g0 g4 g5 g6 g7 g9 g1 g2 hc) (fun _ => rfl)
  by_cases g3 : h >>> 28 = 3
  · by_cases hc : tcnt m CONST (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g3, hc] at hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh (vok CONST hc) g3
    exact pure_h _ hv (liftW.arm11 n m h c k fu hfu hcut hs g0 g4 g5 g6 g7 g9 g1 g2 g3 hc) (fun _ => rfl)
  by_cases g8 : h >>> 28 = 8
  · by_cases hc : tcnt m LIT (tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hfu, hcut, hs, g8, hc] at hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh (vok LIT hc) g8
    exact pure_h _ hv (liftW.arm12 n m h c k fu hfu hcut hs g0 g4 g5 g6 g7 g9 g1 g2 g3 g8 hc) (fun _ => rfl)
  rw [liftW] at hb; simp [hfu, hcut, hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-! ## The arms -/

/-- **The tail of every arm**: intern the rebuilt node (`op`, refined by the `mk_*` model `mkr`)
and record it in the memo. -/
theorem tail_ok (op : AM EIdx) (mkr : Option (Word × Mem)) (a₂ : AState) (h c r : Word) (m' : Mem)
    (hh : h.toNat < 2 ^ 32)
    (hmk : ∀ r₃ m₃, mkr = some (r₃, m₃) →
      AM.ok op a₂ ∧ ArenaD m₃ (AM.st op a₂) ∧ AM.res op a₂ = decE r₃)
    (hb : liftAppW.k_mk_app h c mkr = some (r, m')) :
    ∃ a', (do let r ← op; liftSet (decE h, c.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaD m' a' := by
  cases h3 : mkr with
  | none => simp [h3, liftAppW.k_mk_app] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    by_cases hr : mfindG lfSch m₃ h c = []
    · simp [liftAppW.k_mk_app, hr] at hb
    rw [liftAppW.k_mk_app.arm1 h c r₃ m₃ hr] at hb
    cases h4 : mputG lfSch m₃ h c r₃ ((mfindG lfSch m₃ h c).headD 0)
        ((mfindG lfSch m₃ h c).tail.headD 0) with
    | none => rw [h4] at hb; simp [liftAppW.k_lf_put] at hb
    | some m₄ =>
      rw [h4, liftAppW.k_lf_put.arm1, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hs : msetG lfSch m₃ h c r₃ = some m₄ := by rw [msetG, ite_eq_right hr]; exact h4
      obtain ⟨hok, hA₃, hres⟩ := hmk r₃ m₃ h3
      refine ⟨_, ?_, ArenaD.lmemo_set m₃ m₄ _ hA₃ h c r₃ hh hs⟩
      simp only [StateT.run_bind, AM.run_of_ok _ _ hok, hres, except_ok_bind, liftSet_run]; rfl

/-- **The memo probe of every arm**: a hit is the memo's value; a miss runs `miss`. -/
theorem probe_ok (armW : Option (Word × Mem)) (miss : AM EIdx) (m m' : Mem) (a : AState)
    (hA : ArenaD m a) (h c r : Word) (hh : h.toNat < 2 ^ 32)
    (hhit : mfindG lfSch m h c ≠ [] → (mfindG lfSch m h c).headD 0 ≠ 0 →
      armW = some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m))
    (hnone : mfindG lfSch m h c = [] → armW = none)
    (hmiss : mfindG lfSch m h c ≠ [] → (mfindG lfSch m h c).headD 0 = 0 → armW = some (r, m') →
      ∃ a', miss.run a = .ok (decE r, a') ∧ ArenaD m' a')
    (hb : armW = some (r, m')) :
    ∃ a', (do
        match ← liftGet (decE h, c.toNat) with
        | some r => pure r
        | none => miss : AM EIdx).run a = .ok (decE r, a') ∧ ArenaD m' a' := by
  rw [StateT.run_bind, liftGet_run, except_ok_bind]
  by_cases hr : mfindG lfSch m h c = []
  · rw [hnone hr] at hb; cases hb
  by_cases hh0 : (mfindG lfSch m h c).headD 0 ≠ 0
  · rw [hhit hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.liftC[(decE h, c.toNat)]? = _ from
      memoRG_hit lfSch lfKey decE m _ hA.1.memos.lift h c hr hh0 hh]
    exact ⟨a, rfl, hA⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [show a.memos.liftC[(decE h, c.toNat)]? = none from
      memoRG_miss lfSch lfKey decE m _ hA.1.memos.lift h c hh hr hh0]
    exact hmiss hr hh0 hb

section arms
variable (n : Nat) (ih : LGoOK n) (m m' : Mem) (a : AState) (hA : ArenaD m a)
  (h c k fu r : Word) (hh : h.toNat < 2 ^ 32)
include ih hA hh

theorem appArm_ok (hv : viewOK m h APP) (hg : h >>> 28 = 4) :
    ArmRef (n + 1) liftAppW
      (liftArmApp k.toNat fu.toNat (decE h) c.toNat (decE (tfld m APP (tierW h) (idxW h) 0))
        (decE (tfld m APP (tierW h) (idxW h) 1))) m m' a h c k fu r := by
  intro hb
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1 h hh hv hg
  rw [liftArmApp]
  refine probe_ok _ _ m m' a hA h c r hh (liftAppW.arm1 n m h c k fu) (fun hr => by rw [liftAppW]; simp [hr])
    (fun hr hh0 hb => ?_) hb
  rw [liftAppW.arm2 n m h c k fu hr hh0] at hb
  cases h1 : liftW n m (tfld m APP (tierW h) (idxW h) 0) c k fu with
  | none => simp [h1, liftAppW.k_lift_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : liftW n m₁ (tfld m APP (tierW h) (idxW h) 1) c k fu with
  | none => simp [h1, h2, liftAppW.k_lift_go, liftAppW.k_lift_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, liftAppW.k_lift_go, liftAppW.k_lift_go_2] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ c k fu x hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ c k fu y hA₁ haw h2
  obtain ⟨a', h3, h4⟩ := tail_ok _ _ a₂ h c r m' hh (fun r₃ m₃ h => mkApp_ok m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem lamArm_ok (hv : viewOK m h LAM) (hg : h >>> 28 = 5) :
    ArmRef (n + 1) liftLamW
      (liftArmLam k.toNat fu.toNat (decE h) c.toNat
        (decE (tfld m LAM (tierW h) (idxW h) 0))
        (decE (tfld m LAM (tierW h) (idxW h) 1))) m m' a h c k fu r := by
  intro hb
  by_cases hc1 : c + 1 = 0
  · rw [liftLamW] at hb; simp [hc1] at hb
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1 h hh hv hg
  rw [liftArmLam]
  refine probe_ok _ _ m m' a hA h c r hh (liftLamW.arm1 n m h c k fu hc1)
    (fun hr => by rw [liftLamW]; simp [hc1, hr]) (fun hr hh0 hb => ?_) hb
  rw [liftLamW.arm2 n m h c k fu hc1 hr hh0] at hb
  cases h1 : liftW n m (tfld m LAM (tierW h) (idxW h) 0) c k fu with
  | none => simp [h1, liftLamW.k_lift_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : liftW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (c + 1) k fu with
  | none => simp [h1, h2, liftLamW.k_lift_go, liftLamW.k_lift_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, liftLamW.k_lift_go, liftLamW.k_lift_go_2] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ c k fu x hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ (c + 1) k fu y hA₁ haw h2
  rw [succW_toNat c hc1] at ha₂
  obtain ⟨a', h3, h4⟩ := tail_ok _ _ a₂ h c r m' hh (fun r₃ m₃ h => mkLam_ok m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem forallArm_ok (hv : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    ArmRef (n + 1) liftForallW
      (liftArmForallE k.toNat fu.toNat (decE h) c.toNat
        (decE (tfld m FORALL (tierW h) (idxW h) 0))
        (decE (tfld m FORALL (tierW h) (idxW h) 1))) m m' a h c k fu r := by
  intro hb
  by_cases hc1 : c + 1 = 0
  · rw [liftForallW] at hb; simp [hc1] at hb
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1 h hh hv hg
  rw [liftArmForallE]
  refine probe_ok _ _ m m' a hA h c r hh (liftForallW.arm1 n m h c k fu hc1)
    (fun hr => by rw [liftForallW]; simp [hc1, hr]) (fun hr hh0 hb => ?_) hb
  rw [liftForallW.arm2 n m h c k fu hc1 hr hh0] at hb
  cases h1 : liftW n m (tfld m FORALL (tierW h) (idxW h) 0) c k fu with
  | none => simp [h1, liftForallW.k_lift_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : liftW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (c + 1) k fu with
  | none => simp [h1, h2, liftForallW.k_lift_go, liftForallW.k_lift_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, liftForallW.k_lift_go, liftForallW.k_lift_go_2] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ c k fu x hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ (c + 1) k fu y hA₁ haw h2
  rw [succW_toNat c hc1] at ha₂
  obtain ⟨a', h3, h4⟩ := tail_ok _ _ a₂ h c r m' hh (fun r₃ m₃ h => mkForall_ok m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem letArm_ok (hv : viewOK m h LET) (hg : h >>> 28 = 7) :
    ArmRef (n + 1) liftLetW
      (liftArmLet k.toNat fu.toNat (decE h) c.toNat
        (decE (tfld m LET (tierW h) (idxW h) 0))
        (decE (tfld m LET (tierW h) (idxW h) 1))
        (decE (tfld m LET (tierW h) (idxW h) 2))) m m' a h c k fu r := by
  intro hb
  by_cases hc1 : c + 1 = 0
  · rw [liftLetW] at hb; simp [hc1] at hb
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1 h hh hv hg
  rw [liftArmLet]
  refine probe_ok _ _ m m' a hA h c r hh (liftLetW.arm1 n m h c k fu hc1)
    (fun hr => by rw [liftLetW]; simp [hc1, hr]) (fun hr hh0 hb => ?_) hb
  rw [liftLetW.arm2 n m h c k fu hc1 hr hh0] at hb
  cases h1 : liftW n m (tfld m LET (tierW h) (idxW h) 0) c k fu with
  | none => simp [h1, liftLetW.k_lift_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : liftW n m₁ (tfld m LET (tierW h) (idxW h) 1) c k fu with
  | none => simp [h1, h2, liftLetW.k_lift_go, liftLetW.k_lift_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  cases h3 : liftW n m₂ (tfld m LET (tierW h) (idxW h) 2) (c + 1) k fu with
  | none => simp [h1, h2, h3, liftLetW.k_lift_go, liftLetW.k_lift_go_2, liftLetW.k_lift_go_3] at hb
  | some o =>
  obtain ⟨z, m₃⟩ := o
  simp only [h1, h2, h3, liftLetW.k_lift_go, liftLetW.k_lift_go_2, liftLetW.k_lift_go_3] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ c k fu x hA htw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ c k fu y hA₁ hvw h2
  obtain ⟨a₃, ha₃, hA₃⟩ := ih m₂ m₃ a₂ _ (c + 1) k fu z hA₂ hbw h3
  rw [succW_toNat c hc1] at ha₃
  obtain ⟨a', h4, h5⟩ := tail_ok _ _ a₃ h c r m' hh
    (fun r₄ m₄ h => mkLet_ok m₃ a₃ hA₃ x y z r₄ m₄ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, ha₃, except_ok_bind]; exact h4, h5⟩

theorem projArm_ok (hv : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    ArmRef (n + 1) liftProjW
      (liftArmProj k.toNat fu.toNat (decE h) c.toNat
        (decI (tfld m PROJ (tierW h) (idxW h) 0))
        (tfld m PROJ (tierW h) (idxW h) 1).toNat
        (decE (tfld m PROJ (tierW h) (idxW h) 2))) m m' a h c k fu r := by
  intro hb
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1 h hh hv hg
  rw [liftArmProj]
  refine probe_ok _ _ m m' a hA h c r hh (liftProjW.arm1 n m h c k fu)
    (fun hr => by rw [liftProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  rw [liftProjW.arm2 n m h c k fu hr hh0] at hb
  cases h1 : liftW n m (tfld m PROJ (tierW h) (idxW h) 2) c k fu with
  | none => simp [h1, liftProjW.k_lift_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  simp only [h1, liftProjW.k_lift_go] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ c k fu x hA hew h1
  obtain ⟨a', h3, h4⟩ := tail_ok _ _ a₁ h c r m' hh
    (fun r₃ m₃ h => mkProj_ok m₁ a₁ hA₁ _ _ x r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact h3, h4⟩

end arms

theorem larmOK_succ (n : Nat) (ih : LGoOK n) : LArmOK (n + 1) := by
  intro m m' a h c k fu r hA hh
  exact ⟨appArm_ok n ih m m' a hA h c k fu r hh, lamArm_ok n ih m m' a hA h c k fu r hh,
    forallArm_ok n ih m m' a hA h c k fu r hh, letArm_ok n ih m m' a hA h c k fu r hh,
    projArm_ok n ih m m' a hA h c k fu r hh⟩

/-- **The model of `lift_go` refines `liftLooseBVarsGo`** at every fuel. -/
theorem liftOK (n : Nat) : LGoOK n ∧ LArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ hb => by simp [liftW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ _ hb <;> simp [liftAppW, liftLamW, liftForallW, liftLetW, liftProjW] at hb
  | succ n ih => exact ⟨lgoOK_succ n ih.2, larmOK_succ n ih.1⟩

/-! ## The entry `lift_entry` refines `liftLooseBVarsFast` -/

theorem liftFast_run (F amount c : Nat) (e : EIdx) (a : AState) :
    (liftLooseBVarsFast F amount c e).run a =
      ((liftLooseBVarsGo amount F e c).run (withLC a ∅) >>= fun p => .ok (p.1, withLC p.2 ∅)) := by
  simp only [liftLooseBVarsFast, StateT.run_bind, liftClear_run, except_ok_bind]
  cases (liftLooseBVarsGo amount F e c).run (withLC a ∅) <;> rfl

/-- **The model of `lift_entry` refines `liftLooseBVarsFast`** at the counter's fuel `f.toNat`. -/
theorem liftEntryW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaD m a)
    (h k c f r : Word) (hh : h.toNat < 2 ^ 32) (hb : liftEntryW (n + 1) m h k c f = some (r, m')) :
    ∃ a', (liftLooseBVarsFast f.toNat k.toNat c.toNat (decE h)).run a = .ok (decE r, a') ∧
      ArenaD m' a' := by
  have hcs : lfSch.cs = 42 := rfl
  by_cases h0 : rdW (m.arr64 CTL) 42 + 2 = 0
  · simp [liftEntryW, hcs, h0] at hb
  rw [liftEntryW.arm1 n m h k c f (by rw [hcs]; exact h0)] at hb
  have hA₀ := ArenaD.lmemo_clear m a hA h0
  cases hw : liftW n (mclearG lfSch m) h c k f with
  | none => simp [hw, liftEntryW.k_lift_go] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    by_cases h1 : rdW (m₁.arr64 CTL) 42 + 2 = 0
    · simp [hw, liftEntryW.k_lift_go, hcs, h1] at hb
    rw [hw, liftEntryW.k_lift_go.arm1 r₁ m₁ (by rw [hcs]; exact h1), Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁⟩ := (liftOK n).1 _ _ _ h c k f r₁ hA₀ hh hw
    exact ⟨_, by rw [liftFast_run, ha₁]; rfl, ArenaD.lmemo_clear m₁ a₁ hA₁ h1⟩

/-- **`lift_entry(h, k, c, f)` refines the arena's `liftLooseBVarsFast f k c h` under `ArenaD`**:
if the L walk returns, the arena walk at the counter's fuel `f.toNat` succeeds with the same
handle, in a related state, at every L fuel. -/
@[refines ConRon.Arena.liftLooseBVarsFast]
theorem liftEntry_refines (p : Prog) (hp : LiftProg p) (he : p.lookup "lift_entry" = some liftEntry)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaD s₀.mem a₀) (h k c f : Word)
    (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "lift_entry" [h, k, c, f]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (liftLooseBVarsFast f.toNat k.toNat c.toNat (decE h)) a₀ ∧
      ArenaD s'.mem (AM.st (liftLooseBVarsFast f.toNat k.toNat c.toNat (decE h)) a₀) ∧
      AM.res (liftLooseBVarsFast f.toNat k.toNat c.toNat (decE h)) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (liftEntry_spec p hp he (n + 1) s₀ h k c f)
  subst hs
  obtain ⟨a', ha', hA'⟩ := liftEntryW_correct n _ _ a₀ hA h k c f _ hh hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres⟩

end L.Arena
