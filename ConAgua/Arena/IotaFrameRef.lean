module

public import ConAgua.Arena.IotaFrameModels
public import ConAgua.Arena.DefEqMidQuick
import ConRon.Bridge.Rel
public import ConAgua.Arena.StripTeleSpec

@[expose] public section

/-!
# The ι reading rule, part 1: the refinements (lane ronsync8)

Each L function of `IotaFrame.lean` refines its twin (`ConRon/Arena/Inductives/IotaRead.lean`)
under `StageR` (`RelW` of its run, then the census theorem `@[refines]`): a returning run is the
twin's `.ok` run, the stage kept, the pool grown, the results decoding the twin's.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-! ## Views off `e_view`'s run -/

theorem viewBind_run' {a : AState} {h : EIdx} :
    (viewBind h).run a = .ok (a.store.viewBind h, a) := by
  simp [viewBind, StateT.run_get]; rfl

/-- **`e_view` at a `∀`**: the memory kept, the twin's `viewBind` the two fields. -/
theorem eView_forall {p : Prog} (hp : p.lookup "e_view" = some eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} {r : List Word} (_hh : HW h)
    (h6 : tagW h = 6) (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) ∧
      HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) := by
  obtain ⟨rfl, v, hv, hvr, ht⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, h1, h2⟩ := viewR_forall hvr (by rw [ht, h6])
  exact ⟨rfl, ConRon.Bridge.viewBind_of_view hv (Or.inr rfl), h1, h2⟩

/-! ## `pi_tele` -/

/-- `Option (Nat × EIdx)`-free decoder of `pi_tele`'s `(n, body)`. -/
def decNE (_m : Mem) (r : List Word) (x : Nat × EIdx) : Prop :=
  (r.headD 0).toNat = x.1 ∧ HW (r.tail.headD 0) ∧ decE (r.tail.headD 0) = x.2

theorem piTele_tag (h : Word) (hh : HW h) :
    ((decE h).tag == ETag.forallE) = decide (tagW h = 6) :=
  decE_tag_beq h hh 6 (by decide)

/-- **`pi_tele`'s loop against the twin's recursion**: from count `c`, a returning loop keeps the
memory and ends at a count `c' ≥ c`; below `CWF` the twin at fuel `CWF - c` answers
`(c' - c, h')`. -/
theorem piTele_loop {p : Prog} (hp : p.lookup "e_view" = some eView) {m : Mem} {a : AState}
    (hR : ArenaR m a) :
    ∀ (k : Nat) (c h c' h' : Word) (m' : Mem), HW h → c ≤ CWF →
      piTeleW.loop1 p k m c h = some (c', h', m') →
      m' = m ∧ HW h' ∧ c ≤ c' ∧
        (c' < CWF → (piTele (coreWalkFuel - c.toNat) (decE h)).run a =
          .ok ((c'.toNat - c.toNat, decE h'), a)) := by
  intro k
  induction k with
  | zero => intro c h c' h' m' _ _ hl; rw [piTeleW.loop1.eq_1] at hl; cases hl
  | succ k ih =>
  intro c h c' h' m' hh hc hl
  by_cases h6 : tagW h = 6
  · by_cases hcw : CWF ≤ c
    · rw [piTeleW.loop1.abort1 _ _ _ _ _ h6 hcw] at hl; cases hl
    rw [piTeleW.loop1.arm1 _ _ _ _ _ h6 hcw] at hl
    rcases hv : callW p k "e_view" [h] m with _ | ⟨r, m1⟩
    · rw [hv, piTeleW.k_e_view.none] at hl; cases hl
    rw [hv, piTeleW.k_e_view.arm1] at hl
    obtain ⟨rfl, hvb, -, hb⟩ := eView_forall hp hR hh h6 hv
    have hlt0 : c.toNat < coreWalkFuel := by
      rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, CWF_eq] at hcw; exact hcw
    have hcn : (c + 1).toNat = c.toNat + 1 := by
      simp only [coreWalkFuel] at hlt0
      rw [UInt64.toNat_add]; simp; omega
    have hc1 : c + 1 ≤ CWF := by
      rw [UInt64.le_iff_toNat_le, hcn, CWF_eq]; exact hlt0
    obtain ⟨hm, hh', hle, hrun⟩ := ih (c + 1) _ c' h' m' hb hc1 hl
    refine ⟨hm, hh', ?_, fun hlt => ?_⟩
    · rw [UInt64.le_iff_toNat_le] at hle ⊢; omega
    have hlt' : c.toNat < coreWalkFuel := by
      rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, CWF_eq] at hcw; exact hcw
    have hle' : c.toNat + 1 ≤ c'.toNat := by rw [UInt64.le_iff_toNat_le] at hle; omega
    have e1 : coreWalkFuel - c.toNat = (coreWalkFuel - (c + 1).toNat) + 1 := by rw [hcn]; omega
    rw [e1, piTele, piTele_tag h hh, h6]
    have hr := hrun hlt
    rw [show c'.toNat - c.toNat = c'.toNat - (c + 1).toNat + 1 by omega]
    simp only [decide_true, ite_true]
    rw [StateT.run_bind, viewBind_run', hvb]
    change ((piTele (coreWalkFuel - (c + 1).toNat) (decE (r.tail.tail.headD 0))) >>=
      fun r => pure (r.fst + 1, r.snd)).run a = _
    rw [StateT.run_bind, hr]
    rfl
  · rw [piTeleW.loop1.arm2 _ _ _ _ _ h6] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    refine ⟨rfl, hh, UInt64.le_refl _, fun hlt => ?_⟩
    have hlt' : c.toNat < coreWalkFuel := by rw [UInt64.lt_iff_toNat_lt, CWF_eq] at hlt; exact hlt
    rw [show coreWalkFuel - c.toNat = (coreWalkFuel - c.toNat - 1) + 1 by omega, piTele,
      piTele_tag h hh]
    simp [h6]
    rfl

/-- **`pi_tele` refines `piTele coreWalkFuel`**: memory and twin state unchanged. -/
@[refines ConRon.Arena.piTele]
theorem piTele_rel {p : Prog} (hf : p.lookup "pi_tele" = some piTeleL)
    (hp : p.lookup "e_view" = some eView) (n : Nat) (vis : Word) (fe : IFEnv) (e : Word)
    (he : HW e) :
    RelW (fun m args => callW p n "pi_tele" args m) [e] (StageR vis fe) (piTele coreWalkFuel (decE e))
      (KeepPost vis fe decNE) := by
  intro m m' a r hc hS
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (piTele_specW p hf n _ e) hc
  rcases n with _ | n
  · simp [piTeleW] at hW
  simp only [piTeleW] at hW
  rcases hl : piTeleW.loop1 p (n + 1) m 0 e with _ | ⟨c', h', m1⟩
  · rw [hl] at hW; simp [piTeleW.k_loop1] at hW
  rw [hl] at hW
  simp only [piTeleW.k_loop1] at hW
  by_cases hcw : CWF ≤ c'
  · simp only [hcw, ↓reduceIte] at hW; cases hW
  simp only [hcw, ↓reduceIte] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨rfl, hh', -, hrun⟩ := piTele_loop hp hS.check.arena.base (n + 1) 0 e c' h' _ he
    (by decide) hl
  have := hrun (UInt64.not_le.mp hcw)
  simp only [UInt64.toNat_zero, Nat.sub_zero] at this
  exact ⟨_, a, this, hS, IWGrow.refl _, rfl, hh', rfl⟩

end L.Ind
