import ConAgua.Arena.Tiers
import ConAgua.Arena.WriteSets
import ConAgua.Arena.WalkRefine
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.FVarRangeRefine

/-!
# The walks under the whole relation `CheckR`

Each walk's refinement theorem (`*_run`) gives the walk tier (`ArenaD`, or `ArenaR` for the
memo-only walks). The rest of `CheckR` comes for free: the L frame from the program text
(`WriteSets.lean`: every walk writes below array 64 and `CTL` word 64) and the twin frame by
composition (`Keeps.lean`: every walk keeps `(caches, pins)`; the memo-only walks keep the store
too, which also carries `DerR`). No lemma here looks inside a walk.
-/

namespace L.Arena

open ConRon.Arena

theorem liftC_lt : ∀ x ∈ liftC, x.toNat < 64 := by simp [liftC]
theorem instC_lt : ∀ x ∈ instC, x.toNat < 64 := by simp [instC, liftC]

/-- **`lift_entry` under `CheckR`.** -/
theorem liftEntry_runC (fuel : Nat) (m : Mem) (a₀ : AState) (vis : Word)
    (fe : IFEnv) {dn : NIdx → Option ConLeche.Name} (hR : CheckR dn m a₀ vis fe) (h k c f : Word) (hh : h.toNat < 2 ^ 32) (r : List Word)
    (m' : Mem) (hrun : run liftProg fuel "lift_entry" [h, k, c, f] m = .ok (r, m')) :
    ∃ a', (liftLooseBVarsFast f.toNat k.toNat c.toNat (decE h)).run a₀ = .ok (decE (r.headD 0), a') ∧
      CheckR dn m' a' vis fe := by
  obtain ⟨a', hr, hD⟩ := liftEntry_run fuel m a₀ hR.arena h k c f hh r m' hrun
  exact ⟨a', hr, hR.of_walk hD (liftEntry_frame liftProg_ok rfl hrun) (by decide) liftC_lt
    ((keeps_liftFast _ _ _ _).run hr)⟩

/-- **`inst_entry` under `CheckR`.** -/
theorem instEntry_runC (fuel : Nat) (m : Mem) (a₀ : AState) (vis : Word)
    (fe : IFEnv) {dn : NIdx → Option ConLeche.Name} (hR : CheckR dn m a₀ vis fe) (e v d : Word) (he : e.toNat < 2 ^ 32) (r : List Word)
    (m' : Mem) (hrun : run instProg fuel "inst_entry" [e, v, d] m = .ok (r, m')) :
    ∃ a', (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat).run a₀ =
      .ok (decE (r.headD 0), a') ∧ CheckR dn m' a' vis fe := by
  obtain ⟨a', hr, hD, -⟩ := instEntry_run fuel m a₀ hR.arena e v d he r m' hrun
  exact ⟨a', hr, hR.of_walk hD (instEntry_frame instProg_ok rfl rfl hrun) (by decide) instC_lt
    ((keeps_inst1Fast _ _ _ _).run hr)⟩

/-- **`bb_memo` under `CheckR`**: `bbMemo_run` gives `ArenaR`; the walk keeps the store and
writes only its memo, so `DerR` carries over too. -/
theorem bbMemo_runC (fuel : Nat) (m : Mem) (a₀ : AState) (vis : Word)
    (fe : IFEnv) {dn : NIdx → Option ConLeche.Name} (hR : CheckR dn m a₀ vis fe) (h c : Word) (hh : h.toNat < 2 ^ 32) (r : List Word)
    (m' : Mem) (hrun : run walkProg fuel "bb_memo" [h, c] m = .ok (r, m')) :
    ∃ a', (bvarBoundMemo c.toNat (decE h)).run a₀ = .ok ((r.headD 0).toNat, a') ∧ CheckR dn m' a' vis fe := by
  obtain ⟨a', hr, hR'⟩ := bbMemo_run fuel m a₀ hR.arena.1 h c hh r m' hrun
  have hs := (keeps_bvarBoundMemo _ _).run hr
  have hf := bbMemo_frame rfl rfl rfl rfl rfl rfl hrun
  have hD := DerR.of_store m' a₀ a' (DerR.frameM _ _ m m' hf (by decide) _ hR.arena.2)
    (congrArg Prod.fst hs)
  exact ⟨a', hr, hR.of_walk ⟨hR', hD⟩ hf (by decide) (by simp [walkC]) (congrArg Prod.snd hs)⟩

/-- **`fr_memo` under `CheckR`.** -/
theorem frMemo_runC (fuel : Nat) (m : Mem) (a₀ : AState) (vis : Word)
    (fe : IFEnv) {dn : NIdx → Option ConLeche.Name} (hR : CheckR dn m a₀ vis fe) (h c : Word) (hh : h.toNat < 2 ^ 32) (r : List Word)
    (m' : Mem) (hrun : run fvarRangeProg fuel "fr_memo" [h, c] m = .ok (r, m')) :
    ∃ a', (fvarRangeMemo c.toNat (decE h)).run a₀ = .ok ((r.headD 0).toNat, a') ∧ CheckR dn m' a' vis fe := by
  obtain ⟨a', hr, hR'⟩ := frMemo_run fuel m a₀ hR.arena.1 h c hh r m' hrun
  have hs := (keeps_fvarRangeMemo _ _).run hr
  have hf := frMemo_frame rfl rfl rfl rfl rfl rfl hrun
  have hD := DerR.of_store m' a₀ a' (DerR.frameM _ _ m m' hf (by decide) _ hR.arena.2)
    (congrArg Prod.fst hs)
  exact ⟨a', hr, hR.of_walk ⟨hR', hD⟩ hf (by decide) (by simp [frC]) (congrArg Prod.snd hs)⟩

end L.Arena
