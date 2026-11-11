module

public import ConAgua.Arena.RecCheckSpec.ArfW
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.IndSumSpec.TsrW
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndT.Lift
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.StreamRecs
import all ConAgua.Arena.IndStream
public import ConAgua.Arena.IndT.StreamRecsTy
public import ConRon.Bridge.Inductives.RecCheck

@[expose] public section

/-!
# `generated_fire` under `StageC` (lane `ronsync2`, stage 3)

`generated_fire(M, rP)` (`IndStream.lean`): `.plain` (the word `0`) at a member major, else
`aux_rule_fire` (`arfW_sim`). `gfW` is its model, `gf_sim` its step against con-ron's
`generatedFire`, the fire decoded (`decFireG`: kind `0` plain, kind `1` nested) and denoting
con-leche's `generatedFire`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups `generated_fire` needs. -/
structure GfLook (p : Prog) : Prop where
  gf : p.lookup "generated_fire" = some generatedFireL
  arf : ArfLook p

l_model generatedFire_spec (p : Prog) (h : GfLook p)
  fns [h.gf ↦ gfW]
  specs [auxRuleFire_spec p h.arf n]
  grind [arena_grind]

/-- The fire a `generated_fire` result decodes to: kind `0` `.plain`, kind `1` `.nested`. -/
def decFireG (m' : Mem) (r : List Word) : IRecRuleFire → Prop
  | .plain => r.headD 0 = 0
  | f => decFire m' r f

/-- `decFire` of the five words `generated_fire` returns. -/
theorem decFire_pack {m' : Mem} {r : List Word} {f : IRecRuleFire} (h : decFire m' r f) :
    decFire m' [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.headD 0] f := by
  have e : ∀ i, i < 5 → [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.headD 0].getD i 0 = r.getD i 0 := by
    intro i hi
    rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      (match i, hi with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl)
  cases f with
  | nested lvls pins =>
    simp only [decFire, decRL] at h ⊢
    rw [e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
    exact ⟨by rw [← h.1]; cases r <;> rfl, h.2⟩
  | _ => exact absurd h id

section sims
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env} {m : Mem} {a : AState}

/-- **`generated_fire`'s step**: con-ron's `generatedFire`, the stage and the core step after, the
fire decoded (`decFireG`) and denoting con-leche's `generatedFire`. -/
theorem gf_sim (hG : GfLook p) {n : Nat} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    {M rP : Word} {TM : TargetMajor} {TMP : ConLeche.TargetMajor}
    (hM : DecB (fun m => decTM m M.toNat) m TM)
    (hMP : ConRon.Bridge.Inductives.dMajor a.store TM = some TMP) :
    Sim (callW p n "generated_fire" [M, rP] m) (ConRon.Arena.generatedFire TM rP.toNat) a
      fun r x m' a' => SrPost dn vis fe env m a m' a' ∧ decFireG m' r x ∧
        Frontend.denoteFire a'.store x = some (ConLeche.generatedFire TMP rP.toNat) := by
  intro r m' hc
  rcases n with _ | K
  · rw [callW_zero] at hc; cases hc
  have c' := callW_model (M := fun mm => gfW (K + 1) mm M rP)
    (fun s => generatedFire_spec p hG (K + 1) s M rP) hc
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hC.stage.iw.iwSize
  obtain ⟨k8, hk8, hmem⟩ := decTM_member (show decTM (truncM m) M.toNat = some TM from hM)
  obtain ⟨-, hk8⟩ := L.Ind.iwN_truncM_some hk8
  obtain ⟨e8, e8N⟩ := rec2RdN (w := M) (k := 8) hk8 hsz
  simp only [show UInt64.ofNat 8 = (8 : Word) from rfl] at e8
  -- the twin's run, its step and its fire's denotation
  have hfin : ∀ x a', (ConRon.Arena.generatedFire TM rP.toNat).run a = .ok (x, a') →
      SrPost dn vis fe env m a m' a' → decFireG m' r x →
      ∃ x a'', (ConRon.Arena.generatedFire TM rP.toNat).run a = .ok (x, a'') ∧
        SrPost dn vis fe env m a m' a'' ∧ decFireG m' r x ∧
        Frontend.denoteFire a''.store x = some (ConLeche.generatedFire TMP rP.toNat) :=
    fun x a' hr hR hd => by
      obtain ⟨-, hden⟩ := ConRon.Bridge.Inductives.generatedFire_run hC.check.state hMP hr
      exact ⟨x, a', hr, hR, hd, hden⟩
  by_cases h8 : k8 = 0
  · subst h8
    rw [gfW.arm2 K m M rP (by rw [e8]; rfl)] at c'
    rcases h2 : arfW K m M rP with _ | ⟨r2, m2⟩ <;>
      simp only [h2, gfW.k_aux_rule_fire, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at c'
    obtain ⟨rfl, rfl⟩ := c'
    obtain ⟨x, a2, hrun, ⟨hS2, hg2, hdec⟩, hA2⟩ :=
      arfW_sim dn vis fe K m a M rP TM hC.stage hM (L.Ind.poolSmall_of_stage hC.stage) hA (r2, m2) h2
    have hr : (ConRon.Arena.generatedFire TM rP.toNat).run a = .ok (x, a2) := by
      simp only [ConRon.Arena.generatedFire, hmem, decON, ↓reduceIte]; exact hrun
    obtain ⟨ps, -⟩ := ConRon.Bridge.Inductives.generatedFire_run hC.check.state hMP hr
    refine hfin x a2 hr ⟨hC.of_pstep hS2 hA2 ps, hg2, hA2, ps.toCore hC.check⟩ ?_
    cases x with
    | nested lvls pins => exact decFire_pack hdec
    | _ => exact absurd hdec id
  · rw [gfW.arm1 K m M rP (by rw [e8]; intro h; apply h8; rw [← e8N, h]; rfl)] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    have hr : (ConRon.Arena.generatedFire TM rP.toNat).run a = .ok (.plain, a) := by
      simp only [ConRon.Arena.generatedFire, hmem, decON, h8, ↓reduceIte]; rfl
    exact hfin _ _ hr (SrPost.refl hC hA) rfl

end sims

end L.Ind

end
