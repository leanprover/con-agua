import ConAgua.Arena.IndMaster
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Name and `succ` interning under the stage relation (lane `decls3`, helper `decls3-canon`)

`IndMaster.lean` has the expression constructors and `zero`/`param`/`max` under `StageR`; the
canonical-form code also interns `anonymous`, `num` names (`canonNamesGo`) and a `succ` level
(`ci_to_cv`). Same recipe as `internParam_stage`: master's `_correct` lemma gives `AM.ok`,
`NAnonR`/`NNumR`/`SuccR` after and the result handle; the writer is below array 64 and `CTL[64]`
and the twin keeps caches and pins (`StageR.of_walk`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section names
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
  {r : Word}

/-- A name interning (a proto run over a name lens): the expression tables, caches and pins are
untouched, so `DerR` and `cp` carry over. -/
theorem stage_of_name {β δ : Type} [BEq β] [Hashable β] {L : Lens β δ .name} {op : AM NIdx}
    {key : β} {tag : UInt32} {pf : Option NIdx} {d : δ} {err : CheckError}
    {A : List ArrId} {C : List Word}
    (hS : StageR dn vis fe m a) (hrun : op.run a = protoRun L key tag pf d err a) (hok : AM.ok op a)
    (hR : ArenaR m' (AM.st op a)) (hres : AM.res op a = decI r) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 42 ∨ (256 ≤ b ∧ b < 298)) (hC : ∀ x ∈ C, x.toNat < 64)
    (hset : ∀ t, (DerR m' a → DerR m' (L.setP a t)) ∧ cp (L.setP a t) = cp a)
    (hsetS : ∀ t, (DerR m' a → DerR m' (L.setS a t)) ∧ cp (L.setS a t) = cp a)
    (hv : ∀ t, (L.setP a t).store.view = a.store.view ∧ (L.setS a t).store.view = a.store.view)
    (hmode : ModeOK m') :
    ∃ a', op.run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      a'.store.view = a.store.view ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) := by
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hf
    (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) a hS.1.arena.2
  have hcs := AM.st_proto L op key tag pf d err a hrun hok
  have hDk : DerR m' (AM.st op a) ∧ cp (AM.st op a) = cp a := by
    rcases hcs with h | ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h]
    · exact ⟨hD₁, rfl⟩
    · exact ⟨(hset t).1 hD₁, (hset t).2⟩
    · exact ⟨(hsetS t).1 hD₁, (hsetS t).2⟩
  have hrun' := AM.run_of_ok op a hok
  rw [hres] at hrun'
  obtain ⟨h1, h2⟩ := StageR.of_walkM hS ⟨hR, hDk.1⟩ hf
    (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) hC hDk.2 hmode
  have hvw : (AM.st op a).store.view = a.store.view := by
    rcases hcs with h | ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h]
    · exact (hv t).1
    · exact (hv t).2
  exact ⟨_, hrun', h1, h2, hvw, hf.2.2.1⟩

theorem internNAnon_stage (hS : StageR dn vis fe m a) (hI : nainternW m = some (r, m')) :
    ∃ a', (internNNode .anonymous).run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ a'.store.view = a.store.view ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := naintern_correct m a hR.nanon _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame nanonCS_wf hI₂
  exact stage_of_name hS (internNNode_anon_run a) hok
    (hR.lift_nanon _ _ _ _ hX hfr (AM.st_proto nanonLens _ _ _ _ _ _ a (internNNode_anon_run a) hok))
    hres hfr (by simp [ConsSch.wset, nanonCS, NAREC, NASLOT]) (by simp [nanonCS]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

theorem internNNum_stage (hS : StageR dn vis fe m a) (pre u : Word) (hpre : pre.toNat < 2 ^ 32)
    (hI : nninternW m pre u = some (r, m')) :
    ∃ a', (internNNode (.num (decI pre) u.toNat)).run a = .ok (decI r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ a'.store.view = a.store.view ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := nnintern_correct m a hR.nnum pre u hpre _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame nnumCS_wf hI₂
  exact stage_of_name hS (internNNode_num_run _ _ a) hok
    (hR.lift_nnum _ _ _ _ hX hfr (AM.st_proto nnumLens _ _ _ _ _ _ a (internNNode_num_run _ _ a) hok))
    hres hfr (by simp [ConsSch.wset, nnumCS, NNREC, NNSLOT]) (by simp [nnumCS]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

end names

section succ
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
  {r : Word}

theorem internSucc_stage (hS : StageR dn vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : sinternW m u = some (r, m')) :
    ∃ a', (internLNode (.succ (decI u))).run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hR.succ u hu _ _ hI
  have hfr := sinternW_frame m u _ _ hI
  exact stage_of_level hS (internLNode_succ_run _ a) hok
    (hR.lift_succ _ _ _ _ ⟨hX, sintern_hp m a hR.succ u hu hR.succHp (lvlHPW_ok m a hR u hu) _ _ hI⟩
      hfr (AM.st_proto succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok))
    hres hfr (by simp [SREC, SSLOT, SHP]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

end succ

end L.Ind
