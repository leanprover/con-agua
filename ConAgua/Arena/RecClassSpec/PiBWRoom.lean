import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndRealOpf3
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved

/-!
# PiBWRoom

`RelW.sim`, `simFvarTypeD`, `simGetAppArgs`, `simOpenPisF`, `recW_stage`, `piBW_room` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callee simulations -/

/-- A real callee's `RelW` as a `RSim` (`RelAM.sim` for a model). -/
theorem RelW.sim {α : Type} {W : Mem → List Word → Option (List Word × Mem)} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RelW W args pre op post) {m : Mem} {a : AState} (hp : pre m a) :
    RSim (W m args) op a (fun b a' x => post m b.2 a' b.1 x) := by
  intro b hb
  obtain ⟨r, m'⟩ := b
  exact h m m' a r hb hp

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

theorem simFvarTypeD (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (ftdF m [e]) (fvarTypeD (decI e)) a (KP dn vis fe m decW0E) :=
  (ftdF_ok dn vis fe e he).sim hS

theorem simGetAppArgs (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (gaaF m [CWF, e]) (getAppArgs coreWalkFuel (decI e)) a
      (KP dn vis fe m (decRL (fun m => decHL m) 0)) := by
  have h := (gaaF_ok dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

/-- `open_pis_at_fvars_f`'s real refinement (`opfF_ok`): the walk memos kept. -/
theorem simOpenPisF (hS : StageR dn vis fe m a) (hA : AbsOK m) {k e i : Word} (he : H e) :
    RSim (opfF m [k, e, i]) (openPisAtFvarsF k.toNat (decI e) i.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨x, a', hrun, hK, hA'⟩ := opfF_ok dn vis fe k e i he m m' a r h ⟨hS, hA⟩
  exact ⟨x, a', hrun, hK, hA'⟩

end sims

/-! ## Records under the stage relation -/

/-- **A fresh record keeps the stage relation**: the pointer is the old top, the words are
there, the pool grew. -/
theorem recW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {k : Word} {ws r : List Word} (h : recW m k ws = some (r, m'))
    (hS : StageR dn vis fe m a) (hk : k.toNat = ws.length) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200] ∧
    (∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?) ∧
    iwTop m' = iwTop m + ws.length := by
  obtain ⟨hr, hget, hg, hf, htop, hroom⟩ := recW_post h hS.2.2.2.2.2 hS.2.2.2.1 hk
  refine ⟨stage_frame_iw hS hf (by omega), hg, hr, hget, htop⟩

/-! ## `pi_binders` under the stage relation -/

theorem piBW_room (n : Nat) (m m' : Mem) (a : AState) (fuel h : Word) (rs : List Word)
    (hR : ArenaR m a) (hp : piBW n m fuel h = some (rs, m')) (hh : H h)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (htop : iwTop m ≤ (m.arr64 IW).size) : iwTop m' ≤ (m'.arr64 IW).size := by
  rcases n with _ | n
  · simp [piBW] at hp
  by_cases hf : fuel = 0
  · rw [piBW_fuel0 n m fuel h hf] at hp; simp at hp
  by_cases hg : h >>> 28 ≠ 6
  · rw [piBW_leaf n m fuel h hf hg] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp; exact htop
  rw [piBW_node n m fuel h hf hg] at hp
  have hg6 : h >>> 28 = 6 := by simpa using hg
  by_cases hr : eViewW m h = []
  · rw [hr, piBK1_nil] at hp; simp at hp
  obtain ⟨hvok, hew⟩ := eViewW_forall m h hg6 hr
  rw [piBK1_ne n m fuel _ hr] at hp
  obtain ⟨⟨rs1, m1⟩, hrec, hp⟩ := of_K hp rfl
  rw [piBK2_some] at hp
  obtain ⟨⟨r2, m2⟩, hcons, hp⟩ := of_K hp rfl
  rw [piBK3_some] at hp
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
  obtain ⟨-, hty, hb⟩ := view_forall m a hR h hh hvok hg6
  have hty2 : ((eViewW m h).getD 1 0).toNat < 2 ^ 32 := by rw [hew]; exact hty
  have hb2 : ((eViewW m h).getD 2 0).toNat < 2 ^ 32 := by rw [hew]; exact hb
  obtain ⟨bs1, e1, -, -, hdec1, -, -, -, hf1, hle1⟩ :=
    piBW_ok n m m1 a (fuel - 1) _ rs1 hR hrec hb2 hsz hc
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.2.2.1 IW]; exact hsz
  have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.2.2.1 CTL]; exact hc
  exact consW_room hcons hsz1 hc1 hle1 hty2 hdec1

/-- `pi_binders` as a simulation: the twin keeps its state, the binders a slice below the top. -/
theorem simPiBinders {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) {h : Word} (hh : H h) :
    RSim (piBW n m CWF h) (ConRon.Arena.piBinders coreWalkFuel (decI h)) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
        decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some x.1 ∧
        (b.1.headD 0).toNat + (b.1.tail.headD 0).toNat ≤ iwTop b.2) := by
  rintro ⟨rs, m'⟩ hp
  obtain ⟨bs, e, hrun, -, hdec, -, -, hg, hf, hle⟩ :=
    piBW_ok n m m' a CWF h rs hS.1.arena.1 hp hh hS.2.2.2.1 hS.2.2.2.2.2
  have hroom := piBW_room n m m' a CWF h rs hS.1.arena.1 hp hh hS.2.2.2.1 hS.2.2.2.2.2 hS.2.1
  refine ⟨(bs, e), a, by rw [← CWF_eq]; exact hrun, stage_frame_iw hS hf (by rw [← hf.2.2.1 IW]; exact hroom),
    hg, by simpa [getD_one] using hdec, by simpa [getD_one] using hle⟩

theorem drop3_headD (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

end L.Ind

end
