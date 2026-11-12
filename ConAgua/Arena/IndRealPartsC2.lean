module

public import ConAgua.Arena.IndRealLvlC
public import ConAgua.Arena.IndPartsSpec.BpW
import ConAgua.Arena.IndPartsSpec.Bf
import ConAgua.Arena.IndPartsSpec.BrsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Specs
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.Rel
public import ConAgua.Arena.IndPartsSpec.IndPartsProg5
public import ConAgua.Arena.IndPartsSpec.PlW
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved

@[expose] public section

/-!
# `readBlock` under `StageC`, `lvl_eq_c` the real call (lane `indproofs4`, helper `bp`)

`IndPartsSpec/PlW`'s sims read `lvl_eq_c` through `LvlHyp`: the call's `Sim` at the twin's prefix of
`readBlock` (`TshT`: the split, the counts, the result sort) and at the model's prefix (`AFr`).
Under `StageC` and `AbsOK` at entry the real call meets it (`lvlHyp_real`): con-ron's frame lemmas
make the twin's prefix a `PStep` (`blockMemberCounts_spec`;
`stripPis`, `view`, `zeroLevel` leave the state), so `StageC` holds at the call, `AbsOK` by the
model's frames (`IndRealPartsC1`), the sort reads back by the stage's `StoreDen`, and
`lvlEqC_simC` is the call's `Sim`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`bsoTwin` leaves the state**, and its level is a sort's (`view`) or the zero level. -/
theorem bsoTwin_run {nP : Nat} {ns : List Nat} {ty : EIdx} {tyP : ConLeche.Expr} {a a' : AState}
    {s : LIdx} (hok : ConRon.Bridge.StateOK a) (hp : ConRon.Bridge.PinsOK a)
    (hd : denoteE a.store ty = some tyP) (h : (bsoTwin nP ns ty).run a = .ok (s, a')) :
    a' = a ∧ ((∃ e, a.store.view e = some (.sort s)) ∨ denoteL a.store.ls s = some .zero) := by
  unfold bsoTwin at h
  obtain ⟨o, a1, h1, h2⟩ := partsBindOk h
  obtain ⟨rfl, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hok hd h1
  cases o with
  | none =>
    obtain ⟨rfl, hz⟩ := ConRon.Bridge.Inductives.zeroLevel_run hp h2
    exact ⟨rfl, Or.inr hz⟩
  | some q =>
    obtain ⟨v, a2, h3, h4⟩ := partsBindOk h2
    obtain ⟨rfl, hv⟩ := ConRon.Bridge.view_run h3
    cases v with
    | sort u =>
      obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok h4
      exact ⟨rfl, Or.inl ⟨_, hv⟩⟩
    | _ =>
      obtain ⟨rfl, hz⟩ := ConRon.Bridge.Inductives.zeroLevel_run hp h4
      exact ⟨rfl, Or.inr hz⟩

section
variable (p : Prog) (hcl : CoreStageClosed p) (hL : LvlCacheProg p)
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

include hcl hL in
/-- **The real `lvl_eq_c` meets `LvlHyp` at `readBlock`'s prefix** from a `StageC` state whose
memory holds `AbsOK` and whose store denotes the block. -/
theorem lvlHyp_real (n : Nat) {m : Mem} {a : AState} {nP : Nat} {blk : List IConstantInfo}
    {blkP : List ConLeche.ConstantInfo} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hb : Frontend.denoteCIList a.store blk = some blkP) :
    LvlHyp (realCall p) n dn vis fe m (TshT nP blk a) := by
  intro sv a1 s z m1 hT hf hS1 hs hsv hz
  subst hsv
  obtain ⟨cvT0, cvTs, cs, r0, rs, hsp, nIdxs, a2, hbmc, hbso⟩ := hT
  have hok := hC.check.state
  have hsp' := ConRon.Bridge.Inductives.blockSplit_spec a.store blk blkP hb
  rw [hsp] at hsp'
  obtain ⟨⟨cvTsP, csP, rsP⟩, -, hTs, -, hrs⟩ := hsp'
  dsimp only at hTs hrs
  have hsp1 := ConRon.Bridge.Inductives.blockMemberCounts_spec nP (cvT0 :: cvTs).length cs.length
    ((cvT0 :: cvTs).map (·.name)) (cvTsP.map (·.name)) (r0 :: rs) rsP 0 (cvT0 :: cvTs) cvTsP
  have hpre : Frontend.denoteNList a.store.ns ((cvT0 :: cvTs).map (·.name)) = some (cvTsP.map (·.name)) ∧
      (r0 :: rs).mapM (ConRon.Bridge.Inductives.dRecT a.store) = some rsP ∧
      (cvT0 :: cvTs).mapM (Frontend.denoteCV a.store) = some cvTsP :=
    ⟨ConRon.Bridge.Inductives.cvNames_go hTs, hrs, hTs⟩
  obtain ⟨q, -⟩ := hsp1 a a2 (.ok nIdxs) hok hpre hbmc
  obtain ⟨cvT0P, -, -, hT0, -⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hTs
  have hty := ConRon.Bridge.denote_ext (ConRon.Bridge.denoteCV_type hT0) q.ext
  obtain ⟨rfl, hsv⟩ := bsoTwin_run q.ok (hC.check.pins.mono q.ext q.pins) hty hbso
  have hA1 := hf hA
  have hC1 : StageC dn vis fe env m1 a1 := StageC.of_pstep hC hS1 hA1 q
  obtain ⟨lu, hdu⟩ : ∃ l, denoteL a1.store.ls (decI s) = some l := by
    rcases hsv with ⟨e, hv⟩ | hz0
    · exact hC1.stageT.twin.den.sort e _ hv
    · exact ⟨_, hz0⟩
  have hzh := (pinZero_stage hS1 hz).2
  have hpne : rdW (m1.arr64 PINS) 0 ≠ 0 := by intro h0; simp [pinWordV, h0] at hz
  have hzp : z = pinW m1 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hz
    rw [← hz]; rfl
  have hF := hS1.check.pins.full hpne
  obtain ⟨lz, hdz⟩ : ∃ l, denoteL _ _ = some l := ⟨_, hC1.stageT.twin.den.zero⟩
  rw [hF.zeroLevel, ← hzp] at hdz
  exact Sim.mono (lvlEqC_simC p hcl hL (n + 2) hC1 hA1 s z hs hzh lu lz hdu hdz)
    (fun _ _ _ _ ⟨hC', hg, hd, _, _⟩ => ⟨hC'.stage, hg, hd⟩)

include hcl hL in
/-- **`read_block` refines `readBlock` under `StageC`**, its `lvl_eq_c` the real call
(`lvlHyp_real` for the stub contract): the stage relation with con-ron's `CheckOK` and `AbsOK` at
entry, the block denoting in the twin's store; the answer the reader's reason or the shape record
(`RbR`). -/
@[refines ConRon.Arena.readBlock]
theorem readBlock_refinesC (hP : IndPartsProg5 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (nPd off l : Word) (blk : List IConstantInfo) {blkP : List ConLeche.ConstantInfo}
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbP : Frontend.denoteCIList a₀.store blk = some blkP)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 5)) "read_block" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.readBlock nPd.toNat blk) a₀ ∧
      RbR (AM.res (ConRon.Arena.readBlock nPd.toNat blk) a₀) r s'.mem ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.readBlock nPd.toNat blk) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (rb_spec p hP (realCall p) (realCall_spec p) n s₀ nPd off l) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (rbW_sim (realCall p) n hC.stage hblk (lvlHyp_real p hcl hL n hC hA hbP)) hm
    ⟨hl, hok, hQ⟩


end

end L.Ind
