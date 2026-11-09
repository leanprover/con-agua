module

public import ConAgua.Arena.IndRealLvlC
public import ConAgua.Arena.IndPartsSpec.BpW
import ConAgua.Arena.IndPartsSpec.Bf
import ConAgua.Arena.IndPartsSpec.BrsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Specs

@[expose] public section

/-!
# `blockShape?`, `blockParts?` under `StageC`, `lvl_eq_c` the real call (lane `indproofs4`, helper `bp`)

`IndPartsSpec/PlW`'s sims read `lvl_eq_c` through `LvlHyp`: the call's `Sim` at the twin's prefix of
`blockShape?` (`TshT`: the split, the counts, the reserved names, the result sort) and at the model's
prefix (`AFr`). Under `StageC` and `AbsOK` at entry the real call meets it (`lvlHyp_real`): con-ron's
frame lemmas make the twin's prefix a `PStep` (`blockMemberCounts?_spec`, `reservedBasisNames_pstep`;
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
/-- **The real `lvl_eq_c` meets `LvlHyp` at `blockShape?`'s prefix** from a `StageC` state whose
memory holds `AbsOK` and whose store denotes the block. -/
theorem lvlHyp_real (n : Nat) {m : Mem} {a : AState} {nP : Nat} {blk : List IConstantInfo}
    {blkP : List ConLeche.ConstantInfo} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hb : Frontend.denoteCIList a.store blk = some blkP) :
    LvlHyp (realCall p) n dn vis fe m (TshT nP blk a) := by
  -- the master proof reads con-ron's `CheckOK` off `StageC` (its `check` field, gone at the sync:
  -- `TwinStep.StageC`, outside this area) for `blockMemberCounts?_spec`'s and
  -- `reservedBasisNames_pstep`'s state hypotheses
  sorry

include hcl hL in
/-- **`block_shape` refines `blockShape?` under `StageC`**, its `lvl_eq_c` the real call
(`blockShape_refines`' statement; `lvlHyp_real` for the stub contract): the stage relation with
con-ron's `CheckOK` and `AbsOK` at entry, the block denoting in the twin's store. -/
@[refines ConRon.Arena.blockShape?]
theorem blockShape_refinesC (hP : IndPartsProg5 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (nPd off l : Word) (blk : List IConstantInfo) {blkP : List ConLeche.ConstantInfo}
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbP : Frontend.denoteCIList a₀.store blk = some blkP)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 5)) "block_shape" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.blockShape? nPd.toNat blk) a₀ ∧
      ShapeR (AM.res (ConRon.Arena.blockShape? nPd.toNat blk) a₀) r s'.mem ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.blockShape? nPd.toNat blk) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (bsh_spec p hP (realCall p) (realCall_spec p) n s₀ nPd off l) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (bshW_sim (realCall p) n hC.stage hblk (lvlHyp_real p hcl hL n hC hA hbP)) hm
    ⟨hl, hok, hQ⟩


end

end L.Ind
