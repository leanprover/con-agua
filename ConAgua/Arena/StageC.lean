import ConAgua.Arena.TwinStep
import ConAgua.Arena.LeafFns

/-!
# Carrying `StageC` (lane `loopt2`)

`StageC` (`TwinStep.lean`) is the stage relation with con-ron's `CheckOK` and the memory's half of
`TwinOK`. It is carried

* across a **leaf** call (`StageC.of_leaf`): the L side's stage relation after it, the call's frame
  (`LeafClosed`: no pin, no core memo written), the twin side's `IStepS` (con-ron's `*_run`/`*_sstep`
  lemmas: `StateOK` after, `Ext`, caches and pins unchanged);
* across a **core call** or any `StageT`-keeping callee (`StageC.of_T`): `StageT` after (the
  knot's sims, lane `indproofs3`'s contracts) and `CheckOK` after (con-ron's bridges: `KnotSpec`,
  `checkConstantVal_bridge`, `reducePinGuard_run`, …).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- The frame of a leaf call. -/
theorem callW_leafFrame {p : Prog} (hcl : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {n : Nat}
    {args : List Word} {m m' : Mem} {r : List Word} (h : callW p n f args m = some (r, m')) :
    MemFrame leafA leafC m m' :=
  (run_memFrame hcl hf (run_of_callW h)).1

/-- **`StageC` across a leaf**. -/
theorem StageC.of_leaf {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hf : MemFrame leafA leafC m m')
    (hs : ConRon.Bridge.Frontend.IStepS a a') : StageC dn vis fe env m' a' :=
  ⟨hS, h.check.mono hs.ok hs.ext hs.caches hs.pins,
    ⟨by rw [hf.2.2.1]; exact h.mem.erec, by rw [hf.2.2.1]; exact h.mem.spn,
      by rw [hf.2.2.1]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp,
      fun k x e => hs.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.1 PINS leafA_pins (by decide)]; exact h.flag⟩

/-- **`StageC` after a `StageT`-keeping call**, with con-ron's `CheckOK` after it. -/
theorem StageC.of_T {m : Mem} {a : AState} (hT : StageT dn vis fe m a)
    (hck : ConRon.Bridge.CheckOK .verified env fe a) : StageC dn vis fe env m a :=
  ⟨hT.stage, hck, hT.twin.mem, hT.flag⟩

end L.Ind
