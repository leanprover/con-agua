module

import ConRon.Bridge.Core.Walks.Cached
import ConAgua.Arena.IndRealWalkT
import ConRon.Bridge.Checker.Hyp
public import ConAgua.Arena.IndTwin
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Shift
public import ConRon.Bridge.StateOK

@[expose] public section

/-!
# `check_value_group` under `StageT` (lane `loopt2`)

`check_value_group`'s pieces under `StageT` (its refinement, `cvg_ref`, and
`install_value_guards`', `ivg_ref`, are in `Verdict/DeclValE.lean`): the theorem test's prefix,
`iw_reset`, the walks' twin runs keeping the store (`lbbF_store`, `hffF_store`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- `loose_bvars_bounded_fast`'s twin run keeps the store (it changes the per-call memos only). -/
theorem lbbF_store {f k : Nat} {e : EIdx} {a a' : AState} {x : Bool}
    (h : (looseBVarsBoundedFast f k e).run a = .ok (x, a')) : a'.store = a.store := by
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_bvarB_sp _ _) fun _ => Keeps.pure _) x a' h
  rfl

/-- `has_fvar_fast`'s twin run keeps the store. -/
theorem hffF_store {f : Nat} {e : EIdx} {a a' : AState} {x : Bool}
    (h : (hasFvarFast f e).run a = .ok (x, a')) : a'.store = a.store := by
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_fvarB_sp _ _) fun _ => Keeps.pure _) x a' h
  rfl

/-- The memory after `iw_reset` keeps `StageT`. -/
theorem iwReset_stageT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hT : StageT dn vis fe m a) : StageT dn vis fe (m.set64 CTL 200 0) a :=
  StageT.of_iw hT (iwReset_stage hT.stage).1
    (MemFrame.mono (MemFrame.setCtl m 200 0) (by simp) (by simp))

/-- **The theorem test's prefix extends the twin's store** (con-ron's `KnotSpec.infer` and
`EnsureSortSpec`, as in `checkValueGroup_bridge`): from `CheckOK` and the constant's type denoting
in scope. -/
theorem thmPrefix_ext {env : ConLeche.Env} {fe : IFEnv} {a a1 a2 : AState} {cv : IConstantVal}
    {cP : ConLeche.ConstantVal} {x1 : EIdx} {x2 : LIdx} (henv : ConLeche.EnvWF env)
    (hck : ConRon.Bridge.CheckOK V env fe a) (hcv : Frontend.denoteCV a.store cv = some cP)
    (hws : ConLeche.Expr.WScoped 0 cP.type)
    (h1 : (inferTypeCore V fe checkFuel 0 cv.type).run a = .ok (x1, a1))
    (h2 : (ensureSortCore V fe checkFuel 0 x1).run a1 = .ok (x2, a2)) :
    ConRon.Bridge.CheckOK V env fe a2 ∧ Ext a.store a2.store := by
  obtain ⟨-, -, hty0⟩ := ConRon.Bridge.Core.denoteCV_inv hcv
  obtain ⟨hcka, hxa, -, sty, hsty, hwssty, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl h1
    (((ConRon.Bridge.CoreSpec.of_core rfl).knot env fe henv).infer a 0 cv.type cP.type hck hty0 hws)
  obtain ⟨hckb, hxb, -, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a1) rfl h2
    (((ConRon.Bridge.CoreSpec.of_core rfl).sort env fe henv) a1 0 x1 sty hcka hsty hwssty)
  exact ⟨hckb, hxa.trans hxb⟩

end L.Arena
