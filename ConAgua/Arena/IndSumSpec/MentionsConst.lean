module

public import ConAgua.Arena.IndSumSpec.McGoStep
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.Env
import ConAgua.Arena.IndPosSpec.MatesW
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# MentionsConst: `ConRon.Arena.hasLooseBVarBFast`, `ConRon.Arena.hasLooseBVarBGo`, `ConRon.Arena.hasLooseBVarBIns`, `ConRon.Arena.mentionsConstGo`, `ConRon.Arena.mentionsConst`

The refinement theorems `mentionsConstGo_refines`, `mentionsConst_refines`, `hasLooseBVarBIns_refines`, `hasLooseBVarBGo_refines`, `hasLooseBVarBFast_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section mcCensus
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
  (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
include hv hf hput hgo

/-- **`mentions_const_go` refines `mentionsConstGo`**, from a memo related to the twin's, at the twin
fuel `f.toNat` of the L fuel word `f`, at every exec depth `n`. -/
@[refines ConRon.Arena.mentionsConstGo]
theorem mentionsConstGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f T h : Word) (mp : Std.HashMap EIdx Bool) (hh : H h)
    (hT : H T) (hS : StageR vis fe s₀.mem a₀) (hM : mcMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_const_go" [f, T, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsConstGo (decI T) mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.mentionsConstGo (decI T) mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0 != 0) = (AM.res (ConRon.Arena.mentionsConstGo (decI T) mp f.toNat (decE h)) a₀).1 ∧
      mcMR s'.mem (AM.res (ConRon.Arena.mentionsConstGo (decI T) mp f.toNat (decE h)) a₀).2 ∧
      StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

end mcCensus

/-! ## `mentions_const` -/

def mcConstW (n : Nat) (m : Mem) (T e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) mcSch.cs + 2 = 0 then none else mcGoW n (mclearG mcSch m) CWF T e

theorem mcConstW_eq (n : Nat) (m : Mem) (T e : Word) (h0 : rdW (m.arr64 CTL) mcSch.cs + 2 ≠ 0) :
    mcConstW n m T e = mcGoW n (mclearG mcSch m) CWF T e := by simp [mcConstW, h0]
attribute [ind_grind] mcConstW_eq

theorem mentionsConst_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
    (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
    (hcl : p.lookup "mc_clear" = some (memoClearG mcSch))
    (hp : p.lookup "mentions_const" = some mentionsConstL) (n : Nat) (s₀ : St) (T e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_const" [T, e]
    ⦃fun r s' => LocEq s' s₀ ∧ mcConstW n s₀.mem T e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := mcGo_spec p hv hf hput hgo n
  unfold McGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, mentionsConstL]
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec mcSch p _ hcl n, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Nat.reduceEqDiff, reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, ind_grind]

section mcCensus2
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
  (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
  (hcl : p.lookup "mc_clear" = some (memoClearG mcSch))
  (hp : p.lookup "mentions_const" = some mentionsConstL)
include hv hf hput hgo hcl hp

/-- **`mentions_const` refines `mentionsConst`**: clear the `mc` memo (any well-formed one on entry),
one memoised walk from `coreWalkFuel`, at every exec depth. -/
@[refines ConRon.Arena.mentionsConst]
theorem mentionsConst_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis T e : Word) (mp0 : Std.HashMap EIdx Bool) (hh : H e)
    (hT : H T) (hS : StageR vis fe s₀.mem a₀) (hM : mcMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_const" [T, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsConst (decI T) (decE e)) a₀ ∧
      AM.st (ConRon.Arena.mentionsConst (decI T) (decE e)) a₀ = a₀ ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.mentionsConst (decI T) (decE e)) a₀ ∧
      (∃ mp1, mcMR s'.mem mp1) ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

end mcCensus2

/-! ## The census theorems of the `hb` walk -/

section hbCensus
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p)

include hf hput hins in
/-- **`has_loose_b_var_b_ins` refines `hasLooseBVarBIns`**: the answer's word is recorded in the memo. -/
@[refines ConRon.Arena.hasLooseBVarBIns]
theorem hasLooseBVarBIns_refines (n : Nat) (s₀ : St) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis : Word) (a₀ : AState) (e i r : Word) (b : Bool) (mp : Std.HashMap (EIdx × Nat) Bool) (he : H e)
    (hr : r = if b then 1 else 0) (hS : StageR vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_ins" [e, i, r]
    ⦃fun rr s' => LocEq s' s₀ ∧ rr.headD 0 = r ∧
      hbMR s'.mem (ConRon.Arena.hasLooseBVarBIns (decE e) i.toNat (b, mp)).2 ∧
      StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

include hv hf hput hins hgo hbp in
/-- **`has_loose_b_var_b_go` refines `hasLooseBVarBGo`** from a related memo, at the twin fuel
`f.toNat` of the L fuel word `f`, at every exec depth `n` (`bvar_b` is lane `exprops4`'s,
`bvbW_stageW`). -/
@[refines ConRon.Arena.hasLooseBVarBGo]
theorem hasLooseBVarBGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f i h : Word) (mp : Std.HashMap (EIdx × Nat) Bool) (hh : H h)
    (hS : StageR vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_go" [f, i, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.hasLooseBVarBGo mp i.toNat f.toNat (decE h)) a₀ ∧
      r.headD 0 = (if (AM.res (ConRon.Arena.hasLooseBVarBGo mp i.toNat f.toNat (decE h)) a₀).1 then 1 else 0) ∧
      hbMR s'.mem (AM.res (ConRon.Arena.hasLooseBVarBGo mp i.toNat f.toNat (decE h)) a₀).2 ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.hasLooseBVarBGo mp i.toNat f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

end hbCensus

section hbCensus2
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p)
  (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
  (hp : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
include hv hf hput hins hgo hbp hcl hp

/-- **`has_loose_b_var_b_fast` refines `hasLooseBVarBFast`**: clear the `hb` memo (any well-formed one
on entry), one memoised walk from `coreWalkFuel`. -/
@[refines ConRon.Arena.hasLooseBVarBFast]
theorem hasLooseBVarBFast_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis i e : Word) (mp0 : Std.HashMap (EIdx × Nat) Bool)
    (hh : H e) (hS : StageR vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "has_loose_b_var_b_fast" [i, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)) a₀ ∧
      r.headD 0 = (if AM.res (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)) a₀ then 1 else 0) ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

end hbCensus2

end L.Ind
end
