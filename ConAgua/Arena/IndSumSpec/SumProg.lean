import ConAgua.Arena.IndRealCrF
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndSumSpec.CheckStructFieldSortsISucc

/-!
# SumProg

`SumProg`, `ctlK9`, `ctlK8`, `cscTailT`, `ctorK9`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The program lookups of `check_sum_ctor(s)` and their callees. -/
structure SumProg (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsc : p.lookup "sl_cons" = some slCons
  hg : p.lookup "sl_get" = some slGet
  hpf : p.lookup "param_find" = some paramFind
  hpp : p.lookup "param_push" = some paramPush
  ad : AdF p
  hip : p.lookup "intern_param" = some internParam
  hplg : p.lookup "param_levels_go" = some paramLevelsGoL
  hpl : p.lookup "param_levels" = some paramLevelsL
  hil : IlF p
  hcf : p.lookup "const_find" = some constFind
  hcp : p.lookup "const_push" = some constPush
  hic : p.lookup "intern_const" = some internConst
  heq : p.lookup "sl_eq" = some slEq
  hfdr : p.lookup "field_doms_resolve" = some fieldDomsResolveL
  hiar : p.lookup "idx_args_resolve" = some idxArgsResolveL
  hcr : CrfF p
  hpw : p.lookup "pin_word" = some pinWordL
  het : p.lookup "lvl_eq_true" = some lvlEqTrue
  hcn : p.lookup "sl_contains" = some slContains
  hfsb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL
  hcfg : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL
  hcfs : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL
  htail : p.lookup "check_sum_ctor_tail" = some checkSumCtorTailL
  hbf : p.lookup "bvar_find" = some bvarFind
  hbp : p.lookup "bvar_push" = some bvarPush
  hib : p.lookup "intern_bvar" = some internBVar
  hpg : p.lookup "struct_ps_at_go" = some structPsAtGoL
  hps : p.lookup "struct_ps_at" = some structPsAtL
  hsr : p.lookup "struct_ctor_resid_ok" = some structCtorResidOkL
  hsd : p.lookup "check_struct_doms_at" = some checkStructDomsAtL
  hctor : p.lookup "check_sum_ctor" = some checkSumCtorL
  hrec2 : p.lookup "rec2" = some rec2
  hcs : p.lookup "check_sum_ctors" = some checkSumCtorsL
  strip : StripProg p

/-! ## `check_sum_ctor_tail`: the word model -/

/-- After the field sorts. -/
def ctlK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)
/-- After `idx_args_resolve`: the field sorts. -/
def ctlK8 (cR : CallM) (n : Nat) (vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK9 (fsortsW cR n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF)
/-! ## The relation to the twin: pieces -/

/-- The twin's tail of `checkSumCtor` (from the opened field telescope on), verbatim. -/
def cscTailT (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx)
    (isProp large : Bool) (cvCa : IConstantVal) (nF : Nat) (cq : List EIdx × EIdx) :
    AM (IConstantVal × List LIdx) := do
  let xq ← unwrapOr (← openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let xfn ← getAppFn coreWalkFuel xq.2
  let xargs ← getAppArgs coreWalkFuel xq.2
  unless xfn == hd && xargs.take nP == cq.1 && xargs.length == nP + nIdx do
    fail (.notImplemented "direct sum: opened constructor residual")
  let idxArgs := xargs.drop nP
  unless ← fieldDomsResolve fe₀ xq.1 do
    fail (.notImplemented "direct sum: field domain after the block")
  unless ← idxArgsResolve fe₀ idxArgs do
    fail (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI .verified fe isProp large resSort nP xq.1
    idxArgs nF
  pure (cvCa, sorts)

/-! ## `check_sum_ctor`: the word model -/

/-- After the tail. -/
def ctorK9 (cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([cvC, r.headD 0, r.tail.headD 0], m)
end L.Ind

end
