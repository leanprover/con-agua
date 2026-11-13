module

public import ConAgua.Arena.PropReadLoops
import ConAgua.Arena.InferBodySpine
public import ConAgua.Arena.LevelSubstL
import ConAgua.Arena.InferBodyIntern
import Std.WP.Triple.SpecLemmas
import ConAgua.L.ModelGen
import ConAgua.L.GrindAttr
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndView
public import ConAgua.Arena.KnotSlot
public import ConAgua.L.ProgHas
import all ConAgua.Arena.PropRead

@[expose] public section

/-!
# The prop-ness readers: word-level models of the functions with calls (helper `defeq2-prop`)

One model per L function of `PropRead.lean` that calls another, in the `callW` shape (the callee's
run is an argument of the model's continuation, `InferLeaves.lean`'s `constArmK`), and its spec
(`vcgen` + `simp_all`). A datum result is `(k, o, c, m)` (`PropRead.lean`'s encoding).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- A three-word result of a call. -/
def t3W : Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) => some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m)

/-! ## `residual_pw(fl, h)`, `subst_pw_at(lo, lc, us, k, o, c)` -/

/-- **The model of `residual_pw`.** -/
l_model residualPW_spec (p : Prog) (hp : p.lookup "residual_pw" = some residualPWL)
  fns [hp ↦ rpwW tuple]
  specs [callW_spec p n "lv_zero"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-- **The model of `subst_pw_at`.** -/
l_model substPWAt_spec (p : Prog) (hp : p.lookup "subst_pw_at" = some substPWAtL)
    (hl : p.lookup "ls_node" = some lsNode)
  fns [hp ↦ spaW tuple]
  specs [lsNode_spec p hl n, callW_spec p n "lv_spw"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-! ## The program -/

/-- The functions of `PropReadProg`. -/
def propReadProgFns : Prog :=
  [("binder_dom", binderDomL), ("app_count_at", appCountAtL), ("residual_pw", residualPWL),
   ("lam_proj", lamProjL), ("unwrap_step", unwrapStepL), ("unwrap_id_defs", unwrapIdDefsL),
   ("peel_pis_w", peelPisWL), ("subst_pw_at", substPWAtL), ("head_type_res", headTypeResL),
   ("head_type_const", headTypeConstL), ("head_type_pw", headTypePWL),
   ("type_sort_pw", typeSortPWL), ("head_proof_const", headProofConstL),
   ("head_proof_proj", headProofProjL), ("head_proof_pw", headProofPWL), ("proof_pw", proofPWL),
   ("not_proof_fast", notProofFastL), ("is_proof_fast", isProofFastL),
   ("lv_lookup", lvLookupTG EREC POOL), ("lv_spw", lvSpwG LH), ("lv_zero", lvZero),
   ("lh_push", lhPush), ("lv_node", lvNode), ("ls_node", lsNode), ("e_view", L.Ind.eView), ("env_row_get", envRowGetL), ("base_row_get", baseRowGetL), ("env_find", envFindL),
   ("get_app_args", getAppArgsL), ("app_count", appCountL), ("app_fill", appFillL)]

/-- **What the readers need of a program**: their own functions and the callees they share. -/
abbrev PropReadProg (p : Prog) : Prop := ProgHas p propReadProgFns

/-! ## `head_type_res`, the `.const` arms, `head_type_pw` -/

/-- **The model of `head_type_res`**: `peel_pis_w`, then `residual_pw`. -/
l_model headTypeRes_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "head_type_res" ↦ htrW tuple]
  specs [callW_spec p n "peel_pis_w", callW_spec p n "residual_pw"]
  grind [arena_grind] pfuel

/-! ## The `.const` arms: `head_type_const`, `head_proof_const` -/

/-- After the datum of the constant's type: `subst_pw_at` at the record `q`'s level parameters. -/
def cArmK2 (p : Prog) (n : Nat) (us q : Word) :
    Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, 0, m)
    else t3W (callW p n "subst_pw_at" [erRd m (q + (CI.cv + CV.lpsOff)), erRd m (q + (CI.cv + CV.lpsLen)), us,
      r.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m)

/-- After `env_find`: the stored constant, the level count, then `sub` at its type. -/
def cArmK1 (p : Prog) (n : Nat) (us : Word) (sub : Word → Mem → Option (List Word × Mem)) :
    Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, 0, m)
    else if lsNodeW m us = [] then none
    else if (lsNodeW m us).tail.headD 0 ≠ erRd m (r.tail.headD 0 + (CI.cv + CV.lpsLen)) then
      some (0, 0, 0, m)
    else cArmK2 p n us (r.tail.headD 0) (sub (erRd m (r.tail.headD 0 + (CI.cv + CV.type))) m)

theorem headTypeConst_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St)
    (vis f k cn us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_type_const" [vis, f, k, cn, us]
    ⦃fun r s' => LocEq s' s₀ ∧ cArmK1 p n us (fun ty m => callW p n "head_type_res" [vis, f, k, ty] m)
      (callW p n "env_find" [cn, vis] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "head_type_const")]
  simp only [callFn, headTypeConstL]
  vcgen [evalE_tld, tld, ld64_rdT_spec, evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "env_find", lsNode_spec p (hp.get "ls_node") n, callW_spec p n "head_type_res",
      callW_spec p n "subst_pw_at"] <;>
  simp_all [cArmK1, cArmK2, t3W, erRd, rec_unfold, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

theorem headProofConst_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St)
    (vis f cn us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_proof_const" [vis, f, cn, us]
    ⦃fun r s' => LocEq s' s₀ ∧ cArmK1 p n us (fun ty m => callW p n "type_sort_pw" [vis, f, ty] m)
      (callW p n "env_find" [cn, vis] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "head_proof_const")]
  simp only [callFn, headProofConstL]
  vcgen [evalE_tld, tld, ld64_rdT_spec, evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "env_find", lsNode_spec p (hp.get "ls_node") n, callW_spec p n "type_sort_pw",
      callW_spec p n "subst_pw_at"] <;>
  simp_all [cArmK1, cArmK2, t3W, erRd, rec_unfold, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-- **The model of `head_type_pw`.** -/
l_model headTypePW_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "head_type_pw" ↦ htpW tuple]
  specs [L.Ind.eView_spec p (hp.get "e_view") n, binderDomL_spec p (hp.get "binder_dom") n,
    callW_spec p n "head_type_const", callW_spec p n "head_type_res"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-! ## `type_sort_pw(vis, f, rt)` -/

/-- **The model of `type_sort_pw`.** -/
def tspW (p : Prog) (n : Nat) (m : Mem) (vis f rt : Word) : Option (Word × Word × Word × Mem) :=
  match tsLoopW m f rt 0 with
  | none => none
  | some (f', r, d) =>
    if f' = 0 then none
    else if tagW r = 2 then some (1, 0, 0, m)
    else match acaW m r (f' - 1) with
      | none => none
      | some (c, fn) => t3W (callW p n "head_type_pw" [vis, f' - 1, rt, d, fn, c] m)

theorem typeSortPW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f rt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "type_sort_pw" [vis, f, rt]
    ⦃fun r s' => LocEq s' s₀ ∧
      tspW p n s₀.mem vis f rt = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ (hp.get "type_sort_pw")]
  simp only [callFn, typeSortPWL]
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, typeSortPWLoop_step_spec p n,
      appCountAtL_spec p (hp.get "app_count_at") n, callW_spec p n "head_type_pw"] <;>
  simp_all [tspW, t3W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## `unwrap_step(vis, f, e)`, `unwrap_id_defs(vis, f, k, e)`, `peel_pis_w(vis, f, k, e)` -/

/-- **The model of `unwrap_step`.** -/
l_model unwrapStep_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "unwrap_step" ↦ uwsW tuple]
  specs [appCountAtL_spec p (hp.get "app_count_at") n, callW_spec p n "env_find",
    lamProjL_spec p (hp.get "lam_proj") n, callW_spec p n "get_app_args"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-- **The model of `unwrap_id_defs`.** -/
l_model unwrapIdDefs_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "unwrap_id_defs" ↦ uidW]
  specs [callW_spec p n "unwrap_step", callW_spec p n "unwrap_id_defs"]
  grind [arena_grind] pfuel

/-- **The model of `peel_pis_w`.** -/
l_model peelPisW_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "peel_pis_w" ↦ ppwW tuple]
  specs [callW_spec p n "unwrap_id_defs", callW_spec p n "peel_pis_w"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-! ## `head_proof_proj`, `head_proof_pw`, `proof_pw` -/

/-- **The model of `head_proof_proj`**: the table's body at field `i` (`0` past the bodies),
`never` kept, anything else unknown. -/
l_model headProofProj_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "head_proof_proj" ↦ hppW tuple]
  specs [callW_spec p n "find_proj", callW_spec p n "type_sort_pw"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-- **The model of `head_proof_pw`.** -/
l_model headProofPW_spec (p : Prog) (hp : PropReadProg p)
  fns [hp.get "head_proof_pw" ↦ hpwW tuple]
  specs [L.Ind.eView_spec p (hp.get "e_view") n, callW_spec p n "head_proof_const",
    callW_spec p n "type_sort_pw", callW_spec p n "head_proof_proj"]
  grind [arena_grind] extra [ld64_rdW_spec, ld64_rdT_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE, st64_spec] pfuel

/-- **The model of `proof_pw`.** -/
def prfW (p : Prog) (n : Nat) (m : Mem) (vis f e : Word) : Option (Word × Word × Word × Mem) :=
  match ppLoopW m f e with
  | none => none
  | some (f', e') => if f' = 0 then none else t3W (callW p n "head_proof_pw" [vis, f' - 1, e'] m)

theorem proofPW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proof_pw" [vis, f, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      prfW p n s₀.mem vis f e = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "proof_pw")]
  simp only [callFn, proofPWL]
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, proofPWLoop_step_spec p n,
      callW_spec p n "head_proof_pw"] <;>
  simp_all [prfW, t3W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## The two arms -/

/-- The verdict of `not_proof_fast` on the datum's words. -/
def npfV (k c : Word) : Word := if k = 0 then 0 else if k = 2 ∧ c = 0 then 0 else 1

/-- The verdict of `is_proof_fast` on the datum's words. -/
def ipfV (k c : Word) : Word := if k = 2 ∧ c = 0 then 1 else 0

/-- After `proof_pw`, a verdict. -/
def propArmK (V : Word → Word → Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => some (V (r.headD 0) (r.tail.tail.headD 0), m)

theorem notProofFast_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "not_proof_fast" [vis, a]
    ⦃fun r s' => LocEq s' s₀ ∧ (192 : Word).toNat < (s₀.mem.arr64 CTL).size ∧
      propArmK npfV (callW p n "proof_pw" [vis, 4000000000, a] (s₀.mem.set64 CTL 192 0)) =
        some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "not_proof_fast")]
  simp only [callFn, notProofFastL]
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64_spec,
      callW_spec p n "proof_pw"] <;>
  simp_all [propArmK, npfV, LocEq, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

theorem isProofFast_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_proof_fast" [vis, a]
    ⦃fun r s' => LocEq s' s₀ ∧ (192 : Word).toNat < (s₀.mem.arr64 CTL).size ∧
      propArmK ipfV (callW p n "proof_pw" [vis, 4000000000, a] (s₀.mem.set64 CTL 192 0)) =
        some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "is_proof_fast")]
  simp only [callFn, isProofFastL]
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64_spec,
      callW_spec p n "proof_pw"] <;>
  simp_all [propArmK, ipfV, LocEq, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

end L.Arena
