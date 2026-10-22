import ConAgua.Arena.PropReadLoops
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.InferBodySpine

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
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- A three-word result of a call. -/
def t3W : Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) => some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m)

/-- A two-word result of a call. -/
def t2W : Option (List Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (r, m) => some (r.headD 0, r.tail.headD 0, m)

/-- After a heap computation started at top `t0`: `never` (flag `≠ 0`) or the names pushed. -/
def pushedK (t0 : Word) : Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 ≠ 0 then some (1, 0, 0, m) else some (2, t0, htop m - t0, m)

/-! ## `residual_pw(fl, h)` -/

/-- **The model of `residual_pw`.** -/
def rpwW (p : Prog) (n : Nat) (m : Mem) (fl h : Word) : Option (Word × Word × Word × Mem) :=
  if fl = 0 then some (0, 0, 0, m)
  else if h >>> 28 ≠ 2 then some (0, 0, 0, m)
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none
  else pushedK (htop m) (callW p n "lv_zero" [rdW (m.arr64 SOREC) (idxW h * 2 + tierW h)] m)

theorem residualPW_spec (p : Prog) (hp : p.lookup "residual_pw" = some residualPWL) (n : Nat)
    (s₀ : St) (fl h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "residual_pw" [fl, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      rpwW p n s₀.mem fl h = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, residualPWL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "lv_zero"] <;>
  simp_all [rpwW, pushedK, htop, tierW, idxW, LocEq, BinOp.eval, St.setLocs_cons, CTL, SOREC,
    Cmp.eval, Cmp.evalW, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## `subst_pw_at(lo, lc, us, k, o, c)` -/

/-- **The model of `subst_pw_at`.** -/
def spaW (p : Prog) (n : Nat) (m : Mem) (lo lc us k o c : Word) : Option (Word × Word × Word × Mem) :=
  if k ≠ 2 then some (k, o, c, m)
  else if c = 0 then some (k, o, c, m)
  else if lsNodeW m us = [] then none
  else pushedK (htop m) (callW p n "lv_spw"
    [o, c, lo, lc, (lsNodeW m us).headD 0, (lsNodeW m us).tail.headD 0] m)

theorem substPWAt_spec (p : Prog) (hp : p.lookup "subst_pw_at" = some substPWAtL)
    (hl : p.lookup "ls_node" = some lsNode) (n : Nat) (s₀ : St) (lo lc us k o c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "subst_pw_at" [lo, lc, us, k, o, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      spaW p n s₀.mem lo lc us k o c = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, substPWAtL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      lsNode_spec p hl n, callW_spec p n "lv_spw"] <;>
  simp_all [spaW, pushedK, htop, LocEq, BinOp.eval, St.setLocs_cons, CTL,
    Cmp.eval, Cmp.evalW, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## The program -/

/-- **What the readers need of a program**: their own functions and the callees they share. -/
structure PropReadProg (p : Prog) : Prop where
  bd : p.lookup "binder_dom" = some binderDomL
  aca : p.lookup "app_count_at" = some appCountAtL
  rpw : p.lookup "residual_pw" = some residualPWL
  lp : p.lookup "lam_proj" = some lamProjL
  uws : p.lookup "unwrap_step" = some unwrapStepL
  uid : p.lookup "unwrap_id_defs" = some unwrapIdDefsL
  ppw : p.lookup "peel_pis_w" = some peelPisWL
  spa : p.lookup "subst_pw_at" = some substPWAtL
  htr : p.lookup "head_type_res" = some headTypeResL
  htc : p.lookup "head_type_const" = some headTypeConstL
  htp : p.lookup "head_type_pw" = some headTypePWL
  tsp : p.lookup "type_sort_pw" = some typeSortPWL
  hpc : p.lookup "head_proof_const" = some headProofConstL
  hpp : p.lookup "head_proof_proj" = some headProofProjL
  hpw : p.lookup "head_proof_pw" = some headProofPWL
  prf : p.lookup "proof_pw" = some proofPWL
  npf : p.lookup "not_proof_fast" = some notProofFastL
  ipf : p.lookup "is_proof_fast" = some isProofFastL
  lvl : p.lookup "lv_lookup" = some (lvLookupG EREC POOL)
  spw : p.lookup "lv_spw" = some (lvSpwG LH)
  zero : p.lookup "lv_zero" = some lvZero
  push : p.lookup "lh_push" = some lhPush
  node : p.lookup "lv_node" = some lvNode
  lsnode : p.lookup "ls_node" = some lsNode
  eview : p.lookup "e_view" = some L.Ind.eView
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL
  args : p.lookup "get_app_args" = some getAppArgsL
  cnt : p.lookup "app_count" = some appCountL
  fill : p.lookup "app_fill" = some appFillL

/-! ## `head_type_res(vis, f, k, ty)` -/

/-- After `peel_pis_w`: `residual_pw`. -/
def htrK (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) => t3W (callW p n "residual_pw" [r.headD 0, r.tail.headD 0] m)

theorem headTypeRes_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f k ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_type_res" [vis, f, k, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ htrK p n (callW p n "peel_pis_w" [vis, f, k, ty] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.htr]
  simp only [callFn, headTypeResL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "peel_pis_w", callW_spec p n "residual_pw"] <;>
  simp_all [htrK, t3W, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## The `.const` arms: `head_type_const`, `head_proof_const` -/

/-- After the datum of the constant's type: `subst_pw_at` at the record `q`'s level parameters. -/
def cArmK2 (p : Prog) (n : Nat) (us q : Word) :
    Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, 0, m)
    else t3W (callW p n "subst_pw_at" [rdW (m.arr64 EREC) (q + 2), rdW (m.arr64 EREC) (q + 3), us,
      r.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m)

/-- After `env_find`: the stored constant, the level count, then `sub` at its type. -/
def cArmK1 (p : Prog) (n : Nat) (us : Word) (sub : Word → Mem → Option (List Word × Mem)) :
    Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, 0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) = 6 then some (0, 0, 0, m)
    else if lsNodeW m us = [] then none
    else if (lsNodeW m us).tail.headD 0 ≠ rdW (m.arr64 EREC) (r.tail.headD 0 + 3) then
      some (0, 0, 0, m)
    else cArmK2 p n us (r.tail.headD 0) (sub (rdW (m.arr64 EREC) (r.tail.headD 0 + 4)) m)

theorem headTypeConst_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St)
    (vis f k cn us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_type_const" [vis, f, k, cn, us]
    ⦃fun r s' => LocEq s' s₀ ∧ cArmK1 p n us (fun ty m => callW p n "head_type_res" [vis, f, k, ty] m)
      (callW p n "env_find" [cn, vis] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.htc]
  simp only [callFn, headTypeConstL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "env_find", lsNode_spec p hp.lsnode n, callW_spec p n "head_type_res",
      callW_spec p n "subst_pw_at"] <;>
  simp_all [cArmK1, cArmK2, t3W, LocEq, BinOp.eval, St.setLocs_cons, EREC,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

theorem headProofConst_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St)
    (vis f cn us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_proof_const" [vis, f, cn, us]
    ⦃fun r s' => LocEq s' s₀ ∧ cArmK1 p n us (fun ty m => callW p n "type_sort_pw" [vis, f, ty] m)
      (callW p n "env_find" [cn, vis] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.hpc]
  simp only [callFn, headProofConstL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "env_find", lsNode_spec p hp.lsnode n, callW_spec p n "type_sort_pw",
      callW_spec p n "subst_pw_at"] <;>
  simp_all [cArmK1, cArmK2, t3W, LocEq, BinOp.eval, St.setLocs_cons, EREC,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## `head_type_pw(vis, f, root, d, h, k)` -/

/-- The view's words: tag, first and second field. -/
def vG (v : List Word) : Word := v.headD 0
def vX (v : List Word) : Word := v.tail.headD 0
def vY (v : List Word) : Word := v.tail.tail.headD 0

/-- After `binder_dom`: `head_type_res` at the domain. -/
def htpK (p : Prog) (n : Nat) (vis f k : Word) (m : Mem) :
    Option (Word × Word) → Option (Word × Word × Word × Mem)
  | none => none
  | some (bf, bd) =>
    if bf = 0 then some (0, 0, 0, m) else t3W (callW p n "head_type_res" [vis, f, k, bd] m)

/-- **The model of `head_type_pw`.** -/
def htpW (p : Prog) (n : Nat) (m : Mem) (vis f root d h k : Word) :
    Option (Word × Word × Word × Mem) :=
  if L.Ind.eViewW m h = [] then none
  else if vG (L.Ind.eViewW m h) = 3 then
    t3W (callW p n "head_type_const" [vis, f, k, vX (L.Ind.eViewW m h), vY (L.Ind.eViewW m h)] m)
  else if vG (L.Ind.eViewW m h) = 1 then t3W (callW p n "head_type_res" [vis, f, k, vY (L.Ind.eViewW m h)] m)
  else if vG (L.Ind.eViewW m h) = 0 ∧ vX (L.Ind.eViewW m h) < d then
    htpK p n vis f k m (bdW m (d - 1 - vX (L.Ind.eViewW m h)) root)
  else some (0, 0, 0, m)

theorem headTypePW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St)
    (vis f root d h k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_type_pw" [vis, f, root, d, h, k]
    ⦃fun r s' => LocEq s' s₀ ∧
      htpW p n s₀.mem vis f root d h k = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.htp]
  simp only [callFn, headTypePWL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      L.Ind.eView_spec p hp.eview n, binderDomL_spec p hp.bd n, callW_spec p n "head_type_const",
      callW_spec p n "head_type_res"] <;>
  simp_all [htpW, htpK, vG, vX, vY, t3W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]
  all_goals (intro h; simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega)

/-! ## `type_sort_pw(vis, f, rt)` -/

/-- **The model of `type_sort_pw`.** -/
def tspW (p : Prog) (n : Nat) (m : Mem) (vis f rt : Word) : Option (Word × Word × Word × Mem) :=
  match tsLoopW m f rt 0 with
  | none => none
  | some (f', r, d) =>
    if f' = 0 then none
    else if r >>> 28 = 2 then some (1, 0, 0, m)
    else match acaW m r (f' - 1) with
      | none => none
      | some (c, fn) => t3W (callW p n "head_type_pw" [vis, f' - 1, rt, d, fn, c] m)

theorem typeSortPW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f rt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "type_sort_pw" [vis, f, rt]
    ⦃fun r s' => LocEq s' s₀ ∧
      tspW p n s₀.mem vis f rt = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.tsp]
  simp only [callFn, typeSortPWL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, typeSortPWLoop_step_spec p n,
      appCountAtL_spec p hp.aca n, callW_spec p n "head_type_pw"] <;>
  simp_all [tspW, t3W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## `unwrap_step(vis, f, e)`, `unwrap_id_defs(vis, f, k, e)` -/

/-- After `get_app_args`: the count test, the argument, the top put back. -/
def uwsK2 (k j top : Word) : Option (List Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if (136 : Word).toNat < (m.arr64 CTL).size then
      if r.tail.headD 0 ≠ k then some (0, 0, m.set64 CTL 136 top)
      else some (1, rdW (m.arr64 SPN) (r.headD 0 + (k - 1 - j)), m.set64 CTL 136 top)
    else none

/-- After `env_find`: a definition, its value's `lam_proj`, then the arguments. -/
def uwsK1 (p : Prog) (n : Nat) (f e : Word) : Option (List Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 1 then some (0, 0, m)
    else match lamProjW m f 0 (rdW (m.arr64 EREC) (r.tail.headD 0 + 5)) with
      | none => none
      | some (lf, k, j) =>
        if lf = 0 then some (0, 0, m)
        else uwsK2 k j (rdW (m.arr64 CTL) 136) (callW p n "get_app_args" [e] m)

/-- **The model of `unwrap_step`.** -/
def uwsW (p : Prog) (n : Nat) (m : Mem) (vis f e : Word) : Option (Word × Word × Mem) :=
  match acaW m e f with
  | none => none
  | some (_, hh) =>
    if hh >>> 28 ≠ 3 then some (0, 0, m)
    else if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (18 + tierW hh) ≤ idxW hh then none
    else uwsK1 p n f e (callW p n "env_find" [rdW (m.arr64 CREC) (idxW hh * 4 + tierW hh * 2), vis] m)

theorem unwrapStep_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unwrap_step" [vis, f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ uwsW p n s₀.mem vis f e = some (r.headD 0, r.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.uws]
  simp only [callFn, unwrapStepL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      appCountAtL_spec p hp.aca n, callW_spec p n "env_find", lamProjL_spec p hp.lp n,
      callW_spec p n "get_app_args"] <;>
  simp_all [uwsW, uwsK1, uwsK2, tierW, idxW, LocEq, BinOp.eval, St.setLocs_cons, CTL, EREC, CREC,
    SPN, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, size_set64]

/-- After `unwrap_step`: the rest of the steps. -/
def uidK (p : Prog) (n : Nat) (vis f k e : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (e, m)
    else call1W p n "unwrap_id_defs" [vis, f, k - 1, r.tail.headD 0] m

/-- **The model of `unwrap_id_defs`.** -/
def uidW (p : Prog) (n : Nat) (m : Mem) (vis f k e : Word) : Option (Word × Mem) :=
  if k = 0 then some (e, m) else uidK p n vis f k e (callW p n "unwrap_step" [vis, f, e] m)

theorem unwrapIdDefs_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unwrap_id_defs" [vis, f, k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ uidW p n s₀.mem vis f k e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.uid]
  simp only [callFn, unwrapIdDefsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "unwrap_step", callW_spec p n "unwrap_id_defs"] <;>
  simp_all [uidW, uidK, call1W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## `peel_pis_w(vis, f, k, e)` -/

/-- At a `∀` node `u`: its body, one binder fewer. -/
def ppwK2 (p : Prog) (n : Nat) (vis f k u : Word) (m : Mem) : Option (Word × Word × Mem) :=
  if tierW u ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (30 + tierW u) ≤ idxW u then none
  else t2W (callW p n "peel_pis_w" [vis, f, k - 1, rdW (m.arr64 FAREC) (idxW u * 4 + tierW u * 2 + 1)] m)

/-- After unwrapping a non-`∀`. -/
def ppwK1 (p : Prog) (n : Nat) (vis f k : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (u, m) => if u >>> 28 ≠ 6 then some (0, 0, m) else ppwK2 p n vis f k u m

/-- At `k = 0`. -/
def ppwK0 : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (u, m) => some (1, u, m)

/-- **The model of `peel_pis_w`.** -/
def ppwW (p : Prog) (n : Nat) (m : Mem) (vis f k e : Word) : Option (Word × Word × Mem) :=
  if k = 0 then ppwK0 (call1W p n "unwrap_id_defs" [vis, f, 4, e] m)
  else if e >>> 28 ≠ 6 then ppwK1 p n vis f k (call1W p n "unwrap_id_defs" [vis, f, 4, e] m)
  else ppwK2 p n vis f k e m

theorem peelPisW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_pis_w" [vis, f, k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ppwW p n s₀.mem vis f k e = some (r.headD 0, r.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.ppw]
  simp only [callFn, peelPisWL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "unwrap_id_defs", callW_spec p n "peel_pis_w"] <;>
  simp_all [ppwW, ppwK0, ppwK1, ppwK2, t2W, call1W, tierW, idxW, LocEq, BinOp.eval,
    St.setLocs_cons, CTL, FAREC, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## `head_proof_proj`, `head_proof_pw`, `proof_pw` -/

/-- The body handle of field `i` of the table record `q` (`0` past the bodies). -/
def hppB (m : Mem) (q i : Word) : Word :=
  if i < rdW (m.arr64 EREC) (q + 10) then rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 9) + i) else 0

/-- After the body's datum: `never` stays, anything else is unknown. -/
def hppK2 : Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 1 then some (1, 0, 0, m) else some (0, 0, 0, m)

/-- After `find_proj`. -/
def hppK1 (p : Prog) (n : Nat) (vis f i : Word) :
    Option (List Word × Mem) → Option (Word × Word × Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, 0, m)
    else hppK2 (callW p n "type_sort_pw" [vis, f, hppB m (r.tail.headD 0) i] m)

theorem headProofProj_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f sn i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_proof_proj" [vis, f, sn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ hppK1 p n vis f i (callW p n "find_proj" [vis, sn, i] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.hpp]
  simp only [callFn, headProofProjL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "find_proj", callW_spec p n "type_sort_pw"] <;>
  simp_all [hppK1, hppK2, hppB, LocEq, BinOp.eval, St.setLocs_cons, EREC,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]
  all_goals
    rw [if_neg (by simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega)]
    simp_all

/-- **The model of `head_proof_pw`.** -/
def hpwW (p : Prog) (n : Nat) (m : Mem) (vis f h : Word) : Option (Word × Word × Word × Mem) :=
  if L.Ind.eViewW m h = [] then none
  else if vG (L.Ind.eViewW m h) = 3 then
    t3W (callW p n "head_proof_const" [vis, f, vX (L.Ind.eViewW m h), vY (L.Ind.eViewW m h)] m)
  else if vG (L.Ind.eViewW m h) = 1 then
    t3W (callW p n "type_sort_pw" [vis, f, vY (L.Ind.eViewW m h)] m)
  else if vG (L.Ind.eViewW m h) = 2 then some (1, 0, 0, m)
  else if vG (L.Ind.eViewW m h) = 6 then some (1, 0, 0, m)
  else if vG (L.Ind.eViewW m h) = 8 then some (1, 0, 0, m)
  else if vG (L.Ind.eViewW m h) = 9 then
    t3W (callW p n "head_proof_proj" [vis, f, vX (L.Ind.eViewW m h), vY (L.Ind.eViewW m h)] m)
  else some (0, 0, 0, m)

theorem headProofPW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_proof_pw" [vis, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      hpwW p n s₀.mem vis f h = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.hpw]
  simp only [callFn, headProofPWL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      L.Ind.eView_spec p hp.eview n, callW_spec p n "head_proof_const",
      callW_spec p n "type_sort_pw", callW_spec p n "head_proof_proj"] <;>
  simp_all [hpwW, vG, vX, vY, t3W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-- **The model of `proof_pw`.** -/
def prfW (p : Prog) (n : Nat) (m : Mem) (vis f e : Word) : Option (Word × Word × Word × Mem) :=
  match ppLoopW m f e with
  | none => none
  | some (f', e') => if f' = 0 then none else t3W (callW p n "head_proof_pw" [vis, f' - 1, e'] m)

theorem proofPW_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proof_pw" [vis, f, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      prfW p n s₀.mem vis f e = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.prf]
  simp only [callFn, proofPWL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, proofPWLoop_step_spec p n,
      callW_spec p n "head_proof_pw"] <;>
  simp_all [prfW, t3W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
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
  rw [invoke_eq _ hp.npf]
  simp only [callFn, notProofFastL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64_spec,
      callW_spec p n "proof_pw"] <;>
  simp_all [propArmK, npfV, LocEq, BinOp.eval, St.setLocs_cons, CTL,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

theorem isProofFast_spec (p : Prog) (hp : PropReadProg p) (n : Nat) (s₀ : St) (vis a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_proof_fast" [vis, a]
    ⦃fun r s' => LocEq s' s₀ ∧ (192 : Word).toNat < (s₀.mem.arr64 CTL).size ∧
      propArmK ipfV (callW p n "proof_pw" [vis, 4000000000, a] (s₀.mem.set64 CTL 192 0)) =
        some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ipf]
  simp only [callFn, isProofFastL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64_spec,
      callW_spec p n "proof_pw"] <;>
  simp_all [propArmK, ipfV, LocEq, BinOp.eval, St.setLocs_cons, CTL,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

end L.Arena
