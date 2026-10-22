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

end L.Arena
