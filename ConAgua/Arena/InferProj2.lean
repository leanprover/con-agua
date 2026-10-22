import ConAgua.Arena.InferProj

/-!
# `inferProj`: `infer_proj` (lane `defeq2`, helper `defeq2-proj`)

`infer_proj(mode, io, vis, d, sn, i, pe)` refines `inferProj` at both grades (`io = 0`: the knot;
`io = 1`: its io view, `CoreFnsA.ioView`), at L fuel `n + 1` from `KnotUpTo p n`: the subject's
type (`infer`/`infer_io`, then `whnf`), its head constant `T.{us}` (read once, before
`find_proj`), the table lookup, then `infer_proj_at` (`InferProj.lean`). A miss aborts in L where
the twin fails (`projMissError`'s verdict, an error).

**`inferProj_refines : InferProjProg p → InferProjCallees p → InferProjOK p`**, closing
`InferCallees.proj` (`InferBodyDisp.lean`).

Twin-side facts proved here: `findProj?` keeps every level-list readback (it interns the table's
name, `projTableName`; `EStore.internName_ext`) and answers only entries below the table's field
count.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The twin's lookup -/

/-- **`internNNode` extends the store.** -/
theorem internNNode_ext' (v : NNodeView) (a a' : AState) (h : NIdx)
    (hr : (internNNode v).run a = .ok (h, a')) : Ext a.store a'.store := by
  unfold internNNode at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · cases hr; exact Ext.refl _
  · rename_i hn
    by_cases hc : (if a.store.ns.scratchOn then a.store.ns.scr.sizeOf v
        else a.store.ns.pers.sizeOf v) < Idx.idxCap
    · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind] at hr
      cases hr; exact EStore.internName_ext _ _
    · simp only [hc, ↓reduceIte] at hr
      cases hr

/-- **`findProj?` keeps every level-list readback** (it only interns the table's name). -/
theorem findProj?_lss (fe : IFEnv) (T : NIdx) (i : Nat) (a a' : AState) (o : Option IProjEntry)
    (hr : (fe.findProj? T i).run a = .ok (o, a')) (h : LsIdx) (ls : List ConLeche.Level)
    (hd : denoteLs a.store.lss h = some ls) : denoteLs a'.store.lss h = some ls := by
  simp only [IFEnv.findProj?, projTableName, StateT.run_bind] at hr
  cases h1 : (internNNode (.str T "projTable")).run a with
  | error e => rw [h1] at hr; cases hr
  | ok x =>
  rw [h1] at hr
  simp only [except_ok_bind] at hr
  cases h2 : (internNNode (.num x.1 0)).run x.2 with
  | error e => rw [h2] at hr; cases hr
  | ok y =>
  rw [h2] at hr
  simp only [except_ok_bind] at hr
  have e1 := internNNode_ext' _ _ _ _ h1
  have e2 := internNNode_ext' _ _ _ _ h2
  have hy : a' = y.2 := by
    split at hr <;> (cases hr; rfl)
  rw [hy]
  exact e2.lss.lst h ls (e1.lss.lst h ls hd)

/-- **A hit is below the table's field count.** -/
theorem findProj?_lt (fe : IFEnv) (T : NIdx) (i : Nat) (a a' : AState) (e : IProjEntry)
    (hr : (fe.findProj? T i).run a = .ok (some e, a')) : i < e.numFields := by
  simp only [IFEnv.findProj?, StateT.run_bind] at hr
  cases h1 : (projTableName T).run a with
  | error e => rw [h1] at hr; cases hr
  | ok x =>
  rw [h1] at hr
  simp only [except_ok_bind] at hr
  split at hr
  · rename_i tbl _
    by_cases hi : i < tbl.numFields
    · simp only [hi, ↓reduceIte] at hr
      cases hr; exact hi
    · simp only [hi, ↓reduceIte] at hr
      cases hr
  · cases hr

/-! ## The model of `infer_proj` -/

section ipK
variable (p : Prog) (n : Nat) (mode io vis d sn i pe : Word)

/-- After `find_proj`: a hit's table record, then `infer_proj_at`. -/
def ipK4 (te cT cu : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else call1W p n "infer_proj_at" [vis, sn, i, pe, te, cT, cu, r.tail.headD 0] m

/-- At the head `hh` of the subject's type: a constant past the view checks, its name and levels
read, then `find_proj`. -/
def ipHead (te hh : Word) (m : Mem) : Option (Word × Mem) :=
  if hh >>> 28 ≠ 3 then none
  else if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (18 + tierW hh) ≤ idxW hh then none
  else ipK4 p n vis sn i pe te (rdW (m.arr64 CREC) (idxW hh * 4 + tierW hh * 2))
    (rdW (m.arr64 CREC) (idxW hh * 4 + tierW hh * 2 + 1))
    (callW p n "find_proj" [vis, rdW (m.arr64 CREC) (idxW hh * 4 + tierW hh * 2), i] m)

/-- After `whnf`: the head. -/
def ipK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    match callW p n "get_app_fn" [r.headD 0] m with
    | none => none
    | some (r', m') => ipHead p n vis sn i pe (r.headD 0) (r'.headD 0) m'

/-- After the subject's `infer`: `whnf`. -/
def ipK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ipK2 p n vis sn i pe (callW p n "whnf" [mode, vis, d, r.headD 0] m)

/-- The subject's type at the grade `io`. -/
def ipFirst (m : Mem) : Option (List Word × Mem) :=
  if io ≠ 0 then callW p n "infer_io" [mode, vis, d, pe] m else callW p n "infer" [mode, vis, d, pe] m

end ipK

/-- **The model of `infer_proj`.** -/
def ipW (p : Prog) (n : Nat) (m : Mem) (mode io vis d sn i pe : Word) : Option (Word × Mem) :=
  ipK1 p n mode vis d sn i pe (ipFirst p n mode io vis d pe m)

theorem inferProj_spec (p : Prog) (hp : InferProjProg p) (n : Nat) (s₀ : St)
    (mode io vis d sn i pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_proj" [mode, io, vis, d, sn, i, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ ipW p n s₀.mem mode io vis d sn i pe = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ip]
  simp only [callFn, inferProjL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "infer_io", callW_spec p n "infer", callW_spec p n "whnf",
      callW_spec p n "get_app_fn", callW_spec p n "find_proj", callW_spec p n "infer_proj_at"] <;>
  simp_all [ipW, ipFirst, ipK1, ipK2, ipHead, ipK4, call1W, tierW, idxW, Cmp.eval, LocEq, BinOp.eval,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, CTL, CREC, w_lt_false, w_le_false]

end L.Arena
