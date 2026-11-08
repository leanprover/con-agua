module

public import ConAgua.Arena.DeclBase
import ConAgua.Census.Attr
public import ConAgua.Arena.Reasons

@[expose] public section

/-!
# The declaration loop's L functions: `install_fold_go`, `check_pending_go` and their steps

The L code of the twin's two-phase fold (`installFold`, `checkPendingList`); the refinements are in
`Arena/Checker.lean`. Kept apart from the proofs so that the assembled program
(`Checker/Prog.lean`) does not wait for them.
-/

namespace L.Arena

/-! ## Phase A's step: `install_step` -/

/-- `is_none(vis, v2, nt)`: `installStep`'s `none` arm (`isNoneT`; `nt` the tables list's length
before the step). -/
-- con-ron: ConRon/Arena/Checker.lean:157-214 ConRon.Arena.installStep
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.installStep` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.installStep]
def isNoneL : FunDecl := lfn (vis, v2, nt) locals (k, kt, z) {
  k := 0;
  if vis <= v2 { k := v2 - vis };
  kt := call tbl_grown(nt);
  z := call promote_new(k, kt, v2, 1);
  z := call scratch_drop();
  return 0
}

/-- `pend_push(g, i, v)`: append the pending check `(g, i, v)` to `PEND`. -/
-- con-ron: none — appends to the `PEND` array (the twin's `Array.push` on its pending list)
@[no_expose] def pendPushL : FunDecl := lfn (g, i, v) locals (c) {
  c := CTL.u64[130];
  if 4611686018427387904 <= c { abort };
  PEND.u64[3 * c] := g;
  PEND.u64[3 * c + 1] := i;
  PEND.u64[3 * c + 2] := v;
  CTL.u64[130] := c + 1;
  return 0
}

/-- `is_some(i, vis, v2, nt, g)`: `installStep`'s `some` arm (`isSomeT`); the pending check is
written right after `promote_vg` (where its record is known to decode), the twin pushes it at
the end (a value, so the order is invisible). -/
-- con-ron: ConRon/Arena/Checker.lean:157-214 ConRon.Arena.installStep
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.installStep` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.installStep]
def isSomeL : FunDecl := lfn (i, vis, v2, nt, g) locals (k, kt, z, g2) {
  k := 0;
  if vis <= v2 { k := v2 - vis };
  kt := call tbl_grown(nt);
  g2 := call promote_vg(g, v2);
  z := call pend_push(g2, i, vis);
  z := call promote_new(k, kt, v2, 0);
  z := call scratch_drop();
  return 0
}

/-- `install_step(i, vis)`: `installStep` (the tables list's length read first, the bracket,
`installStepGo`, then one of the arms). -/
-- con-ron: ConRon/Arena/Checker.lean:157-214 ConRon.Arena.installStep
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.installStep` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.installStep]
def installStepL : FunDecl := lfn (i, vis) locals (nt, v2, f, g, z) {
  nt := call tbl_cnt();
  z := call flush_caches();
  z := call scratch_enter();
  (v2, f, g) := call install_step_go(i, vis);
  if f == 0 { z := call is_none(vis, v2, nt) } else { z := call is_some(i, vis, v2, nt, g) };
  return v2
}

/-- `install_decl_step(i, vis)`: `installDeclStep` (the `And` pin, then the step; a rejected pin
or a failing step is an `abort`). -/
-- con-ron: ConRon/Arena/Checker.lean:216-243 ConRon.Arena.installDeclStep
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.installDeclStep` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.installDeclStep]
def installDeclStepL : FunDecl := lfn (i, vis) locals (ok, v) {
  ok := call and_pin_ok(i);
  if ok == 0 { fail L.Arena.R_AND_MUST_BE };
  v := call install_step(i, vis);
  return v
}

/-- `install_fold_go(i, cnt, vis)`: `installFold` over records `i`‥`cnt - 1`. -/
-- con-ron: ConRon/Arena/Checker.lean:245-256 ConRon.Arena.installFold
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.installFold` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.installFold]
def installFoldGoL : FunDecl := lfn (i, cnt, vis) locals (r) {
  if i == cnt { return vis };
  r := call install_fold_next(i, cnt, vis);
  return r
}

/-- `install_fold_next(i, cnt, vis)`: one step of `installFold` (`i < cnt`), then the rest. -/
-- con-ron: ConRon/Arena/Checker.lean:245-256 ConRon.Arena.installFold
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.installFold` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.installFold]
def installFoldNextL : FunDecl := lfn (i, cnt, vis) locals (v, r) {
  v := call install_decl_step(i, vis);
  r := call install_fold_go(i + 1, cnt, v);
  return r
}

/-- `check_pending(j, vis)`: `checkPending` on pending check `j`, the environment seen at its
recorded view. -/
-- con-ron: ConRon/Arena/Checker.lean:258-274 ConRon.Arena.checkPending
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.checkPending` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.checkPending]
def checkPendingL : FunDecl := lfn (j, vis) locals (g, v, z) {
  if 4611686018427387904 <= j { abort };
  z := call scratch_enter();
  g := PEND.u64[3 * j];
  v := PEND.u64[3 * j + 2];
  z := call check_value_group(v, g);
  z := call scratch_drop();
  return 0
}

/-- `check_pending_go(j, cnt, vis)`: `checkPendingList` over pending checks `j`‥`cnt - 1`. -/
-- con-ron: ConRon/Arena/Checker.lean:276-285 ConRon.Arena.checkPendingList
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.checkPendingList` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.checkPendingList]
def checkPendingGoL : FunDecl := lfn (j, cnt, vis) locals (z) {
  if j == cnt { return 0 };
  z := call check_pending_next(j, cnt, vis);
  return 0
}

/-- `check_pending_next(j, cnt, vis)`: one pending check (`j < cnt`), then the rest. -/
-- con-ron: ConRon/Arena/Checker.lean:276-285 ConRon.Arena.checkPendingList
-- con-ron: CHANGED since 97eead2d — `ConRon.Arena.checkPendingList` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.checkPendingList]
def checkPendingNextL : FunDecl := lfn (j, cnt, vis) locals (z) {
  if 4611686018427387904 <= j { abort };
  z := call check_pending(j, vis);
  z := call check_pending_go(j + 1, cnt, vis);
  return 0
}

end L.Arena
