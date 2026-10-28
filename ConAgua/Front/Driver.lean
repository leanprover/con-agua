module

meta import ConAgua.L.Semantics
public import ConAgua.Front.Preserve
public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
public import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# The whole-buffer driver: `front_run()`

`front_run()` is `front_init()` and then `front_line(i)` from `i = 0` while `i` is inside the
input, as con-ron's `parseBytes` runs `feedChunk` over a whole buffer and then `applyFinalLine` on
the tail: `0` when every line applied, else the number of the first line that did not scan (a
line `front_line` cannot apply aborts the run). A last line without a newline is applied by
`front_line` itself (its `next` is `0`), where `feedChunk` leaves it as the tail and
`applyFinalLine` applies it.

Its model and refinement, both outcomes, are `frontRunE` and `frontRun_ref`
(`ConAgua.Front.FrontRunRef`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front

open L.Arena (POOL)

def runLoop : Stmt := lblk (i, ok, nx, ln) {
  while i < len(IN0.u8) {
    (ok, nx) := call front_line(i);
    ln += 1;
    if ok == 0 { return ln };
    if nx == 0 { return 0 };
    if nx <= i { return ln };
    i := nx
  }
}

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:561-574 ConRon.Arena.Frontend.parseBytes -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:520-549 ConRon.Arena.Frontend.feedChunk
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:506-518 ConRon.Arena.Frontend.applyFinalLine
@[l_impl ConRon.Arena.Frontend.parseBytes ConRon.Arena.Frontend.feedChunk
  ConRon.Arena.Frontend.applyFinalLine]
def frontRun : FunDecl := lfn () locals (i, ok, nx, ln) {
  ok := call front_init();
  ⟪runLoop⟫;
  return 0
}

end L.Front
