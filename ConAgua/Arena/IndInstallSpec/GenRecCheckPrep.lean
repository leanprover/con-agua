import ConAgua.Arena.RecGen
import ConAgua.Arena.WhnfBase
import ConAgua.L.Records
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# GenRecCheckPrep

`grpG1`, `grpG2`, `grpG2b`, `grpG3`, `grpPMem`: the memory after `gen_rec_check_prep`'s record stores
(as its unified model writes them, `grpGs_eq` in `GpbWSimF`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The `ClassGen` record's words 0‥4 (`g` the allocation, the read of `p` at the memory of the
store). -/
def grpG1 (m : Mem) (g pp pO pL m2o m2l : Word) : Mem :=
  ((((m.set64 IW g (rdW (m.arr64 IW) (pp + 4))).set64 IW (g + 1) pO).set64 IW (g + 2) pL).set64 IW
    (g + 3) m2o).set64 IW (g + 4) m2l

/-- Words 5‥7 (the read of `rd` at the memory of the store). -/
def grpG2 (m : Mem) (g fo fl rd : Word) : Mem :=
  ((m.set64 IW (g + 5) fo).set64 IW (g + 6) fl).set64 IW (g + 7)
    (rdW (((m.set64 IW (g + 5) fo).set64 IW (g + 6) fl).arr64 IW) rd)

/-- Words 8‥9. -/
def grpG2b (m : Mem) (g rd co : Word) : Mem :=
  (m.set64 IW (g + 8) (rdW (m.arr64 IW) (rd + 1))).set64 IW (g + 9) co

/-- Words 10‥13. -/
def grpG3 (m : Mem) (g cl el : Word) : Mem :=
  (((m.set64 IW (g + 10) cl).set64 IW (g + 11) el).set64 IW (g + 12) 0).set64 IW (g + 13) 0

/-- The prefix's words stored. -/
def grpPMem (m : Mem) (g o l : Word) : Mem := (m.set64 IW (g + 12) o).set64 IW (g + 13) l

end L.Ind
