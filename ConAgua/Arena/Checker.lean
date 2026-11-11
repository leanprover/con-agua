module

public import ConAgua.Arena.DeclCheckLoop
public import ConAgua.Arena.DeclAndPin
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.Arena.Scratch
import all ConAgua.Arena.CheckerL
public import ConAgua.Arena.DeclStepGo
public import ConAgua.Arena.DeclCanonEq

@[expose] public section

/-!
# The loop's program facts: `DeclCallees`, `BracketProg`

The twin's two-phase fold (`installFold`, `checkPendingList`) is gone: the records are checked as
jobs (`recordJob`, `checkJobList`; `Arena/Jobs.lean`) against the stream index's views
(`Arena/IndexBuild.lean`). What remains here are the program facts the jobs and the verdict side
share: the translated callees of `check_decl` (`DeclCallees`) and the per-record bracket
(`flush_caches`, `scratch_enter`, `scratch_drop`: `BracketProg`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- The translated callees of the loop (`Decl*.lean`), as program lookups. -/
structure DeclCallees (dn : NIdx → Option ConLeche.Name) (p : Prog) : Prop where
  and_pin_ok : p.lookup "and_pin_ok" = some andPinOkL
  /-- `check_value_group`'s text (its write set, `DeclCvg.lean`). -/
  cvg : CvgProg p
  /-- `install_step_go`'s body and `install_value`'s text (`DeclStepGo.lean`). -/
  istg : IstgProg p
  iv : IvProg p
  /-- `check_decl`, its arms and their texts (`DeclCheckLoop.lean`). -/
  cd : CheckDeclProg p
  /-- The name decoding is injective (the comparisons of constant records read `PropWhen`'s names
  through it); the top level's `dn` is the store's `denoteN`. -/
  dninj : L.Ind.DnInj dn

/-! ## The bracket: lane `whnf`'s `flush_caches`, `scratch_enter`, `scratch_drop`

They refine `flushCaches`/`enterScratch`/`dropScratch` under `CheckR` (`CoreRefine.lean`,
`ScratchRefine.lean`). -/

/-- The bracket's functions in a program. -/
structure BracketProg (p : Prog) : Prop where
  fl : FlushProg p
  se : p.lookup "scratch_enter" = some scratchEnter
  sd : p.lookup "scratch_drop" = some scratchDrop
  sr : p.lookup "scratch_reset" = some scratchReset
  bm : p.lookup "bm_clear" = some (memoClearG bmSch)
  lf : p.lookup "lf_clear" = some (memoClearG lfSch)
  im : p.lookup "if_clear" = some (memoClearG imSch)
  fm : p.lookup "fm_clear" = some (memoClearG frSch)

attribute [simp] L.Arena.except_ok_bind

end L.Arena
