module

public import ConAgua.Arena.DeclStep
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclStep

@[expose] public section

/-!
# The `And` pin's inductive arm, part 2b: the word models of `ind_block_to_erec`

`dind_copy(d, s, l)` (`dindCopyW`), `ind_rec_copy(s)` (`ircW`), `ind_copy_go(o, bo, bl)`
(`icgW`), `ind_block_to_erec(i)` (`ibeW`), each with its spec (`…_specW`), generated
(`l_model`). What they leave is `DeclAndPinIndCopy2.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP)
open L.Front.Ind (DIND)
open L.Ind (erAllocW erecAlloc erecAlloc_specW erecPut erecPutMem erecPut_specW)

/-! ## The models -/

l_model dindCopy_specW (p : Prog) (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "dind_copy" = some dindCopy)
  fns [hp ↦ dindCopyW void]
  specs [erecPut_specW p hpu n]
  grind [arena_grind, ind_grind]

l_model indRecCopy_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hd : p.lookup "dind_copy" = some dindCopy) (hp : p.lookup "ind_rec_copy" = some indRecCopy)
  fns [hp ↦ ircW]
  specs [erecAlloc_specW p ha n, erecPut_specW p hpu n, dindCopy_specW p hpu hd n]
  grind [arena_grind, ind_grind]

l_model indCopyGo_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hd : p.lookup "dind_copy" = some dindCopy) (hr : p.lookup "ind_rec_copy" = some indRecCopy)
    (hp : p.lookup "ind_copy_go" = some indCopyGo)
  fns [hp ↦ icgW void]
  specs [erecPut_specW p hpu n, indRecCopy_specW p ha hpu hd hr n]
  grind [arena_grind, ind_grind]

l_model indBlockToErec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hd : p.lookup "dind_copy" = some dindCopy) (hr : p.lookup "ind_rec_copy" = some indRecCopy)
    (hg : p.lookup "ind_copy_go" = some indCopyGo)
    (hp : p.lookup "ind_block_to_erec" = some indBlockToErec)
  fns [hp ↦ ibeW list]
  specs [erecAlloc_specW p ha n, indCopyGo_specW p ha hpu hd hr hg n]
  grind [arena_grind, ind_grind]

end L.Arena
