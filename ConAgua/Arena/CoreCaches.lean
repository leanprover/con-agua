module

public import ConAgua.Arena.MemoLib
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The per-declaration caches in L (arrays 96‥106, `CTL` 96‥113, 116‥119)

con-ron's `Caches` (`Arena/CoreState.lean`) has fourteen tables. Eleven are in L, each a memo of the
library (`MemoLib.lean`, four words per slot, epoch stamps):

| array | schema | twin table | key words | value |
|---:|---|---|---|---|
| 96 | `wcSch` (`CTL` 96, 97) | `whnfCoreC` | `e`, `genW 0 g` | `EIdx` |
| 97 | `wkSch` (98, 99) | `whnfCoreCheapC` | `e`, `genW 0 g` | `EIdx` |
| 98 | `whSch` (100, 101) | `whnfC` | `e`, `genW 0 g` | `EIdx` |
| 99 | `inSch` (102, 103) | `inferC` | `e`, `genW 0 g` | `EIdx` |
| 100 | `ioSch` (104, 105) | `inferIOC` | `e`, `genW 0 g` | `EIdx` |
| 101 | `deSch` (106, 107) | `defeqC` | `a`, `genW b g` | `Bool` (`≠ 0`) |
| 102 | `ctSch` (108, 109) | `constTyC` | `n`, `us` | `EIdx` |
| 103 | `cvSch` (110, 111) | `constValC` | `n`, `us` | `EIdx` |
| 104 | `rrSch` (112, 113) | `ruleRhsC` | `rec`, `ctor ∣ us << 32` | `EIdx` |
| 105 | `lqSch` (116, 117) | `lvlEqC` | `u`, `v` | `Bool` (`≠ 0`) |
| 106 | `lsqSch` (118, 119) | `lvlsEqC` | `us`, `vs` | `Bool` (`≠ 0`) |

The first six are con-ron's **mode memos** (`ModeMemos`), of which the twin keeps two sets: the
plain tower's in the six fields of `Caches` and the eager tower's in `Caches.eagerMemos`
(con-ron #127; `enterEager`/`leaveEager` swap them around an eager comparison). In L each table is
one memo holding both sets: the second key word carries the **eager bit** of the knot's mode
(`genW k2 ((mode >> 1) & 1)`, `MemoBank.lean`'s codec), so a slot reads and writes its own set and
an eager comparison moves nothing.

The other three tables, `readLC`/`readNC`/`readLsC`, cache readbacks L never makes (L runs the
level algorithms on the handles, `LevelHeap.lean`), so L does no work they would save; the twin's
entries must still be readbacks (`CoreS.reads`, `WhnfBase.lean`), since the twin computes on them.

`flush_caches()` is con-ron's `flushCaches` (`Caches.empty`): the eleven `clear`s (epoch bumps).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The schemas -/

abbrev wcSch : MemoSch := ⟨96, 96⟩
abbrev wkSch : MemoSch := ⟨97, 98⟩
abbrev whSch : MemoSch := ⟨98, 100⟩
abbrev inSch : MemoSch := ⟨99, 102⟩
abbrev ioSch : MemoSch := ⟨100, 104⟩
abbrev deSch : MemoSch := ⟨101, 106⟩
abbrev ctSch : MemoSch := ⟨102, 108⟩
abbrev cvSch : MemoSch := ⟨103, 110⟩
abbrev rrSch : MemoSch := ⟨104, 112⟩
abbrev lqSch : MemoSch := ⟨105, 116⟩
abbrev lsqSch : MemoSch := ⟨106, 118⟩

/-! ## `flush_caches()` -/

/-- The eleven clears, in order. -/
def flushClears (m : Mem) : Mem :=
  mclearG lsqSch (mclearG lqSch (mclearG rrSch (mclearG cvSch (mclearG ctSch (mclearG deSch
    (mclearG ioSch (mclearG inSch (mclearG whSch (mclearG wkSch (mclearG wcSch m))))))))))

/-- The memory after `flush_caches()`. -/
def flushMem (m : Mem) : Mem := flushClears m

/-- con-ron: ConRon/Arena/Core.lean:3674-3680 ConRon.Arena.flushCaches -/
@[l_impl ConRon.Arena.flushCaches]
def flushCachesL : FunDecl := lfn () locals (r) {
  r := call wc_clear();
  r := call wk_clear();
  r := call wh_clear();
  r := call in_clear();
  r := call io_clear();
  r := call de_clear();
  r := call ct_clear();
  r := call cv_clear();
  r := call rr_clear();
  r := call lq_clear();
  r := call lsq_clear();
  return 0
}

/-- The cache functions: the eleven memos' `find`/`put`/`clear`, the flush. -/
def cacheProg : Prog :=
  [("wc_find", memoFindG wcSch), ("wc_put", memoPutG wcSch), ("wc_clear", memoClearG wcSch),
   ("wk_find", memoFindG wkSch), ("wk_put", memoPutG wkSch), ("wk_clear", memoClearG wkSch),
   ("wh_find", memoFindG whSch), ("wh_put", memoPutG whSch), ("wh_clear", memoClearG whSch),
   ("in_find", memoFindG inSch), ("in_put", memoPutG inSch), ("in_clear", memoClearG inSch),
   ("io_find", memoFindG ioSch), ("io_put", memoPutG ioSch), ("io_clear", memoClearG ioSch),
   ("de_find", memoFindG deSch), ("de_put", memoPutG deSch), ("de_clear", memoClearG deSch),
   ("ct_find", memoFindG ctSch), ("ct_put", memoPutG ctSch), ("ct_clear", memoClearG ctSch),
   ("cv_find", memoFindG cvSch), ("cv_put", memoPutG cvSch), ("cv_clear", memoClearG cvSch),
   ("rr_find", memoFindG rrSch), ("rr_put", memoPutG rrSch), ("rr_clear", memoClearG rrSch),
   ("lq_find", memoFindG lqSch), ("lq_put", memoPutG lqSch), ("lq_clear", memoClearG lqSch),
   ("lsq_find", memoFindG lsqSch), ("lsq_put", memoPutG lsqSch), ("lsq_clear", memoClearG lsqSch),
   ("flush_caches", flushCachesL)]

/-- What the flush's spec needs of a program. -/
structure FlushProg (p : Prog) : Prop where
  fl : p.lookup "flush_caches" = some flushCachesL
  wc : p.lookup "wc_clear" = some (memoClearG wcSch)
  wk : p.lookup "wk_clear" = some (memoClearG wkSch)
  wh : p.lookup "wh_clear" = some (memoClearG whSch)
  inf : p.lookup "in_clear" = some (memoClearG inSch)
  io : p.lookup "io_clear" = some (memoClearG ioSch)
  de : p.lookup "de_clear" = some (memoClearG deSch)
  ct : p.lookup "ct_clear" = some (memoClearG ctSch)
  cv : p.lookup "cv_clear" = some (memoClearG cvSch)
  rr : p.lookup "rr_clear" = some (memoClearG rrSch)
  lq : p.lookup "lq_clear" = some (memoClearG lqSch)
  lsq : p.lookup "lsq_clear" = some (memoClearG lsqSch)

/-- No stamp of the eleven memos is about to wrap (what the nine clears check). -/
def FlushOK (m : Mem) : Prop :=
  rdW (m.arr64 CTL) wcSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG wcSch m).arr64 CTL) wkSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG wkSch (mclearG wcSch m)).arr64 CTL) whSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG whSch (mclearG wkSch (mclearG wcSch m))).arr64 CTL) inSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG inSch (mclearG whSch (mclearG wkSch (mclearG wcSch m)))).arr64 CTL)
    ioSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG ioSch (mclearG inSch (mclearG whSch (mclearG wkSch (mclearG wcSch m))))).arr64
    CTL) deSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG deSch (mclearG ioSch (mclearG inSch (mclearG whSch (mclearG wkSch
    (mclearG wcSch m)))))).arr64 CTL) ctSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG ctSch (mclearG deSch (mclearG ioSch (mclearG inSch (mclearG whSch
    (mclearG wkSch (mclearG wcSch m))))))).arr64 CTL) cvSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG cvSch (mclearG ctSch (mclearG deSch (mclearG ioSch (mclearG inSch
    (mclearG whSch (mclearG wkSch (mclearG wcSch m)))))))).arr64 CTL) rrSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG rrSch (mclearG cvSch (mclearG ctSch (mclearG deSch (mclearG ioSch (mclearG inSch
    (mclearG whSch (mclearG wkSch (mclearG wcSch m))))))))).arr64 CTL) lqSch.cs + 2 ≠ 0 ∧
  rdW ((mclearG lqSch (mclearG rrSch (mclearG cvSch (mclearG ctSch (mclearG deSch (mclearG ioSch
    (mclearG inSch (mclearG whSch (mclearG wkSch (mclearG wcSch m)))))))))).arr64 CTL)
    lsqSch.cs + 2 ≠ 0

theorem flushCaches_spec (p : Prog) (hp : FlushProg p) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp.fl]
  simp only [callFn, flushCachesL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        memoClearG_spec wcSch p _ hp.wc n, memoClearG_spec wkSch p _ hp.wk n,
        memoClearG_spec whSch p _ hp.wh n, memoClearG_spec inSch p _ hp.inf n,
        memoClearG_spec ioSch p _ hp.io n, memoClearG_spec deSch p _ hp.de n,
        memoClearG_spec ctSch p _ hp.ct n, memoClearG_spec cvSch p _ hp.cv n,
        memoClearG_spec rrSch p _ hp.rr n, memoClearG_spec lqSch p _ hp.lq n,
        memoClearG_spec lsqSch p _ hp.lsq n] <;>
      finish [flushMem, flushClears, FlushOK]

end L.Arena
