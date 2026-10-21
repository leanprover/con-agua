module

public import ConAgua.Arena.MemoLib
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The scratch tier's lifecycle in L: open and drop without zeroing a slot

con-ron's arena brackets every declaration check with `enterScratch` (open the scratch tier of all
four stores, clear the walk memos) and `dropScratch` (`flushCaches`, then close the scratch tier
and truncate it). In L the 19 tables keep their scratch tier as tier 1 of their slot and record
arrays (`StoreLib.lean`); a slot of tier 1 holds `B + i + 1` for node `i`, with the **slot base**
`B = CTL[62]` (`SCB`), and reads free at or below `B` (`slotV`). So emptying the scratch tier of
every table is O(1) per table:

* `scratch_reset(f)`: `B += 2^32` (aborting at `B ≥ 2^62`, so `B < 2^63` always holds), the
  scratch flag `CTL[1] := f`, and the 19 tier-1 node counts `CTL[ca + 1] := 0`. Every old scratch
  slot holds at most `B + 2^27` and reads free against the new base; no slot is written.
* `scratch_enter()`: `scratch_reset(1)` and the four walk memos' `clear` (epoch bumps).
* `scratch_drop()`: `scratch_reset(0)` (the caches' `flushCaches` belongs to `CoreR`, a stub).

The refinement (`enterScratch`/`dropScratch` under `ArenaD`) is `ScratchRefine.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The 19 tables' tier-1 node counts (`CTL[ca + 1]`). -/
def scratchCnts : List Word :=
  [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 27, 29, 31, 33, 35, 37, 39, 41]

/-- Zero the `CTL` words `xs`, in order. -/
def zeroCtl (m : Mem) : List Word → Mem
  | [] => m
  | x :: xs => zeroCtl (m.set64 CTL x 0) xs

/-- The memory after `scratch_reset(f)`, store by store. -/
def resetMem (m : Mem) (f : Word) : Mem :=
  (((((((((((((((((((((m.set64 CTL 62 (rdW (m.arr64 CTL) 62 + 4294967296)).set64 CTL 1 f).set64 CTL 3 0).set64 CTL 5 0).set64 CTL 7 0).set64 CTL 9 0).set64 CTL 11 0).set64 CTL 13 0).set64 CTL 15 0).set64 CTL 17 0).set64 CTL 19 0).set64 CTL 21 0).set64 CTL 23 0).set64 CTL 27 0).set64 CTL 29 0).set64 CTL 31 0).set64 CTL 33 0).set64 CTL 35 0).set64 CTL 37 0).set64 CTL 39 0).set64 CTL 41 0)

theorem resetMem_eq (m : Mem) (f : Word) :
    resetMem m f =
      zeroCtl ((m.set64 CTL SCB (rdW (m.arr64 CTL) SCB + 4294967296)).set64 CTL 1 f) scratchCnts :=
  rfl

@[l_impl ConRon.Arena.EStore.enableScratch ConRon.Arena.EStore.dropScratch]
def scratchReset : FunDecl := lfn (f) locals (b) {
  b := CTL.u64[62];
  if b >= 4611686018427387904 { abort };
  CTL.u64[62] := b + 4294967296;
  CTL.u64[1] := f;
  CTL.u64[3] := 0; CTL.u64[5] := 0; CTL.u64[7] := 0; CTL.u64[9] := 0; CTL.u64[11] := 0;
  CTL.u64[13] := 0; CTL.u64[15] := 0; CTL.u64[17] := 0; CTL.u64[19] := 0; CTL.u64[21] := 0;
  CTL.u64[23] := 0; CTL.u64[27] := 0; CTL.u64[29] := 0; CTL.u64[31] := 0; CTL.u64[33] := 0;
  CTL.u64[35] := 0; CTL.u64[37] := 0; CTL.u64[39] := 0; CTL.u64[41] := 0;
  return 0
}

section reset
variable (p : Prog) (hp : p.lookup "scratch_reset" = some scratchReset)

include hp in
theorem scratchReset_spec (n : Nat) (s₀ : St) (f : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_reset" [f]
    ⦃fun _ s' => LocEq s' s₀ ∧ (rdW (s₀.mem.arr64 CTL) SCB).toNat < 2 ^ 62 ∧
      SCB.toNat < (s₀.mem.arr64 CTL).size ∧ s'.mem = resetMem s₀.mem f; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, scratchReset]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [resetMem, zeroCtl, scratchCnts]

end reset

@[l_impl ConRon.Arena.enterScratch]
def scratchEnter : FunDecl := lfn () locals (r) {
  r := call scratch_reset(1);
  r := call bm_clear();
  r := call lf_clear();
  r := call if_clear();
  r := call fm_clear();
  return 0
}

@[l_impl ConRon.Arena.dropScratch]
def scratchDrop : FunDecl := lfn () locals (r) {
  r := call scratch_reset(0);
  return 0
}

/-- The memory after `scratch_enter()`. -/
def enterMem (m : Mem) : Mem :=
  mclearG frSch (mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem m 1))))

/-- The lifecycle functions, with the four memo clears they call. -/
def scratchProg : Prog :=
  [("scratch_reset", scratchReset), ("scratch_enter", scratchEnter), ("scratch_drop", scratchDrop),
   ("bm_clear", memoClearG bmSch), ("lf_clear", memoClearG lfSch), ("if_clear", memoClearG imSch),
   ("fm_clear", memoClearG frSch)]

section enter
variable (p : Prog) (hp : p.lookup "scratch_enter" = some scratchEnter)
  (hr : p.lookup "scratch_reset" = some scratchReset)
  (hb : p.lookup "bm_clear" = some (memoClearG bmSch))
  (hl : p.lookup "lf_clear" = some (memoClearG lfSch))
  (hi : p.lookup "if_clear" = some (memoClearG imSch))
  (hf : p.lookup "fm_clear" = some (memoClearG frSch))

include hp hr hb hl hi hf in
theorem scratchEnter_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ (rdW (s₀.mem.arr64 CTL) SCB).toNat < 2 ^ 62 ∧
      SCB.toNat < (s₀.mem.arr64 CTL).size ∧
      rdW ((resetMem s₀.mem 1).arr64 CTL) bmSch.cs + 2 ≠ 0 ∧
      rdW ((mclearG bmSch (resetMem s₀.mem 1)).arr64 CTL) lfSch.cs + 2 ≠ 0 ∧
      rdW ((mclearG lfSch (mclearG bmSch (resetMem s₀.mem 1))).arr64 CTL) imSch.cs + 2 ≠ 0 ∧
      rdW ((mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem s₀.mem 1)))).arr64 CTL)
        frSch.cs + 2 ≠ 0 ∧
      s'.mem = enterMem s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, scratchEnter]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, scratchReset_spec p hr n,
        memoClearG_spec bmSch p _ hb n, memoClearG_spec lfSch p _ hl n,
        memoClearG_spec imSch p _ hi n, memoClearG_spec frSch p _ hf n] <;>
      finish [enterMem]

end enter

section drop
variable (p : Prog) (hp : p.lookup "scratch_drop" = some scratchDrop)
  (hr : p.lookup "scratch_reset" = some scratchReset)

include hp hr in
theorem scratchDrop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ (rdW (s₀.mem.arr64 CTL) SCB).toNat < 2 ^ 62 ∧
      SCB.toNat < (s₀.mem.arr64 CTL).size ∧ s'.mem = resetMem s₀.mem 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, scratchDrop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, scratchReset_spec p hr n] <;> finish

end drop

end L.Arena
