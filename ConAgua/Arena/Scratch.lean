module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.CoreCaches
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

* `scratch_reset(f)`: `B += 2^32`, the scratch flag `CTL[1] := f`, and the 19 tier-1 node
  counts `CTL[ca + 1] := 0`. Every old scratch slot holds at most `B + 2^27` and reads free
  against the new base; no slot is written. Once every `2^30` resets (`B ≥ 2^62`) the base wraps:
  the 19 scratch slot tables are zeroed and `B` restarts at `0` (con-ron's `clear` at
  `EPOCH_MAX`), so `B < 2^62 + 2^32` always holds.
* `scratch_enter()`: `scratch_reset(1)` and the four walk memos' `clear` (epoch bumps).
* `scratch_drop()`: `flush_caches()` (`CoreCaches.lean`, the per-declaration caches), then
  `scratch_reset(0)`.

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

/-- `scratch_reset`'s pool tops (lane tierpool): leaving tier 0 saves its top in `PT0[0]`; the
new top is the scratch tier's base `2^40` when `f ≠ 0`, else the saved tier-0 top. -/
def resetTopMem (m : Mem) (f : Word) : Mem :=
  let m₁ := if m.top >>> 40 = 0 then m.set64 PT0 0 m.top else m
  m₁.set64 CTL 0 (if f ≠ 0 then 1099511627776 else m₁.ptop0)

/-- The memory after `scratch_reset(f)`'s epoch, flag and count stores. -/
def resetMemA (m : Mem) (f : Word) : Mem :=
  ((((((((((((((((((((m.set64 CTL 62 (rdW (m.arr64 CTL) 62 + 4294967296)).set64 CTL 1 f).set64 CTL 3 0).set64 CTL 5 0).set64 CTL 7 0).set64 CTL 9 0).set64 CTL 11 0).set64 CTL 13 0).set64 CTL 15 0).set64 CTL 17 0).set64 CTL 19 0).set64 CTL 21 0).set64 CTL 23 0).set64 CTL 27 0).set64 CTL 29 0).set64 CTL 31 0).set64 CTL 33 0).set64 CTL 35 0).set64 CTL 37 0).set64 CTL 39 0).set64 CTL 41 0

/-- The memory after `scratch_reset(f)`: the counts' and the tops' stores. -/
def resetMem (m : Mem) (f : Word) : Mem := resetTopMem (resetMemA m f) f

theorem resetMemA_eq (m : Mem) (f : Word) :
    resetMemA m f =
      zeroCtl ((m.set64 CTL SCB (rdW (m.arr64 CTL) SCB + 4294967296)).set64 CTL 1 f) scratchCnts :=
  rfl

/-! ## The slot base's wrap (lane epochwrap; con-ron's `HashMap2::clear` at `EPOCH_MAX`)

The slot base `B` rises by `2^32` per reset. At `B ≥ 2^62` (`SCBLIM`, after `2^30` resets)
`scratch_reset` vacates the scratch tier's slot tables, zeroing the `2 n` words of each of the 19
tables' tier-1 table (the growth's zero loop `kzeroLs`), and restarts `B` at `0`, as con-ron's
`clear` vacates its slots and restarts the epoch at `1` when the epoch reaches `EPOCH_MAX`. Only
the slot tables carry `B`: the memos have their own stamps. -/

/-- The 19 tables' slot arrays (tier 0's ids; the wrap vacates tier 1, `sa + 256`). -/
def scrSlots : List ArrId := [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 26, 28, 30, 32, 34, 36, 38, 40]

/-- The scratch tables' slot arrays (tier 1, `sa + 256`), which the wrap writes. -/
def slot1Arrs : List ArrId :=
  [259, 261, 263, 265, 267, 269, 271, 273, 275, 277, 279, 282, 284, 286, 288, 290, 292, 294, 296]

theorem slot1Arrs_eq : slot1Arrs = scrSlots.map (tierA · 1) := rfl

/-- The arrays `scratch_reset` writes: the saved tier-0 top `PT0` and, at the wrap, the scratch
tables' slot arrays. -/
def scrArrs : List ArrId := PT0 :: slot1Arrs

/-- The slot base's limit: at `B ≥ 2^62` the scratch tables are vacated and `B` restarts. -/
def SCBLIM : Word := 4611686018427387904

/-- Vacate tier 1 of slot array `sa`: the `2 n` words of its table (`n` slots from word `2 + o`),
`n / 4` steps of the growth's zero loop. Template variables as `kgrowB`. -/
def vacB (sa : ArrId) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  t := 1;
  x := sa⟨t⟩[1] + 2;
  e := (sa⟨t⟩[0] + ⟪SN0⟫) >> 2;
  ⟪kzeroLs sa⟫
}

/-- Vacate tier 1 of the slot arrays `l`, in order. -/
def vacS : List ArrId → Stmt
  | [] => .skip
  | a :: as => .seq (vacB a) (vacS as)

/-- The wrap's block in `scratch_reset`: its variables past the parameter `f`. -/
def scrVac : Stmt := mapS (· + 1) (vacS scrSlots)

/-- The memory after vacating tier 1 of slot array `sa`. -/
def vacW (sa : ArrId) (m : Mem) : Mem :=
  kzeroW (tierA sa 1) (koW sa m 1 + 2) (knW sa m 1 >>> 2).toNat m

/-- The memory after vacating tier 1 of the slot arrays `l`, in order. -/
def vacL : List ArrId → Mem → Mem
  | [], m => m
  | a :: as, m => vacL as (vacW a m)

/-- The memory `scratch_reset` starts its stores from: at the limit the scratch tables vacated
and the slot base `0`, else as it is. -/
def preMem (m : Mem) : Mem :=
  if SCBLIM ≤ rdW (m.arr64 CTL) SCB then (vacL scrSlots m).set64 CTL SCB 0 else m

theorem vacW_arr (sa : ArrId) (m : Mem) (b : ArrId) (hb : b ≠ tierA sa 1) :
    (vacW sa m).arr64 b = m.arr64 b := (kzeroW_fr _ _ _ m).1 b hb

theorem vacL_arr : ∀ (l : List ArrId) (m : Mem) (b : ArrId), (∀ sa ∈ l, b ≠ tierA sa 1) →
    (vacL l m).arr64 b = m.arr64 b
  | [], _, _, _ => rfl
  | a :: as, m, b, hb => by
    simp only [vacL]
    rw [vacL_arr as _ b (fun sa h => hb sa (List.mem_cons_of_mem _ h)),
      vacW_arr a m b (hb a List.mem_cons_self)]

theorem rdW_set64_self (m : Mem) (a : ArrId) (k v : Word) (h : k.toNat < (m.arr64 a).size) :
    rdW ((m.set64 a k v).arr64 a) k = v := by
  simp only [Mem.arr64_set64_same, rdW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [h]

theorem vacL_ctl (m : Mem) : (vacL scrSlots m).arr64 CTL = m.arr64 CTL :=
  vacL_arr _ _ _ (by decide)

theorem vacL_pt0 (m : Mem) : (vacL scrSlots m).arr64 PT0 = m.arr64 PT0 :=
  vacL_arr _ _ _ (by decide)

theorem vacL_words : ∀ (l : List ArrId) (m : Mem), (vacL l m).words.size = m.words.size
  | [], _ => rfl
  | a :: as, m => by simp only [vacL]; rw [vacL_words as]; exact (kzeroW_fr _ _ _ m).2.2

/-- `scratch_reset`'s head: at the limit the wrap (the scratch tables vacated, the slot base
restarted at `0`). -/
def scrHead : Stmt := lblk (f, b, t) {
  b := CTL.u64[62];
  if b >= ⟪SCBLIM⟫ { ⟪scrVac⟫; CTL.u64[62] := 0 }
}

/-- `scratch_reset`'s tail: the base raised, the flag, the counts, the tops. -/
def scrTail : Stmt := lblk (f, b, t) {
  b := CTL.u64[62];
  CTL.u64[62] := b + 4294967296;
  CTL.u64[1] := f;
  CTL.u64[3] := 0; CTL.u64[5] := 0; CTL.u64[7] := 0; CTL.u64[9] := 0; CTL.u64[11] := 0;
  CTL.u64[13] := 0; CTL.u64[15] := 0; CTL.u64[17] := 0; CTL.u64[19] := 0; CTL.u64[21] := 0;
  CTL.u64[23] := 0; CTL.u64[27] := 0; CTL.u64[29] := 0; CTL.u64[31] := 0; CTL.u64[33] := 0;
  CTL.u64[35] := 0; CTL.u64[37] := 0; CTL.u64[39] := 0; CTL.u64[41] := 0;
  t := CTL.u64[0];
  if t >> 40 == 0 { PT0.u64[0] := t };
  if f != 0 { CTL.u64[0] := 1099511627776 } else { CTL.u64[0] := PT0.u64[0] };
  return 0
}

/-- con-ron: ConRon/Arena/Store.lean:1413-1416 ConRon.Arena.EStore.enableScratch
con-ron: ConRon/Arena/Store.lean:1418-1422 ConRon.Arena.EStore.dropScratch -/
@[l_impl ConRon.Arena.EStore.enableScratch ConRon.Arena.EStore.dropScratch]
def scratchReset : FunDecl := { nparams := 1, nlocals := 16, body := lblk (f, b, t) {
  ⟪scrHead⟫;
  ⟪scrTail⟫
} }

/-! ### The wrap's block -/

theorem vacZ_step (p : Prog) (sa : ArrId) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (· + 1) (kzeroLs sa))
    ⦃fun r s' => r = .normal ∧ Keep2 8 9 s₀ s' ∧
      s'.mem = kzeroW (tierA sa (s₀.loc 1)) (s₀.loc 8) (s₀.loc 9).toNat s₀.mem; ⊤⦄ :=
  Triple.step_exec (kzeroLs_spec p sa (· + 1) 1 8 9 rfl rfl rfl (by decide) (by decide)
    (by decide) (n + 1) s₀)

theorem vacB_spec (p : Prog) (sa : ArrId) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (· + 1) (vacB sa))
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.mem = vacW sa s₀.mem; ⊤⦄ := by
  unfold vacB
  simp only [mapS, mapE]
  vcgen [step, evalE_spec, setLoc, vacZ_step p sa n]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, rd64_rdWC, ↓reduceIte, Keep2] at *)
  all_goals grind [vacW, knW, koW, SN0]

theorem vacS_spec (p : Prog) (n : Nat) :
    ∀ (l : List ArrId) (s₀ : St), ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (· + 1) (vacS l))
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.mem = vacL l s₀.mem; ⊤⦄
  | [], s₀ => by simp only [vacS, mapS]; vcgen [step] <;> simp_all [vacL]
  | a :: as, s₀ => by
    simp only [vacS, mapS]
    refine triple_seq _ (vacB_spec p a n s₀) (fun s₁ h₁ => ?_)
    obtain ⟨l1, m1⟩ := h₁
    refine triple_weaken (vacS_spec p n as s₁) (fun r s ⟨hr, l2, m2⟩ => ⟨hr, ?_, ?_⟩)
    · rw [l2, l1]
    · rw [m2, m1]; rfl

theorem scrVac_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) scrVac
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.mem = vacL scrSlots s₀.mem; ⊤⦄ :=
  vacS_spec p n scrSlots s₀

section reset
variable (p : Prog) (hp : p.lookup "scratch_reset" = some scratchReset)

theorem scrHead_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) scrHead
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧
      (rdW (s'.mem.arr64 CTL) SCB).toNat < 2 ^ 62 ∧ s'.mem = preMem s₀.mem; ⊤⦄ := by
  unfold scrHead
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, setLoc, ld64, st64, scrVac_spec p n] <;>
    finish [preMem, SCBLIM, vacL_ctl, rdW_set64_self]

theorem scrTail_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) scrTail
    ⦃fun _ s' => SCB.toNat < (s₀.mem.arr64 CTL).size ∧
      ((resetMemA s₀.mem (s₀.loc 0)).top >>> 40 = 0 ∨ s₀.loc 0 = 0 →
        0 < ((resetMemA s₀.mem (s₀.loc 0)).arr64 PT0).size) ∧
      s'.mem = resetMem s₀.mem (s₀.loc 0); ⊤⦄ := by
  unfold scrTail
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
    finish [resetMem, resetMemA, resetTopMem, zeroCtl, scratchCnts]

include hp in
theorem scratchReset_spec (n : Nat) (s₀ : St) (f : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_reset" [f]
    ⦃fun _ s' => LocEq s' s₀ ∧ (rdW ((preMem s₀.mem).arr64 CTL) SCB).toNat < 2 ^ 62 ∧
      SCB.toNat < ((preMem s₀.mem).arr64 CTL).size ∧
      ((resetMemA (preMem s₀.mem) f).top >>> 40 = 0 ∨ f = 0 →
        0 < ((resetMemA (preMem s₀.mem) f).arr64 PT0).size) ∧
      s'.mem = resetMem (preMem s₀.mem) f; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, scratchReset, L.Notation.blk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, scrHead_spec p n, scrTail_spec p n]
    all_goals (simp only [Locals.init_cons_zero] at *)
    all_goals grind [LocEq]

end reset

/-- con-ron: ConRon/Arena/Core.lean:3692-3699 ConRon.Arena.enterScratch -/
@[l_impl ConRon.Arena.enterScratch]
def scratchEnter : FunDecl := lfn () locals (r) {
  r := call scratch_reset(1);
  r := call bm_clear();
  r := call lf_clear();
  r := call if_clear();
  r := call fm_clear();
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:3682-3690 ConRon.Arena.dropScratch -/
@[l_impl ConRon.Arena.dropScratch]
def scratchDrop : FunDecl := lfn () locals (r) {
  r := call flush_caches();
  r := call scratch_reset(0);
  return 0
}

/-- The memory after `scratch_enter()`. -/
def enterMem (m : Mem) : Mem :=
  mclearG frSch (mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1))))

/-- The lifecycle functions, with the four memo clears they call. -/
def scratchProg : Prog :=
  [("scratch_reset", scratchReset), ("scratch_enter", scratchEnter), ("scratch_drop", scratchDrop),
   ("bm_clear", memoClearG bmSch), ("lf_clear", memoClearG lfSch), ("if_clear", memoClearG imSch),
   ("fm_clear", memoClearG frSch)] ++ cacheProg

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
    ⦃fun _ s' => LocEq s' s₀ ∧ (rdW ((preMem s₀.mem).arr64 CTL) SCB).toNat < 2 ^ 62 ∧
      SCB.toNat < ((preMem s₀.mem).arr64 CTL).size ∧
      rdW ((resetMem (preMem s₀.mem) 1).arr64 CTL) bmSch.cs + 2 ≠ 0 ∧
      rdW ((mclearG bmSch (resetMem (preMem s₀.mem) 1)).arr64 CTL) lfSch.cs + 2 ≠ 0 ∧
      rdW ((mclearG lfSch (mclearG bmSch (resetMem (preMem s₀.mem) 1))).arr64 CTL) imSch.cs + 2 ≠ 0 ∧
      rdW ((mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem (preMem s₀.mem) 1)))).arr64 CTL)
        frSch.cs + 2 ≠ 0 ∧
      ((resetMemA (preMem s₀.mem) 1).top >>> 40 = 0 ∨ (1 : Word) = 0 →
        0 < ((resetMemA (preMem s₀.mem) 1).arr64 PT0).size) ∧
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
  (hr : p.lookup "scratch_reset" = some scratchReset) (hfl : FlushProg p)

include hp hr hfl in
theorem scratchDrop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧
      (rdW ((preMem (flushMem s₀.mem)).arr64 CTL) SCB).toNat < 2 ^ 62 ∧
      SCB.toNat < ((preMem (flushMem s₀.mem)).arr64 CTL).size ∧
      ((resetMemA (preMem (flushMem s₀.mem)) 0).top >>> 40 = 0 ∨ (0 : Word) = 0 →
        0 < ((resetMemA (preMem (flushMem s₀.mem)) 0).arr64 PT0).size) ∧
      s'.mem = resetMem (preMem (flushMem s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, scratchDrop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, flushCaches_spec p hfl n,
        scratchReset_spec p hr n] <;> finish

end drop

end L.Arena
