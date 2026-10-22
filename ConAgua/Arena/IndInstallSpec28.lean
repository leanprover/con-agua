import ConAgua.Arena.IndInstallSpec27

/-!
# Refinements of `IndInstall`, part 28 (lane `indproofs3`, helper `tail`): `checkBlockPass`,
`checkBlockTail`, `checkBlock`, the record and the word models

* `decBPass fe m q`: the 19-word `BlockPass` record (`IndIface`'s layout) decoded at `fe` (the
  record's word 0 is the view of `env1`; the environment itself is the twin's, related by the stage
  relation at that view, not decoded). `OMono`, so a decoded record stays decoded as the pools grow.
* The word models of `check_block_pass(vis, p0, isRec)`, `check_block_tail(block.off, block.len, q)`
  and `check_block(vis, block.off, block.len, p0)` (every callee a `callW`, the record's writes as
  one memory `bpMem`), and their `vcgen` specs.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The `BlockPass` record -/

/-- **`BlockPass`**, `[env1, cvTas.off, cvTas.len, p, ctorsAs.off, ctorsAs.len, sortsss.off,
sortsss.len, kinds.off, kinds.len, nfs.off, nfs.len, params.off, params.len, rd, cls.off, cls.len,
tbl.off, tbl.len]`, at the environment `fe` (word 0 is its view). The element decoders are the
producers': `check_block_inds` (`decCVp`), `check_block_ctors` (`decCNS`, `decISS`),
`check_block_positivity` (kinds: a member's list of a constructor's list of field kinds; normal forms:
a member's list of handles), `block_nest_ctx` (handles), `check_block_classes` (`decCR`, `decTM`),
`nest_seeds` (`decNCN`). -/
def decBPass (fe : IFEnv) (m : Mem) (q : Nat) : Option BlockPass := do
  pure { env1 := fe,
         cvTas := ← decAt m (decPL m (decCVp m)) (q + 1),
         p := ⟨← decBS m (← iwN m (q + 3))⟩,
         ctorsAs := ← decAt m (decPL m (decCNS m)) (q + 4),
         sortsss := ← decAt m (decPL m (decISS m)) (q + 6),
         kinds := ← decAt m (decPL m (decLH m (decPL m (decLH m (decKL m))))) (q + 8),
         nfs := ← decAt m (decPL m (decLH m (decHL m))) (q + 10),
         params := ← decAt m (decHL m) (q + 12),
         rd := ← decCR m (← iwN m (q + 14)),
         cls := ← decAt m (decPL m (decTM m)) (q + 15),
         tbl := ← decAt m (decPL m (decNCN m)) (q + 17) }

theorem decBPass_mono (fe : IFEnv) (q : Nat) : OMono (fun m => decBPass fe m q) := by
  unfold decBPass decLH
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decHL
    | apply OMono.decCVp
    | apply OMono.decKL
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decBS_mono
    | apply decCNS_mono
    | apply decISS_mono
    | apply decCR_mono
    | apply decTM_mono
    | apply decNCN_mono
    | apply OMono.bind
    | intro _
    )

/-! ## `check_block_pass` -/

/-- The memory after the record's nineteen writes (`q` the allocation). -/
def bpMem (m : Mem) (q fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) : Mem :=
  ((((((((((((((((((m.set64 IW q fe1).set64 IW (q + 1) cO).set64 IW (q + 2) cL).set64 IW (q + 3) p1
    ).set64 IW (q + 4) aO).set64 IW (q + 5) aL).set64 IW (q + 6) sO).set64 IW (q + 7) sL
    ).set64 IW (q + 8) kO).set64 IW (q + 9) kL).set64 IW (q + 10) nO).set64 IW (q + 11) nL
    ).set64 IW (q + 12) pO).set64 IW (q + 13) pL).set64 IW (q + 14) rd).set64 IW (q + 15) mO
    ).set64 IW (q + 16) mL).set64 IW (q + 17) tO).set64 IW (q + 18) tL

/-- After the allocation: the record. -/
def icpK9 (r1 r3 r5 r6 : List Word) (pO pL tO tL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => some ([rq.headD 0], bpMem m (rq.headD 0) (r1.headD 0) (r1.tail.headD 0)
      (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) (r3.headD 0) (r3.tail.headD 0)
      (r3.tail.tail.headD 0) (r3.tail.tail.tail.headD 0) (r6.headD 0) (r6.tail.headD 0)
      (r6.tail.tail.headD 0) (r6.tail.tail.tail.headD 0) pO pL (r5.headD 0) (r5.tail.headD 0)
      (r5.tail.tail.headD 0) tO tL)
/-- After `nest_seeds`: the allocation. -/
def icpK8 (p : Prog) (n : Nat) (r1 r3 r4 r5 r6 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m) => icpK9 r1 r3 r5 r6 (rdW (m.arr64 IW) (r4.headD 0 + 7)) (rdW (m.arr64 IW) (r4.headD 0 + 8))
      (rdW (m.arr64 IW) (r8.headD 0 + 4)) (rdW (m.arr64 IW) (r8.headD 0 + 5)) (callW p n "iw_alloc" [19] m)
/-- After `class_seeds`: `nest_seeds`. -/
def icpK7 (p : Prog) (n : Nat) (r1 r3 r4 r5 r6 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m) => icpK8 p n r1 r3 r4 r5 r6 (callW p n "nest_seeds"
      [r1.headD 0, r4.headD 0, r7.headD 0, r7.tail.headD 0, r6.tail.tail.tail.tail.headD 0] m)
/-- After `check_block_positivity`: `class_seeds`. -/
def icpK6 (p : Prog) (n : Nat) (r1 r3 r4 r5 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m) => icpK7 p n r1 r3 r4 r5 r6 (callW p n "class_seeds"
      [r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0] m)
/-- After `check_block_classes`: `check_block_positivity`. -/
def icpK5 (p : Prog) (n : Nat) (r1 r3 r4 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m) => icpK6 p n r1 r3 r4 r5 (callW p n "check_block_positivity"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0] m)
/-- After `block_nest_ctx`: `check_block_classes` (the parameters read off the context). -/
def icpK4 (p : Prog) (n : Nat) (r1 r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m) => icpK5 p n r1 r3 r4 (callW p n "check_block_classes"
      [r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r4.headD 0 + 7),
        rdW (m.arr64 IW) (r4.headD 0 + 8), r3.headD 0, r3.tail.headD 0] m)
/-- After `check_block_ctors`: `block_nest_ctx`. -/
def icpK3 (p : Prog) (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m) => icpK4 p n r1 r3 (callW p n "block_nest_ctx"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m)
/-- After the flush: `check_block_ctors` at the formers' environment (the members read off `p1`). -/
def icpK2 (p : Prog) (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => icpK3 p n r1 (callW p n "check_block_ctors"
      [r1.headD 0, r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0),
        rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0 + 1), r1.tail.headD 0, r1.tail.tail.headD 0] m)
/-- After `check_block_inds`: the flush. -/
def icpK1 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => icpK2 p n r1 (callW p n "flush_caches" [] m)

/-- **The model of `check_block_pass(vis, p0, isRec)`** (body fuel `n`). -/
def icpW (p : Prog) (n : Nat) (m : Mem) (vis p0 isRec : Word) : Option (List Word × Mem) :=
  icpK1 p n (callW p n "check_block_inds" [vis, p0, isRec] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (r r1 r3 r4 r5 r6 r8 : List Word) (pO pL tO tL : Word)
theorem icpK9_some : icpK9 r1 r3 r5 r6 pO pL tO tL (some (r, m)) = some ([r.headD 0], bpMem m (r.headD 0)
      (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) (r3.headD 0)
      (r3.tail.headD 0) (r3.tail.tail.headD 0) (r3.tail.tail.tail.headD 0) (r6.headD 0) (r6.tail.headD 0)
      (r6.tail.tail.headD 0) (r6.tail.tail.tail.headD 0) pO pL (r5.headD 0) (r5.tail.headD 0)
      (r5.tail.tail.headD 0) tO tL) := rfl
theorem icpK8_some : icpK8 p n r1 r3 r4 r5 r6 (some (r, m)) =
    icpK9 r1 r3 r5 r6 (rdW (m.arr64 IW) (r4.headD 0 + 7)) (rdW (m.arr64 IW) (r4.headD 0 + 8))
      (rdW (m.arr64 IW) (r.headD 0 + 4)) (rdW (m.arr64 IW) (r.headD 0 + 5)) (callW p n "iw_alloc" [19] m) := rfl
theorem icpK7_some : icpK7 p n r1 r3 r4 r5 r6 (some (r, m)) = icpK8 p n r1 r3 r4 r5 r6 (callW p n "nest_seeds"
      [r1.headD 0, r4.headD 0, r.headD 0, r.tail.headD 0, r6.tail.tail.tail.tail.headD 0] m) := rfl
theorem icpK6_some : icpK6 p n r1 r3 r4 r5 (some (r, m)) = icpK7 p n r1 r3 r4 r5 r (callW p n "class_seeds"
      [r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0] m) := rfl
theorem icpK5_some : icpK5 p n r1 r3 r4 (some (r, m)) = icpK6 p n r1 r3 r4 r (callW p n "check_block_positivity"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0] m) := rfl
theorem icpK4_some : icpK4 p n r1 r3 (some (r, m)) = icpK5 p n r1 r3 r (callW p n "check_block_classes"
      [r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r.headD 0 + 7),
        rdW (m.arr64 IW) (r.headD 0 + 8), r3.headD 0, r3.tail.headD 0] m) := rfl
theorem icpK3_some : icpK3 p n r1 (some (r, m)) = icpK4 p n r1 r (callW p n "block_nest_ctx"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m) := rfl
theorem icpK2_some : icpK2 p n r1 (some (r, m)) = icpK3 p n r1 (callW p n "check_block_ctors"
      [r1.headD 0, r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0),
        rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0 + 1), r1.tail.headD 0, r1.tail.tail.headD 0] m) := rfl
theorem icpK1_some : icpK1 p n (some (r, m)) = icpK2 p n r (callW p n "flush_caches" [] m) := rfl
end arms
attribute [ind_grind] icpK9_some icpK8_some icpK7_some icpK6_some icpK5_some icpK4_some icpK3_some
  icpK2_some icpK1_some

set_option maxHeartbeats 4000000 in
theorem icp_spec (p : Prog) (hp : p.lookup "check_block_pass" = some checkBlockPass) (n : Nat) (s₀ : St)
    (vis p0 isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_pass" [vis, p0, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ icpW p n s₀.mem vis p0 isRec = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPass]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "check_block_inds", callW_spec p n "flush_caches", callW_spec p n "check_block_ctors",
      callW_spec p n "block_nest_ctx", callW_spec p n "check_block_classes",
      callW_spec p n "check_block_positivity", callW_spec p n "class_seeds", callW_spec p n "nest_seeds",
      callW_spec p n "iw_alloc"] <;>
    finish (gen := 40) (instances := 20000) [icpW, bpMem, rdW_eq]

end L.Ind
