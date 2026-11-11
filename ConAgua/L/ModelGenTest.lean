module

import ConAgua.Arena.LdRd
public import ConAgua.Arena.P32
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Front.Preserve
import ConAgua.L.For
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.L.ErrSpec
public import ConAgua.L.Notation

@[expose] public section

/-!
# Tests of `l_model` (`L/ModelGen.lean`)

Small functions over test arrays, one per feature: pool slices (`A⦃x⦄`, `⦃x⦄.tier/.idx/.base`),
`le64!`, `scan!`, `copy!` (words, tiered words, bytes), byte stores, sequential loops and nested
loops (a `break` and a `return` in the inner loop, the outer loop fused or not), a loop followed
by `abort` (fused only if it never exits normally), and `unified` mode through them. Each `l_model`
generates the models and proves their specs; the `example`s check the models' values.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.ModelGenTest

open L.Arena

/-- Test arrays: a tiered word array, a word array, a byte array. -/
abbrev TP : ArrId := 5
abbrev TW : ArrId := 6
abbrev TB : ArrId := 7

/-- Abort codes. -/
abbrev R7 : Word := 7
abbrev R8 : Word := 8

/-- The byte class of the decimal digits. -/
def digC : List UInt8 := (List.range 256).map fun i => if 48 ≤ i ∧ i ≤ 57 then 1 else 0

-- con-ron: none — an `l_model` test function
@[no_expose] def tPool : FunDecl := lfn (x) {
  return TP⦃x⦄ + ⦃x⦄.tier + ⦃x⦄.idx + ⦃x⦄.base
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tLe : FunDecl := lfn (i) {
  return le64!(TB.u8, i) + 1
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tScan : FunDecl := lfn (i, e) locals (j) {
  j := scan!(TB.u8, i, e, digC);
  return j + 1
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tCopy : FunDecl := lfn (d, s, k) {
  copy!(TW.u64, d, TP.u64⟨1⟩, s, k);
  copy!(TP.u64⟨0⟩, d + k, TB.u8, s, k);
  copy!(TW.u64, d, TW.u64, s + 1, 2);
  return TW.u64[d]
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tSt8 : FunDecl := lfn (i, v) {
  TB.u8[i] := v;
  TB.u8[i + 1] := v >> 8;
  return 0
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tSeq : FunDecl := lfn (n) locals (i, s) {
  i := 0;
  while i < n { s += 1; i += 1 };
  i := 0;
  while i < n { s += TW.u64[i]; i += 1 };
  return s
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tNest : FunDecl := lfn (n) locals (i, j, s) {
  i := 0;
  while i < n {
    j := 0;
    while j < i { s += TW.u64[j]; j += 1 };
    i += 1
  };
  return s
}

/-- A `break` and a `return` in the inner loop; the outer loop is fused (`return 99` after it). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tNestR : FunDecl := lfn (n) locals (i, j) {
  i := 0;
  while i < n {
    j := 0;
    while j < n {
      if TW.u64[j] == i { return j };
      if TW.u64[j] == 7 { break };
      j += 1
    };
    i += 1
  };
  return 99
}

/-- The outer loop not fused: code after it reads a local it assigns. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tNestR2 : FunDecl := lfn (n) locals (i, j, r) {
  i := 0;
  while i < n {
    j := 0;
    while j < n {
      if TW.u64[j] == i { return j + 100 };
      j += 1
    };
    TW.u64[i] := j;
    i += 1
  };
  r := i + 1;
  return r
}

/-- Packed 32-bit elements (lane p32): a store, then loads of it and of its neighbour. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tP32 : FunDecl := lfn (t, i, v) locals (x) {
  TP⟨t⟩.u32[i] := v;
  x := TP⟨t⟩.u32[i + 1];
  return TP⟨t⟩.u32[i] + x
}

l_model tP32_spec (p : Prog) (hp : p.lookup "t_p32" = some tP32)
  fns [hp ↦ tP32W]
  grind [arena_grind] extra [ld64_rd_spec, ld32_pcol_spec]

/-- The model reads the element it stored (truncated to 32 bits) back. -/
example (m : Mem) (t i v : Word) (r : Word) (m' : Mem)
    (h : tP32W m t i v = some (r, m')) (hb : (i / 2).toNat < (m.arr64 (tierA TP t)).size) :
    m' = m.set32 (tierA TP t) i v ∧
      r = v % 4294967296 + pcol (m.set32 (tierA TP t) i v) TP t (i + 1) := by
  simp only [tP32W] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  rw [pcol, p32Get_set32, ite_eq_left ⟨rfl, rfl, hb⟩]

l_model tPool_spec (p : Prog) (hp : p.lookup "t_pool" = some tPool)
  fns [hp ↦ tPoolW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tLe_spec (p : Prog) (hp : p.lookup "t_le" = some tLe)
  fns [hp ↦ tLeW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tScan_spec (p : Prog) (hp : p.lookup "t_scan" = some tScan)
  fns [hp ↦ tScanW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tCopy_spec (p : Prog) (hp : p.lookup "t_copy" = some tCopy)
  fns [hp ↦ tCopyW]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tSt8_spec (p : Prog) (hp : p.lookup "t_st8" = some tSt8)
  fns [hp ↦ tSt8W]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tSeq_spec (p : Prog) (hp : p.lookup "t_seq" = some tSeq)
  fns [hp ↦ tSeqW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tNest_spec (p : Prog) (hp : p.lookup "t_nest" = some tNest)
  fns [hp ↦ tNestW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tNestR_spec (p : Prog) (hp : p.lookup "t_nest_r" = some tNestR)
  fns [hp ↦ tNestRW ro]
  grind [arena_grind] extra [ld64_rd_spec]

/-- `tNestR` with the counted-loop sugar (`for`): the same function, and `l_model` reads it as the
plain text (`L.Notation.desugarAll`), so its models and loop blocks are `tNestR`'s. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tNestF : FunDecl := lfn (n) locals (i, j) {
  i := 0;
  for i < n {
    j := 0;
    for j < n {
      if TW.u64[j] == i { return j };
      if TW.u64[j] == 7 { break }
    }
  };
  return 99
}

example : tNestF = tNestR := rfl

l_model tNestF_spec (p : Prog) (hp : p.lookup "t_nest_f" = some tNestF)
  fns [hp ↦ tNestFW ro]
  grind [arena_grind] extra [ld64_rd_spec]

example : tNestFW.loop1.stmt = tNestRW.loop1.stmt := rfl
example : tNestFW.loop2.stmt = tNestRW.loop2.stmt := rfl

/-- `unified` mode: the aborts' codes kept, through the nested loops and the block operations. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tNestE : FunDecl := lfn (n, d) locals (i, j) {
  i := 0;
  while i < n {
    j := 0;
    while j < n {
      if j + d == i { abort R7 };
      if j == 9 { return j };
      j += 1
    };
    copy!(TW.u64, d, TB.u8, i, 2);
    i += 1
  };
  abort R8
}

l_model tNestE_spec (p : Prog) (hp : p.lookup "t_nest_e" = some tNestE)
  fns [hp ↦ tNestEW]
  grind [arena_grind] unified

/-- A loop that never exits normally, then `abort`: fused (the loop's model is the function's). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tFor : FunDecl := lfn (n) locals (i) {
  i := 0;
  while 0 == 0 {
    if i == n { return i };
    i += 1
  };
  abort R8
}

l_model tFor_spec (p : Prog) (hp : p.lookup "t_for" = some tFor)
  fns [hp ↦ tForW ro]
  grind [arena_grind]

/-- A loop that may exit normally, then `abort`: not fused (`unified` mode). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tExit : FunDecl := lfn (n, d) locals (i) {
  i := 0;
  while i < n {
    if i + d == 5 { abort R7 };
    if i == 9 { return i };
    i += 1
  };
  abort R8
}

l_model tExit_spec (p : Prog) (hp : p.lookup "t_exit" = some tExit)
  fns [hp ↦ tExitE]
  grind [arena_grind] unified

/-- A function that only changes the memory (no `return`: the result `0`). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tMem : FunDecl := lfn (i, v) {
  TW.u64[i] := v;
  TB.u8[i] := v
}

l_model tMem_spec (p : Prog) (hp : p.lookup "t_mem" = some tMem)
  fns [hp ↦ tMemW]
  grind [arena_grind]

/-- Nested loops as named blocks (the outer block splices the inner one). -/
-- con-ron: none — an `l_model` test block
def tInLoop : Stmt := lblk (n, i, j, s) {
  while j < i { s += TW.u64[j]; j += 1 }
}

-- con-ron: none — an `l_model` test block
def tOutLoop : Stmt := lblk (n, i, j, s) {
  while i < n { j := 0; ⟪tInLoop⟫; i += 1 }
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tBlk : FunDecl := lfn (n) locals (i, j, s) {
  i := 0;
  ⟪tOutLoop⟫;
  return s
}

l_model tBlk_spec (p : Prog) (hp : p.lookup "t_blk" = some tBlk)
  fns [hp ↦ tBlkW ro]
  grind [arena_grind] extra [ld64_rd_spec]

/-- Models without results (`void`): a store-only function (`Option Mem`), a check
(`Option Unit`, read-only), a caller of both through their specs, and a group whose member
calls a `void` member. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tVSt : FunDecl := lfn (i, v) {
  if v == 9 { abort };
  TW.u64[i] := v;
  return 0
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tVChk : FunDecl := lfn (i) {
  if TW.u64[i] == 7 { abort }
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tVUse : FunDecl := lfn (i, v) locals (x, y) {
  x := call t_v_chk(i);
  y := call t_v_st(i, v + 1);
  return TW.u64[i]
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tVGrp : FunDecl := lfn (i, v) locals (x) {
  x := call t_v_st(i, v);
  return v
}

l_model tVSt_spec (p : Prog) (hp : p.lookup "t_v_st" = some tVSt)
  fns [hp ↦ tVStW void]
  grind [arena_grind]

l_model tVChk_spec (p : Prog) (hp : p.lookup "t_v_chk" = some tVChk)
  fns [hp ↦ tVChkW ro void]
  grind [arena_grind] extra [ld64_rd_spec]

/-- A callee spec with an extra fact over the arguments (ignored by the model). -/
theorem tVChk_spec' (p : Prog) (hp : p.lookup "t_v_chk" = some tVChk) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_v_chk" [i]
    ⦃fun _r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ i = i ∧ tVChkW s₀.mem i = some (); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hr
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hr (tVChk_spec p hp n s₀ i)
  exact ⟨h1, h2, rfl, h3⟩

l_model tVUse_spec (p : Prog) (hp : p.lookup "t_v_use" = some tVUse)
    (hc : p.lookup "t_v_chk" = some tVChk) (hs : p.lookup "t_v_st" = some tVSt)
  fns [hp ↦ tVUseW]
  specs [tVChk_spec' p hc n, tVSt_spec p hs n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tVGrp_spec (p : Prog) (hp : p.lookup "t_v_grp" = some tVGrp)
    (hs : p.lookup "t_v_st" = some tVSt)
  fns [hp ↦ tVGrpW, hs ↦ tVStGW void]
  grind [arena_grind]

/-- Preconditions (`pre [...]`): the spec takes the hypothesis, and a call to a callee whose
spec has one leaves it as a side goal of the step. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tPreC : FunDecl := lfn (i) {
  return TW.u64[i] + i
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tPre : FunDecl := lfn (i) locals (x) {
  x := call t_pre_c(i);
  TW.u64[i] := x;
  return x
}

l_model tPreC_spec (p : Prog) (hp : p.lookup "t_pre_c" = some tPreC)
  fns [hp ↦ tPreCW ro]
  pre [i < 5]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tPre_spec (p : Prog) (hp : p.lookup "t_pre" = some tPre)
    (hc : p.lookup "t_pre_c" = some tPreC)
  fns [hp ↦ tPreW]
  specs [tPreC_spec p hc n]
  pre [i < 4]
  grind [arena_grind]

l_model tNestR2_spec (p : Prog) (hp : p.lookup "t_nest_r2" = some tNestR2)
  fns [hp ↦ tNestR2W]
  grind [arena_grind] extra [ld64_rd_spec]

/-- `keep [h]` (`h : p.noSt8 = true`): the callees' specs and the induction hypotheses wrapped in
`Triple.keep`, whose conjunct `Keep s₀.mem s'.mem` is a fact, not the model; the precondition
over an array's size holds again after each call, for the next call's side goal. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tKeepC : FunDecl := lfn (i) {
  TW.u64[i & 7] := i;
  return i + 1
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tKeep : FunDecl := lfn (i) locals (x, y) {
  x := call t_keep_c(i);
  y := call t_keep_c(x);
  return x + y
}

/-- Recursive: the second recursive call's precondition from the first one's `Keep`. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tKeepR : FunDecl := lfn (i) locals (x, y) {
  if i == 0 { return 0 };
  x := call t_keep_r(i - 1);
  y := call t_keep_r(i - 1);
  return x + y + TW.u64[i & 7]
}

l_model tKeepC_spec (p : Prog) (hp : p.lookup "t_keep_c" = some tKeepC)
  fns [hp ↦ tKeepCW]
  pre [(s₀.mem.arr64 TW).size = 8]
  grind [arena_grind]

l_model tKeep_spec (p : Prog) (hn : p.noSt8 = true) (hp : p.lookup "t_keep" = some tKeep)
    (hc : p.lookup "t_keep_c" = some tKeepC)
  fns [hp ↦ tKeepW]
  specs [tKeepC_spec p hc n]
  pre [(s₀.mem.arr64 TW).size = 8]
  keep [hn]
  grind [arena_grind]

l_model tKeepR_spec (p : Prog) (hn : p.noSt8 = true) (hp : p.lookup "t_keep_r" = some tKeepR)
  fns [hp ↦ tKeepRW]
  pre [(s₀.mem.arr64 TW).size = 8]
  keep [hn]
  grind [arena_grind] extra [ld64_rd_spec]

/-- `defs` / `nodefs`: the models first, then a fact about them, then the specs, whose steps use
the fact (the second recursive call's precondition after the first call). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tTwo : FunDecl := lfn (i) locals (x, y) {
  if i == 0 { return 0 };
  x := call t_two(i - 1);
  y := call t_two(i - 1);
  TW.u64[0] := 0;
  return x + y
}

l_model tTwo_spec (p : Prog) (hp : p.lookup "t_two" = some tTwo)
  fns [hp ↦ tTwoW]
  grind [arena_grind] defs

theorem tTwoW_z (n : Nat) : ∀ (m : Mem) (i r : Word) (m' : Mem), rdW (m.arr64 TW) 0 = 0 →
    tTwoW n m i = some (r, m') → rdW (m'.arr64 TW) 0 = 0 := by
  induction n with
  | zero => intro m i r m' _ h; simp [tTwoW] at h
  | succ n ih =>
    intro m i r m' h0 h
    by_cases hi : i = 0
    · rw [tTwoW.arm1 n m i hi] at h; cases h; exact h0
    rw [tTwoW.eq_2, ite_eq_right hi] at h
    cases h1 : tTwoW n m (i - 1) with
    | none => rw [h1, tTwoW.k_t_two.none] at h; cases h
    | some x =>
      obtain ⟨x, m₁⟩ := x
      rw [h1, tTwoW.k_t_two.arm1] at h
      cases h2 : tTwoW n m₁ (i - 1) with
      | none => rw [h2, tTwoW.k_t_two_2.none] at h; cases h
      | some y =>
        obtain ⟨y, m₂⟩ := y
        rw [h2, tTwoW.k_t_two_2.arm1] at h
        cases h
        simp only [rdW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        split <;> simp_all <;> split <;> rfl

theorem tTwoW_z' (n : Nat) (m : Mem) (i r : Word) (m' : Mem) (h : tTwoW n m i = some (r, m'))
    (h0 : rdW (m.arr64 TW) 0 = 0) : rdW (m'.arr64 TW) 0 = 0 := tTwoW_z n m i r m' h0 h
grind_pattern [arena_grind] tTwoW_z' => tTwoW n m i, some (r, m')

l_model tTwo_spec (p : Prog) (hp : p.lookup "t_two" = some tTwo)
  fns [hp ↦ tTwoW]
  pre [rdW (s₀.mem.arr64 TW) 0 = 0]
  grind [arena_grind] nodefs

/-! ## `unified`: one model for both outcomes

`t_uni` calls a callee outside the verdict closure through its `Option` model (`t_leaf_u`, lifted
by `L.liftE`), aborts, calls itself (its error passes through) and calls a `unified` callee
(`t_uni_c`, through its `Except` model). -/

-- con-ron: none — an `l_model` test function
@[no_expose] def tLeafU : FunDecl := lfn (x) {
  return TW.u64[x] + 1
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tUniC : FunDecl := lfn (y) {
  if y == 3 { abort R8 };
  return y + 1
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tUni : FunDecl := lfn (k, x) locals (a, b) {
  if k == 0 { return 0 };
  a := call t_leaf_u(x);
  if a == 7 { abort R7 };
  b := call t_uni(k - 1, a);
  b := call t_uni_c(b);
  return b
}

l_model tLeafU_spec (p : Prog) (hp : p.lookup "t_leaf_u" = some tLeafU)
  fns [hp ↦ tLeafUW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model tUniC_spec (p : Prog) (hp : p.lookup "t_uni_c" = some tUniC)
  fns [hp ↦ tUniCE]
  grind [arena_grind] unified

l_model tUni_spec (p : Prog) (fs : List FnName)
    (hmem : ∀ {f : FnName}, f ∈ ["t_leaf_u"] → f ∈ fs)
    (hp : p.lookup "t_uni" = some tUni) (hl : p.lookup "t_leaf_u" = some tLeafU)
    (hc : p.lookup "t_uni_c" = some tUniC)
  fns [hp ↦ tUniE]
  specs [tLeafU_spec p hl n, tUniC_spec p hc n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

example (p : Prog) (n : Nat) (m : Mem) : tUniE p (n + 1) m 0 5 = .ok (0, m) := by simp [tUniE]
example (p : Prog) (m : Mem) : tUniCE p m 3 = .error (.abort 8) := by simp [tUniCE]

/-- `flat`: the same steps with the states removed from the conditions (`vc_flat`), closed by
`grind` over the guarded equations; the recursive call goes through the induction hypothesis. -/
l_model tUniF_spec (p : Prog) (fs : List FnName)
    (hmem : ∀ {f : FnName}, f ∈ ["t_leaf_u"] → f ∈ fs)
    (hp : p.lookup "t_uni" = some tUni) (hl : p.lookup "t_leaf_u" = some tLeafU)
    (hc : p.lookup "t_uni_c" = some tUniC)
  fns [hp ↦ tUniFE]
  specs [tLeafU_spec p hl n, tUniC_spec p hc n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

/-- A total callee outside the verdict closure (a list post `r ≠ [] ∧ r = F`, as `e_view`'s; its
`[]` an error of class `0`) and a pure one (`r.headD 0 = F`), both lifted in `unified` mode. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tPair : FunDecl := lfn (x) {
  return (x, TW.u64[x])
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tUniL : FunDecl := lfn (x) locals (a, b) {
  (a, b) := call t_pair(x);
  if b == 7 { abort R7 };
  return a + b
}

theorem tPair_spec (p : Prog) (hp : p.lookup "t_pair" = some tPair) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_pair" [x]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = [x, rdW (s₀.mem.arr64 TW) x]; ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, tPair]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n => vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec] <;> simp_all [Sig.retVal, Sig.retOr, Locals.init]

l_model tUniL_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_pair"] → f ∈ fs)
    (hp : p.lookup "t_uni_l" = some tUniL) (hq : p.lookup "t_pair" = some tPair)
  fns [hp ↦ tUniLE]
  specs [tPair_spec p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

example (p : Prog) (m : Mem) (h : rdW (m.arr64 TW) 2 = 3) : tUniLE p m 2 = .ok (5, m) := by
  simp [tUniLE, h]

/-- A callee whose spec states its one result as a list (`some ([r.headD 0], s'.mem)`). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tOne : FunDecl := lfn (x) {
  if x == 9 { abort };
  TW.u64[0] := x;
  return x + 1
}

/-- `t_one`'s model with its result as a list. -/
def tOneL (m : Mem) (x : Word) : Option (List Word × Mem) :=
  if x = 9 then none else some ([x + 1], m.set64 TW 0 x)

theorem tOne_spec (p : Prog) (hp : p.lookup "t_one" = some tOne) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_one" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ tOneL s₀.mem x = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, tOne]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      simp_all [tOneL, Sig.retVal, Sig.retOr, Locals.init, LocEq, BinOp.eval, Cmp.eval]

-- con-ron: none — an `l_model` test function
@[no_expose] def tUseOne : FunDecl := lfn (x) locals (a) {
  a := call t_one(x);
  return a + a
}

l_model tUseOne_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_one"] → f ∈ fs)
    (hp : p.lookup "t_use_one" = some tUseOne) (hq : p.lookup "t_one" = some tOne)
  fns [hp ↦ tUseOneE]
  specs [tOne_spec p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

example (p : Prog) (m : Mem) : tUseOneE p m 9 = .error .oob := by
  simp [tUseOneE, tOneL, tUseOneE.k_t_one]

/-- A tuple model whose `return (k, x, y)` is in a spliced loop block (three words, not two). -/
-- con-ron: none — an `l_model` test block
def tTupLoop : Stmt := lblk (n, k, x, y) {
  while 0 == 0 {
    if k == n { return (k, x, y) };
    x += 1;
    y += 2;
    k += 1
  }
}

-- con-ron: none — an `l_model` test function
@[no_expose] def tTup3 : FunDecl := lfn (n) locals (k, x, y) {
  ⟪tTupLoop⟫;
  abort
}

l_model tTup3_spec (p : Prog) (hp : p.lookup "t_tup3" = some tTup3)
  fns [hp ↦ tTup3E tuple]
  grind [arena_grind] unified

example (p : Prog) (n : Nat) (m : Mem) : tTup3E p (n + 3) m 1 = .ok (1, 1, 2, m) := by
  simp [tTup3E, tTup3E.loop1]

/-- A callee guard without a `Decidable` instance (as `flush_caches`' `FlushOK`): the model
decides it classically (and is `noncomputable`), it does not hold `sorry`. -/
def UG (_m : Mem) : Prop := ∀ k : Nat, k = k

-- con-ron: none — an `l_model` test function
@[no_expose] def tUg : FunDecl := lfn (x) {
  TW.u64[0] := x;
  return 0
}

theorem tUg_spec (p : Prog) (hp : p.lookup "t_ug" = some tUg) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_ug" [x]
    ⦃fun _r s' => LocEq s' s₀ ∧ UG s₀.mem ∧ s'.mem = s₀.mem.set64 TW 0 x; ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, tUg]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      simp_all [UG, Locals.init, LocEq]

-- con-ron: none — an `l_model` test function
@[no_expose] def tUseUg : FunDecl := lfn (x) locals (a) {
  a := call t_ug(x);
  return x + 1
}

l_model tUseUg_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_ug"] → f ∈ fs)
    (hp : p.lookup "t_use_ug" = some tUseUg) (hq : p.lookup "t_ug" = some tUg)
  fns [hp ↦ tUseUgE]
  specs [tUg_spec p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

example (p : Prog) (m : Mem) : tUseUgE p m 1 = .ok (2, m.set64 TW 0 1) := by
  simp [tUseUgE, UG]

/-- A callee post with the result's length (`r = [r.headD 0, r.getD 1 0]`, `piBinders_spec`'s
shape; also as `r.tail.headD 0`): the model reads it as the list, and `simp_all` takes it apart
(`L.List.eq_headD_cons`) instead of looping on it. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tLen : FunDecl := lfn (x) locals (a, b) {
  if x == 9 { abort };
  a := x;
  b := x + 1;
  return (a, b)
}

/-- `t_len`'s model. -/
def tLenL (m : Mem) (x : Word) : Option (List Word × Mem) :=
  if x = 9 then none else some ([x, x + 1], m)

theorem tLen_spec (p : Prog) (hp : p.lookup "t_len" = some tLen) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_len" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ tLenL s₀.mem x = some (r, s'.mem) ∧ r = [r.headD 0, r.getD 1 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, tLen]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      simp_all [tLenL, Sig.retVal, Sig.retOr, Locals.init, LocEq, BinOp.eval, Cmp.eval, St.setLoc_loc,
        L.St.setLoc_mem]

theorem tLen_specT (p : Prog) (hp : p.lookup "t_len" = some tLen) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_len" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ tLenL s₀.mem x = some (r, s'.mem) ∧ r = [r.headD 0, r.tail.headD 0]; ⊤⦄ :=
  M.triple_of_run fun _ _ _ hs hr => by
    obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hr (tLen_spec p hp n s₀ x)
    exact ⟨h1, h2, by rw [h3]; rfl⟩

-- con-ron: none — an `l_model` test function
@[no_expose] def tUseLen : FunDecl := lfn (x) locals (a, b) {
  (a, b) := call t_len(x);
  TW.u64[0] := b;
  return a + b
}

l_model tUseLen_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_len"] → f ∈ fs)
    (hp : p.lookup "t_use_len" = some tUseLen) (hq : p.lookup "t_len" = some tLen)
  fns [hp ↦ tUseLenE]
  specs [tLen_spec p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

l_model tUseLenT_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_len"] → f ∈ fs)
    (hp : p.lookup "t_use_len" = some tUseLen) (hq : p.lookup "t_len" = some tLen)
  fns [hp ↦ tUseLenTE]
  specs [tLen_specT p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

example (p : Prog) (m : Mem) : tUseLenE p m 1 = .ok (3, m.set64 TW 0 2) := by
  simp [tUseLenE, tUseLenE.k_t_len, tLenL]

/-- A callee model with a pair of results, `some ((r.headD 0, r.tail.headD 0), s'.mem)`
(`vi_map`'s): read through `L.flat3` as a tuple of two. -/
def tLenP (m : Mem) (x : Word) : Option ((Word × Word) × Mem) :=
  if x = 9 then none else some ((x, x + 1), m)

theorem tLen_specP (p : Prog) (hp : p.lookup "t_len" = some tLen) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_len" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ tLenP s₀.mem x = some ((r.headD 0, r.tail.headD 0), s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, tLen]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      simp_all [tLenP, Sig.retVal, Sig.retOr, Locals.init, LocEq, BinOp.eval, Cmp.eval, St.setLoc_loc,
        L.St.setLoc_mem]

l_model tUseLenP_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_len"] → f ∈ fs)
    (hp : p.lookup "t_use_len" = some tUseLen) (hq : p.lookup "t_len" = some tLen)
  fns [hp ↦ tUseLenPE]
  specs [tLen_specP p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem]

example (p : Prog) (m : Mem) : tUseLenPE p m 1 = .ok (3, m.set64 TW 0 2) := by
  simp [tUseLenPE, tUseLenPE.k_t_len, tLenP]

/-- `cut k`: two `if`s that only set locals, then a call: the code after them (the join point
`j2`) gets its own step theorem `tCut_spec.tail`, so the step's paths are not four copies of the
call's. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tCut : FunDecl := lfn (x, y) locals (a, b, c) {
  if x < 5 { a := x } else { a := x + 1 };
  if y < 5 { b := y } else { b := y - 1 };
  c := call t_len(a);
  if c == 0 { return 0 };
  TW.u64[0] := b;
  return c + b
}

l_model tCut_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_len"] → f ∈ fs)
    (hp : p.lookup "t_cut" = some tCut) (hq : p.lookup "t_len" = some tLen)
  fns [hp ↦ tCutE]
  specs [tLen_spec p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem] cut 2

example (p : Prog) (m : Mem) : tCutE p m 1 7 = .ok (7, m.set64 TW 0 6) := by
  simp [tCutE, tCutE.j1, tCutE.j2, tCutE.k_t_len, tLenL]

/-- `flat` with `cut`: the tail's step theorem and the step both by `vc_flat` and `grind`. -/
l_model tCutF_spec (p : Prog) (fs : List FnName) (hmem : ∀ {f : FnName}, f ∈ ["t_len"] → f ∈ fs)
    (hp : p.lookup "t_cut" = some tCut) (hq : p.lookup "t_len" = some tLen)
  fns [hp ↦ tCutFE]
  specs [tLen_spec p hq n]
  grind [arena_grind] unified nv [closedNV p fs = true, hmem] cut 2

/-- `pfuel`: a callee read as a function of the fuel (`C n m x`, as `callW p n "f"` is), so the
model takes the fuel as a parameter, without a `match` on it, and the spec is at `exec p (n + 1)`
with the model at `n`. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tPf : FunDecl := lfn (x) locals (y) {
  y := call t_c(x);
  if y == 0 { return 1 };
  return y + x
}

l_model tPf_spec (p : Prog) (C : Nat → Mem → Word → Option (Word × Mem))
    (hc : ∀ n (s₀ : St) (x : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_c" [x]
      ⦃fun r s' => LocEq s' s₀ ∧ C n s₀.mem x = some (r.headD 0, s'.mem); ⊤⦄)
    (hp : p.lookup "t_pf" = some tPf)
  fns [hp ↦ tPfW]
  specs [hc n]
  grind [arena_grind] pfuel

example (C : Nat → Mem → Word → Option (Word × Mem)) (n : Nat) (m : Mem) (x : Word)
    (h : C n m x = some (0, m)) : tPfW C n m x = some (1, m) := by
  simp [tPfW, tPfW.k_t_c, h]

example (p : Prog) (C : Nat → Mem → Word → Option (Word × Mem))
    (hc : ∀ n (s₀ : St) (x : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_c" [x]
      ⦃fun r s' => LocEq s' s₀ ∧ C n s₀.mem x = some (r.headD 0, s'.mem); ⊤⦄)
    (hp : p.lookup "t_pf" = some tPf) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "t_pf" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ tPfW C n s₀.mem x = some (r.headD 0, s'.mem); ⊤⦄ :=
  tPf_spec p C hc hp n s₀ x

/-- `guards`: a callee whose post is a table lookup (`G m x = true ∧ r = [F m x]`, as
`name_get`'s): its guard is the model's, its result the literal's element. -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tGd : FunDecl := lfn (x) locals (y) {
  y := call t_look(x);
  return y + 1
}

l_model tGd_spec (p : Prog) (G : Mem → Word → Bool) (F : Mem → Word → Word)
    (hc : ∀ n (s₀ : St) (x : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_look" [x]
      ⦃fun r s' => s' = s₀ ∧ G s₀.mem x = true ∧ r = [F s₀.mem x]; ⊤⦄)
    (hp : p.lookup "t_gd" = some tGd)
  fns [hp ↦ tGdW ro]
  specs [hc n]
  grind [arena_grind] guards ["t_look"]

example (G : Mem → Word → Bool) (F : Mem → Word → Word) (m : Mem) (x : Word)
    (h : G m x = false) : tGdW G F m x = none := by
  simp [tGdW, h]

example (G : Mem → Word → Bool) (F : Mem → Word → Word) (m : Mem) (x : Word)
    (h : G m x = true) : tGdW G F m x = some (F m x + 1) := by
  simp [tGdW, h]

/-- `share`: calls of a total memory callee, each reading the memory the call before it left
(`rule_copy`'s shape). Inline, the memory after a call would hold three copies of the one before
it (the callee's memory, the read, the guard): `3 ^ k` memories after `k` calls. With `share` each
call after the first is a join point over the memory (`tShW.j1`, …). -/
-- con-ron: none — an `l_model` test function
@[no_expose] def tSh : FunDecl := lfn (b, old) locals (z) {
  z := call t_put(b, TW.u64[old]);
  z := call t_put(b + 1, TW.u64[old + 1]);
  z := call t_put(b + 2, TW.u64[old + 2]);
  z := call t_put(b + 3, TW.u64[old + 3]);
  return 0
}

l_model tSh_spec (p : Prog) (P : Mem → Word → Word → Mem) (G : Mem → Word → Bool)
    (hc : ∀ n (s₀ : St) (a v : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "t_put" [a, v]
      ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = P s₀.mem a v ∧ G s₀.mem a = true; ⊤⦄)
    (hp : p.lookup "t_sh" = some tSh)
  fns [hp ↦ tShW]
  specs [hc n]
  grind [arena_grind] share

example (m : Mem) (b old : Word) : tShW (fun m _ _ => m) (fun _ _ => true) m b old = some (0, m) := by
  simp [tShW, tShW.j1, tShW.j2, tShW.j3]

example (P : Mem → Word → Word → Mem) (m : Mem) (b old : Word) :
    tShW P (fun _ _ => false) m b old = none := by
  simp [tShW]

end L.ModelGenTest
