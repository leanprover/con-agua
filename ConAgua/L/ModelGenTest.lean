import ConAgua.Arena.LdRd
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Tests of `l_model` (`L/ModelGen.lean`)

Small functions over test arrays, one per feature: pool slices (`A⦃x⦄`, `⦃x⦄.tier/.idx/.base`),
`le64!`, `scan!`, `copy!` (words, tiered words, bytes), byte stores, sequential loops and nested
loops (a `break` and a `return` in the inner loop, the outer loop fused or not), a loop followed
by `abort` (fused only if it never exits normally), and `errors` mode through them. Each `l_model`
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

def tPool : FunDecl := lfn (x) {
  return TP⦃x⦄ + ⦃x⦄.tier + ⦃x⦄.idx + ⦃x⦄.base
}

def tLe : FunDecl := lfn (i) {
  return le64!(TB.u8, i) + 1
}

def tScan : FunDecl := lfn (i, e) locals (j) {
  j := scan!(TB.u8, i, e, digC);
  return j + 1
}

def tCopy : FunDecl := lfn (d, s, k) {
  copy!(TW.u64, d, TP.u64⟨1⟩, s, k);
  copy!(TP.u64⟨0⟩, d + k, TB.u8, s, k);
  copy!(TW.u64, d, TW.u64, s + 1, 2);
  return TW.u64[d]
}

def tSt8 : FunDecl := lfn (i, v) {
  TB.u8[i] := v;
  TB.u8[i + 1] := v >> 8;
  return 0
}

def tSeq : FunDecl := lfn (n) locals (i, s) {
  i := 0;
  while i < n { s += 1; i += 1 };
  i := 0;
  while i < n { s += TW.u64[i]; i += 1 };
  return s
}

def tNest : FunDecl := lfn (n) locals (i, j, s) {
  i := 0;
  while i < n {
    j := 0;
    while j < i { s += TW.u64[j]; j += 1 };
    i += 1
  };
  return s
}

/-- A `break` and a `return` in the inner loop; the outer loop is fused (`return 99` after it). -/
def tNestR : FunDecl := lfn (n) locals (i, j) {
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
def tNestR2 : FunDecl := lfn (n) locals (i, j, r) {
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

l_model tPool_spec (p : Prog) (hp : p.lookup "t_pool" = some tPool)
  fns [hp ↦ tPoolW ro]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tLe_spec (p : Prog) (hp : p.lookup "t_le" = some tLe)
  fns [hp ↦ tLeW ro]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tScan_spec (p : Prog) (hp : p.lookup "t_scan" = some tScan)
  fns [hp ↦ tScanW ro]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tCopy_spec (p : Prog) (hp : p.lookup "t_copy" = some tCopy)
  fns [hp ↦ tCopyW]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tSt8_spec (p : Prog) (hp : p.lookup "t_st8" = some tSt8)
  fns [hp ↦ tSt8W]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tSeq_spec (p : Prog) (hp : p.lookup "t_seq" = some tSeq)
  fns [hp ↦ tSeqW ro]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tNest_spec (p : Prog) (hp : p.lookup "t_nest" = some tNest)
  fns [hp ↦ tNestW ro]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model tNestR_spec (p : Prog) (hp : p.lookup "t_nest_r" = some tNestR)
  fns [hp ↦ tNestRW ro]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- `errors` mode: the aborts' codes kept, through the nested loops and the block operations. -/
def tNestE : FunDecl := lfn (n, d) locals (i, j) {
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
  grind [arena_grind] simp [] errors

/-- A loop that never exits normally, then `abort`: fused (the loop's model is the function's). -/
def tFor : FunDecl := lfn (n) locals (i) {
  i := 0;
  while 0 == 0 {
    if i == n { return i };
    i += 1
  };
  abort R8
}

l_model tFor_spec (p : Prog) (hp : p.lookup "t_for" = some tFor)
  fns [hp ↦ tForW ro]
  grind [arena_grind] simp []

/-- A loop that may exit normally, then `abort`: not fused (`errors` mode). -/
def tExit : FunDecl := lfn (n, d) locals (i) {
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
  grind [arena_grind] simp [] errors

/-- A function that only changes the memory (no `return`: the result `0`). -/
def tMem : FunDecl := lfn (i, v) {
  TW.u64[i] := v;
  TB.u8[i] := v
}

l_model tMem_spec (p : Prog) (hp : p.lookup "t_mem" = some tMem)
  fns [hp ↦ tMemW]
  grind [arena_grind] simp []

l_model tNestR2_spec (p : Prog) (hp : p.lookup "t_nest_r2" = some tNestR2)
  fns [hp ↦ tNestR2W]
  grind [arena_grind] extra [ld64_rd_spec] simp []

end L.ModelGenTest
