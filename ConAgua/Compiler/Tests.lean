module

import ConAgua.Compiler.Run
import ConAgua.L.Notation
import ConAgua.L.Examples
import ConAgua.Scan.Lit
import ConAgua.Scan.Utf8

/-!
# Differential tests: compiled code on Kraken's semantics against `L.run`

`agrees p f args m` runs `f` both ways with plenty of fuel and stack and compares the outcomes.
The x64 fuel counter counts every loop iteration and call, `L`'s fuel only their nesting, so with
little fuel the compiled code may run out where `L` does not (never the other way round); the
`exhausted` tests check the direction that matters.
-/

open L L.Compiler L.Examples

namespace L.Compiler.Tests

def agrees (p : Prog) (f : FnName) (args : List Word) (m : Mem) (fuel : Nat := 100000)
    (stack : Nat := 4096) : Bool :=
  (runKraken p f args m fuel.toUInt64 stack).toOption ==
    some (Outcome.ofL (Prog.tab p m.bytes.size m.words.size).nres (run p fuel f args m))

def inp (s : String) : Mem := { bytes := #[s.toUTF8.data] }

/-! `skip_braced` and `str_close` (`L/Examples.lean`). -/

-- The compiler theorem applies: the program is well formed for one byte array.
#guard Prog.wf (Prog.tab scanProg 1 0) scanProg

#guard agrees scanProg "skip_braced" [1, 0] (inp "{\"a\":[1,{\"b\\\"\":2}]} x")
#guard agrees scanProg "skip_braced" [1, 0] (inp "{\"a\":1")
#guard agrees scanProg "skip_braced" [1, 0] (inp "{\"a\n\":1}")
#guard agrees scanProg "skip_braced" [1, 0] (inp "{[[[]]]}")
#guard agrees scanProg "skip_braced" [1, 3] (inp "{]]]]}")
#guard agrees scanProg "skip_braced" [0, 0] (inp "")
#guard agrees scanProg "skip_braced" [100, 0] (inp "{}")
#guard agrees scanProg "str_close" [1] (inp "\"ab\\\"c\" ")
#guard agrees scanProg "str_close" [1] (inp "\"ab\\")
#guard agrees scanProg "str_close" [1] (inp "\"a\x01\"")

-- Fuel: both run out on a long input with fuel 3.
#guard (runKraken scanProg "skip_braced" [1, 0] (inp "{aaaaaaaaaa}") 3).toOption == some .exhausted
#guard Outcome.ofL 1 (run scanProg 3 "skip_braced" [1, 0] (inp "{aaaaaaaaaa}")) == .exhausted

/-! Word arrays, stores, arithmetic, signed comparisons, recursion, `break`, `abort`. -/

def W : ArrId := 0
def B : ArrId := 0

/-- Sums `W.u64[0..n)` into `W.u64[n]`, doubles every byte of `B`, mixes some arithmetic. -/
-- con-ron: none — a compiler test program
def mix : FunDecl := lfn (n) locals (i, s, t) {
  while i < n {
    s := s + W.u64[i];
    i += 1
  };
  W.u64[n] := s;
  i := 0;
  while 1 == 1 {
    if i >= len(B.u8) { break };
    B.u8[i] := B.u8[i] * 2 + 1;
    i += 1
  };
  t := (s << 3) ^ (s >> 1) | (s & 255) - 7;
  if t <ₛ 0 || !(t ≤ₛ 100) && t != 5 { t := t * 3 } else { t := 0 };
  return t + W.u64[n] + B.u8[1]
}

def mixMem : Mem := { bytes := #[#[1, 2, 3, 200]], words := #[#[5, 0xffffffffffffff00, 7, 0]] }

#guard agrees [("mix", mix)] "mix" [3] mixMem
-- Out of bounds: `W.u64[4]` does not exist.
#guard agrees [("mix", mix)] "mix" [4] mixMem
#guard (runKraken [("mix", mix)] "mix" [4] mixMem 100000).toOption == some .error

/-- con-ron: none — a compiler test program -/
def sumTo : FunDecl := lfn (n) locals (r) {
  if n == 0 { return 0 };
  r := call sum_to(n - 1);
  return r + n
}

/-- con-ron: none — a compiler test program -/
def boom : FunDecl := lfn (n) {
  if n == 7 { abort };
  return n
}

def recProg : Prog := [("sum_to", sumTo), ("boom", boom)]

#guard Prog.wf { nb := 0, nw := 0 } recProg
#guard Prog.wf { nb := 1, nw := 1 } [("mix", mix)]

#guard agrees recProg "sum_to" [100] {}
#guard agrees recProg "boom" [7] {}
#guard agrees recProg "boom" [8] {}
-- A small stack: a call of `sum_to` takes 24 bytes (a 2-word frame and the return address), and
-- the stack check also reserves the next return address: 128 bytes hold five calls, not six.
#guard agrees recProg "sum_to" [4] {} 100000 128
#guard (runKraken recProg "sum_to" [5] {} 100000 128).toOption == some .exhausted

/-! `mulhi`, comparisons as words, constant data. -/

def LITS : List UInt8 := "truefalse".toUTF8.toList

/-- `mulhi(x, y)`, the carry of `x + y`, and whether `IN[i..]` starts with `"false"`. -/
-- con-ron: none — a compiler test program
def ext : FunDecl := lfn (x, y, i) locals (k, ok) {
  ok := 1;
  while k < 5 {
    if i + k >= len(B.u8) { ok := 0; break };
    if B.u8[i + k] != LITS.c8[k + 4] { ok := 0 };
    k += 1
  };
  return mulhi(x, y) ^ (u64(x + y < x) << 32) ^ (ok << 40) ^ u64(x ≤ₛ y) << 41
}

def extProg : Prog := [("ext", ext)]

#guard Prog.wf (Prog.tab extProg 1 0) extProg
#guard Prog.rom extProg = LITS
#guard agrees extProg "ext" [0xffffffffffffffff, 0xffffffffffffffff, 0] (inp "false")
#guard agrees extProg "ext" [0x123456789abcdef0, 0x0fedcba987654321, 1] (inp " false")
#guard agrees extProg "ext" [3, 5, 1] (inp " fals")
#guard agrees extProg "ext" [0x8000000000000000, 5, 0] (inp "falsy")
/-- con-ron: none — a compiler test program -/
-- `LITS.c8[9]` is out of bounds.
def oobC : FunDecl := lfn (i) { return LITS.c8[i] }
#guard agrees [("c", oobC)] "c" [8] {}
#guard (runKraken [("c", oobC)] "c" [9] {} 100000).toOption == some .error

/-! Several results. -/

/-- The 128-bit product, the carry of a sum, and a third value. -/
-- con-ron: none — a compiler test program
def wide : FunDecl := lfn (x, y) {
  return (x * y, mulhi(x, y), u64(x + y < x))
}

/-- Returns one value: a caller reading three gets `0` for the other two. -/
-- con-ron: none — a compiler test program
def one : FunDecl := lfn (x) { return x + 1 }

/-- Returns nothing (falls off the end). -/
-- con-ron: none — a compiler test program
def none' : FunDecl := lfn (x) { skip }

/-- con-ron: none — a compiler test program -/
def useWide : FunDecl := lfn (x, y) locals (lo, hi, c, a, b, z) {
  (lo, hi, c) := call wide(x, y);
  (a, b, z) := call one(lo);
  (b, z) := call none'(a);
  (hi, hi) := call wide(hi, 3);
  return lo ^ (hi << 1) ^ (c << 60) ^ a ^ b ^ z
}

def wideProg : Prog := [("use", useWide), ("wide", wide), ("one", one), ("none'", none')]

#guard (Prog.tab wideProg 0 0).nres = 3
#guard Prog.wf (Prog.tab wideProg 0 0) wideProg
#guard agrees wideProg "use" [0xffffffffffffffff, 0xfffffffffffffff0] {}
#guard agrees wideProg "use" [12345, 678910] {}
#guard agrees wideProg "wide" [0xffffffffffffffff, 0xfffffffffffffff0] {}
#guard agrees wideProg "one" [41] {}
#guard agrees wideProg "none'" [41] {}
#guard (runKraken wideProg "wide" [0xffffffffffffffff, 2] {} 1000).toOption == some (.ok [0xfffffffffffffffe, 1, 1])
#guard (run wideProg 100 "wide" [0xffffffffffffffff, 2] {}).toOption.map (·.1) ==
  some [0xfffffffffffffffe, 1, 1]

/-! More results than registers (lane `cresults`): results 6, 7, 8 go through the table's result
area. -/

/-- con-ron: none — a compiler test program -/
def nine : FunDecl := lfn (x) {
  return (x, x + 1, x + 2, x + 3, x + 4, x + 5, x + 6, x + 7, x + 8)
}

/-- Returns seven of nine: the caller reads `0` for results 7 and 8. -/
-- con-ron: none — a compiler test program
def seven : FunDecl := lfn (x) {
  return (x, x * 2, x * 3, x * 4, x * 5, x * 6, x * 7)
}

/-- con-ron: none — a compiler test program -/
def useNine : FunDecl := lfn (x) locals (a, b, c, d, e, f, g, h, i, z) {
  (a, b, c, d, e, f, g, h, i) := call nine(x);
  z := a ^ (b << 4) ^ (c << 8) ^ (d << 12) ^ (e << 16) ^ (f << 20) ^ (g << 24) ^ (h << 28) ^ (i << 32);
  (a, b, c, d, e, f, g, h, i) := call seven(i);
  (b, i) := call nine(z);
  return (z, a, b, c, d, e, f, g, h, i)
}

def nineProg : Prog := [("use", useNine), ("nine", nine), ("seven", seven)]

#guard (Prog.tab nineProg 0 0).nres = 10
#guard Prog.wf (Prog.tab nineProg 0 0) nineProg
#guard agrees nineProg "use" [5] {}
#guard agrees nineProg "use" [0xfffffffffffffff0] {}
#guard agrees nineProg "nine" [7] {}
#guard agrees nineProg "seven" [7] {}
#guard (runKraken nineProg "nine" [7] {} 1000).toOption == some (.ok [7, 8, 9, 10, 11, 12, 13, 14, 15, 0])

/-! `match_lit`/`scan_bool` (`Scan/Lit.lean`): constant data and three results. -/

open L.Scan.Lit in
#guard Prog.wf (Prog.tab litProg 1 0) litProg
open L.Scan.Lit in
#guard [" true", "false", "fals", "", "falsetto", "tru"].all fun t =>
  [0, 1].all fun i => agrees litProg "scan_bool" [i] (inp t)

/-! `utf8_decode` (`Scan/Utf8.lean`): two results, stores into a word array. -/

open L.Scan.Utf8 in
#guard Prog.wf (Prog.tab utf8Prog 1 1) utf8Prog
open L.Scan.Utf8 in
#guard [[], "plain ascii".toUTF8.toList, [0xC3, 0xA9], [0xE2, 0x86, 0x92], [0xF0, 0x9F, 0x98, 0x80],
    [0x80], [0xC0, 0x80], [0xE0, 0x80, 0x80], [0xED, 0xA0, 0x80], [0xF4, 0x90, 0x80, 0x80],
    [0xF5, 0x80, 0x80, 0x80], [0xE2, 0x86], [0x41, 0xC3, 0xA9, 0x42]].all fun (bs : List UInt8) =>
  agrees utf8Prog "utf8_decode" [0, UInt64.ofNat bs.length]
    { bytes := #[bs.toArray], words := #[Array.replicate 16 0] }
-- `OUT` too small: an out-of-bounds store.
open L.Scan.Utf8 in
#guard (runKraken utf8Prog "utf8_decode" [0, 5] { bytes := #["hello".toUTF8.data], words := #[#[0, 0]] }
  100000).toOption == some .error

/-! Global variables (`GVar`): reads, writes, `+=`, across calls and in conditions, next to
arrays, the result area (nine results) and entry arguments. -/

abbrev GA : GVar := ⟨0⟩
abbrev GB : GVar := ⟨2⟩

/-- con-ron: none — a compiler test program -/
def gbump : FunDecl := lfn (x) { GA += x; GB := GB + 1; return GA }
/-- con-ron: none — a compiler test program -/
def gmain : FunDecl := lfn (n) locals (i, r) {
  GA := 10;
  while i < n { r := call gbump(i); i += 1 };
  if GB == n { W.u64[0] := GA };
  return (GA, GB, r, W.u64[0], n, 0, GA + GB, GB, GA)
}
def globProg : Prog := [("gmain", gmain), ("gbump", gbump)]

#guard (Prog.tab globProg 0 1).ng == 3
#guard Prog.wf (Prog.tab globProg 0 1) globProg
#guard agrees globProg "gmain" [5] { words := #[#[0]] }
#guard agrees globProg "gmain" [0] { words := #[#[0]] }
#guard (runKraken globProg "gmain" [4] { words := #[#[0]] } 1000).toOption ==
  some (.ok [16, 4, 16, 16, 4, 0, 20, 4, 16])
-- Initial values of the globals come from the memory.
#guard (runKraken globProg "gbump" [1] { glob := fun g => if g = GA then 41 else 0 } 1000).toOption ==
  some (.ok [42, 0, 0, 0, 0, 0, 0, 0, 0])

/-! Records (`R[i].f`, `L/Records.lean`): field stores and reads compile to word-array accesses. -/

#guard agrees L.Examples.nodeProg "node_mk" [2, 0, 7, 9] { words := #[#[], Array.replicate 9 5] }
#guard (runKraken L.Examples.nodeProg "node_mk" [2, 0, 7, 9] { words := #[#[], Array.replicate 9 5] }
  1000).toOption == some (.ok [7, 5, 10])
-- record 3 is past the end: an out-of-bounds store
#guard (runKraken L.Examples.nodeProg "node_mk" [3, 0, 7, 9] { words := #[#[], Array.replicate 9 5] }
  1000).toOption == some .error

/-! Tiered arrays (lane tierarr): tier `t` of word array `W` is `W` or `W + tierOff`. The tier of
a load may be any expression (`W⟨h >> 27⟩`, the handle's tier bit) or a simple one; a store's
tier is simple. -/

/-- Writes `i * 3 + t` to `W⟨t⟩[i]` for `i < n`, then reads both tiers and their lengths. -/
-- con-ron: none — a compiler test program
def tiers : FunDecl := lfn (h, n) locals (t, i, s) {
  t := h >> 27;
  while i < n {
    W⟨t⟩[i] := i * 3 + t;
    i += 1
  };
  W⟨0⟩[0] := W⟨0⟩[0] + 100;
  s := W⟨h >> 27⟩[1] + W⟨t⟩[2] * 10 + len(W⟨t⟩) * 1000 + len(W⟨h⟩) * 100000 + W⟨1 - t⟩[0];
  return s
}

def tierProg : Prog := [("tiers", tiers)]

/-- Array `0` (tier 0 of `W`) has 4 words, array `256` (its tier 1) 6. -/
def tierMem : Mem :=
  { words := ((Array.replicate 257 (#[] : Array Word)).set! 0 (Array.replicate 4 7)).set! 256
      (Array.replicate 6 9) }

#guard Prog.wf { nb := 0, nw := 257 } tierProg
#guard Prog.arrs tierProg == (0, 257)
#guard agrees tierProg "tiers" [0, 3] tierMem
#guard agrees tierProg "tiers" [0x08000000, 3] tierMem
#guard agrees tierProg "tiers" [0x08000000, 6] tierMem
-- out of bounds in tier 0 (4 words), not in tier 1 (6 words)
#guard agrees tierProg "tiers" [0, 5] tierMem
#guard (run tierProg 1000 "tiers" [0, 5] tierMem).toOption.isNone
#guard (run tierProg 1000 "tiers" [0x08000000, 5] tierMem).toOption.isSome

end L.Compiler.Tests
