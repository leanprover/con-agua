module

meta import ConAgua.Compiler.WF
meta import ConAgua.L.Arrays
meta import ConAguaX86.Compiler.Run
meta import ConAgua.L.Examples
meta import ConAgua.Scan.Lit
meta import ConAgua.Scan.Utf8
import ConAguaX86.Compiler.Run
import ConAgua.L.Notation
import ConAgua.Layout
/-!
# Differential tests: compiled code on Kraken's semantics against `L.run`

`agrees p f args m` runs `f` both ways with plenty of fuel and stack and compares the outcomes.
The x64 fuel counter counts every loop iteration and call, `L`'s fuel only their nesting, so with
little fuel the compiled code may run out where `L` does not (never the other way round); the
`exhausted` tests check the direction that matters.
-/

open L L.Compiler L.Examples

namespace L.Compiler.Tests

/-- `runKraken` on the table of the arrays `p` names (`Prog.tab`). -/
def rk (p : Prog) (f : FnName) (args : List Word) (m : Mem) (fuel : Word) (stack : Nat := 4096) :
    Except String Outcome :=
  runKraken p f args m fuel stack

def agrees (p : Prog) (f : FnName) (args : List Word) (m : Mem) (fuel : Nat := 100000)
    (stack : Nat := 4096) : Bool :=
  (rk p f args m fuel.toUInt64 stack).toOption ==
    some (Outcome.ofL (Prog.tab p).nres (run p fuel f args m))

def inp (s : String) : Mem := Mem.ofBytes [(IN, s.toUTF8.data)]

/-! `skip_braced` and `str_close` (`L/Examples.lean`). -/

-- The compiler theorem applies: the program is well formed for one byte array.
#guard Prog.wf (Prog.tab scanProg) scanProg

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
#guard (rk scanProg "skip_braced" [1, 0] (inp "{aaaaaaaaaa}") 3).toOption == some .exhausted
#guard Outcome.ofL 1 (run scanProg 3 "skip_braced" [1, 0] (inp "{aaaaaaaaaa}")) == .exhausted

/-! Word arrays, stores, arithmetic, signed comparisons, recursion, `break`, `abort`. -/

def W : ArrId := 0
def B : ArrId := IN

/-- Sums `W.u64[0..n)` into `W.u64[n]`, doubles every byte of `B`, mixes some arithmetic. -/
-- con-ron: none — a compiler test program
@[no_expose] def mix : FunDecl := lfn (n) locals (i, s, t) {
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

def mixMem : Mem := (Mem.ofWords [(W, #[5, 0xffffffffffffff00, 7, 0])]).putBytes B #[1, 2, 3, 200]

#guard agrees [("mix", mix)] "mix" [3] mixMem
-- Out of bounds: `W.u64[4]` does not exist.
#guard agrees [("mix", mix)] "mix" [4] mixMem
#guard (rk [("mix", mix)] "mix" [4] mixMem 100000).toOption == some .error

/-- con-ron: none — a compiler test program -/
@[no_expose] def sumTo : FunDecl := lfn (n) locals (r) {
  if n == 0 { return 0 };
  r := call sum_to(n - 1);
  return r + n
}

/-- con-ron: none — a compiler test program -/
@[no_expose] def boom : FunDecl := lfn (n) {
  if n == 7 { abort };
  return n
}

def recProg : Prog := [("sum_to", sumTo), ("boom", boom)]

#guard Prog.wf (Prog.tab recProg) recProg
#guard Prog.wf (Prog.tab [("mix", mix)]) [("mix", mix)]

#guard agrees recProg "sum_to" [100] {}
#guard agrees recProg "boom" [7] {}
#guard agrees recProg "boom" [8] {}
-- A small stack: a call of `sum_to` takes 24 bytes (a 2-word frame and the return address), and
-- the stack check also reserves the next return address: 128 bytes hold five calls, not six.
#guard agrees recProg "sum_to" [4] {} 100000 128
#guard (rk recProg "sum_to" [5] {} 100000 128).toOption == some .exhausted

/-! `mulhi`, comparisons as words, constant data. -/

def LITS : List UInt8 := "truefalse".toUTF8.toList

/-- `mulhi(x, y)`, the carry of `x + y`, and whether `IN[i..]` starts with `"false"`. -/
-- con-ron: none — a compiler test program
@[no_expose] def ext : FunDecl := lfn (x, y, i) locals (k, ok) {
  ok := 1;
  while k < 5 {
    if i + k >= len(B.u8) { ok := 0; break };
    if B.u8[i + k] != LITS.c8[k + 4] { ok := 0 };
    k += 1
  };
  return mulhi(x, y) ^ (u64(x + y < x) << 32) ^ (ok << 40) ^ u64(x ≤ₛ y) << 41
}

def extProg : Prog := [("ext", ext)]

#guard Prog.wf (Prog.tab extProg) extProg
#guard Prog.rom extProg = LITS
#guard agrees extProg "ext" [0xffffffffffffffff, 0xffffffffffffffff, 0] (inp "false")
#guard agrees extProg "ext" [0x123456789abcdef0, 0x0fedcba987654321, 1] (inp " false")
#guard agrees extProg "ext" [3, 5, 1] (inp " fals")
#guard agrees extProg "ext" [0x8000000000000000, 5, 0] (inp "falsy")
/-- con-ron: none — a compiler test program -/
-- `LITS.c8[9]` is out of bounds.
@[no_expose] def oobC : FunDecl := lfn (i) { return LITS.c8[i] }
#guard agrees [("c", oobC)] "c" [8] {}
#guard (rk [("c", oobC)] "c" [9] {} 100000).toOption == some .error

/-! Several results. -/

/-- The 128-bit product, the carry of a sum, and a third value. -/
-- con-ron: none — a compiler test program
@[no_expose] def wide : FunDecl := lfn (x, y) {
  return (x * y, mulhi(x, y), u64(x + y < x))
}

/-- Returns one value: a caller reading three gets `0` for the other two. -/
-- con-ron: none — a compiler test program
@[no_expose] def one : FunDecl := lfn (x) { return x + 1 }

/-- Returns nothing (falls off the end). -/
-- con-ron: none — a compiler test program
@[no_expose] def none' : FunDecl := lfn (x) { skip }

/-- con-ron: none — a compiler test program -/
@[no_expose] def useWide : FunDecl := lfn (x, y) locals (lo, hi, c, a, b, z) {
  (lo, hi, c) := call wide(x, y);
  (a, b, z) := call one(lo);
  (b, z) := call none'(a);
  (hi, hi) := call wide(hi, 3);
  return lo ^ (hi << 1) ^ (c << 60) ^ a ^ b ^ z
}

def wideProg : Prog := [("use", useWide), ("wide", wide), ("one", one), ("none'", none')]

#guard (Prog.tab wideProg).nres = 3
#guard Prog.wf (Prog.tab wideProg) wideProg
#guard agrees wideProg "use" [0xffffffffffffffff, 0xfffffffffffffff0] {}
#guard agrees wideProg "use" [12345, 678910] {}
#guard agrees wideProg "wide" [0xffffffffffffffff, 0xfffffffffffffff0] {}
#guard agrees wideProg "one" [41] {}
#guard agrees wideProg "none'" [41] {}
#guard (rk wideProg "wide" [0xffffffffffffffff, 2] {} 1000).toOption == some (.ok [0xfffffffffffffffe, 1, 1])
#guard (run wideProg 100 "wide" [0xffffffffffffffff, 2] {}).toOption.map (·.1) ==
  some [0xfffffffffffffffe, 1, 1]

/-! More results than registers (lane `cresults`): results 6, 7, 8 go through the table's result
area. -/

/-- con-ron: none — a compiler test program -/
@[no_expose] def nine : FunDecl := lfn (x) {
  return (x, x + 1, x + 2, x + 3, x + 4, x + 5, x + 6, x + 7, x + 8)
}

/-- Returns seven of nine: the caller reads `0` for results 7 and 8. -/
-- con-ron: none — a compiler test program
@[no_expose] def seven : FunDecl := lfn (x) {
  return (x, x * 2, x * 3, x * 4, x * 5, x * 6, x * 7)
}

/-- con-ron: none — a compiler test program -/
@[no_expose] def useNine : FunDecl := lfn (x) locals (a, b, c, d, e, f, g, h, i, z) {
  (a, b, c, d, e, f, g, h, i) := call nine(x);
  z := a ^ (b << 4) ^ (c << 8) ^ (d << 12) ^ (e << 16) ^ (f << 20) ^ (g << 24) ^ (h << 28) ^ (i << 32);
  (a, b, c, d, e, f, g, h, i) := call seven(i);
  (b, i) := call nine(z);
  return (z, a, b, c, d, e, f, g, h, i)
}

def nineProg : Prog := [("use", useNine), ("nine", nine), ("seven", seven)]

#guard (Prog.tab nineProg).nres = 10
#guard Prog.wf (Prog.tab nineProg) nineProg
#guard agrees nineProg "use" [5] {}
#guard agrees nineProg "use" [0xfffffffffffffff0] {}
#guard agrees nineProg "nine" [7] {}
#guard agrees nineProg "seven" [7] {}
#guard (rk nineProg "nine" [7] {} 1000).toOption == some (.ok [7, 8, 9, 10, 11, 12, 13, 14, 15, 0])

/-! `match_lit`/`scan_bool` (`Scan/Lit.lean`): constant data and three results. -/

open L.Scan.Lit in
#guard Prog.wf (Prog.tab litProg) litProg
open L.Scan.Lit in
#guard [" true", "false", "fals", "", "falsetto", "tru"].all fun t =>
  [0, 1].all fun i => agrees litProg "scan_bool" [i] (inp t)

/-! `utf8_decode` (`Scan/Utf8.lean`): two results, stores into a word array. -/

open L.Scan.Utf8 in
#guard Prog.wf (Prog.tab utf8Prog) utf8Prog
open L.Scan.Utf8 in
#guard [[], "plain ascii".toUTF8.toList, [0xC3, 0xA9], [0xE2, 0x86, 0x92], [0xF0, 0x9F, 0x98, 0x80],
    [0x80], [0xC0, 0x80], [0xE0, 0x80, 0x80], [0xED, 0xA0, 0x80], [0xF4, 0x90, 0x80, 0x80],
    [0xF5, 0x80, 0x80, 0x80], [0xE2, 0x86], [0x41, 0xC3, 0xA9, 0x42]].all fun (bs : List UInt8) =>
  agrees utf8Prog "utf8_decode" [0, UInt64.ofNat bs.length]
    ((Mem.ofWords [(L.Scan.Utf8.OUT, Array.replicate 16 0)]).putBytes IN bs.toArray)
-- `OUT` too small: an out-of-bounds store.
open L.Scan.Utf8 in
#guard (rk utf8Prog "utf8_decode" [0, 5] ((Mem.ofWords [(OUT, #[0, 0])]).putBytes IN "hello".toUTF8.data)
  100000).toOption == some .error

/-! Global variables (`GVar`): reads, writes, `+=`, across calls and in conditions, next to
arrays, the result area (nine results) and entry arguments. -/

abbrev GA : GVar := ⟨0⟩
abbrev GB : GVar := ⟨2⟩

/-- con-ron: none — a compiler test program -/
@[no_expose] def gbump : FunDecl := lfn (x) { GA += x; GB := GB + 1; return GA }
/-- con-ron: none — a compiler test program -/
@[no_expose] def gmain : FunDecl := lfn (n) locals (i, r) {
  GA := 10;
  while i < n { r := call gbump(i); i += 1 };
  if GB == n { W.u64[0] := GA };
  return (GA, GB, r, W.u64[0], n, 0, GA + GB, GB, GA)
}
def globProg : Prog := [("gmain", gmain), ("gbump", gbump)]

#guard (Prog.tab globProg).ng == 3
#guard Prog.wf (Prog.tab globProg) globProg
#guard agrees globProg "gmain" [5] (Mem.ofWords [(W, #[0])])
#guard agrees globProg "gmain" [0] (Mem.ofWords [(W, #[0])])
#guard (rk globProg "gmain" [4] (Mem.ofWords [(W, #[0])]) 1000).toOption ==
  some (.ok [16, 4, 16, 16, 4, 0, 20, 4, 16])
-- Initial values of the globals come from the memory.
#guard (rk globProg "gbump" [1] { glob := fun g => if g = GA then 41 else 0 } 1000).toOption ==
  some (.ok [42, 0, 0, 0, 0, 0, 0, 0, 0])

/-! Records (`R[i].f`, `L/Records.lean`): field stores and reads compile to word-array accesses. -/

#guard agrees L.Examples.nodeProg "node_mk" [2, 0, 7, 9] (Mem.ofWords [(NODE.arr, Array.replicate 9 5)])
#guard (rk L.Examples.nodeProg "node_mk" [2, 0, 7, 9] (Mem.ofWords [(NODE.arr, Array.replicate 9 5)])
  1000).toOption == some (.ok [7, 5, 10])
-- record 3 is past the end: an out-of-bounds store
#guard (rk L.Examples.nodeProg "node_mk" [3, 0, 7, 9] (Mem.ofWords [(NODE.arr, Array.replicate 9 5)])
  1000).toOption == some .error

/-! Tiered arrays (lane tierarr): tier `t` of word array `W` is `↑W` or `tier1 W`. The tier of
a load may be any expression (`W⟨h >> 27⟩`, the handle's tier bit) or a simple one; a store's
tier is simple. -/

/-- Writes `i * 3 + t` to `W⟨t⟩[i]` for `i < n`, then reads both tiers and their lengths. -/
-- con-ron: none — a compiler test program
@[no_expose] def tiers : FunDecl := lfn (h, n) locals (t, i, s) {
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

/-- Tier 0 of `W` has 4 words, its tier 1 has 6. -/
def tierMem : Mem :=
  Mem.ofWords [(W, Array.replicate 4 7), (tier1 W, Array.replicate 6 9)]

#guard Prog.wf (Prog.tab tierProg) tierProg
#guard (Prog.tab tierProg).nw == 2
#guard agrees tierProg "tiers" [0, 3] tierMem
#guard agrees tierProg "tiers" [0x08000000, 3] tierMem
#guard agrees tierProg "tiers" [0x08000000, 6] tierMem
-- out of bounds in tier 0 (4 words), not in tier 1 (6 words)
#guard agrees tierProg "tiers" [0, 5] tierMem
#guard (run tierProg 1000 "tiers" [0, 5] tierMem).toOption.isNone
#guard (run tierProg 1000 "tiers" [0x08000000, 5] tierMem).toOption.isSome

/-! The array table's surface check (`ArrTable.progOK`, `L/Arrays.lean`) on `tierProg`: with `W`
declared tiered it accepts; with `W` not tiered the tiered accesses are rejected; two word arrays
with the same number are not a well-formed table. -/

def tierTab : ArrTable := [{ name := "W", id := W, kind := .word, tiered := true }]

#guard tierTab.wf
#guard tierTab.progOK tierProg
#guard !ArrTable.progOK [{ name := "W", id := W, kind := .word, tiered := false }] tierProg
#guard !ArrTable.wf (tierTab ++ [{ name := "V", id := W, kind := .word, tiered := false }])

/-! Packed 32-bit elements (lane p32): element `i` of a word array is half `i % 2` of word `i / 2`,
the low half first; a store writes the low 32 bits and keeps the other half; an index whose word
does not exist is out of bounds. -/

/-- con-ron: none — a compiler test program

Writes `i * 65537 + t + 2^40 (i + 1)` (the high bits dropped) to `W⟨t⟩.u32[i]` for `i < n`, then
reads elements back (a loop-carried index, a computed tier, a computed index) and a whole word. -/
@[no_expose] def p32 : FunDecl := lfn (h, n) locals (t, i, s, x) {
  t := (h >> 27) & 1;
  i := 0;
  while i < n {
    W⟨t⟩.u32[i] := i * 65537 + t + (i + 1) * 1099511627776;
    i := i + 1
  };
  W⟨0⟩.u32[1] := W⟨0⟩.u32[1] + 4294967295;
  x := W⟨h >> 27⟩.u32[n - 1];
  s := x + W⟨t⟩.u32[n >> 1] * 1000 + W⟨t⟩[0] * 7 + W⟨1 - t⟩.u32[(n + 1) & 3];
  return s
}

def p32Prog : Prog := [("p32", p32)]

#guard Prog.wf (Prog.tab p32Prog) p32Prog
#guard agrees p32Prog "p32" [0, 3] tierMem
#guard agrees p32Prog "p32" [0, 8] tierMem
#guard agrees p32Prog "p32" [0x08000000, 12] tierMem
-- element 8 needs word 4: out of bounds in tier 0 (4 words), not in tier 1 (6 words)
#guard agrees p32Prog "p32" [0, 9] tierMem
#guard (run p32Prog 1000 "p32" [0, 9] tierMem).toOption.isNone
#guard (run p32Prog 1000 "p32" [0x08000000, 9] tierMem).toOption.isSome
-- the halves of word 0 of tier 0 after `n = 2`: element 0 low, element 1 high
#guard (run p32Prog 1000 "p32" [0, 2] tierMem).toOption.map (fun (_, m) => (m.arr64 W)[0]!) ==
  some ((65537 + 4294967295) % 4294967296 * 4294967296)

/-! One half of a word (`Expr.ld32h`, lane p32use, the packed records' fields): the bounds check of
a word load, then the 4-byte load of the low or the high half. -/

/-- con-ron: none — a compiler test program

`lo + 1000 hi` of word `i` of tier `t` of `W`, each half by its own 32-bit load (the register
stack's code and, under a call's argument, the fallback's). -/
@[no_expose] def p32h : FunDecl :=
  { nparams := 2, nlocals := 3,
    body := .seq (.set 2 (.bin .add (.ld32h W (.var 0) (.var 1) false)
        (.bin .mul (.ld32h W (.var 0) (.var 1) true) (.const 1000))))
      (.ret [.var 2]) }

def p32hProg : Prog := [("p32h", p32h)]

/-- Words with distinct halves. -/
def halfMem : Mem :=
  Mem.ofWords [(W, #[0x0000000500000003, 0x00000011FFFFFFFF]), (tier1 W, #[0x0000000700000002])]

#guard Prog.wf (Prog.tab p32hProg) p32hProg
#guard agrees p32hProg "p32h" [0, 0] halfMem
#guard agrees p32hProg "p32h" [0, 1] halfMem
#guard agrees p32hProg "p32h" [1, 0] halfMem
-- word 1 exists in tier 0 only
#guard agrees p32hProg "p32h" [1, 1] halfMem
#guard (run p32hProg 1000 "p32h" [0, 0] halfMem).toOption.map (·.1) == some [5003]

end L.Compiler.Tests
