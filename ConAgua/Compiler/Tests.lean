module

public import ConAgua.Compiler.Run
public import ConAgua.Compiler.WF
meta import ConAgua.Compiler.WF
public import ConAgua.L.Notation
public import ConAgua.L.Examples
meta import ConAgua.Compiler.Run
meta import ConAgua.L.Examples

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
  (runKraken p f args m fuel.toUInt64 stack).toOption == some (Outcome.ofL (run p fuel f args m))

def inp (s : String) : Mem := { bytes := #[s.toUTF8.data] }

/-! `skip_braced` and `str_close` (`L/Examples.lean`). -/

-- The compiler theorem applies: the program is well formed for one byte array.
#guard Prog.wf { nb := 1, nw := 0 } scanProg

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
#guard Outcome.ofL (run scanProg 3 "skip_braced" [1, 0] (inp "{aaaaaaaaaa}")) == .exhausted

/-! Word arrays, stores, arithmetic, signed comparisons, recursion, `break`, `abort`. -/

def W : ArrId := 0
def B : ArrId := 0

/-- Sums `W.u64[0..n)` into `W.u64[n]`, doubles every byte of `B`, mixes some arithmetic. -/
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

def sumTo : FunDecl := lfn (n) locals (r) {
  if n == 0 { return 0 };
  r := call sum_to(n - 1);
  return r + n
}

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
-- A small stack: a call of `sum_to` takes 32 bytes (a 3-word frame and the return address), and
-- the stack check also reserves the next return address: 128 bytes hold three calls, not four.
#guard agrees recProg "sum_to" [2] {} 100000 128
#guard (runKraken recProg "sum_to" [3] {} 100000 128).toOption == some .exhausted

/-! `mulhi`, comparisons as words, constant data. -/

def LITS : List UInt8 := "truefalse".toUTF8.toList

/-- `mulhi(x, y)`, the carry of `x + y`, and whether `IN[i..]` starts with `"false"`. -/
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
-- `LITS.c8[9]` is out of bounds.
def oobC : FunDecl := lfn (i) { return LITS.c8[i] }
#guard agrees [("c", oobC)] "c" [8] {}
#guard (runKraken [("c", oobC)] "c" [9] {} 100000).toOption == some .error

/-! Several results. -/

/-- The 128-bit product, the carry of a sum, and a third value. -/
def wide : FunDecl := lfn (x, y) {
  return (x * y, mulhi(x, y), u64(x + y < x))
}

/-- Returns one value: a caller reading three gets `0` for the other two. -/
def one : FunDecl := lfn (x) { return x + 1 }

/-- Returns nothing (falls off the end). -/
def none' : FunDecl := lfn (x) { skip }

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
#guard (run wideProg 100 "wide" [0xffffffffffffffff, 2] {}).toOption.map (·.1) ==
  some [0xfffffffffffffffe, 1, 1]

end L.Compiler.Tests
