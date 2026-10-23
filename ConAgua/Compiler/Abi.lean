module

public import ConAgua.Compiler.Run

@[expose] public section

/-!
# The entry stub: `ca_start(in, in_len, pins, pins_len, base, base_len)` (lane `abi`, prototype)

The harness's whole job shrinks to: map a zero region, hand over the two input buffers, call once.
The stub, emitted before the trampoline, sets up inside the region everything the harness used to
lay out (`L.Compiler.Tab`), then tail-jumps into the trampoline `ca_enter(T, fuel)`:

* System V arguments: `rdi`/`rsi` = the input bytes (byte array `0`), `rdx`/`rcx` = the pin-data
  bytes (byte array `1`; ignored if the program has one byte array), `r8` = `base`, `r9` =
  `base_len`. Returns `rax`/`rdx` as `ca_enter` does.
* If `base_len < abiNeed`, it returns at once with `rdx = 1` (resources exhausted; never accept).
* The region is a static partition into `abiSlot`-byte slots (no allocator; the pages that are
  never touched never become real): slot `0` is the table (`T = base`), slot `1` the L stack
  (`abiStack` bytes at its bottom), then one slot per byte array `2, …, nb - 1` and per word array.
  Each array starts at its slot's start; its length is `abiSlot` bytes, resp. `abiWords a` words.
* The constant data is written into the table by immediate stores (no `.rodata` read); the result
  area and the global variables are the region's zeros.
* The fuel is `2^62 - 1` (`checker_x64_accepts` takes any `N < 2^62`).

Nothing here is trusted: the stub's job is to establish `Layout.Ok`/`MemRel` (the proof, later). -/

namespace L.Compiler

/-- The slot size: `2^35` bytes (`2^32` words). -/
def abiSlot : Nat := 2 ^ 35
/-- The L stack: `2^30` bytes (the old harness's default `CA_STACK`). -/
def abiStack : Nat := 2 ^ 30
/-- The fuel the stub passes to the trampoline. -/
def abiFuel : Nat := 2 ^ 62 - 1

/-- The slot of byte array `a ≥ 2`. -/
def abiSlot8 (a : Nat) : Nat := a
/-- The slot of word array `a`. -/
def abiSlot64 (tab : Tab) (a : Nat) : Nat := 2 + (tab.nb - 2) + a
/-- The region size the stub needs. -/
def abiNeed (tab : Tab) : Nat := abiSlot * (2 + (tab.nb - 2) + tab.nw)

/-- The little-endian words of `rom`, padded with zeros. -/
def romWordList : List UInt8 → List Word
  | [] => []
  | b :: bs => ((List.range 8).foldr (fun i acc => (acc <<< 8) ||| ((b :: bs).getD i 0).toUInt64) 0) ::
      romWordList (bs.drop 7)
termination_by bs => bs.length
decreasing_by simp; omega

/-- `[r8 + d] := w` (through `rax`). -/
def abiStoreW (d : Nat) (w : Word) : Program := [movRI .rax w, movMR (mb .r8 d) .rax]
/-- `[r8 + d] := r8 + off`. -/
def abiStoreA (d off : Nat) : Program :=
  [movRI .rax off.toUInt64, i64 (.add (.reg (rr .rax)) (oR .r8)), movMR (mb .r8 d) .rax]

def abiDeclineL : Label := "ca_abi_decline"
def abiStartL : Label := "ca_start"

/-- The stub, for the table `tab` and word-array lengths `words`. -/
def abiStub (tab : Tab) (words : Nat → Nat) : Program :=
  [.label abiStartL,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiDeclineL,
   movMR (mb .r8 (tab.base8 0)) .rdi, movMR (mb .r8 (tab.len8 0)) .rsi] ++
  (if 2 ≤ tab.nb then [movMR (mb .r8 (tab.base8 1)) .rdx, movMR (mb .r8 (tab.len8 1)) .rcx] else []) ++
  abiStoreA Tab.stackTop.toNat (abiSlot + abiStack) ++ abiStoreA Tab.stackLimit.toNat abiSlot ++
  ((List.range tab.nb).drop 2).flatMap (fun a =>
    abiStoreA (tab.base8 a).toNat (abiSlot * abiSlot8 a) ++ abiStoreW (tab.len8 a).toNat abiSlot.toUInt64) ++
  (List.range tab.nw).flatMap (fun a =>
    abiStoreA (tab.base64 a).toNat (abiSlot * abiSlot64 tab a) ++
      abiStoreW (tab.len64 a).toNat (words a).toUInt64) ++
  ((romWordList tab.rom).zipIdx.flatMap fun (w, i) => abiStoreW (tab.romBase.toNat + 8 * i) w) ++
  [movRR .rdi .r8, movRI .rsi abiFuel.toUInt64, jmpL enterL,
   .label abiDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-! ## Word-array lengths

`abiWords` gives every word array its whole slot, `2^32` words. Until lane slotgrow lands, the
intern slot tables still span their whole array (`n := len64 a >>> 1`, and a random insert touches
a fresh page), so those get `abiSlotTableWords`; they are found in the program as the arrays whose
length it reads as `len64 a >>> 1`. -/

def abiSlotTableWords : Nat := 2 ^ 25

def Expr.halfLen : Expr → List ArrId
  | .bin .shr (.len64 a) (.const 1) => [a]
  | .bin _ x y | .cmpw _ x y => Expr.halfLen x ++ Expr.halfLen y
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.halfLen i
  | _ => []

def Cond.halfLen : Cond → List ArrId
  | .cmp _ x y => Expr.halfLen x ++ Expr.halfLen y
  | .and p q | .or p q => Cond.halfLen p ++ Cond.halfLen q
  | .not p => Cond.halfLen p

def Stmt.halfLen : Stmt → List ArrId
  | .set _ e | .gset _ e => Expr.halfLen e
  | .st8 _ i e | .st64 _ i e => Expr.halfLen i ++ Expr.halfLen e
  | .seq s t => Stmt.halfLen s ++ Stmt.halfLen t
  | .ite c s t => Cond.halfLen c ++ Stmt.halfLen s ++ Stmt.halfLen t
  | .while c s => Cond.halfLen c ++ Stmt.halfLen s
  | .ret es | .call _ _ es => es.flatMap Expr.halfLen
  | _ => []

/-- The word-array lengths for program `p`. -/
def abiWords (p : Prog) (slotWords : Nat := abiSlotTableWords) : Nat → Nat :=
  let half := p.flatMap fun (_, fd) => Stmt.halfLen fd.body
  fun a => if half.contains a then slotWords else 2 ^ 32

/-- The stub's symbols for the harness: `ca_region_size` (the least `base_len`), `ca_slot` and
`ca_w0` (the offset of word array `0`; for diagnostics). -/
def abiSymbols (tab : Tab) : String :=
  s!".section .rodata\n.globl ca_region_size\n.globl ca_slot\n.globl ca_w0\nca_region_size: .quad {abiNeed tab}\nca_slot: .quad {abiSlot}\nca_w0: .quad {abiSlot * abiSlot64 tab 0}\n"

/-- The assembler file: the stub, then `code` (the trampoline and the functions), as `asmTextOf`. -/
def asmTextAbi (tab : Tab) (words : Nat → Nat) (code : Program) : String :=
  ".text\n.globl " ++ abiStartL ++ "\n" ++ asmTextOf tab (abiStub tab words ++ code) ++ abiSymbols tab

end L.Compiler
