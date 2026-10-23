module

public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# Growable cons tables: the growth block, generic in the table (lane slotgrow)

con-ron's cons tables are `HashMap2`s (`ron/hashmap2.rs`): `insert_at` writes the new entry and,
past the load threshold, `try_resize` doubles the slot count and rehashes every live entry into
the new table. L's cons tables (`StoreLib.lean`: slot `j` of tier `t` at `sa[2 j + t]`, `0` free,
`B t + i + 1` node `i`) do the same. A tier has `SN0 + G` slots, where `G` is the slot array's last
word (`0` in a fresh array); `X_find` reads it, and `X_push` runs the growth block when the tier it
appended to passes half load.

The growth block (`growBlkG`, in `X_push`) doubles the slot count, capped at the largest multiple of
8 that leaves the slot array's last word clear (aborting when that is no growth), zeroes the old table's slot words (`[0, 2 n)`; the words above them were never
written), and re-registers every node of both tiers: the hash of node `i` (the schema's `hash`
block), its home slot, the first free slot from there (linear probing, as `X_find`), `B t + i + 1`.
The records are dense and are the source: the old slots are not read, so the table grows in place.

The L code is generic in a **growth schema** `GrowSch` (the slot and record arrays, the record
width, the `CTL` index of tier 0's count, the hash block); an instance is a splice
`⟪growBlkG XGS o⟫` in `X_push`, `o` the index of the push's first growth variable.
-/

set_option experimental.vcgen true

namespace L.Arena

/-- FNV-1a offset basis and prime (con-ron's `nat::hash64`). -/
def fnvBasis : Word := 0xcbf29ce484222325
def fnvPrime : Word := 0x100000001b3
/-- The multiply-xor finaliser of con-ron's `home_index` (`ron/hashmap2.rs`). -/
def golden : Word := 0x9e3779b97f4a7c15

/-! ## Words and slots -/

/-- A word of `a`, `0` past its end. -/
def rdW (a : Array Word) (x : Word) : Word := a[x.toNat]?.getD 0

theorem rdW_eq (a : Array Word) (x : Word) (k : Nat) (hk : k = x.toNat) (h : k < a.size) :
    rdW a x = a[k] := by subst hk; simp [rdW, h]
grind_pattern [arena_grind] rdW_eq => rdW a x, a[k]

/-- The home slot of hash `h` among `n`: con-ron's multiply-xor finaliser, then the high word
of the product with `n` (Lemire's range reduction) in place of the power-of-two mask. -/
def homeW (h n : Word) : Word :=
  UInt64.ofNat (((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64)

/-- The `CTL` word of the scratch tier's **slot base** `B` (`scratch_reset` adds `2^32`). A slot of
tier `t` holds `B t + i + 1` for node `i`, with `B 0 = 0` and `B 1 = CTL[62]`; a slot word at or
below the base is free. So the scratch tier is emptied by raising its base: every old slot falls
at or below the new base, and no slot is zeroed. -/
abbrev SCB : Word := 62

/-- The slot base of tier `t` (`t ≤ 1`): `CTL[62] * t`. -/
def baseW (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) SCB * t

/-- A slot word `v` against the base `b`: `0` (free) at or below `b`, else `i + 1`. -/
def slotRd (v b : Word) : Word := if v ≤ b then 0 else v - b

/-- Slot word `k` of `sl` against the base `b`. -/
def slotV (sl : Array Word) (b k : Word) : Word := slotRd (rdW sl k) b

theorem slotV_free (sl : Array Word) (b x : Word) (k : Nat) (hk : k = x.toNat) (h : k < sl.size)
    (hv : sl[k] ≤ b) : slotV sl b x = 0 := by
  simp only [slotV, slotRd, rdW_eq sl x k hk h, hv, ↓reduceIte]

theorem slotV_used (sl : Array Word) (b x : Word) (k : Nat) (hk : k = x.toNat) (h : k < sl.size)
    (hv : ¬ sl[k] ≤ b) : slotV sl b x = sl[k] - b ∧ sl[k] - b ≠ 0 := by
  simp only [slotV, slotRd, rdW_eq sl x k hk h, hv, ↓reduceIte, true_and]
  intro h0
  exact hv (by grind)

/-- The initial slot count of a tier (last word `0`). -/
def SN0 : Word := 8

/-- A growable cons table: slot array `sa`, record array `ra` (`w` words per node and tier, tiers
interleaved), tier `t`'s node count at `CTL[ca + t]`, and `hash`, the block
that sets `h` to the hash of node `i` of tier `t` (FNV-1a over its words, or the hash word the
record stores), written with the variables `(n, k, t, i, c, h)` of `growB`. -/
structure GrowSch where
  sa : ArrId
  ra : ArrId
  w : Word
  ca : Word
  hash : Stmt

/-! ## Shifting local variables

The growth code is a block inside each `X_push` (not a function of its own: a call would add a
callee to every spec that runs a push). It is written once, with its nine variables first, and
spliced into a push with its variables moved past the push's own (`shiftS o`). -/

/-- Expression `e` with every local variable index raised by `o`. -/
def shiftE (o : Nat) : Expr → Expr
  | .var x => .var (x + o)
  | .bin op a b => .bin op (shiftE o a) (shiftE o b)
  | .ld8 a i => .ld8 a (shiftE o i)
  | .ld64 a i => .ld64 a (shiftE o i)
  | .cmpw c a b => .cmpw c (shiftE o a) (shiftE o b)
  | .ldc d i => .ldc d (shiftE o i)
  | e => e

/-- Condition `c` with every local variable index raised by `o`. -/
def shiftC (o : Nat) : Cond → Cond
  | .cmp c a b => .cmp c (shiftE o a) (shiftE o b)
  | .and p q => .and (shiftC o p) (shiftC o q)
  | .or p q => .or (shiftC o p) (shiftC o q)
  | .not p => .not (shiftC o p)

/-- Statement `s` with every local variable index raised by `o`. -/
def shiftS (o : Nat) : Stmt → Stmt
  | .set x e => .set (x + o) (shiftE o e)
  | .st8 a i e => .st8 a (shiftE o i) (shiftE o e)
  | .st64 a i e => .st64 a (shiftE o i) (shiftE o e)
  | .seq s t => .seq (shiftS o s) (shiftS o t)
  | .ite c s t => .ite (shiftC o c) (shiftS o s) (shiftS o t)
  | .while c s => .while (shiftC o c) (shiftS o s)
  | .ret es => .ret (es.map (shiftE o))
  | .call xs f args => .call (xs.map (· + o)) f (args.map (shiftE o))
  | .gset g e => .gset g (shiftE o e)
  | s => s

/-! ## The growth block -/

/-- Zero the slot words `[k, c)`, eight at a time (`c` a multiple of 8). -/
def zeroLoopB (S : GrowSch) : Stmt := lblk (n, k, t, i, c, h, j, b, d) {
  while k < c {
    S.sa.u64[k] := 0; S.sa.u64[k + 1] := 0; S.sa.u64[k + 2] := 0; S.sa.u64[k + 3] := 0;
    S.sa.u64[k + 4] := 0; S.sa.u64[k + 5] := 0; S.sa.u64[k + 6] := 0; S.sa.u64[k + 7] := 0;
    k += 8
  }
}

/-- From slot `j` of tier `t`, the first free slot (aborting after `n` steps). -/
def probeLoopB (S : GrowSch) : Stmt := lblk (n, k, t, i, c, h, j, b, d) {
  while S.sa.u64[j * 2 + t] != 0 {
    if d >= n { abort };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- Register nodes `i, …, c - 1` of tier `t` (slot base `b`) among `n` slots. -/
def nodeLoopB (S : GrowSch) : Stmt := lblk (n, k, t, i, c, h, j, b, d) {
  while i < c {
    ⟪S.hash⟫;
    j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
    d := 0;
    ⟪probeLoopB S⟫;
    S.sa.u64[j * 2 + t] := b + i + 1;
    i += 1
  }
}

/-- Register every node of tiers `t, …, 1`. -/
def tierLoopB (S : GrowSch) : Stmt := lblk (n, k, t, i, c, h, j, b, d) {
  while t < 2 {
    c := CTL.u64[⟪S.ca⟫ + t];
    b := CTL.u64[62] * t;
    i := 0;
    ⟪nodeLoopB S⟫;
    t += 1
  }
}

/-- The growth: double the slot count `n = SN0 + G` (`G` the slot array's last word), but to at
most the largest multiple of 8 that leaves the last word clear, and abort if that is no growth;
zero the old table, register every node again. Variables `0‥8` (`n, k, t, i, c, h, j, b, d`). -/
def growB (S : GrowSch) : Stmt := lblk (n, k, t, i, c, h, j, b, d) {
  k := S.sa.u64[len(S.sa.u64) - 1] + ⟪SN0⟫;
  n := k * 2;
  c := ((len(S.sa.u64) - 1) >> 4) << 3;
  if c < n { n := c };
  if n <= k { abort };
  S.sa.u64[len(S.sa.u64) - 1] := n - ⟪SN0⟫;
  c := k * 2;
  k := 0;
  ⟪zeroLoopB S⟫;
  t := 0;
  ⟪tierLoopB S⟫
}

/-- con-ron: none — the cons table's growth (the twin's `HashMap2::try_resize`, `ron/hashmap2.rs`,
below the arena model's `Std.HashMap`), spliced into `X_push` with its variables from `o` on. -/
def growBlkG (S : GrowSch) (o : Nat) : Stmt := shiftS o (growB S)

end L.Arena
