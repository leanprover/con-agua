module

public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# Growable cons tables: `X_grow()`, generic in the table (lane slotgrow)

con-ron's cons tables are `HashMap2`s (`ron/hashmap2.rs`): `insert_at` writes the new entry and,
past the load threshold, `try_resize` doubles the slot count and rehashes every live entry into
the new table. L's cons tables (`StoreLib.lean`: slot `j` of tier `t` at `sa[2 j + t]`, `0` free,
`B t + i + 1` node `i`) do the same. A tier has `SN0 << G` slots, where `G`, the **growth
exponent**, is the slot array's last word (`0` in a fresh array); `X_find` reads it, and `X_push`
calls `X_grow()` when the tier it appended to passes half load.

`X_grow()` doubles the slot count (`G += 1`, aborting when the new table and the last word do not
fit the slot array), zeroes the old table's slot words (`[0, 2 n)`; the words above them were never
written), and re-registers every node of both tiers: the hash of node `i` (the schema's `hash`
block), its home slot, the first free slot from there (linear probing, as `X_find`), `B t + i + 1`.
The records are dense and are the source: the old slots are not read, so the table grows in place.

The L code is generic in a **growth schema** `GrowSch` (the slot and record arrays, the record
width, the `CTL` index of tier 0's count, the hash block); an instance is one program entry
`("X_grow", slotGrowG XGS)`.
-/

set_option experimental.vcgen true

namespace L.Arena

/-- FNV-1a offset basis and prime (con-ron's `nat::hash64`). -/
def fnvBasis : Word := 0xcbf29ce484222325
def fnvPrime : Word := 0x100000001b3
/-- The multiply-xor finaliser of con-ron's `home_index` (`ron/hashmap2.rs`). -/
def golden : Word := 0x9e3779b97f4a7c15

/-- The initial slot count of a tier (`G = 0`). -/
def SN0 : Word := 8

/-- A growable cons table: slot array `sa`, record array `ra` (`w` words per node and tier, tiers
interleaved), tier `t`'s node count at `CTL[ca + t]`, and `hash`, the block
that sets `h` to the hash of node `i` of tier `t` (FNV-1a over its words, or the hash word the
record stores), written with the variables `(n, k, t, i, c, h)` of `slotGrowG`. -/
structure GrowSch where
  sa : ArrId
  ra : ArrId
  w : Word
  ca : Word
  hash : Stmt

/-- con-ron: none — the cons table's growth (the twin's `HashMap2::try_resize`, `ron/hashmap2.rs`,
below the arena model's `Std.HashMap`) -/
def slotGrowG (S : GrowSch) : FunDecl := lfn () locals (n, k, t, i, c, h, j, b, d) {
  k := S.sa.u64[len(S.sa.u64) - 1];
  n := (⟪SN0⟫ << k) * 2;
  if (len(S.sa.u64) - 1) >> 1 < n { abort };
  S.sa.u64[len(S.sa.u64) - 1] := k + 1;
  k := 0;
  while k < n {
    S.sa.u64[k] := 0; S.sa.u64[k + 1] := 0; S.sa.u64[k + 2] := 0; S.sa.u64[k + 3] := 0;
    S.sa.u64[k + 4] := 0; S.sa.u64[k + 5] := 0; S.sa.u64[k + 6] := 0; S.sa.u64[k + 7] := 0;
    k += 8
  };
  t := 0;
  while t < 2 {
    c := CTL.u64[⟪S.ca⟫ + t];
    b := CTL.u64[62] * t;
    i := 0;
    while i < c {
      ⟪S.hash⟫;
      j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
      d := 0;
      while S.sa.u64[j * 2 + t] != 0 {
        if d >= n { abort };
        j := (j + 1) * u64(j + 1 < n);
        d += 1
      };
      S.sa.u64[j * 2 + t] := b + i + 1;
      i += 1
    };
    t += 1
  };
  return 0
}

end L.Arena
