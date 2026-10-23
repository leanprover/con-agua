module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The name store's `num` node store in L: a prefix handle and a `Nat` field per node

The arena's name store keeps `num pre n` nodes in a `Tbl NumNode NIdx UInt64` per tier
(`vendor/con-ron/ConRon/Arena/Store.lean:119`, `NTables.nums`). Its L representation is the
`max` store's (`MaxStore.lean`) two-word shape, but the second field is the `Nat` itself (as
`bvar` stores its index, `BVarStore.lean`), not a handle:

* **Records.** Word array `NNREC`, two words per node: the prefix's handle word, then the number
  as a word. Tiers interleaved: node `i` of tier `t` at `NNREC[4 i + 2 t ..]`. The node count of
  tier `t` is `CTL[38 + t]`.
* **Cons table.** Word array `NNSLOT`, the same open addressing as `SLOT`/`MSLOT`.

A `num` node has one child (its prefix), but the name store's `NStore.find?` probes the persistent
tier unconditionally (no scratch skip), as the level store's `LStore.find?` does.

The functions: `nnum_find(t, pre, u, h)`, `nnum_push(t, pre, u, j)` and `intern_nnum(pre, u)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `num` records, both tiers interleaved (two words per node). -/
abbrev NNREC : ArrId := 37
/-- The `num` cons-table slots, both tiers interleaved. -/
abbrev NNSLOT : ArrId := 38

/-- The growth schema of this table (`SlotGrow.lean`). -/
def nnumGS : GrowSch :=
  ⟨NNSLOT, NNREC, 2, 38, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ NNREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ NNREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of a `num` record (FNV-1a over its two words). -/
def nnumHashW (pre u : Word) : Word := ((fnvBasis ^^^ pre) * fnvPrime ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(pre, u)`. -/
def nnmatchW (r : Array Word) (t i pre u : Word) : Bool :=
  rdW r (i * 4 + t * 2) == pre && rdW r (i * 4 + t * 2 + 1) == u

/-! ## `nnum_find(t, pre, u, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `nnmatchW`). -/
def nnprobeW (sl r : Array Word) (t pre u b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if nnmatchW r t (slotV sl b (j * 2 + t) - 1) pre u then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else nnprobeW sl r t pre u b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t pre u b n j d : Word)

theorem nnprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : nnprobeW sl r t pre u b n j d = [0, 0, j, d] := by
  rw [nnprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem nnprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : nnmatchW r t (sl[k] - b - 1) pre u = true) :
    nnprobeW sl r t pre u b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [nnprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem nnprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : nnmatchW r t (sl[k] - b - 1) pre u = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    nnprobeW sl r t pre u b n j d = nnprobeW sl r t pre u b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [nnprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] nnprobeW_free => nnprobeW sl r t pre u b n j d, sl[k]
grind_pattern [arena_grind] nnprobeW_hit => nnprobeW sl r t pre u b n j d, sl[k]
grind_pattern [arena_grind] nnprobeW_next =>
  nnprobeW sl r t pre u b n j d, sl[k], nnprobeW sl r t pre u b n j' d'

def nnfindLoop : Stmt := lblk (t, pre, u, h, n, j, d, w, b) {
  while d < n {
    w := NNSLOT.u64[j * 2 + t];
    if w <= b { return (0, 0, j, d) };
    w := w - b;
    if NNREC.u64[(w - 1) * 4 + t * 2] == pre && NNREC.u64[(w - 1) * 4 + t * 2 + 1] == u {
      return (1, w - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def nnumFind : FunDecl := lfn (t, pre, u, h) locals (n, j, d, w, b) {
  n := ⟪SN0⟫ << NNSLOT.u64[len(NNSLOT.u64) - 1];
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪nnfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "nnum_find" = some nnumFind)

theorem nnfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n nnfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (nnprobeW (s₀.mem.arr64 NNSLOT) (s₀.mem.arr64 NNREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      nnprobeW (s₀.mem.arr64 NNSLOT) (s₀.mem.arr64 NNREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := nnfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [nnmatchW, baseW]

theorem nnfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) nnfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (nnprobeW (s₀.mem.arr64 NNSLOT) (s₀.mem.arr64 NNREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      nnprobeW (s₀.mem.arr64 NNSLOT) (s₀.mem.arr64 NNREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (nnfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `num` table. -/
def nSlotsNN (m : Mem) : Word := SN0 <<< rdW (m.arr64 NNSLOT) (m.len64 NNSLOT - 1)

include hp in
theorem nnumFind_spec (n : Nat) (s₀ : St) (t pre u h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nnum_find" [t, pre, u, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = nnprobeW (s₀.mem.arr64 NNSLOT) (s₀.mem.arr64 NNREC) t pre u
        (baseW s₀.mem t) (nSlotsNN s₀.mem) (homeW h (nSlotsNN s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nnumFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, nnfindLoop_step_spec p n, ld64] <;>
      finish [nSlotsNN, homeW, baseW]

end find

/-! ## `nnum_push(t, pre, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `num` table, `CTL[38 + t]`. -/
def nncnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (38 + t)

/-- `nnum_push`'s room checks: the handle index, the record array. -/
def nnpushOK (m : Mem) (t : Word) : Bool :=
  decide (nncnt m t < (134217728 : Word)) && decide (nncnt m t < m.len64 NNREC >>> (2 : Word))

/-- The memory after `nnum_push(t, pre, u, j)` appended node `c`. -/
def nnpushMem (m : Mem) (t pre u j c : Word) : Mem :=
  ((((m.set64 NNREC (c * 4 + t * 2) pre).set64 NNREC (c * 4 + t * 2 + 1) u).set64 NNSLOT
    (j * 2 + t) (baseW m t + c + 1)).set64 CTL (38 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def nnumPush : FunDecl := lfn (t, pre, u, j) locals (c, k, gn, gk, gt, gi, gc, gh, gj, gb, gd) {
  c := CTL.u64[38 + t];
  if c >= 134217728 { abort };
  if len(NNREC.u64) >> 2 <= c { abort };
  k := c * 4 + t * 2;
  gk := NNSLOT.u64[len(NNSLOT.u64) - 1];
  NNREC.u64[k] := pre;
  NNREC.u64[k + 1] := u;
  NNSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[38 + (t & 1)] := c + 1;
  if (⟪SN0⟫ << gk) < (c + 1) * 2 { ⟪growBlkG nnumGS 6⟫ };
  return c
}

/-- The hash of node `i` of tier `t`. -/
def nnhash (m : Mem) (t i : Word) : Word :=
  nnumHashW (rdW (m.arr64 NNREC) (i * 4 + t * 2)) (rdW (m.arr64 NNREC) (i * 4 + t * 2 + 1))

section push
variable (p : Prog) (hp : p.lookup "nnum_push" = some nnumPush)

/-- The growth's hash block computes `nnhash`. -/
theorem nnhash_ok : HashOK p nnumGS 6 nnhash := by
  intro k s₀
  simp only [nnumGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [nnhash, nnumHashW, LocEq, St.setLoc]

include hp in
theorem nnumPush_spec (n : Nat) (s₀ : St) (t pre u j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nnum_push" [t, pre, u, j]
    ⦃fun r s' => LocEq s' s₀ ∧ nnpushOK s₀.mem t = true ∧ r = [nncnt s₀.mem t] ∧
      growIf NNSLOT 38 nnhash s₀.mem (nnpushMem s₀.mem t pre u j (nncnt s₀.mem t))
        (nncnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nnumPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64,
        growBlkG_spec p nnumGS NNSLOT 38 rfl rfl 6 nnhash (nnhash_ok p) n] <;>
      finish [nnpushMem, nncnt, nnpushOK, baseW, growIf_grow', growIf_keep']

end push

/-! ## `intern_nnum(pre, u)`: hash-cons the name `num pre u`

con-ron's `NStore::intern` at `num` and the arena's `internNNode (.num pre n)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `num` tier (tag `2`). -/
def nnP : Word := 0x20000000
def nnS : Word := 0x28000000

/-- The model of `intern_nnum`: the handle and the memory after, or `none` where the L code
aborts. -/
def nninternW (m : Mem) (pre u : Word) : Option (Word × Mem) :=
  let h := nnumHashW pre u
  let rs₀ := nnprobeW (m.arr64 NNSLOT) (m.arr64 NNREC) 0 pre u (baseW m 0) (nSlotsNN m) (homeW h (nSlotsNN m)) 0
  let rs₁ := nnprobeW (m.arr64 NNSLOT) (m.arr64 NNREC) 1 pre u (baseW m 1) (nSlotsNN m) (homeW h (nSlotsNN m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (nnP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (nnS + rs₁.tail.headD 0, m)
    else if nnpushOK m 1 then
      match growIf NNSLOT 38 nnhash m (nnpushMem m 1 pre u (rs₁.tail.tail.headD 0) (nncnt m 1)) (nncnt m 1) with
      | some m' => some (nnS + nncnt m 1, m')
      | none => none
    else none
  else if nnpushOK m 0 then
    match growIf NNSLOT 38 nnhash m (nnpushMem m 0 pre u (rs₀.tail.tail.headD 0) (nncnt m 0)) (nncnt m 0) with
    | some m' => some (nnP + nncnt m 0, m')
    | none => none
  else none

/-- con-ron: ConRon/Arena/Monad.lean:381-397 ConRon.Arena.internNNode -/
@[l_impl ConRon.Arena.internNNode]
def internNNum : FunDecl := lfn (pre, u) locals (h, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ pre) * ⟪fnvPrime⟫ ^ u) * ⟪fnvPrime⟫;
  (fd, i, j, d) := call nnum_find(0, pre, u, h);
  if fd != 0 { return ⟪nnP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call nnum_find(1, pre, u, h);
    if fd != 0 { return ⟪nnS⟫ + i };
    i := call nnum_push(1, pre, u, j);
    return ⟪nnS⟫ + i
  };
  i := call nnum_push(0, pre, u, j);
  return ⟪nnP⟫ + i
}

/-- The `num` store functions, as one `#eval`-able program. -/
def nnumProg : Prog :=
  [("nnum_find", nnumFind), ("nnum_push", nnumPush), ("intern_nnum", internNNum)]

/-- A memory with 8 `num` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥36 (the other tables') are unused here and left empty. -/
def nnumMem (scratch : Word) : Mem :=
  { words := ((Array.replicate 37 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch)) ++
      #[Array.replicate 32 0, Array.replicate 32 0] }

/-- Intern each `(pre, u)` pair in turn; the handles. -/
def internNNums (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (pre, u) :: xs => match run nnumProg 100 "intern_nnum" [pre, u] m with
    | .ok (r, m') => (internNNums m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0 (sharing). -/
#guard internNNums (nnumMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x20000000, 0x20000001, 0x20000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internNNums (nnumMem 1) [(1, 2), (2, 1), (1, 2)] == some [0x28000000, 0x28000001, 0x28000000]

section intern
variable (p : Prog) (hpf : p.lookup "nnum_find" = some nnumFind)
  (hpp : p.lookup "nnum_push" = some nnumPush) (hp : p.lookup "intern_nnum" = some internNNum)

include hpf hpp hp in
theorem internNNum_spec (n : Nat) (s₀ : St) (pre u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nnum" [pre, u]
    ⦃fun r s' => LocEq s' s₀ ∧ nninternW s₀.mem pre u = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internNNum]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nnumFind_spec p hpf n, nnumPush_spec p hpp n] <;>
      finish [nninternW, nnumHashW, baseW]

end intern

end L.Arena
