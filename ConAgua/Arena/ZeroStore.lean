module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level `zero` node store in L: a table with no fields

The arena's level store keeps the single `zero` node in a `Tbl ZeroNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.zeros`). `ZeroNode` has no fields (`mk ::`), so there is at
most one node per tier and the cons key never distinguishes two nodes: the match function is the
constant `true` (**any** node that is there is the `zero` node). Following the schema library's
recommendation for a fieldless constructor, this uses a one-word dummy record (`w = 0` is excluded
by `Schema.WF`'s shape; a genuine `w = 0` schema would also collide every node's address, which a
dummy field avoids needing to reason about).

* **Records.** Word array `ZREC`, one (unused) word per node, tiers interleaved: node `i` of tier
  `t` at `ZREC[2 i + t]`. The node count of tier `t` is `CTL[8 + t]`.
* **Cons table.** Word array `ZSLOT`, the same open addressing as `SLOT`/`SSLOT`.

The functions: `zero_find(t, h)`, `zero_push(t, j)` and `intern_zero()`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `zero` records, both tiers interleaved (one dummy word per node). -/
abbrev ZREC : ArrId := 8
/-- The `zero` cons-table slots, both tiers interleaved. -/
abbrev ZSLOT : ArrId := 9

/-- The (constant) hash of the `zero` record: there is only one key, so the home slot of every
probe is the same, fixed slot. -/
def zeroHashW : Word := fnvBasis

/-- The model of the match: **every** node of this table is the `zero` node. -/
def zmatchW (_r : Array Word) (_t _i : Word) : Bool := true

/-! ## `zero_find(t, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `zmatchW`). -/
def zprobeW (sl r : Array Word) (t n j d : Word) : List Word :=
  if d < n then
    if rdW sl (j * 2 + t) = 0 then [0, 0, j, d]
    else if zmatchW r t (rdW sl (j * 2 + t) - 1) then [1, rdW sl (j * 2 + t) - 1, j, d]
    else zprobeW sl r t n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t n j d : Word)

theorem zprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] = 0) : zprobeW sl r t n j d = [0, 0, j, d] := by
  rw [zprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv]

theorem zprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≠ 0) (hm : zmatchW r t (sl[k] - 1) = true) :
    zprobeW sl r t n j d = [1, sl[k] - 1, j, d] := by
  rw [zprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]

theorem zprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hm : zmatchW r t (sl[k] - 1) = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    zprobeW sl r t n j d = zprobeW sl r t n j' d' := by
  subst hj' hd'
  rw [zprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]; simp

end probeArms

grind_pattern [arena_grind] zprobeW_free => zprobeW sl r t n j d, sl[k]
grind_pattern [arena_grind] zprobeW_hit => zprobeW sl r t n j d, sl[k]
grind_pattern [arena_grind] zprobeW_next =>
  zprobeW sl r t n j d, sl[k], zprobeW sl r t n j' d'

def zfindLoop : Stmt := lblk (t, h, n, j, d, v) {
  while d < n {
    v := ZSLOT.u64[j * 2 + t];
    if v == 0 { return (0, 0, j, d) };
    if 0 == 0 { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def zeroFind : FunDecl := lfn (t, h) locals (n, j, d, v) {
  n := len(ZSLOT.u64) >> 1;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪zfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "zero_find" = some zeroFind)

theorem zfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n zfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (zprobeW (s₀.mem.arr64 ZSLOT) (s₀.mem.arr64 ZREC) (s₀.loc 0)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)) =
      zprobeW (s₀.mem.arr64 ZSLOT) (s₀.mem.arr64 ZREC) (s₀.loc 0)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 4); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := zfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [zmatchW]

theorem zfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) zfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (zprobeW (s₀.mem.arr64 ZSLOT) (s₀.mem.arr64 ZREC) (s₀.loc 0)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)) =
      zprobeW (s₀.mem.arr64 ZSLOT) (s₀.mem.arr64 ZREC) (s₀.loc 0)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 4); ⊤⦄ :=
  Triple.step_exec (zfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `zero` table. -/
def nSlotsZ (m : Mem) : Word := m.len64 ZSLOT >>> 1

include hp in
theorem zeroFind_spec (n : Nat) (s₀ : St) (t h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "zero_find" [t, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = zprobeW (s₀.mem.arr64 ZSLOT) (s₀.mem.arr64 ZREC) t
        (nSlotsZ s₀.mem) (homeW h (nSlotsZ s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, zeroFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, zfindLoop_step_spec p n] <;>
      finish [nSlotsZ, homeW]

end find

/-! ## `zero_push(t, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `zero` table, `CTL[8 + t]`. -/
def zcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (8 + t)

/-- `zero_push`'s room checks: the handle index, the record array, the load limit. -/
def zpushOK (m : Mem) (t : Word) : Bool :=
  decide (zcnt m t < (134217728 : Word)) && decide (zcnt m t < m.len64 ZREC >>> (1 : Word)) &&
    decide (zcnt m t + 1 ≤ (nSlotsZ m >>> (2 : Word)) * 3)

/-- The memory after `zero_push(t, j)` appended node `c`. -/
def zpushMem (m : Mem) (t j c : Word) : Mem :=
  (((m.set64 ZREC (c * 2 + t) 0).set64 ZSLOT (j * 2 + t) (c + 1)).set64 CTL (8 + (t &&& 1)) (c + 1))

def zeroPush : FunDecl := lfn (t, j) locals (c) {
  c := CTL.u64[8 + t];
  if c >= 134217728 { abort };
  if len(ZREC.u64) >> 1 <= c { abort };
  if ((len(ZSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  ZREC.u64[c * 2 + t] := 0;
  ZSLOT.u64[j * 2 + t] := c + 1;
  CTL.u64[8 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "zero_push" = some zeroPush)

include hp in
theorem zeroPush_spec (n : Nat) (s₀ : St) (t j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "zero_push" [t, j]
    ⦃fun r s' => LocEq s' s₀ ∧ zpushOK s₀.mem t = true ∧ r = [zcnt s₀.mem t] ∧
      s'.mem = zpushMem s₀.mem t j (zcnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, zeroPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [zcnt, zpushOK, zpushMem, nSlotsZ]

end push

/-! ## `intern_zero()`: hash-cons the level `zero`

con-ron's `LStore::intern` at `zero` and the arena's `internLNode .zero`: the persistent probe,
the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `zero` tier (tag `0`). -/
def zeroP : Word := 0x00000000
def zeroS : Word := 0x08000000

/-- The model of `intern_zero`: the handle and the memory after, or `none` where the L code
aborts. -/
def zinternW (m : Mem) : Option (Word × Mem) :=
  let h := zeroHashW
  let rs₀ := zprobeW (m.arr64 ZSLOT) (m.arr64 ZREC) 0 (nSlotsZ m) (homeW h (nSlotsZ m)) 0
  let rs₁ := zprobeW (m.arr64 ZSLOT) (m.arr64 ZREC) 1 (nSlotsZ m) (homeW h (nSlotsZ m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (zeroP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (zeroS + rs₁.tail.headD 0, m)
    else if zpushOK m 1 then
      some (zeroS + zcnt m 1, zpushMem m 1 (rs₁.tail.tail.headD 0) (zcnt m 1))
    else none
  else if zpushOK m 0 then
    some (zeroP + zcnt m 0, zpushMem m 0 (rs₀.tail.tail.headD 0) (zcnt m 0))
  else none

@[l_impl ConRon.Arena.internLNode]
def internZero : FunDecl := lfn () locals (h, fd, i, j, d) {
  h := ⟪zeroHashW⟫;
  (fd, i, j, d) := call zero_find(0, h);
  if fd != 0 { return ⟪zeroP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call zero_find(1, h);
    if fd != 0 { return ⟪zeroS⟫ + i };
    i := call zero_push(1, j);
    return ⟪zeroS⟫ + i
  };
  i := call zero_push(0, j);
  return ⟪zeroP⟫ + i
}

/-- The `zero` store functions, as one `#eval`-able program. -/
def zeroProg : Prog :=
  [("zero_find", zeroFind), ("zero_push", zeroPush), ("intern_zero", internZero)]

/-- A memory with 8 `zero` slots per tier, the scratch tier closed or open. -/
def zeroMem (scratch : Word) : Mem :=
  { words := #[#[], #[0, scratch, 0, 0, 0, 0, 0, 0, 0, 0], #[], #[], #[], #[], #[], #[],
      Array.replicate 16 0, Array.replicate 32 0] }

/-- Intern `zero` `k` times in a row: the handle, every time, is the first persistent node. -/
def internZeros (m : Mem) : Nat → Option (List Word)
  | 0 => some []
  | k + 1 => match run zeroProg 100 "intern_zero" [] m with
    | .ok (r, m') => (internZeros m' k).map (r.headD 0 :: ·)
    | .error _ => none

/- Interning `zero` three times in a row: the same persistent handle every time (sharing). -/
#guard internZeros (zeroMem 0) 3 == some [0x00000000, 0x00000000, 0x00000000]

/- Scratch open: the one node goes to the scratch tier (the persistent tier is empty). -/
#guard internZeros (zeroMem 1) 2 == some [0x08000000, 0x08000000]

section intern
variable (p : Prog) (hpf : p.lookup "zero_find" = some zeroFind)
  (hpp : p.lookup "zero_push" = some zeroPush) (hp : p.lookup "intern_zero" = some internZero)

include hpf hpp hp in
theorem internZero_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_zero" []
    ⦃fun r s' => LocEq s' s₀ ∧ zinternW s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internZero]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        zeroFind_spec p hpf n, zeroPush_spec p hpp n] <;>
      finish [zinternW, zeroHashW]

end intern

end L.Arena
