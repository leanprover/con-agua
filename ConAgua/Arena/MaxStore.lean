module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level `max` node store in L: a fourth store, two level-handle fields per node

The arena's level store keeps `max u v` nodes in a `Tbl BinLNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.maxs`). Its L representation is the `app` store's
(`AppStore.lean`) with two handle fields and no scratch skip (the level store's `LStore.find?`
probes the persistent tier unconditionally, as for `succ`):

* **Records.** Word array `MREC`, two words per node (the handle words of `u` and `v`), tiers
  interleaved: node `i` of tier `t` at `MREC[4 i + 2 t ..]`. The node count of tier `t` is
  `CTL[10 + t]`.
* **Cons table.** Word array `MSLOT`, the same open addressing as `SLOT`/`ASLOT`/`SSLOT`.

The functions: `max_find(t, u, v, h)`, `max_push(t, u, v, j)` and `intern_max(u, v)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `max` records, both tiers interleaved (two words per node). -/
abbrev MREC : ArrId := 10
/-- The `max` cons-table slots, both tiers interleaved. -/
abbrev MSLOT : ArrId := 11

/-- The hash of a `max` record (FNV-1a over its two words). -/
def maxHashW (u v : Word) : Word := ((fnvBasis ^^^ u) * fnvPrime ^^^ v) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(u, v)`. -/
def mmatchW (r : Array Word) (t i u v : Word) : Bool :=
  rdW r (i * 4 + t * 2) == u && rdW r (i * 4 + t * 2 + 1) == v

/-! ## `max_find(t, u, v, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `mmatchW`). -/
def mprobeW (sl r : Array Word) (t u v b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if mmatchW r t (slotV sl b (j * 2 + t) - 1) u v then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else mprobeW sl r t u v b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t u v b n j d : Word)

theorem mprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : mprobeW sl r t u v b n j d = [0, 0, j, d] := by
  rw [mprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem mprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : mmatchW r t (sl[k] - b - 1) u v = true) :
    mprobeW sl r t u v b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [mprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem mprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : mmatchW r t (sl[k] - b - 1) u v = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    mprobeW sl r t u v b n j d = mprobeW sl r t u v b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [mprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] mprobeW_free => mprobeW sl r t u v b n j d, sl[k]
grind_pattern [arena_grind] mprobeW_hit => mprobeW sl r t u v b n j d, sl[k]
grind_pattern [arena_grind] mprobeW_next =>
  mprobeW sl r t u v b n j d, sl[k], mprobeW sl r t u v b n j' d'

def mfindLoop : Stmt := lblk (t, u, v, h, n, j, d, w, b) {
  while d < n {
    w := MSLOT.u64[j * 2 + t];
    if w <= b { return (0, 0, j, d) };
    w := w - b;
    if MREC.u64[(w - 1) * 4 + t * 2] == u && MREC.u64[(w - 1) * 4 + t * 2 + 1] == v {
      return (1, w - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def maxFind : FunDecl := lfn (t, u, v, h) locals (n, j, d, w, b) {
  n := len(MSLOT.u64) >> 1;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪mfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "max_find" = some maxFind)

theorem mfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n mfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (mprobeW (s₀.mem.arr64 MSLOT) (s₀.mem.arr64 MREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      mprobeW (s₀.mem.arr64 MSLOT) (s₀.mem.arr64 MREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := mfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [mmatchW, baseW]

theorem mfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) mfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (mprobeW (s₀.mem.arr64 MSLOT) (s₀.mem.arr64 MREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      mprobeW (s₀.mem.arr64 MSLOT) (s₀.mem.arr64 MREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (mfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `max` table. -/
def nSlotsM (m : Mem) : Word := m.len64 MSLOT >>> 1

include hp in
theorem maxFind_spec (n : Nat) (s₀ : St) (t u v h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "max_find" [t, u, v, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = mprobeW (s₀.mem.arr64 MSLOT) (s₀.mem.arr64 MREC) t u v
        (baseW s₀.mem t) (nSlotsM s₀.mem) (homeW h (nSlotsM s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, maxFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, mfindLoop_step_spec p n, ld64] <;>
      finish [nSlotsM, homeW, baseW]

end find

/-! ## `max_push(t, u, v, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `max` table, `CTL[10 + t]`. -/
def mcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (10 + t)

/-- `max_push`'s room checks: the handle index, the record array, the load limit. -/
def mpushOK (m : Mem) (t : Word) : Bool :=
  decide (mcnt m t < (134217728 : Word)) && decide (mcnt m t < m.len64 MREC >>> (2 : Word)) &&
    decide (mcnt m t < m.len64 MHP >>> (1 : Word)) &&
    decide (mcnt m t + 1 ≤ (nSlotsM m >>> (2 : Word)) * 3)

/-- The memory after `max_push(t, u, v, j)` appended node `c`. -/
def mpushMem (m : Mem) (t u v j c : Word) : Mem :=
  ((((m.set64 MREC (c * 4 + t * 2) u).set64 MREC (c * 4 + t * 2 + 1) v).set64 MSLOT (j * 2 + t)
    (baseW m t + c + 1)).set64 CTL (10 + (t &&& 1)) (c + 1)).set64 MHP (c * 2 + t)
    (lvlHPW m u ||| lvlHPW m v)

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def maxPush : FunDecl := lfn (t, u, v, j) locals (c, k, x, g, ti, ix, y) {
  ⟪hpBlkM1⟫;
  ⟪hpBlkM2⟫;
  x := x | y;
  c := CTL.u64[10 + t];
  if c >= 134217728 { abort };
  if len(MREC.u64) >> 2 <= c { abort };
  if len(MHP.u64) >> 1 <= c { abort };
  if ((len(MSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 4 + t * 2;
  MREC.u64[k] := u;
  MREC.u64[k + 1] := v;
  MSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[10 + (t & 1)] := c + 1;
  MHP.u64[c * 2 + t] := x;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "max_push" = some maxPush)

include hp in
theorem maxPush_spec (n : Nat) (s₀ : St) (t u v j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "max_push" [t, u, v, j]
    ⦃fun r s' => LocEq s' s₀ ∧ mpushOK s₀.mem t = true ∧ r = [mcnt s₀.mem t] ∧
      s'.mem = mpushMem s₀.mem t u v j (mcnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, maxPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64, hpBlkM1_spec p (exec p n),
        hpBlkM2_spec p (exec p n)] <;>
      finish [mcnt, mpushOK, mpushMem, nSlotsM, baseW]

end push

/-! ## `intern_max(u, v)`: hash-cons the level `max u v`

con-ron's `LStore::intern` at `max` and the arena's `internLNode (.max u v)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `max` tier (tag `2`). -/
def maxP : Word := 0x20000000
def maxS : Word := 0x28000000

/-- The model of `intern_max`: the handle and the memory after, or `none` where the L code
aborts. -/
def minternW (m : Mem) (u v : Word) : Option (Word × Mem) :=
  let h := maxHashW u v
  let rs₀ := mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 0 u v (baseW m 0) (nSlotsM m) (homeW h (nSlotsM m)) 0
  let rs₁ := mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 1 u v (baseW m 1) (nSlotsM m) (homeW h (nSlotsM m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (maxP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (maxS + rs₁.tail.headD 0, m)
    else if mpushOK m 1 then
      some (maxS + mcnt m 1, mpushMem m 1 u v (rs₁.tail.tail.headD 0) (mcnt m 1))
    else none
  else if mpushOK m 0 then
    some (maxP + mcnt m 0, mpushMem m 0 u v (rs₀.tail.tail.headD 0) (mcnt m 0))
  else none

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internMax : FunDecl := lfn (u, v) locals (h, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ ^ v) * ⟪fnvPrime⟫;
  (fd, i, j, d) := call max_find(0, u, v, h);
  if fd != 0 { return ⟪maxP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call max_find(1, u, v, h);
    if fd != 0 { return ⟪maxS⟫ + i };
    i := call max_push(1, u, v, j);
    return ⟪maxS⟫ + i
  };
  i := call max_push(0, u, v, j);
  return ⟪maxP⟫ + i
}

/-- The `max` store functions, as one `#eval`-able program. -/
def maxProg : Prog :=
  [("max_find", maxFind), ("max_push", maxPush), ("intern_max", internMax)]

/-- A memory with 8 `max` nodes and 16 slots per tier, the scratch tier closed or open. -/
def maxMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], #[], #[],
      #[], #[], Array.replicate 32 0, Array.replicate 32 0] ++
      Array.replicate 62 (Array.replicate 32 0) }

/-- Intern each pair in turn; the handles. -/
def internMaxs (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (u, v) :: xs => match run maxProg 100 "intern_max" [u, v] m with
    | .ok (r, m') => (internMaxs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internMaxs (maxMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x20000000, 0x20000001, 0x20000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internMaxs (maxMem 1) [(1, 2), (2, 1), (1, 2)] == some [0x28000000, 0x28000001, 0x28000000]

section intern
variable (p : Prog) (hpf : p.lookup "max_find" = some maxFind)
  (hpp : p.lookup "max_push" = some maxPush) (hp : p.lookup "intern_max" = some internMax)

include hpf hpp hp in
theorem internMax_spec (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_max" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ minternW s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internMax]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        maxFind_spec p hpf n, maxPush_spec p hpp n] <;>
      finish [minternW, maxHashW, baseW]

end intern

end L.Arena
