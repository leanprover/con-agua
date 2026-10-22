module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level `imax` node store in L: a fourth store, two level-handle fields per node

The arena's level store keeps `imax u v` nodes in a `Tbl BinLNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.imaxs`). Its L representation is the `app` store's
(`AppStore.lean`) with two handle fields and no scratch skip (the level store's `LStore.find?`
probes the persistent tier unconditionally, as for `succ`):

* **Records.** Word array `IREC`, two words per node (the handle words of `u` and `v`), tiers
  interleaved: node `i` of tier `t` at `IREC[4 i + 2 t ..]`. The node count of tier `t` is
  `CTL[12 + t]`.
* **Cons table.** Word array `ISLOT`, the same open addressing as `SLOT`/`ASLOT`/`SSLOT`.

The functions: `imax_find(t, u, v, h)`, `imax_push(t, u, v, j)` and `intern_imax(u, v)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `imax` records, both tiers interleaved (two words per node). -/
abbrev IREC : ArrId := 12
/-- The `imax` cons-table slots, both tiers interleaved. -/
abbrev ISLOT : ArrId := 13

/-- The hash of an `imax` record (FNV-1a over its two words). -/
def imaxHashW (u v : Word) : Word := ((fnvBasis ^^^ u) * fnvPrime ^^^ v) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(u, v)`. -/
def immatchW (r : Array Word) (t i u v : Word) : Bool :=
  rdW r (i * 4 + t * 2) == u && rdW r (i * 4 + t * 2 + 1) == v

/-! ## `imax_find(t, u, v, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `immatchW`). -/
def improbeW (sl r : Array Word) (t u v b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if immatchW r t (slotV sl b (j * 2 + t) - 1) u v then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else improbeW sl r t u v b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
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

theorem improbeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : improbeW sl r t u v b n j d = [0, 0, j, d] := by
  rw [improbeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem improbeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : immatchW r t (sl[k] - b - 1) u v = true) :
    improbeW sl r t u v b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [improbeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem improbeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : immatchW r t (sl[k] - b - 1) u v = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    improbeW sl r t u v b n j d = improbeW sl r t u v b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [improbeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] improbeW_free => improbeW sl r t u v b n j d, sl[k]
grind_pattern [arena_grind] improbeW_hit => improbeW sl r t u v b n j d, sl[k]
grind_pattern [arena_grind] improbeW_next =>
  improbeW sl r t u v b n j d, sl[k], improbeW sl r t u v b n j' d'

def imfindLoop : Stmt := lblk (t, u, v, h, n, j, d, w, b) {
  while d < n {
    w := ISLOT.u64[j * 2 + t];
    if w <= b { return (0, 0, j, d) };
    w := w - b;
    if IREC.u64[(w - 1) * 4 + t * 2] == u && IREC.u64[(w - 1) * 4 + t * 2 + 1] == v {
      return (1, w - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def imaxFind : FunDecl := lfn (t, u, v, h) locals (n, j, d, w, b) {
  n := len(ISLOT.u64) >> 1;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪imfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "imax_find" = some imaxFind)

theorem imfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n imfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (improbeW (s₀.mem.arr64 ISLOT) (s₀.mem.arr64 IREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      improbeW (s₀.mem.arr64 ISLOT) (s₀.mem.arr64 IREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := imfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [immatchW, baseW]

theorem imfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) imfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (improbeW (s₀.mem.arr64 ISLOT) (s₀.mem.arr64 IREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      improbeW (s₀.mem.arr64 ISLOT) (s₀.mem.arr64 IREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (imfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `imax` table. -/
def nSlotsI (m : Mem) : Word := m.len64 ISLOT >>> 1

include hp in
theorem imaxFind_spec (n : Nat) (s₀ : St) (t u v h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "imax_find" [t, u, v, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = improbeW (s₀.mem.arr64 ISLOT) (s₀.mem.arr64 IREC) t u v
        (baseW s₀.mem t) (nSlotsI s₀.mem) (homeW h (nSlotsI s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, imaxFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, imfindLoop_step_spec p n, ld64] <;>
      finish [nSlotsI, homeW, baseW]

end find

/-! ## `imax_push(t, u, v, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `imax` table, `CTL[12 + t]`. -/
def imcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (12 + t)

/-- `imax_push`'s room checks: the handle index, the record array, the load limit. -/
def impushOK (m : Mem) (t : Word) : Bool :=
  decide (imcnt m t < (134217728 : Word)) && decide (imcnt m t < m.len64 IREC >>> (2 : Word)) &&
    decide (imcnt m t + 1 ≤ (nSlotsI m >>> (2 : Word)) * 3)

/-- The memory after `imax_push(t, u, v, j)` appended node `c`. -/
def impushMem (m : Mem) (t u v j c : Word) : Mem :=
  ((((m.set64 IREC (c * 4 + t * 2) u).set64 IREC (c * 4 + t * 2 + 1) v).set64 ISLOT (j * 2 + t)
    (baseW m t + c + 1)).set64 CTL (12 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def imaxPush : FunDecl := lfn (t, u, v, j) locals (c, k) {
  c := CTL.u64[12 + t];
  if c >= 134217728 { abort };
  if len(IREC.u64) >> 2 <= c { abort };
  if ((len(ISLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 4 + t * 2;
  IREC.u64[k] := u;
  IREC.u64[k + 1] := v;
  ISLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[12 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "imax_push" = some imaxPush)

include hp in
theorem imaxPush_spec (n : Nat) (s₀ : St) (t u v j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "imax_push" [t, u, v, j]
    ⦃fun r s' => LocEq s' s₀ ∧ impushOK s₀.mem t = true ∧ r = [imcnt s₀.mem t] ∧
      s'.mem = impushMem s₀.mem t u v j (imcnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, imaxPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [imcnt, impushOK, impushMem, nSlotsI, baseW]

end push

/-! ## `intern_imax(u, v)`: hash-cons the level `imax u v`

con-ron's `LStore::intern` at `imax` and the arena's `internLNode (.imax u v)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `imax` tier (tag `3`). -/
def imaxP : Word := 0x30000000
def imaxS : Word := 0x38000000

/-- The model of `intern_imax`: the handle and the memory after, or `none` where the L code
aborts. -/
def iminternW (m : Mem) (u v : Word) : Option (Word × Mem) :=
  let h := imaxHashW u v
  let rs₀ := improbeW (m.arr64 ISLOT) (m.arr64 IREC) 0 u v (baseW m 0) (nSlotsI m) (homeW h (nSlotsI m)) 0
  let rs₁ := improbeW (m.arr64 ISLOT) (m.arr64 IREC) 1 u v (baseW m 1) (nSlotsI m) (homeW h (nSlotsI m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (imaxP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (imaxS + rs₁.tail.headD 0, m)
    else if impushOK m 1 then
      some (imaxS + imcnt m 1, impushMem m 1 u v (rs₁.tail.tail.headD 0) (imcnt m 1))
    else none
  else if impushOK m 0 then
    some (imaxP + imcnt m 0, impushMem m 0 u v (rs₀.tail.tail.headD 0) (imcnt m 0))
  else none

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internImax : FunDecl := lfn (u, v) locals (h, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ ^ v) * ⟪fnvPrime⟫;
  (fd, i, j, d) := call imax_find(0, u, v, h);
  if fd != 0 { return ⟪imaxP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call imax_find(1, u, v, h);
    if fd != 0 { return ⟪imaxS⟫ + i };
    i := call imax_push(1, u, v, j);
    return ⟪imaxS⟫ + i
  };
  i := call imax_push(0, u, v, j);
  return ⟪imaxP⟫ + i
}

/-- The `imax` store functions, as one `#eval`-able program. -/
def imaxProg : Prog :=
  [("imax_find", imaxFind), ("imax_push", imaxPush), ("intern_imax", internImax)]

/-- A memory with 8 `imax` nodes and 16 slots per tier, the scratch tier closed or open. -/
def imaxMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], #[],
      #[], #[], #[], #[], #[], Array.replicate 32 0, Array.replicate 32 0] }

/-- Intern each pair in turn; the handles. -/
def internImaxs (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (u, v) :: xs => match run imaxProg 100 "intern_imax" [u, v] m with
    | .ok (r, m') => (internImaxs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internImaxs (imaxMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x30000000, 0x30000001, 0x30000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internImaxs (imaxMem 1) [(1, 2), (2, 1), (1, 2)] == some [0x38000000, 0x38000001, 0x38000000]

section intern
variable (p : Prog) (hpf : p.lookup "imax_find" = some imaxFind)
  (hpp : p.lookup "imax_push" = some imaxPush) (hp : p.lookup "intern_imax" = some internImax)

include hpf hpp hp in
theorem internImax_spec (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_imax" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ iminternW s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internImax]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        imaxFind_spec p hpf n, imaxPush_spec p hpp n] <;>
      finish [iminternW, imaxHashW, baseW]

end intern

end L.Arena
