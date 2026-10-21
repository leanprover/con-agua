module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The name store's `anonymous` node store in L: a table with no fields

The arena's name store keeps the single `anonymous` node in a `Tbl AnonNode NIdx UInt64` per tier
(`vendor/con-ron/ConRon/Arena/Store.lean:137`, `NTables.anons`). `AnonNode` has no fields
(`mk ::`), so there is at most one node per tier and the cons key never distinguishes two nodes:
the match function is the constant `true` (**any** node that is there is the `anonymous` node).
As the level store's `zero` table (`ZeroStore.lean`), this uses a one-word dummy record (`w = 0`
is excluded by `Schema.WF`'s shape).

* **Records.** Word array `NAREC`, one (unused) word per node, tiers interleaved: node `i` of
  tier `t` at `NAREC[2 i + t]`. The node count of tier `t` is `CTL[34 + t]`.
* **Cons table.** Word array `NASLOT`, the same open addressing as `SLOT`/`ZSLOT`.

The functions: `nanon_find(t, h)`, `nanon_push(t, j)` and `intern_nanon()`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The name store's `anonymous` records, both tiers interleaved (one dummy word per node). -/
abbrev NAREC : ArrId := 33
/-- The name store's `anonymous` cons-table slots, both tiers interleaved. -/
abbrev NASLOT : ArrId := 34

/-- The (constant) hash of the `anonymous` record: there is only one key, so the home slot of
every probe is the same, fixed slot. -/
def nahashW : Word := fnvBasis

/-- The model of the match: **every** node of this table is the `anonymous` node. -/
def namatchW (_r : Array Word) (_t _i : Word) : Bool := true

/-! ## `nanon_find(t, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `namatchW`). -/
def naprobeW (sl r : Array Word) (t b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if namatchW r t (slotV sl b (j * 2 + t) - 1) then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else naprobeW sl r t b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t b n j d : Word)

theorem naprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : naprobeW sl r t b n j d = [0, 0, j, d] := by
  rw [naprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem naprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : namatchW r t (sl[k] - b - 1) = true) :
    naprobeW sl r t b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [naprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem naprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : namatchW r t (sl[k] - b - 1) = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    naprobeW sl r t b n j d = naprobeW sl r t b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [naprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] naprobeW_free => naprobeW sl r t b n j d, sl[k]
grind_pattern [arena_grind] naprobeW_hit => naprobeW sl r t b n j d, sl[k]
grind_pattern [arena_grind] naprobeW_next =>
  naprobeW sl r t b n j d, sl[k], naprobeW sl r t b n j' d'

def nafindLoop : Stmt := lblk (t, h, n, j, d, v, b) {
  while d < n {
    v := NASLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    if 0 == 0 { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def nanonFind : FunDecl := lfn (t, h) locals (n, j, d, v, b) {
  n := len(NASLOT.u64) >> 1;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪nafindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "nanon_find" = some nanonFind)

theorem nafindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n nafindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (naprobeW (s₀.mem.arr64 NASLOT) (s₀.mem.arr64 NAREC) (s₀.loc 0)
        (s₀.loc 6) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)) =
      naprobeW (s₀.mem.arr64 NASLOT) (s₀.mem.arr64 NAREC) (s₀.loc 0)
        (s₀.loc 6) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := nafindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [namatchW, baseW]

theorem nafindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) nafindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (naprobeW (s₀.mem.arr64 NASLOT) (s₀.mem.arr64 NAREC) (s₀.loc 0)
        (s₀.loc 6) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)) =
      naprobeW (s₀.mem.arr64 NASLOT) (s₀.mem.arr64 NAREC) (s₀.loc 0)
        (s₀.loc 6) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4); ⊤⦄ :=
  Triple.step_exec (nafindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `anonymous` table. -/
def nSlotsNA (m : Mem) : Word := m.len64 NASLOT >>> 1

include hp in
theorem nanonFind_spec (n : Nat) (s₀ : St) (t h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nanon_find" [t, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = naprobeW (s₀.mem.arr64 NASLOT) (s₀.mem.arr64 NAREC) t
        (baseW s₀.mem t) (nSlotsNA s₀.mem) (homeW h (nSlotsNA s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nanonFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, nafindLoop_step_spec p n, ld64] <;>
      finish [nSlotsNA, homeW, baseW]

end find

/-! ## `nanon_push(t, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `anonymous` table, `CTL[34 + t]`. -/
def nacnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (34 + t)

/-- `nanon_push`'s room checks: the handle index, the record array, the load limit. -/
def napushOK (m : Mem) (t : Word) : Bool :=
  decide (nacnt m t < (134217728 : Word)) && decide (nacnt m t < m.len64 NAREC >>> (1 : Word)) &&
    decide (nacnt m t + 1 ≤ (nSlotsNA m >>> (2 : Word)) * 3)

/-- The memory after `nanon_push(t, j)` appended node `c`. -/
def napushMem (m : Mem) (t j c : Word) : Mem :=
  (((m.set64 NAREC (c * 2 + t) 0).set64 NASLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (34 + (t &&& 1)) (c + 1))

def nanonPush : FunDecl := lfn (t, j) locals (c) {
  c := CTL.u64[34 + t];
  if c >= 134217728 { abort };
  if len(NAREC.u64) >> 1 <= c { abort };
  if ((len(NASLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  NAREC.u64[c * 2 + t] := 0;
  NASLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[34 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "nanon_push" = some nanonPush)

include hp in
theorem nanonPush_spec (n : Nat) (s₀ : St) (t j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nanon_push" [t, j]
    ⦃fun r s' => LocEq s' s₀ ∧ napushOK s₀.mem t = true ∧ r = [nacnt s₀.mem t] ∧
      s'.mem = napushMem s₀.mem t j (nacnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nanonPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [nacnt, napushOK, napushMem, nSlotsNA, baseW]

end push

/-! ## `intern_nanon()`: hash-cons the name `anonymous`

con-ron's `NStore::intern` at `anonymous` and the arena's `internNNode .anonymous`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `anonymous` tier (tag `0`). -/
def naP : Word := 0x00000000
def naS : Word := 0x08000000

/-- The model of `intern_nanon`: the handle and the memory after, or `none` where the L code
aborts. -/
def nainternW (m : Mem) : Option (Word × Mem) :=
  let h := nahashW
  let rs₀ := naprobeW (m.arr64 NASLOT) (m.arr64 NAREC) 0 (baseW m 0) (nSlotsNA m) (homeW h (nSlotsNA m)) 0
  let rs₁ := naprobeW (m.arr64 NASLOT) (m.arr64 NAREC) 1 (baseW m 1) (nSlotsNA m) (homeW h (nSlotsNA m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (naP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (naS + rs₁.tail.headD 0, m)
    else if napushOK m 1 then
      some (naS + nacnt m 1, napushMem m 1 (rs₁.tail.tail.headD 0) (nacnt m 1))
    else none
  else if napushOK m 0 then
    some (naP + nacnt m 0, napushMem m 0 (rs₀.tail.tail.headD 0) (nacnt m 0))
  else none

@[l_impl ConRon.Arena.internNNode]
def internNAnon : FunDecl := lfn () locals (h, fd, i, j, d) {
  h := ⟪nahashW⟫;
  (fd, i, j, d) := call nanon_find(0, h);
  if fd != 0 { return ⟪naP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call nanon_find(1, h);
    if fd != 0 { return ⟪naS⟫ + i };
    i := call nanon_push(1, j);
    return ⟪naS⟫ + i
  };
  i := call nanon_push(0, j);
  return ⟪naP⟫ + i
}

/-- The `anonymous` store functions, as one `#eval`-able program. -/
def nanonProg : Prog :=
  [("nanon_find", nanonFind), ("nanon_push", nanonPush), ("intern_nanon", internNAnon)]

/-- A memory with 8 `anonymous` slots per tier, the scratch tier closed or open. Arrays 0‥32 (the
other tables') are unused here and left empty. -/
def nanonMem (scratch : Word) : Mem :=
  { words := ((Array.replicate 33 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch)) ++
      #[Array.replicate 16 0, Array.replicate 32 0] }

/-- Intern `anonymous` `k` times in a row: the handle, every time, is the first persistent
node. -/
def internNAnons (m : Mem) : Nat → Option (List Word)
  | 0 => some []
  | k + 1 => match run nanonProg 100 "intern_nanon" [] m with
    | .ok (r, m') => (internNAnons m' k).map (r.headD 0 :: ·)
    | .error _ => none

/- Interning `anonymous` three times in a row: the same persistent handle every time (sharing). -/
#guard internNAnons (nanonMem 0) 3 == some [0x00000000, 0x00000000, 0x00000000]

/- Scratch open: the one node goes to the scratch tier (the persistent tier is empty). -/
#guard internNAnons (nanonMem 1) 2 == some [0x08000000, 0x08000000]

section intern
variable (p : Prog) (hpf : p.lookup "nanon_find" = some nanonFind)
  (hpp : p.lookup "nanon_push" = some nanonPush) (hp : p.lookup "intern_nanon" = some internNAnon)

include hpf hpp hp in
theorem internNAnon_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nanon" []
    ⦃fun r s' => LocEq s' s₀ ∧ nainternW s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internNAnon]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nanonFind_spec p hpf n, nanonPush_spec p hpp n] <;>
      finish [nainternW, nahashW, baseW]

end intern

end L.Arena
