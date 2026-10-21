module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The expression `bvar` node store in L: one `Nat` field per node

The arena's expression store keeps `bvar i` nodes in a `Tbl BVarNode EIdx UInt64` per tier
(`Arena/Store.lean:252`, `ETables.bvars`). Its L representation is the `succ` store's
(`LevelStore.lean`, one word per node), the word being the de Bruijn index itself (below `2^64`)
rather than a handle. A `bvar` has no child, so the scratch skip never fires
(`eViewHasScratchChild (.bvar _) = false`): the persistent tier is always probed.

* **Records.** Word array `BREC`, one word per node (the index `i` as a word), tiers
  interleaved: node `i` of tier `t` at `BREC[2 i + t]`. The node count of tier `t` is
  `CTL[22 + t]`.
* **Cons table.** Word array `BSLOT`, the same open addressing as `SLOT`.

The functions: `bvar_find(t, u, h)`, `bvar_push(t, u, j)` and `intern_bvar(u)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `bvar` records, both tiers interleaved (one word per node). -/
abbrev BREC : ArrId := 22
/-- The `bvar` cons-table slots, both tiers interleaved. -/
abbrev BSLOT : ArrId := 23

/-- The hash of a `bvar` record (FNV-1a over its word). -/
def bvarHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `bvar u`. -/
def bmatchW (r : Array Word) (t i u : Word) : Bool := rdW r (i * 2 + t) == u

/-! ## `bvar_find(t, u, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def bprobeW (sl r : Array Word) (t u n j d : Word) : List Word :=
  if d < n then
    if rdW sl (j * 2 + t) = 0 then [0, 0, j, d]
    else if bmatchW r t (rdW sl (j * 2 + t) - 1) u then [1, rdW sl (j * 2 + t) - 1, j, d]
    else bprobeW sl r t u n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t u n j d : Word)

theorem bprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] = 0) : bprobeW sl r t u n j d = [0, 0, j, d] := by
  rw [bprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv]

theorem bprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≠ 0) (hm : bmatchW r t (sl[k] - 1) u = true) :
    bprobeW sl r t u n j d = [1, sl[k] - 1, j, d] := by
  rw [bprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]

theorem bprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hm : bmatchW r t (sl[k] - 1) u = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    bprobeW sl r t u n j d = bprobeW sl r t u n j' d' := by
  subst hj' hd'
  rw [bprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]; simp

end probeArms

grind_pattern [arena_grind] bprobeW_free => bprobeW sl r t u n j d, sl[k]
grind_pattern [arena_grind] bprobeW_hit => bprobeW sl r t u n j d, sl[k]
grind_pattern [arena_grind] bprobeW_next =>
  bprobeW sl r t u n j d, sl[k], bprobeW sl r t u n j' d'

def bfindLoop : Stmt := lblk (t, u, h, n, j, d, v) {
  while d < n {
    v := BSLOT.u64[j * 2 + t];
    if v == 0 { return (0, 0, j, d) };
    if BREC.u64[(v - 1) * 2 + t] == u { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def bvarFind : FunDecl := lfn (t, u, h) locals (n, j, d, v) {
  n := len(BSLOT.u64) >> 1;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪bfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "bvar_find" = some bvarFind)

theorem bfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n bfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (bprobeW (s₀.mem.arr64 BSLOT) (s₀.mem.arr64 BREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      bprobeW (s₀.mem.arr64 BSLOT) (s₀.mem.arr64 BREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := bfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [bmatchW]

theorem bfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) bfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (bprobeW (s₀.mem.arr64 BSLOT) (s₀.mem.arr64 BREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      bprobeW (s₀.mem.arr64 BSLOT) (s₀.mem.arr64 BREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ :=
  Triple.step_exec (bfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `bvar` table. -/
def nSlotsB (m : Mem) : Word := m.len64 BSLOT >>> 1

include hp in
theorem bvarFind_spec (n : Nat) (s₀ : St) (t u h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bvar_find" [t, u, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = bprobeW (s₀.mem.arr64 BSLOT) (s₀.mem.arr64 BREC) t u
        (nSlotsB s₀.mem) (homeW h (nSlotsB s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, bvarFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, bfindLoop_step_spec p n] <;>
      finish [nSlotsB, homeW]

end find

/-! ## `bvar_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `bvar` table, `CTL[22 + t]`. -/
def bcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (22 + t)

/-- `bvar_push`'s room checks: the handle index, the record array, the load limit. -/
def bpushOK (m : Mem) (t : Word) : Bool :=
  decide (bcnt m t < (134217728 : Word)) && decide (bcnt m t < m.len64 BREC >>> (1 : Word)) &&
    decide (bcnt m t + 1 ≤ (nSlotsB m >>> (2 : Word)) * 3)

/-- The memory after `bvar_push(t, u, j)` appended node `c`. -/
def bpushMem (m : Mem) (t u j c : Word) : Mem :=
  (((m.set64 BREC (c * 2 + t) u).set64 BSLOT (j * 2 + t) (c + 1)).set64 CTL (22 + (t &&& 1)) (c + 1))

def bvarPush : FunDecl := lfn (t, u, j) locals (c) {
  c := CTL.u64[22 + t];
  if c >= 134217728 { abort };
  if len(BREC.u64) >> 1 <= c { abort };
  if ((len(BSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  BREC.u64[c * 2 + t] := u;
  BSLOT.u64[j * 2 + t] := c + 1;
  CTL.u64[22 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "bvar_push" = some bvarPush)

include hp in
theorem bvarPush_spec (n : Nat) (s₀ : St) (t u j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bvar_push" [t, u, j]
    ⦃fun r s' => LocEq s' s₀ ∧ bpushOK s₀.mem t = true ∧ r = [bcnt s₀.mem t] ∧
      s'.mem = bpushMem s₀.mem t u j (bcnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, bvarPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [bcnt, bpushOK, bpushMem, nSlotsB]

end push

/-! ## `intern_bvar(u)`: hash-cons the expression `bvar u`

con-ron's `EStore::intern` at `bvar` and the arena's `internE (.bvar u)`: the persistent probe,
the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `bvar` tier (tag `0`). -/
def bvarP : Word := 0x00000000
def bvarS : Word := 0x08000000

/-- The model of `intern_bvar`: the handle and the memory after, or `none` where the L code
aborts. -/
def binternW (m : Mem) (u : Word) : Option (Word × Mem) :=
  let h := bvarHashW u
  let rs₀ := bprobeW (m.arr64 BSLOT) (m.arr64 BREC) 0 u (nSlotsB m) (homeW h (nSlotsB m)) 0
  let rs₁ := bprobeW (m.arr64 BSLOT) (m.arr64 BREC) 1 u (nSlotsB m) (homeW h (nSlotsB m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (bvarP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (bvarS + rs₁.tail.headD 0, m)
    else if bpushOK m 1 then
      some (bvarS + bcnt m 1, bpushMem m 1 u (rs₁.tail.tail.headD 0) (bcnt m 1))
    else none
  else if bpushOK m 0 then
    some (bvarP + bcnt m 0, bpushMem m 0 u (rs₀.tail.tail.headD 0) (bcnt m 0))
  else none

def internBVar : FunDecl := lfn (u) locals (h, fd, i, j, d) {
  h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫;
  (fd, i, j, d) := call bvar_find(0, u, h);
  if fd != 0 { return ⟪bvarP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call bvar_find(1, u, h);
    if fd != 0 { return ⟪bvarS⟫ + i };
    i := call bvar_push(1, u, j);
    return ⟪bvarS⟫ + i
  };
  i := call bvar_push(0, u, j);
  return ⟪bvarP⟫ + i
}

/-- The `bvar` store functions, as one `#eval`-able program. -/
def bvarProg : Prog :=
  [("bvar_find", bvarFind), ("bvar_push", bvarPush), ("intern_bvar", internBVar)]

/-- A memory with 8 `bvar` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥21 (the other tables') are unused here and left empty. -/
def bvarMem (scratch : Word) : Mem :=
  { words := (Array.replicate 22 #[]).set! 1 ((Array.replicate 24 0).set! 1 scratch) ++
      #[Array.replicate 16 0, Array.replicate 32 0] }

/-- Intern each index in turn; the handles. -/
def internBVars (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run bvarProg 100 "intern_bvar" [u] m with
    | .ok (r, m') => (internBVars m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `bvar 0`, `bvar 1`, `bvar 0`, `bvar 7`: persistent handles 0, 1, 0, 2. -/
#guard internBVars (bvarMem 0) [0, 1, 0, 7] == some [0, 1, 0, 2]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internBVars (bvarMem 1) [0, 1, 0] == some [0x08000000, 0x08000001, 0x08000000]

section intern
variable (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
  (hpp : p.lookup "bvar_push" = some bvarPush) (hp : p.lookup "intern_bvar" = some internBVar)

include hpf hpp hp in
theorem internBVar_spec (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_bvar" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ binternW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internBVar]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvarFind_spec p hpf n, bvarPush_spec p hpp n] <;>
      finish [binternW, bvarHashW]

end intern

end L.Arena
