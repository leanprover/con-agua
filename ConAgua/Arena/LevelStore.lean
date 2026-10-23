module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level `succ` node store in L: a third store, one handle field per node

The arena's level store keeps `succ u` nodes in a `Tbl SuccNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.succs`). Its L representation is the `app` store's
(`AppStore.lean`) with one word per node and no scratch skip (`LStore.find?` probes the
persistent tier unconditionally):

* **Records.** Word array `SREC`, one word per node (the handle word of `u`), tiers
  interleaved: node `i` of tier `t` at `SREC[2 i + t]`. The node count of tier `t` is
  `CTL[6 + t]`.
* **Cons table.** Word array `SSLOT`, the same open addressing as `SLOT`.

The functions: `succ_find(t, u, h)`, `succ_push(t, u, j)` and `intern_succ(u)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `succ` records, both tiers interleaved (one word per node). -/
abbrev SREC : ArrId := 6
/-- The `succ` cons-table slots, both tiers interleaved. -/
abbrev SSLOT : ArrId := 7

/-- The growth schema of this table (`SlotGrow.lean`). -/
def succGS : GrowSch :=
  ⟨SSLOT, SREC, 1, 6, lblk (n, k, t, i, c, h) {
    h := (⟪fnvBasis⟫ ^ SREC.u64[i * 2 + t]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of a `succ` record (FNV-1a over its word). -/
def succHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `succ u`. -/
def smatchW (r : Array Word) (t i u : Word) : Bool := rdW r (i * 2 + t) == u

/-! ## `succ_find(t, u, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def sprobeW (sl r : Array Word) (t u b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if smatchW r t (slotV sl b (j * 2 + t) - 1) u then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else sprobeW sl r t u b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t u b n j d : Word)

theorem sprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : sprobeW sl r t u b n j d = [0, 0, j, d] := by
  rw [sprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem sprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : smatchW r t (sl[k] - b - 1) u = true) :
    sprobeW sl r t u b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [sprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem sprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : smatchW r t (sl[k] - b - 1) u = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    sprobeW sl r t u b n j d = sprobeW sl r t u b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [sprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] sprobeW_free => sprobeW sl r t u b n j d, sl[k]
grind_pattern [arena_grind] sprobeW_hit => sprobeW sl r t u b n j d, sl[k]
grind_pattern [arena_grind] sprobeW_next =>
  sprobeW sl r t u b n j d, sl[k], sprobeW sl r t u b n j' d'

def sfindLoop : Stmt := lblk (t, u, h, n, j, d, v, b) {
  while d < n {
    v := SSLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    if SREC.u64[(v - 1) * 2 + t] == u { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def succFind : FunDecl := lfn (t, u, h) locals (n, j, d, v, b) {
  n := ⟪SN0⟫ << SSLOT.u64[len(SSLOT.u64) - 1];
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪sfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "succ_find" = some succFind)

theorem sfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n sfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (sprobeW (s₀.mem.arr64 SSLOT) (s₀.mem.arr64 SREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      sprobeW (s₀.mem.arr64 SSLOT) (s₀.mem.arr64 SREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := sfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [smatchW, baseW]

theorem sfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) sfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (sprobeW (s₀.mem.arr64 SSLOT) (s₀.mem.arr64 SREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      sprobeW (s₀.mem.arr64 SSLOT) (s₀.mem.arr64 SREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ :=
  Triple.step_exec (sfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `succ` table. -/
def nSlotsS (m : Mem) : Word := SN0 <<< rdW (m.arr64 SSLOT) (m.len64 SSLOT - 1)

include hp in
theorem succFind_spec (n : Nat) (s₀ : St) (t u h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "succ_find" [t, u, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = sprobeW (s₀.mem.arr64 SSLOT) (s₀.mem.arr64 SREC) t u
        (baseW s₀.mem t) (nSlotsS s₀.mem) (homeW h (nSlotsS s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, succFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, sfindLoop_step_spec p n, ld64] <;>
      finish [nSlotsS, homeW, baseW]

end find

/-! ## `succ_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `succ` table, `CTL[6 + t]`. -/
def scnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (6 + t)

/-- `succ_push`'s room checks: the handle index, the record array, the load limit. -/
def spushOK (m : Mem) (t : Word) : Bool :=
  decide (scnt m t < (134217728 : Word)) && decide (scnt m t < m.len64 SREC >>> (1 : Word)) &&
    decide (scnt m t < m.len64 SHP >>> (1 : Word)) &&
    decide (scnt m t + 1 ≤ (nSlotsS m >>> (2 : Word)) * 3)

/-- The memory after `succ_push(t, u, j)` appended node `c`. -/
def spushMem (m : Mem) (t u j c : Word) : Mem :=
  ((((m.set64 SREC (c * 2 + t) u).set64 SSLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (6 + (t &&& 1)) (c + 1)).set64
    SHP (c * 2 + t) (lvlHPW m u))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def succPush : FunDecl := lfn (t, u, j) locals (c, x, g, ti, ix, gn, gk, gt, gi, gc, gh, gj, gb, gd) {
  ⟪hpBlkS⟫;
  c := CTL.u64[6 + t];
  if c >= 134217728 { abort };
  if len(SREC.u64) >> 1 <= c { abort };
  if len(SHP.u64) >> 1 <= c { abort };
  SREC.u64[c * 2 + t] := u;
  SSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[6 + (t & 1)] := c + 1;
  if (⟪SN0⟫ << SSLOT.u64[len(SSLOT.u64) - 1]) < (c + 1) * 2 { ⟪growBlkG succGS 8⟫ };
  SHP.u64[c * 2 + t] := x;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "succ_push" = some succPush)

include hp in
theorem succPush_spec (n : Nat) (s₀ : St) (t u j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "succ_push" [t, u, j]
    ⦃fun r s' => LocEq s' s₀ ∧ spushOK s₀.mem t = true ∧ r = [scnt s₀.mem t] ∧
      s'.mem = spushMem s₀.mem t u j (scnt s₀.mem t); ⊤⦄ := by
  sorry -- slotgrow: the push grows the table

end push

/-! ## `intern_succ(u)`: hash-cons the level `succ u`

con-ron's `LStore::intern` at `succ` and the arena's `internLNode (.succ u)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `succ` tier (tag `1`). -/
def succP : Word := 0x10000000
def succS : Word := 0x18000000

/-- The model of `intern_succ`: the handle and the memory after, or `none` where the L code
aborts. -/
def sinternW (m : Mem) (u : Word) : Option (Word × Mem) :=
  let h := succHashW u
  let rs₀ := sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 0 u (baseW m 0) (nSlotsS m) (homeW h (nSlotsS m)) 0
  let rs₁ := sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 1 u (baseW m 1) (nSlotsS m) (homeW h (nSlotsS m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (succP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (succS + rs₁.tail.headD 0, m)
    else if spushOK m 1 then
      some (succS + scnt m 1, spushMem m 1 u (rs₁.tail.tail.headD 0) (scnt m 1))
    else none
  else if spushOK m 0 then
    some (succP + scnt m 0, spushMem m 0 u (rs₀.tail.tail.headD 0) (scnt m 0))
  else none

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internSucc : FunDecl := lfn (u) locals (h, fd, i, j, d) {
  h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫;
  (fd, i, j, d) := call succ_find(0, u, h);
  if fd != 0 { return ⟪succP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call succ_find(1, u, h);
    if fd != 0 { return ⟪succS⟫ + i };
    i := call succ_push(1, u, j);
    return ⟪succS⟫ + i
  };
  i := call succ_push(0, u, j);
  return ⟪succP⟫ + i
}

/-- The `succ` store functions, as one `#eval`-able program. -/
def succProg : Prog :=
  [("succ_find", succFind), ("succ_push", succPush), ("intern_succ", internSucc)]

/-- A memory with 8 `succ` nodes and 16 slots per tier, the scratch tier closed or open. -/
def succMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], Array.replicate 16 0,
      Array.replicate 32 0] ++ Array.replicate 62 (Array.replicate 32 0) }

/-- Intern each word in turn; the handles. -/
def internSuccs (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run succProg 100 "intern_succ" [u] m with
    | .ok (r, m') => (internSuccs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `succ 0`, `succ 1`, `succ 0`, `succ (succ 0)`: persistent handles 0, 1, 0, 2. -/
#guard internSuccs (succMem 0) [0, 1, 0, 0x10000000] ==
  some [0x10000000, 0x10000001, 0x10000000, 0x10000002]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internSuccs (succMem 1) [0, 1, 0] == some [0x18000000, 0x18000001, 0x18000000]

section intern
variable (p : Prog) (hpf : p.lookup "succ_find" = some succFind)
  (hpp : p.lookup "succ_push" = some succPush) (hp : p.lookup "intern_succ" = some internSucc)

include hpf hpp hp in
theorem internSucc_spec (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_succ" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ sinternW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internSucc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        succFind_spec p hpf n, succPush_spec p hpp n] <;>
      finish [sinternW, succHashW, baseW]

end intern

end L.Arena
