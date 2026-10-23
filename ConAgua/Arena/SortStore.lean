module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The expression `sort` node store in L: a store with a scratch skip, one handle field

The arena's expression store keeps `sort u` nodes in a `Tbl SortNode EIdx UInt64` per tier
(`Arena/Store.lean:278`, `ETables.sorts`). Its L representation is the `succ` store's shape
(`LevelStore.lean`: one handle field) but, like `app`, with the expression store's scratch skip:
`internE (.sort u)` does not probe the persistent tier when the scratch tier is open and `u` is a
scratch handle (`EStore.persFindMaybe`, `eViewHasScratchChild (.sort u) = !u.isPersistent`).

* **Records.** Word array `SOREC`, one word per node (the handle word of `u`), tiers interleaved:
  node `i` of tier `t` at `SOREC[2 i + t]`. The node count of tier `t` is `CTL[16 + t]`.
* **Cons table.** Word array `SOSLOT`, the same open addressing as `SLOT`.

The functions: `sort_find(t, u, h)`, `sort_push(t, u, j)` and `intern_sort(u)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `sort` records, both tiers interleaved (one word per node). -/
abbrev SOREC : ArrId := 16
/-- The `sort` cons-table slots, both tiers interleaved. -/
abbrev SOSLOT : ArrId := 17

/-- The growth schema of this table (`SlotGrow.lean`). -/
def sortGS : GrowSch :=
  ⟨SOSLOT, SOREC, 1, 16, lblk (n, k, t, i, c, h) {
    h := (⟪fnvBasis⟫ ^ SOREC.u64[i * 2 + t]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of a `sort` record (FNV-1a over its word). -/
def sortHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `sort u`. -/
def somatchW (r : Array Word) (t i u : Word) : Bool := rdW r (i * 2 + t) == u

/-! ## `sort_find(t, u, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def soprobeW (sl r : Array Word) (t u b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if somatchW r t (slotV sl b (j * 2 + t) - 1) u then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else soprobeW sl r t u b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
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

theorem soprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : soprobeW sl r t u b n j d = [0, 0, j, d] := by
  rw [soprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem soprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : somatchW r t (sl[k] - b - 1) u = true) :
    soprobeW sl r t u b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [soprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem soprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : somatchW r t (sl[k] - b - 1) u = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    soprobeW sl r t u b n j d = soprobeW sl r t u b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [soprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] soprobeW_free => soprobeW sl r t u b n j d, sl[k]
grind_pattern [arena_grind] soprobeW_hit => soprobeW sl r t u b n j d, sl[k]
grind_pattern [arena_grind] soprobeW_next =>
  soprobeW sl r t u b n j d, sl[k], soprobeW sl r t u b n j' d'

def sofindLoop : Stmt := lblk (t, u, h, n, j, d, v, b) {
  while d < n {
    v := SOSLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    if SOREC.u64[(v - 1) * 2 + t] == u { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def sortFind : FunDecl := lfn (t, u, h) locals (n, j, d, v, b) {
  n := ⟪SN0⟫ << SOSLOT.u64[len(SOSLOT.u64) - 1];
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪sofindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "sort_find" = some sortFind)

theorem sofindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n sofindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (soprobeW (s₀.mem.arr64 SOSLOT) (s₀.mem.arr64 SOREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      soprobeW (s₀.mem.arr64 SOSLOT) (s₀.mem.arr64 SOREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := sofindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [somatchW, baseW]

theorem sofindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) sofindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (soprobeW (s₀.mem.arr64 SOSLOT) (s₀.mem.arr64 SOREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      soprobeW (s₀.mem.arr64 SOSLOT) (s₀.mem.arr64 SOREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ :=
  Triple.step_exec (sofindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `sort` table. -/
def nSlotsSo (m : Mem) : Word := SN0 <<< rdW (m.arr64 SOSLOT) (m.len64 SOSLOT - 1)

include hp in
theorem sortFind_spec (n : Nat) (s₀ : St) (t u h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sort_find" [t, u, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = soprobeW (s₀.mem.arr64 SOSLOT) (s₀.mem.arr64 SOREC) t u
        (baseW s₀.mem t) (nSlotsSo s₀.mem) (homeW h (nSlotsSo s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, sortFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, sofindLoop_step_spec p n, ld64] <;>
      finish [nSlotsSo, homeW, baseW]

end find

/-! ## `sort_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `sort` table, `CTL[16 + t]`. -/
def socnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (16 + t)

/-- `sort_push`'s room checks: the handle index, the record array. -/
def sopushOK (m : Mem) (t : Word) : Bool :=
  decide (socnt m t < (134217728 : Word)) && decide (socnt m t < m.len64 SOREC >>> (1 : Word)) &&
    decide (socnt m t < m.len64 SOLP >>> (1 : Word))

/-- The memory after `sort_push(t, u, j)` appended node `c`. -/
def sopushMem (m : Mem) (t u j c : Word) : Mem :=
  ((((m.set64 SOREC (c * 2 + t) u).set64 SOSLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (16 + (t &&& 1)) (c + 1)).set64
    SOLP (c * 2 + t) (lvlHPW m u))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def sortPush : FunDecl := lfn (t, u, j) locals (c, x, g, ti, ix, gn, gk, gt, gi, gc, gh, gj, gb, gd) {
  ⟪hpBlkS⟫;
  c := CTL.u64[16 + t];
  if c >= 134217728 { abort };
  if len(SOREC.u64) >> 1 <= c { abort };
  if len(SOLP.u64) >> 1 <= c { abort };
  SOREC.u64[c * 2 + t] := u;
  gk := SOSLOT.u64[len(SOSLOT.u64) - 1];
  SOSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[16 + (t & 1)] := c + 1;
  SOLP.u64[c * 2 + t] := x;
  if (⟪SN0⟫ << gk) < (c + 1) * 2 { ⟪growBlkG sortGS 8⟫ };
  return c
}

/-- The hash of node `i` of tier `t`. -/
def sohash (m : Mem) (t i : Word) : Word := sortHashW (rdW (m.arr64 SOREC) (i * 2 + t))

section push
variable (p : Prog) (hp : p.lookup "sort_push" = some sortPush)

/-- The growth's hash block computes `sohash`. -/
theorem sohash_ok : HashOK p sortGS 8 sohash := by
  intro k s₀
  simp only [sortGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [sohash, sortHashW, LocEq, St.setLoc]

include hp in
theorem sortPush_spec (n : Nat) (s₀ : St) (t u j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sort_push" [t, u, j]
    ⦃fun r s' => LocEq s' s₀ ∧ sopushOK s₀.mem t = true ∧ r = [socnt s₀.mem t] ∧
      growIf SOSLOT 16 sohash s₀.mem (sopushMem s₀.mem t u j (socnt s₀.mem t))
        (socnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, sortPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64, hpBlkS_spec p (exec p n),
        growBlkG_spec p sortGS SOSLOT 16 rfl rfl 8 sohash (sohash_ok p) n]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals first
      | (rw [growIf_grow]; (focus simp only [sopushMem, socnt, baseW, SCB]; grind [arena_grind, lang_grind]);
          grind [arena_grind, lang_grind, socnt, gnW, gexpW])
      | (rw [growIf_keep]; (focus simp only [sopushMem, socnt, baseW, SCB]; grind [arena_grind, lang_grind]);
          grind [arena_grind, lang_grind, socnt, gnW, gexpW])
      | grind [arena_grind, lang_grind, socnt, sopushOK, baseW, LocEq]

end push

/-! ## `intern_sort(u)`: hash-cons the expression `sort u`

con-ron's `EStore::intern` at `sort` and the arena's `internE (.sort u)`: the persistent probe
unless the scratch tier is open and `u` is a scratch handle, the scratch probe if the scratch
tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `sort` tier (tag `2`). -/
def sortP : Word := 0x20000000
def sortS : Word := 0x28000000

/-- The scratch skip: the scratch tier is open and `u` is a scratch handle. -/
def soskipW (m : Mem) (u : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then (u >>> 27) &&& 1 else 0

/-- The model of `intern_sort`: the handle and the memory after, or `none` where the L code
aborts. -/
def sointernW (m : Mem) (u : Word) : Option (Word × Mem) :=
  let h := sortHashW u
  let rs₀ := soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 0 u (baseW m 0) (nSlotsSo m) (homeW h (nSlotsSo m)) 0
  let rs₁ := soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 1 u (baseW m 1) (nSlotsSo m) (homeW h (nSlotsSo m)) 0
  if soskipW m u = 0 ∧ rs₀ = [] then none
  else if soskipW m u = 0 ∧ rs₀.headD 0 ≠ 0 then some (sortP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (sortS + rs₁.tail.headD 0, m)
    else if sopushOK m 1 then
      match growIf SOSLOT 16 sohash m (sopushMem m 1 u (rs₁.tail.tail.headD 0) (socnt m 1)) (socnt m 1) with
      | some m' => some (sortS + socnt m 1, m')
      | none => none
    else none
  else if sopushOK m 0 then
    match growIf SOSLOT 16 sohash m (sopushMem m 0 u (rs₀.tail.tail.headD 0) (socnt m 0)) (socnt m 0) with
    | some m' => some (sortP + socnt m 0, m')
    | none => none
  else none

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internSort : FunDecl := lfn (u) locals (h, sk, fd, i, j, d) {
  h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := (u >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call sort_find(0, u, h);
    if fd != 0 { return ⟪sortP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call sort_find(1, u, h);
    if fd != 0 { return ⟪sortS⟫ + i };
    i := call sort_push(1, u, j);
    return ⟪sortS⟫ + i
  };
  i := call sort_push(0, u, j);
  return ⟪sortP⟫ + i
}

/-- The `sort` store functions, as one `#eval`-able program. -/
def sortProg : Prog :=
  [("sort_find", sortFind), ("sort_push", sortPush), ("intern_sort", internSort)]

/-- A memory with 8 `sort` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥15 (the other tables') are unused here and left empty. -/
def sortMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], Array.replicate 16 0,
      Array.replicate 32 0] ++ Array.replicate 44 (Array.replicate 32 0) }

/-- Intern each handle word in turn; the handles. -/
def internSorts (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run sortProg 100 "intern_sort" [u] m with
    | .ok (r, m') => (internSorts m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `sort` of handles `1`, `2`, `1`: persistent handles 0, 1, 0 (sharing). -/
#guard internSorts (sortMem 0) [1, 2, 1] == some [0x20000000, 0x20000001, 0x20000000]

/- Scratch open: a persistent child is probed in the persistent tier (empty); the nodes go to
the scratch tier; a scratch child (`0x28000000`) skips the persistent probe. -/
#guard internSorts (sortMem 1) [1, 0x28000000, 1, 0x28000000] ==
  some [0x28000000, 0x28000001, 0x28000000, 0x28000001]

section intern
variable (p : Prog) (hpf : p.lookup "sort_find" = some sortFind)
  (hpp : p.lookup "sort_push" = some sortPush) (hp : p.lookup "intern_sort" = some internSort)

include hpf hpp hp in
theorem internSort_spec (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_sort" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ sointernW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internSort]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        sortFind_spec p hpf n, sortPush_spec p hpp n] <;>
      finish [sointernW, soskipW, sortHashW, baseW]

end intern

end L.Arena
