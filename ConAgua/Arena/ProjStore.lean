module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The expression `proj` node store in L: two handle fields and a `Nat` field per node

The arena's expression store keeps `proj n i e` nodes in a `Tbl ProjNode EIdx UInt64` per tier
(`Arena/Store.lean:308`, `ETables.projs`). Its L representation is `letE`'s shape (three words per
node, open addressing, scratch-skipping), except the middle word is a plain `Nat` (the projection
index, as `bvar`'s word is) rather than a handle:

* **Records.** Word array `PJREC`, three words per node (the name handle word `n`, the index `i`
  as a word, then the expression handle word `e`), tiers interleaved: node `i` of tier `t` at
  `PJREC[6 i + 3 t ..]`. The node count of tier `t` is `CTL[32 + t]`.
* **Cons table.** Word array `PJSLOT`, the same open addressing as `SLOT`/`LESLOT`.
* **The scratch skip.** `internE (.proj n i e)` does not probe the persistent tier when the
  scratch tier is open and `n` or `e` is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild (.proj n _ e) = if n.isPersistent then !e.isPersistent else true`): bit 27
  of `n | e`, the index `i` not being a handle at all. `letE`'s record width (3) is not a power of
  two, so (as for `letE`) the record-room check is stated by multiplication, not a shift: `L` has
  no division (`PLAN.md`, "the language L").

The functions: `proj_find(t, n, u, e, h)` (the probe, the match inline: two handle-word
comparisons and a word comparison), `proj_push(t, n, u, e, j)` and `intern_proj(n, u, e)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `proj` records, both tiers interleaved (three words per node). -/
abbrev PJREC : ArrId := 31
/-- The `proj` cons-table slots, both tiers interleaved. -/
abbrev PJSLOT : ArrId := 32

/-- The hash of a `proj` record (FNV-1a over its three words). -/
def projHashW (n u e : Word) : Word :=
  (((fnvBasis ^^^ n) * fnvPrime ^^^ u) * fnvPrime ^^^ e) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(n, u, e)`. -/
def pjmatchW (r : Array Word) (t i n u e : Word) : Bool :=
  rdW r (i * 6 + t * 3) == n && rdW r (i * 6 + t * 3 + 1) == u && rdW r (i * 6 + t * 3 + 2) == e

/-! ## `proj_find(t, n, u, e, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `pjmatchW`). -/
def pjprobeW (sl r : Array Word) (t n u e nn j d : Word) : List Word :=
  if d < nn then
    if rdW sl (j * 2 + t) = 0 then [0, 0, j, d]
    else if pjmatchW r t (rdW sl (j * 2 + t) - 1) n u e then [1, rdW sl (j * 2 + t) - 1, j, d]
    else pjprobeW sl r t n u e nn ((j + 1) * (if j + 1 < nn then 1 else 0)) (d + 1)
  else []
termination_by nn.toNat - d.toNat
decreasing_by
  have : d.toNat < nn.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < nn›
  have := nn.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t n u e nn j d : Word)

theorem pjprobeW_free (k : Nat) (hd : d < nn) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] = 0) : pjprobeW sl r t n u e nn j d = [0, 0, j, d] := by
  rw [pjprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv]

theorem pjprobeW_hit (k : Nat) (hd : d < nn) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≠ 0) (hm : pjmatchW r t (sl[k] - 1) n u e = true) :
    pjprobeW sl r t n u e nn j d = [1, sl[k] - 1, j, d] := by
  rw [pjprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]

theorem pjprobeW_next (k : Nat) (j' d' : Word) (hd : d < nn) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hm : pjmatchW r t (sl[k] - 1) n u e = false)
    (hj' : j' = (j + 1) * (if j + 1 < nn then 1 else 0)) (hd' : d' = d + 1) :
    pjprobeW sl r t n u e nn j d = pjprobeW sl r t n u e nn j' d' := by
  subst hj' hd'
  rw [pjprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]; simp

end probeArms

grind_pattern [arena_grind] pjprobeW_free => pjprobeW sl r t n u e nn j d, sl[k]
grind_pattern [arena_grind] pjprobeW_hit => pjprobeW sl r t n u e nn j d, sl[k]
grind_pattern [arena_grind] pjprobeW_next =>
  pjprobeW sl r t n u e nn j d, sl[k], pjprobeW sl r t n u e nn j' d'

def pjfindLoop : Stmt := lblk (t, n, u, e, h, nn, j, d, w) {
  while d < nn {
    w := PJSLOT.u64[j * 2 + t];
    if w == 0 { return (0, 0, j, d) };
    if PJREC.u64[(w - 1) * 6 + t * 3] == n && PJREC.u64[(w - 1) * 6 + t * 3 + 1] == u
        && PJREC.u64[(w - 1) * 6 + t * 3 + 2] == e {
      return (1, w - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < nn);
    d += 1
  }
}

def projFind : FunDecl := lfn (t, n, u, e, h) locals (nn, j, d, w) {
  nn := len(PJSLOT.u64) >> 1;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), nn);
  ⟪pjfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "proj_find" = some projFind)

theorem pjfindLoop_spec (nn : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p nn pjfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (pjprobeW (s₀.mem.arr64 PJSLOT) (s₀.mem.arr64 PJREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)) =
      pjprobeW (s₀.mem.arr64 PJSLOT) (s₀.mem.arr64 PJREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7); ⊤⦄ := by
  induction nn generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ nn ih =>
    rw [exec, step_while (w := pjfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [pjmatchW]

theorem pjfindLoop_step_spec (nn : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p nn) pjfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (pjprobeW (s₀.mem.arr64 PJSLOT) (s₀.mem.arr64 PJREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)) =
      pjprobeW (s₀.mem.arr64 PJSLOT) (s₀.mem.arr64 PJREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7); ⊤⦄ :=
  Triple.step_exec (pjfindLoop_spec p (nn + 1) s₀)

/-- The slot count of a tier of the `proj` table. -/
def nSlotsPj (m : Mem) : Word := m.len64 PJSLOT >>> 1

include hp in
theorem projFind_spec (nn : Nat) (s₀ : St) (t n u e h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p nn) "proj_find" [t, n, u, e, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = pjprobeW (s₀.mem.arr64 PJSLOT) (s₀.mem.arr64 PJREC) t n u e
        (nSlotsPj s₀.mem) (homeW h (nSlotsPj s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, projFind]
  cases nn with
  | zero => vcgen [exec] <;> grind
  | succ nn =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, pjfindLoop_step_spec p nn] <;>
      finish [nSlotsPj, homeW]

end find

/-! ## `proj_push(t, n, u, e, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `proj` table, `CTL[32 + t]`. -/
def pjcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (32 + t)

/-- `proj_push`'s room checks: the handle index, the record array, the load limit. `PJREC`'s
width (3) is not a power of two, so (as for `letE`) the record-room check is stated by
multiplication, `(c + 1) * 6 ≤ len`, matching `PushRoom`'s own shape directly (`L` has no
division). -/
def pjpushOK (m : Mem) (t : Word) : Bool :=
  decide (pjcnt m t < (134217728 : Word)) && decide ((pjcnt m t + 1) * 6 ≤ m.len64 PJREC) &&
    decide (pjcnt m t + 1 ≤ (nSlotsPj m >>> (2 : Word)) * 3)

/-- The memory after `proj_push(t, n, u, e, j)` appended node `c`. -/
def pjpushMem (m : Mem) (t n u e j c : Word) : Mem :=
  ((((m.set64 PJREC (c * 6 + t * 3) n).set64 PJREC (c * 6 + t * 3 + 1) u).set64 PJREC
    (c * 6 + t * 3 + 2) e).set64 PJSLOT (j * 2 + t) (c + 1)).set64 CTL (32 + t) (c + 1)

def projPush : FunDecl := lfn (t, n, u, e, j) locals (c, k) {
  c := CTL.u64[32 + t];
  if c >= 134217728 { abort };
  if len(PJREC.u64) < (c + 1) * 6 { abort };
  if ((len(PJSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 6 + t * 3;
  PJREC.u64[k] := n;
  PJREC.u64[k + 1] := u;
  PJREC.u64[k + 2] := e;
  PJSLOT.u64[j * 2 + t] := c + 1;
  CTL.u64[32 + t] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "proj_push" = some projPush)

include hp in
theorem projPush_spec (nn : Nat) (s₀ : St) (t n u e j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p nn) "proj_push" [t, n, u, e, j]
    ⦃fun r s' => LocEq s' s₀ ∧ pjpushOK s₀.mem t = true ∧ r = [pjcnt s₀.mem t] ∧
      s'.mem = pjpushMem s₀.mem t n u e j (pjcnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, projPush]
  cases nn with
  | zero => vcgen [exec] <;> grind
  | succ nn =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [pjcnt, pjpushOK, pjpushMem, nSlotsPj]

end push

/-! ## `intern_proj(n, u, e)`: hash-cons the expression `proj n u e`

con-ron's `EStore::intern` at `proj` and the arena's `internE (.proj n u.toNat e)`: the persistent
probe unless the scratch tier is open and `n` or `e` is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `proj` tier (tag `9`). -/
def projP : Word := 0x90000000
def projS : Word := 0x98000000

/-- The scratch skip: the scratch tier is open and `n` or `e` is a scratch handle. The index `u`
is not a handle, so it is not tested. -/
def pjskipW (m : Mem) (n e : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((n ||| e) >>> 27) &&& 1 else 0

/-- The model of `intern_proj`: the handle and the memory after, or `none` where the L code
aborts. -/
def pjinternW (m : Mem) (n u e : Word) : Option (Word × Mem) :=
  let h := projHashW n u e
  let rs₀ := pjprobeW (m.arr64 PJSLOT) (m.arr64 PJREC) 0 n u e (nSlotsPj m) (homeW h (nSlotsPj m)) 0
  let rs₁ := pjprobeW (m.arr64 PJSLOT) (m.arr64 PJREC) 1 n u e (nSlotsPj m) (homeW h (nSlotsPj m)) 0
  if pjskipW m n e = 0 ∧ rs₀ = [] then none
  else if pjskipW m n e = 0 ∧ rs₀.headD 0 ≠ 0 then some (projP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (projS + rs₁.tail.headD 0, m)
    else if pjpushOK m 1 then
      some (projS + pjcnt m 1, pjpushMem m 1 n u e (rs₁.tail.tail.headD 0) (pjcnt m 1))
    else none
  else if pjpushOK m 0 then
    some (projP + pjcnt m 0, pjpushMem m 0 n u e (rs₀.tail.tail.headD 0) (pjcnt m 0))
  else none

def internProj : FunDecl := lfn (n, u, e) locals (h, sk, fd, i, j, d) {
  h := (((⟪fnvBasis⟫ ^ n) * ⟪fnvPrime⟫ ^ u) * ⟪fnvPrime⟫ ^ e) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := ((n | e) >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call proj_find(0, n, u, e, h);
    if fd != 0 { return ⟪projP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call proj_find(1, n, u, e, h);
    if fd != 0 { return ⟪projS⟫ + i };
    i := call proj_push(1, n, u, e, j);
    return ⟪projS⟫ + i
  };
  i := call proj_push(0, n, u, e, j);
  return ⟪projP⟫ + i
}

/-- The `proj` store functions, as one `#eval`-able program. -/
def projProg : Prog :=
  [("proj_find", projFind), ("proj_push", projPush), ("intern_proj", internProj)]

/-- A memory with 8 `proj` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥30 (the other tables') are unused here and left empty. -/
def projMem (scratch : Word) : Mem :=
  { words := (Array.replicate 31 #[]).set! 1 ((Array.replicate 34 0).set! 1 scratch) ++
      #[Array.replicate 48 0, Array.replicate 32 0] }

/-- Intern each `(n, i, e)` triple in turn; the handles. -/
def internProjs (m : Mem) : List (Word × Word × Word) → Option (List Word)
  | [] => some []
  | (n, u, e) :: xs => match run projProg 100 "intern_proj" [n, u, e] m with
    | .ok (r, m') => (internProjs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `proj 1 0 2`, `proj 2 0 1`, `proj 1 1 2`, `proj 1 0 2`: persistent handles 0, 1, 2, 0 (sharing
is on the whole triple, not any one field). -/
#guard internProjs (projMem 0) [(1, 0, 2), (2, 0, 1), (1, 1, 2), (1, 0, 2)] ==
  some [0x90000000, 0x90000001, 0x90000002, 0x90000000]

/- Scratch open: a scratch `e` (`0x98000000`) skips the persistent probe; the index `u` alone
being a bit-27 word does not (it is not tested). -/
#guard internProjs (projMem 1) [(1, 0, 2), (1, 0, 0x98000000), (1, 0, 2), (1, 0, 0x98000000)] ==
  some [0x98000000, 0x98000001, 0x98000000, 0x98000001]

section intern
variable (p : Prog) (hpf : p.lookup "proj_find" = some projFind)
  (hpp : p.lookup "proj_push" = some projPush) (hp : p.lookup "intern_proj" = some internProj)

include hpf hpp hp in
theorem internProj_spec (nn : Nat) (s₀ : St) (n u e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p nn) "intern_proj" [n, u, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pjinternW s₀.mem n u e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internProj]
  cases nn with
  | zero => vcgen [exec] <;> grind
  | succ nn =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        projFind_spec p hpf nn, projPush_spec p hpp nn] <;>
      finish [pjinternW, pjskipW, projHashW]

end intern

end L.Arena
