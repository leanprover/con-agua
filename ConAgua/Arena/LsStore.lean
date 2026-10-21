module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level-list store in L: a variable-length key in the shared pool

The arena's level-list store keeps one node per universe-argument list, a
`Tbl ListNode LsIdx LDer` per tier (`Arena/Store.lean:229`, `LsTables.lists`), keyed by the whole
`List LIdx`. Its L representation keeps the list in the **pool** (`POOL`, the array the `lit`
store keeps its limbs in), one handle word per element, and the record points at the slice:

* **Records.** Word array `LSREC`, three words per node: pool offset, length, and the hash of the
  slice (`lit_hash`, FNV-1a over the words). Tiers interleaved: node `i` of tier `t` at
  `LSREC[6 i + 3 t ..]`. The node count of tier `t` is `CTL[40 + t]`.
* **Cons table.** Word array `LSSLOT`, the same open addressing as `SLOT`.
* **The key.** A slice `(o, l)` below the pool top. Matching is `lit`'s: the hash, the length,
  then `limbs_eq` word for word. The level-list store has no scratch skip
  (`LsStore.find?` probes the persistent tier unconditionally).

The functions: `ls_match(t, i, o, l, h)`, `ls_find(t, o, l, h)`, `ls_push(t, o, l, h, j)` and
`intern_ls(o, l)` (`internLsNode us` for the list whose handle words are the slice). They call
`lit_hash` and `limbs_eq` (`Store.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The level-list records, both tiers interleaved (three words per node). -/
abbrev LSREC : ArrId := 39
/-- The level-list cons-table slots, both tiers interleaved. -/
abbrev LSSLOT : ArrId := 40

/-! ## `ls_match(t, i, o, l, h)` -/

/-- The model of `ls_match`: node `i` of tier `t` has hash `h`, length `l` and the words of the
slice `(o, l)`. -/
def lsmatchW (r p : Array Word) (t i o l h : Word) : Bool :=
  rdW r (i * 6 + t * 3 + 2) == h && rdW r (i * 6 + t * 3 + 1) == l &&
    eqW p (rdW r (i * 6 + t * 3)) o l 0

def lsMatch : FunDecl := lfn (t, i, o, l, h) locals (k, e) {
  k := i * 6 + t * 3;
  if LSREC.u64[k + 2] != h { return 0 };
  if LSREC.u64[k + 1] != l { return 0 };
  e := call limbs_eq(LSREC.u64[k], o, l);
  return e
}

section match_
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hp : p.lookup "ls_match" = some lsMatch)

include hpe hp in
theorem lsMatch_spec (n : Nat) (s₀ : St) (t i o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_match" [t, i, o, l, h]
    ⦃fun r s' => s' = s₀ ∧
      r = [if lsmatchW (s₀.mem.arr64 LSREC) (s₀.mem.arr64 POOL) t i o l h then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lsMatch]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, limbsEq_spec p hpe n] <;>
      finish [lsmatchW, baseW]

end match_

/-! ## `ls_find(t, o, l, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def lsprobeW (sl r p : Array Word) (t o l h b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if lsmatchW r p t (slotV sl b (j * 2 + t) - 1) o l h then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else lsprobeW sl r p t o l h b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r p : Array Word) (t o l h b n j d : Word)

theorem lsprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : lsprobeW sl r p t o l h b n j d = [0, 0, j, d] := by
  rw [lsprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem lsprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : lsmatchW r p t (sl[k] - b - 1) o l h = true) :
    lsprobeW sl r p t o l h b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [lsprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem lsprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : lsmatchW r p t (sl[k] - b - 1) o l h = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    lsprobeW sl r p t o l h b n j d = lsprobeW sl r p t o l h b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [lsprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] lsprobeW_free => lsprobeW sl r p t o l h b n j d, sl[k]
grind_pattern [arena_grind] lsprobeW_hit => lsprobeW sl r p t o l h b n j d, sl[k]
grind_pattern [arena_grind] lsprobeW_next =>
  lsprobeW sl r p t o l h b n j d, sl[k], lsprobeW sl r p t o l h b n j' d'

def lsfindLoop : Stmt := lblk (t, o, l, h, n, j, d, v, m, b) {
  while d < n {
    v := LSSLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    m := call ls_match(t, v - 1, o, l, h);
    if m != 0 { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def lsFind : FunDecl := lfn (t, o, l, h) locals (n, j, d, v, m, b) {
  n := len(LSSLOT.u64) >> 1;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪lsfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hpm : p.lookup "ls_match" = some lsMatch) (hp : p.lookup "ls_find" = some lsFind)

include hpe hpm in
theorem lsfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lsfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (lsprobeW (s₀.mem.arr64 LSSLOT) (s₀.mem.arr64 LSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      lsprobeW (s₀.mem.arr64 LSSLOT) (s₀.mem.arr64 LSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lsfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        lsMatch_spec p hpe hpm n] <;> finish

include hpe hpm in
theorem lsfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) lsfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (lsprobeW (s₀.mem.arr64 LSSLOT) (s₀.mem.arr64 LSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      lsprobeW (s₀.mem.arr64 LSSLOT) (s₀.mem.arr64 LSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (lsfindLoop_spec p hpe hpm (n + 1) s₀)

/-- The slot count of a tier of the level-list table. -/
def nSlotsLs (m : Mem) : Word := m.len64 LSSLOT >>> 1

include hpe hpm hp in
theorem lsFind_spec (n : Nat) (s₀ : St) (t o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_find" [t, o, l, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = lsprobeW (s₀.mem.arr64 LSSLOT) (s₀.mem.arr64 LSREC) (s₀.mem.arr64 POOL) t o l h
        (baseW s₀.mem t) (nSlotsLs s₀.mem) (homeW h (nSlotsLs s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lsFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, lsfindLoop_step_spec p hpe hpm n, ld64] <;>
      finish [nSlotsLs, homeW, baseW]

end find

/-! ## `ls_push(t, o, l, h, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the level-list table, `CTL[40 + t]`. -/
def lscnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (40 + t)

/-- `ls_push`'s room checks: the handle index, the record array (width 3: by multiplication,
as `letE`'s), the load limit. -/
def lspushOK (m : Mem) (t : Word) : Bool :=
  decide (lscnt m t < (134217728 : Word)) && decide ((lscnt m t + 1) * 6 ≤ m.len64 LSREC) &&
    decide (lscnt m t + 1 ≤ (nSlotsLs m >>> (2 : Word)) * 3)

/-- The memory after `ls_push(t, o, l, h, j)` appended node `c`. -/
def lspushMem (m : Mem) (t o l h j c : Word) : Mem :=
  ((((m.set64 LSREC (c * 6 + t * 3) o).set64 LSREC (c * 6 + t * 3 + 1) l).set64 LSREC
    (c * 6 + t * 3 + 2) h).set64 LSSLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (40 + (t &&& 1)) (c + 1)

def lsPush : FunDecl := lfn (t, o, l, h, j) locals (c, k) {
  c := CTL.u64[40 + t];
  if c >= 134217728 { abort };
  if len(LSREC.u64) < (c + 1) * 6 { abort };
  if ((len(LSSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 6 + t * 3;
  LSREC.u64[k] := o;
  LSREC.u64[k + 1] := l;
  LSREC.u64[k + 2] := h;
  LSSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[40 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "ls_push" = some lsPush)

include hp in
theorem lsPush_spec (n : Nat) (s₀ : St) (t o l h j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_push" [t, o, l, h, j]
    ⦃fun r s' => LocEq s' s₀ ∧ lspushOK s₀.mem t = true ∧ r = [lscnt s₀.mem t] ∧
      s'.mem = lspushMem s₀.mem t o l h j (lscnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lsPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [lscnt, lspushOK, lspushMem, nSlotsLs, baseW]

end push

/-! ## `intern_ls(o, l)`: hash-cons the level list whose handle words are the slice `(o, l)`

The arena's `internLsNode us`: the persistent probe, the scratch probe if the scratch tier is
open, the append to the tier the store is in. Handle tag `0` (`LsTag.list`). -/

/-- The handle word of node `0` of the persistent / scratch level-list tier. -/
def lsP : Word := 0x00000000
def lsS : Word := 0x08000000

/-- The model of `intern_ls`: the handle and the memory after, or `none` where the L code
aborts. -/
def lsinternW (m : Mem) (o l : Word) : Option (Word × Mem) :=
  let h := hashN (m.arr64 POOL) o.toNat l.toNat
  let rs₀ := lsprobeW (m.arr64 LSSLOT) (m.arr64 LSREC) (m.arr64 POOL) 0 o l h (baseW m 0) (nSlotsLs m)
    (homeW h (nSlotsLs m)) 0
  let rs₁ := lsprobeW (m.arr64 LSSLOT) (m.arr64 LSREC) (m.arr64 POOL) 1 o l h (baseW m 1) (nSlotsLs m)
    (homeW h (nSlotsLs m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (lsP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (lsS + rs₁.tail.headD 0, m)
    else if lspushOK m 1 then
      some (lsS + lscnt m 1, lspushMem m 1 o l h (rs₁.tail.tail.headD 0) (lscnt m 1))
    else none
  else if lspushOK m 0 then
    some (lsP + lscnt m 0, lspushMem m 0 o l h (rs₀.tail.tail.headD 0) (lscnt m 0))
  else none

@[l_impl ConRon.Arena.internLsNode]
def internLs : FunDecl := lfn (o, l) locals (h, f, i, j, d, sc) {
  h := call lit_hash(o, l);
  (f, i, j, d) := call ls_find(0, o, l, h);
  if f != 0 { return ⟪lsP⟫ + i };
  sc := CTL.u64[1];
  if sc != 0 {
    (f, i, j, d) := call ls_find(1, o, l, h);
    if f != 0 { return ⟪lsS⟫ + i };
    i := call ls_push(1, o, l, h, j);
    return ⟪lsS⟫ + i
  };
  i := call ls_push(0, o, l, h, j);
  return ⟪lsP⟫ + i
}

/-- The level-list store functions, as one `#eval`-able program. -/
def lsProg : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("ls_match", lsMatch), ("ls_find", lsFind),
   ("ls_push", lsPush), ("intern_ls", internLs)]

/-- A memory with the lists `[5]`, `[7]`, `[5]`, `[5, 7]`, `[]` in the pool (top 5), 8 nodes and
16 slots per tier, the scratch tier closed or open. -/
def lsMem (scratch : Word) : Mem :=
  { words := #[#[5, 7, 5, 5, 7, 0, 0, 0], (Array.replicate 64 0).set! 1 scratch |>.set! 0 5] ++
      Array.replicate 37 #[] ++ #[Array.replicate 48 0, Array.replicate 32 0] }

/-- Intern each slice in turn; the handles. -/
def internLss (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (o, l) :: xs => match run lsProg 100 "intern_ls" [o, l] m with
    | .ok (r, m') => (internLss m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `[5]`, `[7]`, `[5]` (another copy), `[5, 7]`, `[]`, `[]`: persistent handles 0, 1, 0, 2, 3, 3. -/
#guard internLss (lsMem 0) [(0, 1), (1, 1), (2, 1), (3, 2), (0, 0), (4, 0)] ==
  some [0, 1, 0, 2, 3, 3]

/- With the scratch tier open the nodes go there. -/
#guard internLss (lsMem 1) [(0, 1), (1, 1), (2, 1)] == some [0x08000000, 0x08000001, 0x08000000]

section intern
variable (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
  (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "ls_match" = some lsMatch)
  (hpf : p.lookup "ls_find" = some lsFind) (hpp : p.lookup "ls_push" = some lsPush)
  (hp : p.lookup "intern_ls" = some internLs)

include hph hpe hpm hpf hpp hp in
theorem internLs_spec (n : Nat) (s₀ : St) (o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_ls" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ lsinternW s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internLs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, litHash_spec p hph n,
        lsFind_spec p hpe hpm hpf n, lsPush_spec p hpp n] <;>
      finish [lsinternW, baseW]

end intern

end L.Arena
