module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# The name store's `str` table in L: a prefix handle and a string in the shared pool

The arena's name store keeps `str pre s` nodes in a `Tbl StrNode NIdx UInt64` per tier
(`Arena/Store.lean:113`, `NTables.strs`), keyed by the prefix handle and the whole `String`. Its L
representation keeps the string's UTF-8 bytes in the **pool** (`POOL`), one byte per word, and the
record points at the slice, as the level-list store (`LsStore.lean`) does with handle words:

* **Records.** Word array `NSREC`, four words per node: the prefix's handle word, pool offset,
  length, and the hash (`lit_hash` of the slice, then one FNV step with the prefix). Tiers
  interleaved: node `i` of tier `t` at `NSREC[8 i + 4 t ..]`. The node count of tier `t` is
  `CTL[36 + t]`.
* **Cons table.** Word array `NSSLOT`, the same open addressing as `SLOT`.
* **The key.** The prefix word and a slice `(o, l)` below the pool top. Matching: the prefix, the
  hash, the length, then `limbs_eq`. The name store has no scratch skip.

One byte per word keeps the comparison and the hash `lit`'s (`limbs_eq`, `lit_hash`) and the key
a list of words (`PoolSlice.lean`); packing eight bytes per word is a later optimisation.

The functions: `nstr_match(t, i, q, o, l, h)`, `nstr_find(t, q, o, l, h)`,
`nstr_push(t, q, o, l, h, j)` and `intern_nstr(q, o, l)` (`internNNode (.str pre s)` for the
prefix `q` and the string whose bytes the slice holds).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The name `str` records, both tiers interleaved (four words per node). -/
abbrev NSREC : ArrId := 35
/-- The name `str` cons-table slots, both tiers interleaved. -/
abbrev NSSLOT : ArrId := 36

/-- The growth schema of this table (`SlotGrow.lean`). -/
def nstrGS : GrowSch :=
  ⟨NSSLOT, NSREC, 4, 36, NSSLOT_G, lblk (n, k, t, i, c, h) {
    h := NSREC.u64[i * 8 + t * 4 + 3]
  }⟩

/-! ## `nstr_match(t, i, q, o, l, h)` -/

/-- The model of `nstr_match`: node `i` of tier `t` has prefix `q`, hash `h`, length `l` and the
words of the slice `(o, l)`. -/
def nsmatchW (r p : Array Word) (t i q o l h : Word) : Bool :=
  rdW r (i * 8 + t * 4) == q && rdW r (i * 8 + t * 4 + 3) == h &&
    rdW r (i * 8 + t * 4 + 2) == l && eqW p (rdW r (i * 8 + t * 4 + 1)) o l 0

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def nsMatch : FunDecl := lfn (t, i, q, o, l, h) locals (k, e) {
  k := i * 8 + t * 4;
  if NSREC.u64[k] != q { return 0 };
  if NSREC.u64[k + 3] != h { return 0 };
  if NSREC.u64[k + 2] != l { return 0 };
  e := call limbs_eq(NSREC.u64[k + 1], o, l);
  return e
}

section match_
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hp : p.lookup "nstr_match" = some nsMatch)

include hpe hp in
theorem nsMatch_spec (n : Nat) (s₀ : St) (t i q o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nstr_match" [t, i, q, o, l, h]
    ⦃fun r s' => s' = s₀ ∧
      r = [if nsmatchW (s₀.mem.arr64 NSREC) (s₀.mem.arr64 POOL) t i q o l h then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nsMatch]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, limbsEq_spec p hpe n] <;>
      finish [nsmatchW, baseW]

end match_

/-! ## `nstr_find(t, q, o, l, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def nsprobeW (sl r p : Array Word) (t q o l h b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if nsmatchW r p t (slotV sl b (j * 2 + t) - 1) q o l h then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else nsprobeW sl r p t q o l h b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r p : Array Word) (t q o l h b n j d : Word)

theorem nsprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : nsprobeW sl r p t q o l h b n j d = [0, 0, j, d] := by
  rw [nsprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem nsprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : nsmatchW r p t (sl[k] - b - 1) q o l h = true) :
    nsprobeW sl r p t q o l h b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [nsprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem nsprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : nsmatchW r p t (sl[k] - b - 1) q o l h = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    nsprobeW sl r p t q o l h b n j d = nsprobeW sl r p t q o l h b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [nsprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] nsprobeW_free => nsprobeW sl r p t q o l h b n j d, sl[k]
grind_pattern [arena_grind] nsprobeW_hit => nsprobeW sl r p t q o l h b n j d, sl[k]
grind_pattern [arena_grind] nsprobeW_next =>
  nsprobeW sl r p t q o l h b n j d, sl[k], nsprobeW sl r p t q o l h b n j' d'

def nsfindLoop : Stmt := lblk (t, q, o, l, h, n, j, d, v, m, b) {
  while d < n {
    v := NSSLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    m := call nstr_match(t, v - 1, q, o, l, h);
    if m != 0 { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def nsFind : FunDecl := lfn (t, q, o, l, h) locals (n, j, d, v, m, b) {
  n := ⟪SN0⟫ << NSSLOT_G;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪nsfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hpm : p.lookup "nstr_match" = some nsMatch) (hp : p.lookup "nstr_find" = some nsFind)

include hpe hpm in
theorem nsfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n nsfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (nsprobeW (s₀.mem.arr64 NSSLOT) (s₀.mem.arr64 NSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 10) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)) =
      nsprobeW (s₀.mem.arr64 NSSLOT) (s₀.mem.arr64 NSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 10) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := nsfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        nsMatch_spec p hpe hpm n] <;> finish

include hpe hpm in
theorem nsfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) nsfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (nsprobeW (s₀.mem.arr64 NSSLOT) (s₀.mem.arr64 NSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 10) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)) =
      nsprobeW (s₀.mem.arr64 NSSLOT) (s₀.mem.arr64 NSREC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 10) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7); ⊤⦄ :=
  Triple.step_exec (nsfindLoop_spec p hpe hpm (n + 1) s₀)

/-- The slot count of a tier of the name `str` table. -/
def nSlotsNs (m : Mem) : Word := SN0 <<< m.glob NSSLOT_G

include hpe hpm hp in
theorem nsFind_spec (n : Nat) (s₀ : St) (t q o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nstr_find" [t, q, o, l, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = nsprobeW (s₀.mem.arr64 NSSLOT) (s₀.mem.arr64 NSREC) (s₀.mem.arr64 POOL) t q o l h
        (baseW s₀.mem t) (nSlotsNs s₀.mem) (homeW h (nSlotsNs s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nsFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, nsfindLoop_step_spec p hpe hpm n, ld64] <;>
      finish [nSlotsNs, homeW, baseW]

end find

/-! ## `nstr_push(t, q, o, l, h, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the name `str` table, `CTL[36 + t]`. -/
def nscnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (36 + t)

/-- `nstr_push`'s room checks: the handle index, the record array (by multiplication, as
`letE`'s), the load limit. -/
def nspushOK (m : Mem) (t : Word) : Bool :=
  decide (nscnt m t < (134217728 : Word)) && decide ((nscnt m t + 1) * 8 ≤ m.len64 NSREC) &&
    decide (nscnt m t + 1 ≤ (nSlotsNs m >>> (2 : Word)) * 3)

/-- The memory after `nstr_push(t, q, o, l, h, j)` appended node `c`. -/
def nspushMem (m : Mem) (t q o l h j c : Word) : Mem :=
  (((((m.set64 NSREC (c * 8 + t * 4) q).set64 NSREC (c * 8 + t * 4 + 1) o).set64 NSREC
    (c * 8 + t * 4 + 2) l).set64 NSREC (c * 8 + t * 4 + 3) h).set64 NSSLOT (j * 2 + t)
    (baseW m t + c + 1)).set64 CTL (36 + (t &&& 1)) (c + 1)

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def nsPush : FunDecl := lfn (t, q, o, l, h, j) locals (c, k, gr) {
  c := CTL.u64[36 + t];
  if c >= 134217728 { abort };
  if len(NSREC.u64) < (c + 1) * 8 { abort };
  k := c * 8 + t * 4;
  NSREC.u64[k] := q;
  NSREC.u64[k + 1] := o;
  NSREC.u64[k + 2] := l;
  NSREC.u64[k + 3] := h;
  NSSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[36 + (t & 1)] := c + 1;
  if (⟪SN0⟫ << NSSLOT_G) < (c + 1) * 2 { gr := call nstr_grow() };
  return c
}

section push
variable (p : Prog) (hp : p.lookup "nstr_push" = some nsPush)

include hp in
theorem nsPush_spec (n : Nat) (s₀ : St) (t q o l h j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nstr_push" [t, q, o, l, h, j]
    ⦃fun r s' => LocEq s' s₀ ∧ nspushOK s₀.mem t = true ∧ r = [nscnt s₀.mem t] ∧
      s'.mem = nspushMem s₀.mem t q o l h j (nscnt s₀.mem t); ⊤⦄ := by
  sorry -- slotgrow: the push grows the table

end push

/-! ## `intern_nstr(q, o, l)`: hash-cons the name `str q s`, `s` the string the slice holds

The arena's `internNNode (.str pre s)`: the persistent probe, the scratch probe if the scratch
tier is open, the append to the tier the store is in. Handle tag `1` (`NTag.str`). -/

/-- The handle word of node `0` of the persistent / scratch name `str` tier. -/
def nsP : Word := 0x10000000
def nsS : Word := 0x18000000

/-- The hash of a name `str` record: the slice's, then one FNV step with the prefix. -/
def nstrHashW (q hs : Word) : Word := (hs ^^^ q) * fnvPrime

/-- The model of `intern_nstr`: the handle and the memory after, or `none` where the L code
aborts. -/
def nsinternW (m : Mem) (q o l : Word) : Option (Word × Mem) :=
  let h := nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)
  let rs₀ := nsprobeW (m.arr64 NSSLOT) (m.arr64 NSREC) (m.arr64 POOL) 0 q o l h (baseW m 0) (nSlotsNs m)
    (homeW h (nSlotsNs m)) 0
  let rs₁ := nsprobeW (m.arr64 NSSLOT) (m.arr64 NSREC) (m.arr64 POOL) 1 q o l h (baseW m 1) (nSlotsNs m)
    (homeW h (nSlotsNs m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (nsP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (nsS + rs₁.tail.headD 0, m)
    else if nspushOK m 1 then
      some (nsS + nscnt m 1, nspushMem m 1 q o l h (rs₁.tail.tail.headD 0) (nscnt m 1))
    else none
  else if nspushOK m 0 then
    some (nsP + nscnt m 0, nspushMem m 0 q o l h (rs₀.tail.tail.headD 0) (nscnt m 0))
  else none

/-- con-ron: ConRon/Arena/Monad.lean:381-397 ConRon.Arena.internNNode -/
@[l_impl ConRon.Arena.internNNode]
def internNStr : FunDecl := lfn (q, o, l) locals (h, f, i, j, d, sc) {
  h := call lit_hash(o, l);
  h := (h ^ q) * ⟪fnvPrime⟫;
  (f, i, j, d) := call nstr_find(0, q, o, l, h);
  if f != 0 { return ⟪nsP⟫ + i };
  sc := CTL.u64[1];
  if sc != 0 {
    (f, i, j, d) := call nstr_find(1, q, o, l, h);
    if f != 0 { return ⟪nsS⟫ + i };
    i := call nstr_push(1, q, o, l, h, j);
    return ⟪nsS⟫ + i
  };
  i := call nstr_push(0, q, o, l, h, j);
  return ⟪nsP⟫ + i
}

/-- The name `str` store functions, as one `#eval`-able program. -/
def nstrProg : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind),
   ("nstr_push", nsPush), ("nstr_grow", slotGrowG nstrGS), ("intern_nstr", internNStr)]

/-- A memory with the strings `"a"`, `"b"`, `"a"`, `"ab"` in the pool (top 5), 8 nodes and 16
slots per tier, the scratch tier closed or open. -/
def nstrMem (scratch : Word) : Mem :=
  { words := #[#[97, 98, 97, 97, 98, 0, 0, 0], (Array.replicate 64 0).set! 1 scratch |>.set! 0 5] ++
      Array.replicate 33 #[] ++ #[Array.replicate 64 0, Array.replicate 32 0] }

/-- Intern each `(prefix, offset, length)` in turn; the handles. -/
def internNStrs (m : Mem) : List (Word × Word × Word) → Option (List Word)
  | [] => some []
  | (q, o, l) :: xs => match run nstrProg 100 "intern_nstr" [q, o, l] m with
    | .ok (r, m') => (internNStrs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `0.a`, `0.b`, `0.a` (another copy), `0.ab`, `1.a`: persistent handles 0, 1, 0, 2, 3. -/
#guard internNStrs (nstrMem 0) [(0, 0, 1), (0, 1, 1), (0, 2, 1), (0, 3, 2), (1, 0, 1)] ==
  some [0x10000000, 0x10000001, 0x10000000, 0x10000002, 0x10000003]

/- With the scratch tier open the nodes go there. -/
#guard internNStrs (nstrMem 1) [(0, 0, 1), (0, 1, 1), (0, 2, 1)] ==
  some [0x18000000, 0x18000001, 0x18000000]

section intern
variable (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
  (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "nstr_match" = some nsMatch)
  (hpf : p.lookup "nstr_find" = some nsFind) (hpp : p.lookup "nstr_push" = some nsPush)
  (hp : p.lookup "intern_nstr" = some internNStr)

include hph hpe hpm hpf hpp hp in
theorem internNStr_spec (n : Nat) (s₀ : St) (q o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nstr" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ nsinternW s₀.mem q o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internNStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, litHash_spec p hph n,
        nsFind_spec p hpe hpm hpf n, nsPush_spec p hpp n] <;>
      finish [nsinternW, nstrHashW, baseW]

end intern

end L.Arena
