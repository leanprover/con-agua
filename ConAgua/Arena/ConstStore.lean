module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The `const` node store in L: an expression store with a two-field, mixed-kind key

The arena's `const` constructor is a `Tbl ConstNode EIdx UInt64` per tier, `ConstNode { n : NIdx,
us : LsIdx }` (`Arena/Store.lean:278`): a name handle and a level-list handle (both just words in
L; the variable names below are `f`/`a`, the `app` store's, standing for `n`/`us` here — the two
handle words of the key, of whichever kind). Its L representation follows `app`'s exactly, the
same width-2, scratch-skipping shape:

* **Records.** Word array `CREC`, two words per node (the handle words of `n` and `us`), tiers
  interleaved: node `i` of tier `t` at `CREC[4 i + 2 t ..]`. No stored hash: the hash is a
  cheap function of the two words. The node count of tier `t` is `CTL[18 + t]`.
* **Cons table.** Word array `CSLOT`, the same open addressing as `SLOT` (slot `j` of tier `t`
  at `CSLOT[2 j + t]`, `0` free, `i + 1` node `i`, linear probing from `homeW`).
* **The scratch skip.** `internE (.const n us)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `n | us`.

The functions: `const_find(t, n, us, h)` (the probe, the match inline: two word comparisons),
`const_push(t, n, us, j)` and `intern_const(n, us)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `const` records, both tiers interleaved (two words per node). -/
abbrev CREC : ArrId := 18
/-- The `const` cons-table slots, both tiers interleaved. -/
abbrev CSLOT : ArrId := 19

/-- The hash of a `const` record (FNV-1a over its two words). -/
def constHashW (f a : Word) : Word := ((fnvBasis ^^^ f) * fnvPrime ^^^ a) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(f, a)`. -/
def cematchW (r : Array Word) (t i f a : Word) : Bool :=
  rdW r (i * 4 + t * 2) == f && rdW r (i * 4 + t * 2 + 1) == a

/-! ## `const_find(t, n, us, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `cematchW`). -/
def ceprobeW (sl r : Array Word) (t f a n j d : Word) : List Word :=
  if d < n then
    if rdW sl (j * 2 + t) = 0 then [0, 0, j, d]
    else if cematchW r t (rdW sl (j * 2 + t) - 1) f a then [1, rdW sl (j * 2 + t) - 1, j, d]
    else ceprobeW sl r t f a n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t f a n j d : Word)

theorem ceprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] = 0) : ceprobeW sl r t f a n j d = [0, 0, j, d] := by
  rw [ceprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv]

theorem ceprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≠ 0) (hm : cematchW r t (sl[k] - 1) f a = true) :
    ceprobeW sl r t f a n j d = [1, sl[k] - 1, j, d] := by
  rw [ceprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]

theorem ceprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hm : cematchW r t (sl[k] - 1) f a = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    ceprobeW sl r t f a n j d = ceprobeW sl r t f a n j' d' := by
  subst hj' hd'
  rw [ceprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]; simp

end probeArms

grind_pattern [arena_grind] ceprobeW_free => ceprobeW sl r t f a n j d, sl[k]
grind_pattern [arena_grind] ceprobeW_hit => ceprobeW sl r t f a n j d, sl[k]
grind_pattern [arena_grind] ceprobeW_next =>
  ceprobeW sl r t f a n j d, sl[k], ceprobeW sl r t f a n j' d'

def cefindLoop : Stmt := lblk (t, f, a, h, n, j, d, v) {
  while d < n {
    v := CSLOT.u64[j * 2 + t];
    if v == 0 { return (0, 0, j, d) };
    if CREC.u64[(v - 1) * 4 + t * 2] == f && CREC.u64[(v - 1) * 4 + t * 2 + 1] == a {
      return (1, v - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def constFind : FunDecl := lfn (t, f, a, h) locals (n, j, d, v) {
  n := len(CSLOT.u64) >> 1;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪cefindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "const_find" = some constFind)

theorem cefindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n cefindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (ceprobeW (s₀.mem.arr64 CSLOT) (s₀.mem.arr64 CREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      ceprobeW (s₀.mem.arr64 CSLOT) (s₀.mem.arr64 CREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := cefindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [cematchW]

theorem cefindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) cefindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (ceprobeW (s₀.mem.arr64 CSLOT) (s₀.mem.arr64 CREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      ceprobeW (s₀.mem.arr64 CSLOT) (s₀.mem.arr64 CREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (cefindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `const` table. -/
def nSlotsCe (m : Mem) : Word := m.len64 CSLOT >>> 1

include hp in
theorem constFind_spec (n : Nat) (s₀ : St) (t f a h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "const_find" [t, f, a, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = ceprobeW (s₀.mem.arr64 CSLOT) (s₀.mem.arr64 CREC) t f a
        (nSlotsCe s₀.mem) (homeW h (nSlotsCe s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, cefindLoop_step_spec p n] <;>
      finish [nSlotsCe, homeW]

end find

/-! ## `const_push(t, n, us, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `const` table, `CTL[18 + t]`. -/
def cecnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (18 + t)

/-- `const_push`'s room checks: the handle index, the record array, the load limit. -/
def cepushOK (m : Mem) (t : Word) : Bool :=
  decide (cecnt m t < (134217728 : Word)) && decide (cecnt m t < m.len64 CREC >>> (2 : Word)) &&
    decide (cecnt m t + 1 ≤ (nSlotsCe m >>> (2 : Word)) * 3)

/-- The memory after `const_push(t, n, us, j)` appended node `c`. -/
def cepushMem (m : Mem) (t f a j c : Word) : Mem :=
  ((((m.set64 CREC (c * 4 + t * 2) f).set64 CREC (c * 4 + t * 2 + 1) a).set64 CSLOT (j * 2 + t)
    (c + 1)).set64 CTL (18 + (t &&& 1)) (c + 1))

def constPush : FunDecl := lfn (t, f, a, j) locals (c, k) {
  c := CTL.u64[18 + t];
  if c >= 134217728 { abort };
  if len(CREC.u64) >> 2 <= c { abort };
  if ((len(CSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 4 + t * 2;
  CREC.u64[k] := f;
  CREC.u64[k + 1] := a;
  CSLOT.u64[j * 2 + t] := c + 1;
  CTL.u64[18 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "const_push" = some constPush)

include hp in
theorem constPush_spec (n : Nat) (s₀ : St) (t f a j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "const_push" [t, f, a, j]
    ⦃fun r s' => LocEq s' s₀ ∧ cepushOK s₀.mem t = true ∧ r = [cecnt s₀.mem t] ∧
      s'.mem = cepushMem s₀.mem t f a j (cecnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [cecnt, cepushOK, cepushMem, nSlotsCe]

end push

/-! ## `intern_const(n, us)`: hash-cons the `const` node with children `n` and `us`

con-ron's `EStore::intern` at `const` and the arena's `internE (.const n us)`: the persistent
probe unless the scratch tier is open and a child is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `const` tier (tag `3`). -/
def constP : Word := 0x30000000
def constS : Word := 0x38000000

/-- The scratch skip: the scratch tier is open and `f` or `a` is a scratch handle. -/
def ceskipW (m : Mem) (f a : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((f ||| a) >>> 27) &&& 1 else 0

/-- The model of `intern_const`: the handle and the memory after, or `none` where the L code
aborts. -/
def ceinternW (m : Mem) (f a : Word) : Option (Word × Mem) :=
  let h := constHashW f a
  let rs₀ := ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 0 f a (nSlotsCe m) (homeW h (nSlotsCe m)) 0
  let rs₁ := ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 1 f a (nSlotsCe m) (homeW h (nSlotsCe m)) 0
  if ceskipW m f a = 0 ∧ rs₀ = [] then none
  else if ceskipW m f a = 0 ∧ rs₀.headD 0 ≠ 0 then some (constP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (constS + rs₁.tail.headD 0, m)
    else if cepushOK m 1 then
      some (constS + cecnt m 1, cepushMem m 1 f a (rs₁.tail.tail.headD 0) (cecnt m 1))
    else none
  else if cepushOK m 0 then
    some (constP + cecnt m 0, cepushMem m 0 f a (rs₀.tail.tail.headD 0) (cecnt m 0))
  else none

def internConst : FunDecl := lfn (f, a) locals (h, sk, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ f) * ⟪fnvPrime⟫ ^ a) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := ((f | a) >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call const_find(0, f, a, h);
    if fd != 0 { return ⟪constP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call const_find(1, f, a, h);
    if fd != 0 { return ⟪constS⟫ + i };
    i := call const_push(1, f, a, j);
    return ⟪constS⟫ + i
  };
  i := call const_push(0, f, a, j);
  return ⟪constP⟫ + i
}

/-- The `const` store functions, as one `#eval`-able program. -/
def constProg : Prog :=
  [("const_find", constFind), ("const_push", constPush), ("intern_const", internConst)]

/-- A memory with 8 `const` nodes and 16 slots per tier, the scratch tier closed or open.
Arrays 0‥17 (the other tables') are unused here and left empty. -/
def constMem (scratch : Word) : Mem :=
  { words := #[#[], #[0, scratch, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate 32 0, Array.replicate 32 0] }

/-- Intern each pair in turn; the handles. -/
def internConsts (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (f, a) :: xs => match run constProg 100 "intern_const" [f, a] m with
    | .ok (r, m') => (internConsts m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internConsts (constMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x30000000, 0x30000001, 0x30000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x38000000`) skips the persistent probe. -/
#guard internConsts (constMem 1) [(1, 2), (0x38000000, 1), (1, 2), (0x38000000, 1)] ==
  some [0x38000000, 0x38000001, 0x38000000, 0x38000001]

section intern
variable (p : Prog) (hpf : p.lookup "const_find" = some constFind)
  (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)

include hpf hpp hp in
theorem internConst_spec (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_const" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ceinternW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internConst]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        constFind_spec p hpf n, constPush_spec p hpp n] <;>
      finish [ceinternW, ceskipW, constHashW]

end intern

end L.Arena
