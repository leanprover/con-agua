module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The `app` node store in L: a second store, two handle fields per node

The arena's `app` constructor is a `Tbl AppNode EIdx UInt64` per tier, `AppNode { f a : EIdx }`
(`Arena/Store.lean:278`). Its L representation follows the `lit` store's
(`ConAgua/Arena/Store.lean`), written out again for this record:

* **Records.** Word array `AREC`, two words per node (the handle words of `f` and `a`), tiers
  interleaved: node `i` of tier `t` at `AREC[4 i + 2 t ..]`. No stored hash: the hash is a
  cheap function of the two words. The node count of tier `t` is `CTL[4 + t]`.
* **Cons table.** Word array `ASLOT`, the same open addressing as `SLOT` (slot `j` of tier `t`
  at `ASLOT[2 j + t]`, `0` free, `i + 1` node `i`, linear probing from `homeW`).
* **The scratch skip.** `internE (.app f a)` does not probe the persistent tier when the scratch
  tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `f | a`.

The functions: `app_find(t, f, a, h)` (the probe, the match inline: two word comparisons),
`app_push(t, f, a, j)` and `intern_app(f, a)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `app` records, both tiers interleaved (two words per node). -/
abbrev AREC : ArrId := 4
/-- The `app` cons-table slots, both tiers interleaved. -/
abbrev ASLOT : ArrId := 5

/-- The hash of an `app` record (FNV-1a over its two words). -/
def appHashW (f a : Word) : Word := ((fnvBasis ^^^ f) * fnvPrime ^^^ a) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(f, a)`. -/
def amatchW (r : Array Word) (t i f a : Word) : Bool :=
  rdW r (i * 4 + t * 2) == f && rdW r (i * 4 + t * 2 + 1) == a

/-! ## `app_find(t, f, a, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `amatchW`). -/
def aprobeW (sl r : Array Word) (t f a n j d : Word) : List Word :=
  if d < n then
    if rdW sl (j * 2 + t) = 0 then [0, 0, j, d]
    else if amatchW r t (rdW sl (j * 2 + t) - 1) f a then [1, rdW sl (j * 2 + t) - 1, j, d]
    else aprobeW sl r t f a n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
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

theorem aprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] = 0) : aprobeW sl r t f a n j d = [0, 0, j, d] := by
  rw [aprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv]

theorem aprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≠ 0) (hm : amatchW r t (sl[k] - 1) f a = true) :
    aprobeW sl r t f a n j d = [1, sl[k] - 1, j, d] := by
  rw [aprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]

theorem aprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hm : amatchW r t (sl[k] - 1) f a = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    aprobeW sl r t f a n j d = aprobeW sl r t f a n j' d' := by
  subst hj' hd'
  rw [aprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]; simp

end probeArms

grind_pattern [arena_grind] aprobeW_free => aprobeW sl r t f a n j d, sl[k]
grind_pattern [arena_grind] aprobeW_hit => aprobeW sl r t f a n j d, sl[k]
grind_pattern [arena_grind] aprobeW_next =>
  aprobeW sl r t f a n j d, sl[k], aprobeW sl r t f a n j' d'

def afindLoop : Stmt := lblk (t, f, a, h, n, j, d, v) {
  while d < n {
    v := ASLOT.u64[j * 2 + t];
    if v == 0 { return (0, 0, j, d) };
    if AREC.u64[(v - 1) * 4 + t * 2] == f && AREC.u64[(v - 1) * 4 + t * 2 + 1] == a {
      return (1, v - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def appFind : FunDecl := lfn (t, f, a, h) locals (n, j, d, v) {
  n := len(ASLOT.u64) >> 1;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪afindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "app_find" = some appFind)

theorem afindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n afindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (aprobeW (s₀.mem.arr64 ASLOT) (s₀.mem.arr64 AREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      aprobeW (s₀.mem.arr64 ASLOT) (s₀.mem.arr64 AREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := afindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [amatchW]

theorem afindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) afindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (aprobeW (s₀.mem.arr64 ASLOT) (s₀.mem.arr64 AREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      aprobeW (s₀.mem.arr64 ASLOT) (s₀.mem.arr64 AREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (afindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `app` table. -/
def nSlotsA (m : Mem) : Word := m.len64 ASLOT >>> 1

include hp in
theorem appFind_spec (n : Nat) (s₀ : St) (t f a h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "app_find" [t, f, a, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = aprobeW (s₀.mem.arr64 ASLOT) (s₀.mem.arr64 AREC) t f a
        (nSlotsA s₀.mem) (homeW h (nSlotsA s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, afindLoop_step_spec p n] <;>
      finish [nSlotsA, homeW]

end find

/-! ## `app_push(t, f, a, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `app` table, `CTL[4 + t]`. -/
def acnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (4 + t)

/-- `app_push`'s room checks: the handle index, the record array, the load limit. -/
def apushOK (m : Mem) (t : Word) : Bool :=
  decide (acnt m t < (134217728 : Word)) && decide (acnt m t < m.len64 AREC >>> (2 : Word)) &&
    decide (acnt m t + 1 ≤ (nSlotsA m >>> (2 : Word)) * 3)

/-- The memory after `app_push(t, f, a, j)` appended node `c`. -/
def apushMem (m : Mem) (t f a j c : Word) : Mem :=
  ((((m.set64 AREC (c * 4 + t * 2) f).set64 AREC (c * 4 + t * 2 + 1) a).set64 ASLOT (j * 2 + t)
    (c + 1)).set64 CTL (4 + t) (c + 1))

def appPush : FunDecl := lfn (t, f, a, j) locals (c, k) {
  c := CTL.u64[4 + t];
  if c >= 134217728 { abort };
  if len(AREC.u64) >> 2 <= c { abort };
  if ((len(ASLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 4 + t * 2;
  AREC.u64[k] := f;
  AREC.u64[k + 1] := a;
  ASLOT.u64[j * 2 + t] := c + 1;
  CTL.u64[4 + t] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "app_push" = some appPush)

include hp in
theorem appPush_spec (n : Nat) (s₀ : St) (t f a j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "app_push" [t, f, a, j]
    ⦃fun r s' => LocEq s' s₀ ∧ apushOK s₀.mem t = true ∧ r = [acnt s₀.mem t] ∧
      s'.mem = apushMem s₀.mem t f a j (acnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [acnt, apushOK, apushMem, nSlotsA]

end push

/-! ## `intern_app(f, a)`: hash-cons the `app` node with children `f` and `a`

con-ron's `EStore::intern` at `app` and the arena's `internE (.app f a)`: the persistent probe
unless the scratch tier is open and a child is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `app` tier (tag `4`). -/
def appP : Word := 0x40000000
def appS : Word := 0x48000000

/-- The scratch skip: the scratch tier is open and `f` or `a` is a scratch handle. -/
def askipW (m : Mem) (f a : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((f ||| a) >>> 27) &&& 1 else 0

/-- The model of `intern_app`: the handle and the memory after, or `none` where the L code
aborts. -/
def ainternW (m : Mem) (f a : Word) : Option (Word × Mem) :=
  let h := appHashW f a
  let rs₀ := aprobeW (m.arr64 ASLOT) (m.arr64 AREC) 0 f a (nSlotsA m) (homeW h (nSlotsA m)) 0
  let rs₁ := aprobeW (m.arr64 ASLOT) (m.arr64 AREC) 1 f a (nSlotsA m) (homeW h (nSlotsA m)) 0
  if askipW m f a = 0 ∧ rs₀ = [] then none
  else if askipW m f a = 0 ∧ rs₀.headD 0 ≠ 0 then some (appP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (appS + rs₁.tail.headD 0, m)
    else if apushOK m 1 then
      some (appS + acnt m 1, apushMem m 1 f a (rs₁.tail.tail.headD 0) (acnt m 1))
    else none
  else if apushOK m 0 then
    some (appP + acnt m 0, apushMem m 0 f a (rs₀.tail.tail.headD 0) (acnt m 0))
  else none

def internApp : FunDecl := lfn (f, a) locals (h, sk, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ f) * ⟪fnvPrime⟫ ^ a) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := ((f | a) >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call app_find(0, f, a, h);
    if fd != 0 { return ⟪appP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call app_find(1, f, a, h);
    if fd != 0 { return ⟪appS⟫ + i };
    i := call app_push(1, f, a, j);
    return ⟪appS⟫ + i
  };
  i := call app_push(0, f, a, j);
  return ⟪appP⟫ + i
}

/-- The `app` store functions, as one `#eval`-able program. -/
def appProg : Prog :=
  [("app_find", appFind), ("app_push", appPush), ("intern_app", internApp)]

/-- A memory with 8 `app` nodes and 16 slots per tier, the scratch tier closed or open. -/
def appMem (scratch : Word) : Mem :=
  { words := #[#[], #[0, scratch, 0, 0, 0, 0], #[], #[], Array.replicate 32 0,
      Array.replicate 32 0] }

/-- Intern each pair in turn; the handles. -/
def internApps (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (f, a) :: xs => match run appProg 100 "intern_app" [f, a] m with
    | .ok (r, m') => (internApps m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internApps (appMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x40000000, 0x40000001, 0x40000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x48000000`) skips the persistent probe. -/
#guard internApps (appMem 1) [(1, 2), (0x48000000, 1), (1, 2), (0x48000000, 1)] ==
  some [0x48000000, 0x48000001, 0x48000000, 0x48000001]

section intern
variable (p : Prog) (hpf : p.lookup "app_find" = some appFind)
  (hpp : p.lookup "app_push" = some appPush) (hp : p.lookup "intern_app" = some internApp)

include hpf hpp hp in
theorem internApp_spec (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_app" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ainternW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internApp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        appFind_spec p hpf n, appPush_spec p hpp n] <;>
      finish [ainternW, askipW, appHashW]

end intern

end L.Arena
