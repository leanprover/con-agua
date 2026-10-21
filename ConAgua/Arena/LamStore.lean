module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The `lam` node store in L: a binder record, two handle fields per node

The arena's `lam` constructor is a `Tbl BindNode EIdx UInt64` per tier (`Arena/Store.lean:287`,
`ETables.lams`), shared with `forallE` (`ForallStore.lean`). `BindNode { ty body : EIdx }` has the
`app`/`AppNode` shape exactly (two handle fields), so the L representation is `app`'s, written out
again for this record:

* **Records.** Word array `LAREC`, two words per node (the handle words of `ty` and `body`),
  tiers interleaved: node `i` of tier `t` at `LAREC[4 i + 2 t ..]`. The node count of tier `t` is
  `CTL[28 + t]`.
* **Cons table.** Word array `LASLOT`, the same open addressing as `SLOT`/`ASLOT`.
* **The scratch skip.** `internE (.lam ty body)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindBindMaybe`,
  `bindHasScratchChild`): bit 27 of `ty | body`.

Unlike `app`, `internE` at `lam` does **not** go through `internNodeE`: it is `internLamE`
(`ConRon/Arena/Monad.lean`), which probes with `EStore.findBind ETag.lam ty body`, tests
`bindSizeOf` at the tier the append goes to, then calls `EStore.internLam = EStore.internBind
ETag.lam`, which re-probes and pushes via `ETables.pushBind` (`ConRon/Arena/Store.lean`). The L
side (this file) is unaffected: it is still one probe-loop, one push, one dispatcher, as `app`'s.
`LamRefine.lean` carries the different unfolding to `protoRun`.

The functions: `lam_find(t, ty, body, h)` (the probe, the match inline: two word comparisons),
`lam_push(t, ty, body, j)` and `intern_lam(ty, body)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `lam` records, both tiers interleaved (two words per node). -/
abbrev LAREC : ArrId := 27
/-- The `lam` cons-table slots, both tiers interleaved. -/
abbrev LASLOT : ArrId := 28

/-- The hash of a `lam` record (FNV-1a over its two words). -/
def lamHashW (ty body : Word) : Word := ((fnvBasis ^^^ ty) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, body)`. -/
def lamatchW (r : Array Word) (t i ty body : Word) : Bool :=
  rdW r (i * 4 + t * 2) == ty && rdW r (i * 4 + t * 2 + 1) == body

/-! ## `lam_find(t, ty, body, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `lamatchW`). -/
def laprobeW (sl r : Array Word) (t ty body n j d : Word) : List Word :=
  if d < n then
    if rdW sl (j * 2 + t) = 0 then [0, 0, j, d]
    else if lamatchW r t (rdW sl (j * 2 + t) - 1) ty body then [1, rdW sl (j * 2 + t) - 1, j, d]
    else laprobeW sl r t ty body n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t ty body n j d : Word)

theorem laprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] = 0) : laprobeW sl r t ty body n j d = [0, 0, j, d] := by
  rw [laprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv]

theorem laprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≠ 0) (hm : lamatchW r t (sl[k] - 1) ty body = true) :
    laprobeW sl r t ty body n j d = [1, sl[k] - 1, j, d] := by
  rw [laprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]

theorem laprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hm : lamatchW r t (sl[k] - 1) ty body = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    laprobeW sl r t ty body n j d = laprobeW sl r t ty body n j' d' := by
  subst hj' hd'
  rw [laprobeW]; simp only [hd, ↓reduceIte, rdW_eq sl _ k hk hks, hv, hm]; simp

end probeArms

grind_pattern [arena_grind] laprobeW_free => laprobeW sl r t ty body n j d, sl[k]
grind_pattern [arena_grind] laprobeW_hit => laprobeW sl r t ty body n j d, sl[k]
grind_pattern [arena_grind] laprobeW_next =>
  laprobeW sl r t ty body n j d, sl[k], laprobeW sl r t ty body n j' d'

def lafindLoop : Stmt := lblk (t, ty, body, h, n, j, d, v) {
  while d < n {
    v := LASLOT.u64[j * 2 + t];
    if v == 0 { return (0, 0, j, d) };
    if LAREC.u64[(v - 1) * 4 + t * 2] == ty && LAREC.u64[(v - 1) * 4 + t * 2 + 1] == body {
      return (1, v - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def lamFind : FunDecl := lfn (t, ty, body, h) locals (n, j, d, v) {
  n := len(LASLOT.u64) >> 1;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪lafindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "lam_find" = some lamFind)

theorem lafindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lafindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (laprobeW (s₀.mem.arr64 LASLOT) (s₀.mem.arr64 LAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      laprobeW (s₀.mem.arr64 LASLOT) (s₀.mem.arr64 LAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lafindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [lamatchW]

theorem lafindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) lafindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (laprobeW (s₀.mem.arr64 LASLOT) (s₀.mem.arr64 LAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      laprobeW (s₀.mem.arr64 LASLOT) (s₀.mem.arr64 LAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (lafindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `lam` table. -/
def nSlotsLa (m : Mem) : Word := m.len64 LASLOT >>> 1

include hp in
theorem lamFind_spec (n : Nat) (s₀ : St) (t ty body h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lam_find" [t, ty, body, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = laprobeW (s₀.mem.arr64 LASLOT) (s₀.mem.arr64 LAREC) t ty body
        (nSlotsLa s₀.mem) (homeW h (nSlotsLa s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lamFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, lafindLoop_step_spec p n] <;>
      finish [nSlotsLa, homeW]

end find

/-! ## `lam_push(t, ty, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `lam` table, `CTL[28 + t]`. -/
def lacnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (28 + t)

/-- `lam_push`'s room checks: the handle index, the record array, the load limit. -/
def lapushOK (m : Mem) (t : Word) : Bool :=
  decide (lacnt m t < (134217728 : Word)) && decide (lacnt m t < m.len64 LAREC >>> (2 : Word)) &&
    decide (lacnt m t + 1 ≤ (nSlotsLa m >>> (2 : Word)) * 3)

/-- The memory after `lam_push(t, ty, body, j)` appended node `c`. -/
def lapushMem (m : Mem) (t ty body j c : Word) : Mem :=
  ((((m.set64 LAREC (c * 4 + t * 2) ty).set64 LAREC (c * 4 + t * 2 + 1) body).set64 LASLOT
    (j * 2 + t) (c + 1)).set64 CTL (28 + t) (c + 1))

def lamPush : FunDecl := lfn (t, ty, body, j) locals (c, k) {
  c := CTL.u64[28 + t];
  if c >= 134217728 { abort };
  if len(LAREC.u64) >> 2 <= c { abort };
  if ((len(LASLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  k := c * 4 + t * 2;
  LAREC.u64[k] := ty;
  LAREC.u64[k + 1] := body;
  LASLOT.u64[j * 2 + t] := c + 1;
  CTL.u64[28 + t] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "lam_push" = some lamPush)

include hp in
theorem lamPush_spec (n : Nat) (s₀ : St) (t ty body j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lam_push" [t, ty, body, j]
    ⦃fun r s' => LocEq s' s₀ ∧ lapushOK s₀.mem t = true ∧ r = [lacnt s₀.mem t] ∧
      s'.mem = lapushMem s₀.mem t ty body j (lacnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lamPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [lacnt, lapushOK, lapushMem, nSlotsLa]

end push

/-! ## `intern_lam(ty, body)`: hash-cons the `lam` binder with binder type `ty` and body `body`

con-ron's `EStore::internLam` (through `internBind`) and the arena's `internLamE`: the persistent
probe unless the scratch tier is open and a child is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. Same L shape as `app`'s
`intern_app`; `LamRefine.lean` carries the different unfolding of `internLamE` to `protoRun`. -/

/-- The handle word of node `0` of the persistent / scratch `lam` tier (tag `5`). -/
def lamP : Word := 0x50000000
def lamS : Word := 0x58000000

/-- The scratch skip: the scratch tier is open and `ty` or `body` is a scratch handle. -/
def laskipW (m : Mem) (ty body : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((ty ||| body) >>> 27) &&& 1 else 0

/-- The model of `intern_lam`: the handle and the memory after, or `none` where the L code
aborts. -/
def lainternW (m : Mem) (ty body : Word) : Option (Word × Mem) :=
  let h := lamHashW ty body
  let rs₀ := laprobeW (m.arr64 LASLOT) (m.arr64 LAREC) 0 ty body (nSlotsLa m) (homeW h (nSlotsLa m)) 0
  let rs₁ := laprobeW (m.arr64 LASLOT) (m.arr64 LAREC) 1 ty body (nSlotsLa m) (homeW h (nSlotsLa m)) 0
  if laskipW m ty body = 0 ∧ rs₀ = [] then none
  else if laskipW m ty body = 0 ∧ rs₀.headD 0 ≠ 0 then some (lamP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (lamS + rs₁.tail.headD 0, m)
    else if lapushOK m 1 then
      some (lamS + lacnt m 1, lapushMem m 1 ty body (rs₁.tail.tail.headD 0) (lacnt m 1))
    else none
  else if lapushOK m 0 then
    some (lamP + lacnt m 0, lapushMem m 0 ty body (rs₀.tail.tail.headD 0) (lacnt m 0))
  else none

/-- The L FunDecl for `intern_lam`. Named `internLamL`, not `internLam`: con-ron's
`EStore.internLam` (`ConRon/Arena/Store.lean`) is a sibling name in a different namespace, but the
`L`-suffix keeps the two visually apart in this file, which `open`s `ConRon.Arena`. -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internLamE]
def internLamL : FunDecl := lfn (ty, body) locals (h, sk, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := ((ty | body) >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call lam_find(0, ty, body, h);
    if fd != 0 { return ⟪lamP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call lam_find(1, ty, body, h);
    if fd != 0 { return ⟪lamS⟫ + i };
    i := call lam_push(1, ty, body, j);
    return ⟪lamS⟫ + i
  };
  i := call lam_push(0, ty, body, j);
  return ⟪lamP⟫ + i
}

/-- The `lam` store functions, as one `#eval`-able program. -/
def lamProg : Prog :=
  [("lam_find", lamFind), ("lam_push", lamPush), ("intern_lam", internLamL)]

/-- A memory with 8 `lam` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
other than `CTL`/`LAREC`/`LASLOT` are unused here and left empty; `CTL` reaches `28 + 2 = 30`
words. -/
def lamMem (scratch : Word) : Mem :=
  { words := #[#[],
      #[0, scratch, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0],
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[],
      Array.replicate 32 0, Array.replicate 32 0] }

/-- Intern each pair in turn; the handles. -/
def internLams (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (ty, body) :: xs => match run lamProg 100 "intern_lam" [ty, body] m with
    | .ok (r, m') => (internLams m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internLams (lamMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x50000000, 0x50000001, 0x50000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x58000000`) skips the persistent probe. -/
#guard internLams (lamMem 1) [(1, 2), (0x58000000, 1), (1, 2), (0x58000000, 1)] ==
  some [0x58000000, 0x58000001, 0x58000000, 0x58000001]

section intern
variable (p : Prog) (hpf : p.lookup "lam_find" = some lamFind)
  (hpp : p.lookup "lam_push" = some lamPush) (hp : p.lookup "intern_lam" = some internLamL)

include hpf hpp hp in
theorem internLamL_spec (n : Nat) (s₀ : St) (ty body : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lam" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ lainternW s₀.mem ty body = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internLamL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lamFind_spec p hpf n, lamPush_spec p hpp n] <;>
      finish [lainternW, laskipW, lamHashW]

end intern

end L.Arena
