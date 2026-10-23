module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The `forallE` node store in L: a binder record, two handle fields per node

The arena's `forallE` constructor is a `Tbl BindNode EIdx UInt64` per tier
(`Arena/Store.lean:287`, `ETables.foralls`), `BindNode`'s other array, shared with `lam`
(`LamStore.lean`). Same record shape as `app`/`lam` (two handle fields), so the L representation
is theirs, written out again for this record:

* **Records.** Word array `FAREC`, two words per node (the handle words of `ty` and `body`),
  tiers interleaved: node `i` of tier `t` at `FAREC[4 i + 2 t ..]`. The node count of tier `t` is
  `CTL[30 + t]`.
* **Cons table.** Word array `FASLOT`, the same open addressing as `SLOT`/`ASLOT`/`LASLOT`.
* **The scratch skip.** `internE (.forallE ty body)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindBindMaybe`,
  `bindHasScratchChild`): bit 27 of `ty | body`.

As `lam`, `internE` at `forallE` does **not** go through `internNodeE`: it is `internForallEE`
(`ConRon/Arena/Monad.lean`), which probes with `EStore.findBind ETag.forallE ty body`, tests
`bindSizeOf` at the tier the append goes to, then calls `EStore.internForallE = EStore.internBind
ETag.forallE`, which re-probes and pushes via `ETables.pushBind`. The L side (this file) is
unaffected: it is still one probe-loop, one push, one dispatcher, as `app`'s/`lam`'s.
`ForallRefine.lean` carries the different unfolding to `protoRun`.

The functions: `forall_find(t, ty, body, h)` (the probe, the match inline: two word comparisons),
`forall_push(t, ty, body, j)` and `intern_forall(ty, body)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `forallE` records, both tiers interleaved (two words per node). -/
abbrev FAREC : ArrId := 29
/-- The `forallE` cons-table slots, both tiers interleaved. -/
abbrev FASLOT : ArrId := 30

/-- The growth schema of this table (`SlotGrow.lean`). -/
def forallGS : GrowSch := ⟨FASLOT, FAREC, 2, 30, FASLOT_G, 2⟩

/-- The hash of a `forallE` record (FNV-1a over its two words). -/
def forallHashW (ty body : Word) : Word := ((fnvBasis ^^^ ty) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, body)`. -/
def famatchW (r : Array Word) (t i ty body : Word) : Bool :=
  rdW r (i * 4 + t * 2) == ty && rdW r (i * 4 + t * 2 + 1) == body

/-! ## `forall_find(t, ty, body, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `famatchW`). -/
def faprobeW (sl r : Array Word) (t ty body b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if famatchW r t (slotV sl b (j * 2 + t) - 1) ty body then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else faprobeW sl r t ty body b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t ty body b n j d : Word)

theorem faprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : faprobeW sl r t ty body b n j d = [0, 0, j, d] := by
  rw [faprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem faprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : famatchW r t (sl[k] - b - 1) ty body = true) :
    faprobeW sl r t ty body b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [faprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem faprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : famatchW r t (sl[k] - b - 1) ty body = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    faprobeW sl r t ty body b n j d = faprobeW sl r t ty body b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [faprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] faprobeW_free => faprobeW sl r t ty body b n j d, sl[k]
grind_pattern [arena_grind] faprobeW_hit => faprobeW sl r t ty body b n j d, sl[k]
grind_pattern [arena_grind] faprobeW_next =>
  faprobeW sl r t ty body b n j d, sl[k], faprobeW sl r t ty body b n j' d'

def fafindLoop : Stmt := lblk (t, ty, body, h, n, j, d, v, b) {
  while d < n {
    v := FASLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    if FAREC.u64[(v - 1) * 4 + t * 2] == ty && FAREC.u64[(v - 1) * 4 + t * 2 + 1] == body {
      return (1, v - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def forallFind : FunDecl := lfn (t, ty, body, h) locals (n, j, d, v, b) {
  n := ⟪SN0⟫ << FASLOT_G;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪fafindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "forall_find" = some forallFind)

theorem fafindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n fafindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (faprobeW (s₀.mem.arr64 FASLOT) (s₀.mem.arr64 FAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      faprobeW (s₀.mem.arr64 FASLOT) (s₀.mem.arr64 FAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := fafindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [famatchW, baseW]

theorem fafindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) fafindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (faprobeW (s₀.mem.arr64 FASLOT) (s₀.mem.arr64 FAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      faprobeW (s₀.mem.arr64 FASLOT) (s₀.mem.arr64 FAREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (fafindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `forallE` table. -/
def nSlotsFa (m : Mem) : Word := SN0 <<< m.glob FASLOT_G

include hp in
theorem forallFind_spec (n : Nat) (s₀ : St) (t ty body h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "forall_find" [t, ty, body, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = faprobeW (s₀.mem.arr64 FASLOT) (s₀.mem.arr64 FAREC) t ty body
        (baseW s₀.mem t) (nSlotsFa s₀.mem) (homeW h (nSlotsFa s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, forallFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, fafindLoop_step_spec p n, ld64] <;>
      finish [nSlotsFa, homeW, baseW]

end find

/-! ## `forall_push(t, ty, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `forallE` table, `CTL[30 + t]`. -/
def facnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (30 + t)

/-- `forall_push`'s room checks: the handle index, the record array, the load limit. -/
def fapushOK (m : Mem) (t : Word) : Bool :=
  decide (facnt m t < (134217728 : Word)) && decide (facnt m t < m.len64 FAREC >>> (2 : Word)) &&
    decide (facnt m t + 1 ≤ (nSlotsFa m >>> (2 : Word)) * 3)

/-- The memory after `forall_push(t, ty, body, j)` appended node `c`. -/
def fapushMem (m : Mem) (t ty body j c : Word) : Mem :=
  ((((m.set64 FAREC (c * 4 + t * 2) ty).set64 FAREC (c * 4 + t * 2 + 1) body).set64 FASLOT
    (j * 2 + t) (baseW m t + c + 1)).set64 CTL (30 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def forallPush : FunDecl := lfn (t, ty, body, j) locals (c, k, gr) {
  c := CTL.u64[30 + t];
  if c >= 134217728 { abort };
  if len(FAREC.u64) >> 2 <= c { abort };
  k := c * 4 + t * 2;
  FAREC.u64[k] := ty;
  FAREC.u64[k + 1] := body;
  FASLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[30 + (t & 1)] := c + 1;
  if (⟪SN0⟫ << FASLOT_G) < (c + 1) * 2 { gr := call forall_grow() };
  return c
}

section push
variable (p : Prog) (hp : p.lookup "forall_push" = some forallPush)

include hp in
theorem forallPush_spec (n : Nat) (s₀ : St) (t ty body j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "forall_push" [t, ty, body, j]
    ⦃fun r s' => LocEq s' s₀ ∧ fapushOK s₀.mem t = true ∧ r = [facnt s₀.mem t] ∧
      s'.mem = fapushMem s₀.mem t ty body j (facnt s₀.mem t); ⊤⦄ := by
  sorry -- slotgrow: the push grows the table

end push

/-! ## `intern_forall(ty, body)`: hash-cons the `forallE` binder with binder type `ty` and body
`body`

con-ron's `EStore::internForallE` (through `internBind`) and the arena's `internForallEE`: the
persistent probe unless the scratch tier is open and a child is a scratch handle, the scratch
probe if the scratch tier is open, the append to the tier the store is in. Same L shape as
`app`'s/`lam`'s; `ForallRefine.lean` carries the different unfolding of `internForallEE` to
`protoRun`. -/

/-- The handle word of node `0` of the persistent / scratch `forallE` tier (tag `6`). -/
def forallP : Word := 0x60000000
def forallS : Word := 0x68000000

/-- The scratch skip: the scratch tier is open and `ty` or `body` is a scratch handle. -/
def faskipW (m : Mem) (ty body : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((ty ||| body) >>> 27) &&& 1 else 0

/-- The model of `intern_forall`: the handle and the memory after, or `none` where the L code
aborts. -/
def fainternW (m : Mem) (ty body : Word) : Option (Word × Mem) :=
  let h := forallHashW ty body
  let rs₀ := faprobeW (m.arr64 FASLOT) (m.arr64 FAREC) 0 ty body (baseW m 0) (nSlotsFa m) (homeW h (nSlotsFa m)) 0
  let rs₁ := faprobeW (m.arr64 FASLOT) (m.arr64 FAREC) 1 ty body (baseW m 1) (nSlotsFa m) (homeW h (nSlotsFa m)) 0
  if faskipW m ty body = 0 ∧ rs₀ = [] then none
  else if faskipW m ty body = 0 ∧ rs₀.headD 0 ≠ 0 then some (forallP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (forallS + rs₁.tail.headD 0, m)
    else if fapushOK m 1 then
      some (forallS + facnt m 1, fapushMem m 1 ty body (rs₁.tail.tail.headD 0) (facnt m 1))
    else none
  else if fapushOK m 0 then
    some (forallP + facnt m 0, fapushMem m 0 ty body (rs₀.tail.tail.headD 0) (facnt m 0))
  else none

/-- The L FunDecl for `intern_forall`. Named `internForallL`, not `internForallE`: con-ron's
`ConRon.Arena.internForallEE`/`EStore.internForallE` are sibling names in a different namespace,
but the `L`-suffix keeps the two visually apart in this file, which `open`s `ConRon.Arena`. -/
-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
-- con-ron: ConRon/Arena/Monad.lean:199-216 ConRon.Arena.internForallEE
@[l_impl ConRon.Arena.internE ConRon.Arena.internForallEE]
def internForallL : FunDecl := lfn (ty, body) locals (h, sk, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := ((ty | body) >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call forall_find(0, ty, body, h);
    if fd != 0 { return ⟪forallP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call forall_find(1, ty, body, h);
    if fd != 0 { return ⟪forallS⟫ + i };
    i := call forall_push(1, ty, body, j);
    return ⟪forallS⟫ + i
  };
  i := call forall_push(0, ty, body, j);
  return ⟪forallP⟫ + i
}

/-- The `forallE` store functions, as one `#eval`-able program. -/
def forallProg : Prog :=
  [("forall_find", forallFind), ("forall_push", forallPush), ("forall_grow", slotGrowG forallGS), ("intern_forall", internForallL)]

/-- A memory with 8 `forallE` nodes and 16 slots per tier, the scratch tier closed or open.
Arrays other than `CTL`/`FAREC`/`FASLOT` are unused here and left empty; `CTL` reaches
`30 + 2 = 32` words. -/
def forallMem (scratch : Word) : Mem :=
  { words := #[#[],
      (#[0, scratch] ++ Array.replicate 62 0),
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate 32 0, Array.replicate 32 0] }

/-- Intern each pair in turn; the handles. -/
def internForalls (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (ty, body) :: xs => match run forallProg 100 "intern_forall" [ty, body] m with
    | .ok (r, m') => (internForalls m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internForalls (forallMem 0) [(1, 2), (2, 1), (1, 2)] ==
  some [0x60000000, 0x60000001, 0x60000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x68000000`) skips the persistent probe. -/
#guard internForalls (forallMem 1) [(1, 2), (0x68000000, 1), (1, 2), (0x68000000, 1)] ==
  some [0x68000000, 0x68000001, 0x68000000, 0x68000001]

section intern
variable (p : Prog) (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush)
  (hp : p.lookup "intern_forall" = some internForallL)

include hpf hpp hp in
theorem internForallL_spec (n : Nat) (s₀ : St) (ty body : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_forall" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ fainternW s₀.mem ty body = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internForallL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        forallFind_spec p hpf n, forallPush_spec p hpp n] <;>
      finish [fainternW, faskipW, forallHashW, baseW]

end intern

end L.Arena
