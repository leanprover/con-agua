module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The expression `fvar` node store in L: a `Nat` field and a handle field per node

The arena's expression store keeps `fvar idx ty` nodes in a `Tbl FVarNode EIdx UInt64` per tier
(`Arena/Store.lean:258`, `ETables.fvars`). Its L representation is `app`'s shape (two words per
node, open addressing, scratch-skipping), except the first word is a plain `Nat` (the free
variable index, as `bvar`'s word is) rather than a handle:

* **Records.** Word array `FVREC`, two words per node (the index `idx` as a word, then the handle
  word of `ty`), tiers interleaved: node `i` of tier `t` at `FVREC[4 i + 2 t ..]`. The node count
  of tier `t` is `CTL[26 + t]`.
* **Cons table.** Word array `FVSLOT`, the same open addressing as `SLOT`/`ASLOT`.
* **The scratch skip.** `internE (.fvar idx ty)` does not probe the persistent tier when the
  scratch tier is open and `ty` is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild (.fvar _ ty) = !ty.isPersistent`): only the `ty` word, not `idx`, the
  index not being a handle at all.

The functions: `fvar_find(t, u, ty, h)` (the probe, the match inline: a word comparison and a
handle-word comparison), `fvar_push(t, u, ty, j)` and `intern_fvar(u, ty)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `fvar` records, both tiers interleaved (two words per node). -/
abbrev FVREC : ArrId := 25
/-- The `fvar` cons-table slots, both tiers interleaved. -/
abbrev FVSLOT : ArrId := 26

/-- The growth schema of this table (`SlotGrow.lean`). -/
def fvarGS : GrowSch :=
  ⟨FVSLOT, FVREC, 2, 26, FVSLOT_G, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ FVREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ FVREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of an `fvar` record (FNV-1a over its two words). -/
def fvarHashW (u ty : Word) : Word := ((fnvBasis ^^^ u) * fnvPrime ^^^ ty) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(u, ty)` (the index word, the child's handle
word). -/
def fvmatchW (r : Array Word) (t i u ty : Word) : Bool :=
  rdW r (i * 4 + t * 2) == u && rdW r (i * 4 + t * 2 + 1) == ty

/-! ## `fvar_find(t, u, ty, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `fvmatchW`). -/
def fvprobeW (sl r : Array Word) (t u ty b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if fvmatchW r t (slotV sl b (j * 2 + t) - 1) u ty then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else fvprobeW sl r t u ty b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t u ty b n j d : Word)

theorem fvprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : fvprobeW sl r t u ty b n j d = [0, 0, j, d] := by
  rw [fvprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem fvprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : fvmatchW r t (sl[k] - b - 1) u ty = true) :
    fvprobeW sl r t u ty b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [fvprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem fvprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : fvmatchW r t (sl[k] - b - 1) u ty = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    fvprobeW sl r t u ty b n j d = fvprobeW sl r t u ty b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [fvprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] fvprobeW_free => fvprobeW sl r t u ty b n j d, sl[k]
grind_pattern [arena_grind] fvprobeW_hit => fvprobeW sl r t u ty b n j d, sl[k]
grind_pattern [arena_grind] fvprobeW_next =>
  fvprobeW sl r t u ty b n j d, sl[k], fvprobeW sl r t u ty b n j' d'

def fvfindLoop : Stmt := lblk (t, u, ty, h, n, j, d, v, b) {
  while d < n {
    v := FVSLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    if FVREC.u64[(v - 1) * 4 + t * 2] == u && FVREC.u64[(v - 1) * 4 + t * 2 + 1] == ty {
      return (1, v - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def fvarFind : FunDecl := lfn (t, u, ty, h) locals (n, j, d, v, b) {
  n := ⟪SN0⟫ << FVSLOT_G;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪fvfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "fvar_find" = some fvarFind)

theorem fvfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n fvfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (fvprobeW (s₀.mem.arr64 FVSLOT) (s₀.mem.arr64 FVREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      fvprobeW (s₀.mem.arr64 FVSLOT) (s₀.mem.arr64 FVREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := fvfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [fvmatchW, baseW]

theorem fvfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) fvfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (fvprobeW (s₀.mem.arr64 FVSLOT) (s₀.mem.arr64 FVREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      fvprobeW (s₀.mem.arr64 FVSLOT) (s₀.mem.arr64 FVREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 8) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (fvfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `fvar` table. -/
def nSlotsFv (m : Mem) : Word := SN0 <<< m.glob FVSLOT_G

include hp in
theorem fvarFind_spec (n : Nat) (s₀ : St) (t u ty h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fvar_find" [t, u, ty, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = fvprobeW (s₀.mem.arr64 FVSLOT) (s₀.mem.arr64 FVREC) t u ty
        (baseW s₀.mem t) (nSlotsFv s₀.mem) (homeW h (nSlotsFv s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, fvarFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, fvfindLoop_step_spec p n, ld64] <;>
      finish [nSlotsFv, homeW, baseW]

end find

/-! ## `fvar_push(t, u, ty, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `fvar` table, `CTL[26 + t]`. -/
def fvcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (26 + t)

/-- `fvar_push`'s room checks: the handle index, the record array, the load limit. -/
def fvpushOK (m : Mem) (t : Word) : Bool :=
  decide (fvcnt m t < (134217728 : Word)) && decide (fvcnt m t < m.len64 FVREC >>> (2 : Word)) &&
    decide (fvcnt m t < m.len64 FVLP >>> (1 : Word)) &&
    decide (fvcnt m t + 1 ≤ (nSlotsFv m >>> (2 : Word)) * 3)

/-- The memory after `fvar_push(t, u, ty, j)` appended node `c`. -/
def fvpushMem (m : Mem) (t u ty j c : Word) : Mem :=
  ((((m.set64 FVREC (c * 4 + t * 2) u).set64 FVREC (c * 4 + t * 2 + 1) ty).set64 FVSLOT
    (j * 2 + t) (baseW m t + c + 1)).set64 CTL (26 + (t &&& 1)) (c + 1)).set64 FVLP (c * 2 + t)
    (exprLPW m ty)

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def fvarPush : FunDecl := lfn (t, u, ty, j) locals (c, k, x, g, ti, ix, gr) {
  ⟪lpBlkF⟫;
  c := CTL.u64[26 + t];
  if c >= 134217728 { abort };
  if len(FVREC.u64) >> 2 <= c { abort };
  if len(FVLP.u64) >> 1 <= c { abort };
  k := c * 4 + t * 2;
  FVREC.u64[k] := u;
  FVREC.u64[k + 1] := ty;
  FVSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[26 + (t & 1)] := c + 1;
  if (⟪SN0⟫ << FVSLOT_G) < (c + 1) * 2 { gr := call fvar_grow() };
  FVLP.u64[c * 2 + t] := x;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "fvar_push" = some fvarPush)

include hp in
theorem fvarPush_spec (n : Nat) (s₀ : St) (t u ty j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fvar_push" [t, u, ty, j]
    ⦃fun r s' => LocEq s' s₀ ∧ fvpushOK s₀.mem t = true ∧ r = [fvcnt s₀.mem t] ∧
      s'.mem = fvpushMem s₀.mem t u ty j (fvcnt s₀.mem t); ⊤⦄ := by
  sorry -- slotgrow: the push grows the table

end push

/-! ## `intern_fvar(u, ty)`: hash-cons the expression `fvar u ty`

con-ron's `EStore::intern` at `fvar` and the arena's `internE (.fvar u.toNat ty)`: the persistent
probe unless the scratch tier is open and `ty` is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `fvar` tier (tag `1`). -/
def fvarP : Word := 0x10000000
def fvarS : Word := 0x18000000

/-- The scratch skip: the scratch tier is open and `ty` is a scratch handle. The index `u` is not
a handle, so only `ty` is tested. -/
def fvskipW (m : Mem) (ty : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then (ty >>> 27) &&& 1 else 0

/-- The model of `intern_fvar`: the handle and the memory after, or `none` where the L code
aborts. -/
def fvinternW (m : Mem) (u ty : Word) : Option (Word × Mem) :=
  let h := fvarHashW u ty
  let rs₀ := fvprobeW (m.arr64 FVSLOT) (m.arr64 FVREC) 0 u ty (baseW m 0) (nSlotsFv m) (homeW h (nSlotsFv m)) 0
  let rs₁ := fvprobeW (m.arr64 FVSLOT) (m.arr64 FVREC) 1 u ty (baseW m 1) (nSlotsFv m) (homeW h (nSlotsFv m)) 0
  if fvskipW m ty = 0 ∧ rs₀ = [] then none
  else if fvskipW m ty = 0 ∧ rs₀.headD 0 ≠ 0 then some (fvarP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (fvarS + rs₁.tail.headD 0, m)
    else if fvpushOK m 1 then
      some (fvarS + fvcnt m 1, fvpushMem m 1 u ty (rs₁.tail.tail.headD 0) (fvcnt m 1))
    else none
  else if fvpushOK m 0 then
    some (fvarP + fvcnt m 0, fvpushMem m 0 u ty (rs₀.tail.tail.headD 0) (fvcnt m 0))
  else none

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internFVar : FunDecl := lfn (u, ty) locals (h, sk, fd, i, j, d) {
  h := ((⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ ^ ty) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := (ty >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call fvar_find(0, u, ty, h);
    if fd != 0 { return ⟪fvarP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call fvar_find(1, u, ty, h);
    if fd != 0 { return ⟪fvarS⟫ + i };
    i := call fvar_push(1, u, ty, j);
    return ⟪fvarS⟫ + i
  };
  i := call fvar_push(0, u, ty, j);
  return ⟪fvarP⟫ + i
}

/-- The `fvar` store functions, as one `#eval`-able program. -/
def fvarProg : Prog :=
  [("fvar_find", fvarFind), ("fvar_push", fvarPush), ("fvar_grow", slotGrowG fvarGS), ("intern_fvar", internFVar)]

/-- A memory with 8 `fvar` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥24 (the other tables') are unused here and left empty. -/
def fvarMem (scratch : Word) : Mem :=
  { words := (Array.replicate 25 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch) ++
      #[Array.replicate 32 0, Array.replicate 32 0] ++ Array.replicate 62 (Array.replicate 32 0) }

/-- Intern each `(index, ty)` pair in turn; the handles. -/
def internFVars (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (u, ty) :: xs => match run fvarProg 100 "intern_fvar" [u, ty] m with
    | .ok (r, m') => (internFVars m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `fvar 0 1`, `fvar 1 1`, `fvar 0 2`, `fvar 0 1`: persistent handles 0, 1, 2, 0 (sharing is on the
whole pair, not the index alone or the type alone). -/
#guard internFVars (fvarMem 0) [(0, 1), (1, 1), (0, 2), (0, 1)] ==
  some [0x10000000, 0x10000001, 0x10000002, 0x10000000]

/- Scratch open: a persistent `ty` is probed in the persistent tier (empty); the nodes go to the
scratch tier; a scratch `ty` (`0x08000000`) skips the persistent probe. -/
#guard internFVars (fvarMem 1) [(0, 1), (0, 0x08000000), (0, 1), (0, 0x08000000)] ==
  some [0x18000000, 0x18000001, 0x18000000, 0x18000001]

section intern
variable (p : Prog) (hpf : p.lookup "fvar_find" = some fvarFind)
  (hpp : p.lookup "fvar_push" = some fvarPush) (hp : p.lookup "intern_fvar" = some internFVar)

include hpf hpp hp in
theorem internFVar_spec (n : Nat) (s₀ : St) (u ty : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_fvar" [u, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ fvinternW s₀.mem u ty = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internFVar]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        fvarFind_spec p hpf n, fvarPush_spec p hpp n] <;>
      finish [fvinternW, fvskipW, fvarHashW, baseW]

end intern

end L.Arena
