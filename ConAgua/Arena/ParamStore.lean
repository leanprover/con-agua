module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level `param` node store in L: a third store, one handle field per node

The arena's level store keeps `param n` nodes in a `Tbl ParamNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.params`). Its L representation is the `app` store's
(`AppStore.lean`) with one word per node and no scratch skip (`LStore.find?` probes the
persistent tier unconditionally):

* **Records.** Word array `PREC`, one word per node (the handle word of `u`), tiers
  interleaved: node `i` of tier `t` at `PREC[2 i + t]`. The node count of tier `t` is
  `CTL[14 + t]`.
* **Cons table.** Word array `PSLOT`, the same open addressing as `SLOT`.

The functions: `param_find(t, u, h)`, `param_push(t, u, j)` and `intern_param(u)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `param` records, both tiers interleaved (one word per node). -/
abbrev PREC : ArrId := 14
/-- The `param` cons-table slots, both tiers interleaved. -/
abbrev PSLOT : ArrId := 15

/-- The hash of a `param` record (FNV-1a over its word). -/
def paramHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `param n`. -/
def pmatchW (r : Array Word) (t i u : Word) : Bool := rdW r (i * 2 + t) == u

/-! ## `param_find(t, u, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def pprobeW (sl r : Array Word) (t u b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if pmatchW r t (slotV sl b (j * 2 + t) - 1) u then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else pprobeW sl r t u b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
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

theorem pprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : pprobeW sl r t u b n j d = [0, 0, j, d] := by
  rw [pprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem pprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : pmatchW r t (sl[k] - b - 1) u = true) :
    pprobeW sl r t u b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [pprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem pprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : pmatchW r t (sl[k] - b - 1) u = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    pprobeW sl r t u b n j d = pprobeW sl r t u b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [pprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] pprobeW_free => pprobeW sl r t u b n j d, sl[k]
grind_pattern [arena_grind] pprobeW_hit => pprobeW sl r t u b n j d, sl[k]
grind_pattern [arena_grind] pprobeW_next =>
  pprobeW sl r t u b n j d, sl[k], pprobeW sl r t u b n j' d'

def pfindLoop : Stmt := lblk (t, u, h, n, j, d, v, b) {
  while d < n {
    v := PSLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    if PREC.u64[(v - 1) * 2 + t] == u { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def paramFind : FunDecl := lfn (t, u, h) locals (n, j, d, v, b) {
  n := len(PSLOT.u64) >> 1;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪pfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "param_find" = some paramFind)

theorem pfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n pfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (pprobeW (s₀.mem.arr64 PSLOT) (s₀.mem.arr64 PREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      pprobeW (s₀.mem.arr64 PSLOT) (s₀.mem.arr64 PREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := pfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [pmatchW, baseW]

theorem pfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) pfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (pprobeW (s₀.mem.arr64 PSLOT) (s₀.mem.arr64 PREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)) =
      pprobeW (s₀.mem.arr64 PSLOT) (s₀.mem.arr64 PREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 7) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5); ⊤⦄ :=
  Triple.step_exec (pfindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `param` table. -/
def nSlotsP (m : Mem) : Word := m.len64 PSLOT >>> 1

include hp in
theorem paramFind_spec (n : Nat) (s₀ : St) (t u h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "param_find" [t, u, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = pprobeW (s₀.mem.arr64 PSLOT) (s₀.mem.arr64 PREC) t u
        (baseW s₀.mem t) (nSlotsP s₀.mem) (homeW h (nSlotsP s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, paramFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, pfindLoop_step_spec p n, ld64] <;>
      finish [nSlotsP, homeW, baseW]

end find

/-! ## `param_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `param` table, `CTL[14 + t]`. -/
def pcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (14 + t)

/-- `param_push`'s room checks: the handle index, the record array, the load limit. -/
def ppushOK (m : Mem) (t : Word) : Bool :=
  decide (pcnt m t < (134217728 : Word)) && decide (pcnt m t < m.len64 PREC >>> (1 : Word)) &&
    decide (pcnt m t + 1 ≤ (nSlotsP m >>> (2 : Word)) * 3)

/-- The memory after `param_push(t, u, j)` appended node `c`. -/
def ppushMem (m : Mem) (t u j c : Word) : Mem :=
  (((m.set64 PREC (c * 2 + t) u).set64 PSLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (14 + (t &&& 1)) (c + 1))

def paramPush : FunDecl := lfn (t, u, j) locals (c) {
  c := CTL.u64[14 + t];
  if c >= 134217728 { abort };
  if len(PREC.u64) >> 1 <= c { abort };
  if ((len(PSLOT.u64) >> 1) >> 2) * 3 < c + 1 { abort };
  PREC.u64[c * 2 + t] := u;
  PSLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[14 + (t & 1)] := c + 1;
  return c
}

section push
variable (p : Prog) (hp : p.lookup "param_push" = some paramPush)

include hp in
theorem paramPush_spec (n : Nat) (s₀ : St) (t u j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "param_push" [t, u, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ppushOK s₀.mem t = true ∧ r = [pcnt s₀.mem t] ∧
      s'.mem = ppushMem s₀.mem t u j (pcnt s₀.mem t); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, paramPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [pcnt, ppushOK, ppushMem, nSlotsP, baseW]

end push

/-! ## `intern_param(u)`: hash-cons the level `param n`

con-ron's `LStore::intern` at `param` and the arena's `internLNode (.param n)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `param` tier (tag `4`). -/
def paramP : Word := 0x40000000
def paramS : Word := 0x48000000

/-- The model of `intern_param`: the handle and the memory after, or `none` where the L code
aborts. -/
def pinternW (m : Mem) (u : Word) : Option (Word × Mem) :=
  let h := paramHashW u
  let rs₀ := pprobeW (m.arr64 PSLOT) (m.arr64 PREC) 0 u (baseW m 0) (nSlotsP m) (homeW h (nSlotsP m)) 0
  let rs₁ := pprobeW (m.arr64 PSLOT) (m.arr64 PREC) 1 u (baseW m 1) (nSlotsP m) (homeW h (nSlotsP m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (paramP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (paramS + rs₁.tail.headD 0, m)
    else if ppushOK m 1 then
      some (paramS + pcnt m 1, ppushMem m 1 u (rs₁.tail.tail.headD 0) (pcnt m 1))
    else none
  else if ppushOK m 0 then
    some (paramP + pcnt m 0, ppushMem m 0 u (rs₀.tail.tail.headD 0) (pcnt m 0))
  else none

@[l_impl ConRon.Arena.internLNode]
def internParam : FunDecl := lfn (u) locals (h, fd, i, j, d) {
  h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫;
  (fd, i, j, d) := call param_find(0, u, h);
  if fd != 0 { return ⟪paramP⟫ + i };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call param_find(1, u, h);
    if fd != 0 { return ⟪paramS⟫ + i };
    i := call param_push(1, u, j);
    return ⟪paramS⟫ + i
  };
  i := call param_push(0, u, j);
  return ⟪paramP⟫ + i
}

/-- The `param` store functions, as one `#eval`-able program. -/
def paramProg : Prog :=
  [("param_find", paramFind), ("param_push", paramPush), ("intern_param", internParam)]

/-- A memory with 8 `param` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥13 (the other tables' `REC`/`SLOT` arrays) are unused here and left empty. -/
def paramMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], Array.replicate 16 0, Array.replicate 32 0] }

/-- Intern each (name handle) word in turn; the handles. -/
def internParams (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run paramProg 100 "intern_param" [u] m with
    | .ok (r, m') => (internParams m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `param` of name handles `0`, `1`, `0`: persistent handles 0, 1, 0 (sharing). -/
#guard internParams (paramMem 0) [0, 1, 0] == some [0x40000000, 0x40000001, 0x40000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internParams (paramMem 1) [0, 1, 0] == some [0x48000000, 0x48000001, 0x48000000]

section intern
variable (p : Prog) (hpf : p.lookup "param_find" = some paramFind)
  (hpp : p.lookup "param_push" = some paramPush) (hp : p.lookup "intern_param" = some internParam)

include hpf hpp hp in
theorem internParam_spec (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_param" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ pinternW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internParam]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        paramFind_spec p hpf n, paramPush_spec p hpp n] <;>
      finish [pinternW, paramHashW, baseW]

end intern

end L.Arena
