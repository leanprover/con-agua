module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The expression `letE` node store in L: three handle fields per node

The arena's expression store keeps `letE ty val body` nodes in a `Tbl LetNode EIdx UInt64` per
tier (`Arena/Store.lean:294`, `ETables.lets`). Its L representation is `app`'s/`const`'s shape
(open addressing, scratch-skipping) at three fields instead of two:

* **Records.** Word array `LEREC`, three words per node (the handle words of `ty`, `val` and
  `body`), tiers interleaved: node `i` of tier `t` at `LEREC[6 i + 3 t ..]`. The node count of
  tier `t` is `CTL[20 + t]`.
* **Cons table.** Word array `LESLOT`, the same open addressing as `SLOT`/`ASLOT`.
* **The scratch skip.** `internE (.letE ty val body)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `ty | val | body`.

The functions: `letE_find(t, ty, val, body, h)`, `letE_push(t, ty, val, body, j)` and
`intern_letE(ty, val, body)`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `letE` records, both tiers interleaved (three words per node). -/
abbrev LEREC : ArrId := 20
/-- The `letE` cons-table slots, both tiers interleaved. -/
abbrev LESLOT : ArrId := 21

/-- The growth schema of this table (`SlotGrow.lean`). -/
def letGS : GrowSch :=
  ⟨LESLOT, LEREC, 3, 20, lblk (n, k, t, i, c, h) {
    h := (((⟪fnvBasis⟫ ^ LEREC.u64[i * 6 + t * 3]) * ⟪fnvPrime⟫ ^ LEREC.u64[i * 6 + t * 3 + 1]) * ⟪fnvPrime⟫ ^ LEREC.u64[i * 6 + t * 3 + 2]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of a `letE` record (FNV-1a over its three words). -/
def letHashW (ty val body : Word) : Word :=
  (((fnvBasis ^^^ ty) * fnvPrime ^^^ val) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, val, body)`. -/
def lematchW (r : Array Word) (t i ty val body : Word) : Bool :=
  rdW r (i * 6 + t * 3) == ty && rdW r (i * 6 + t * 3 + 1) == val && rdW r (i * 6 + t * 3 + 2) == body

/-! ## `letE_find(t, ty, val, body, h)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps (`probeW` with `lematchW`). -/
def leprobeW (sl r : Array Word) (t ty val body b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if lematchW r t (slotV sl b (j * 2 + t) - 1) ty val body then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else leprobeW sl r t ty val body b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r : Array Word) (t ty val body b n j d : Word)

theorem leprobeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : leprobeW sl r t ty val body b n j d = [0, 0, j, d] := by
  rw [leprobeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem leprobeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : lematchW r t (sl[k] - b - 1) ty val body = true) :
    leprobeW sl r t ty val body b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [leprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem leprobeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : lematchW r t (sl[k] - b - 1) ty val body = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    leprobeW sl r t ty val body b n j d = leprobeW sl r t ty val body b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [leprobeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] leprobeW_free => leprobeW sl r t ty val body b n j d, sl[k]
grind_pattern [arena_grind] leprobeW_hit => leprobeW sl r t ty val body b n j d, sl[k]
grind_pattern [arena_grind] leprobeW_next =>
  leprobeW sl r t ty val body b n j d, sl[k], leprobeW sl r t ty val body b n j' d'

def lefindLoop : Stmt := lblk (t, ty, val, body, h, n, j, d, w, b) {
  while d < n {
    w := LESLOT.u64[j * 2 + t];
    if w <= b { return (0, 0, j, d) };
    w := w - b;
    if LEREC.u64[(w - 1) * 6 + t * 3] == ty && LEREC.u64[(w - 1) * 6 + t * 3 + 1] == val
        && LEREC.u64[(w - 1) * 6 + t * 3 + 2] == body {
      return (1, w - 1, j, d)
    };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def letFind : FunDecl := lfn (t, ty, val, body, h) locals (n, j, d, w, b) {
  n := ⟪SN0⟫ << LESLOT.u64[len(LESLOT.u64) - 1];
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪lefindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "letE_find" = some letFind)

theorem lefindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lefindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (leprobeW (s₀.mem.arr64 LESLOT) (s₀.mem.arr64 LEREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)) =
      leprobeW (s₀.mem.arr64 LESLOT) (s₀.mem.arr64 LEREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lefindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [lematchW, baseW]

theorem lefindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) lefindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (leprobeW (s₀.mem.arr64 LESLOT) (s₀.mem.arr64 LEREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)) =
      leprobeW (s₀.mem.arr64 LESLOT) (s₀.mem.arr64 LEREC) (s₀.loc 0) (s₀.loc 1)
        (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7); ⊤⦄ :=
  Triple.step_exec (lefindLoop_spec p (n + 1) s₀)

/-- The slot count of a tier of the `letE` table. -/
def nSlotsLe (m : Mem) : Word := SN0 <<< rdW (m.arr64 LESLOT) (m.len64 LESLOT - 1)

include hp in
theorem letFind_spec (n : Nat) (s₀ : St) (t ty val body h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "letE_find" [t, ty, val, body, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = leprobeW (s₀.mem.arr64 LESLOT) (s₀.mem.arr64 LEREC) t ty val body
        (baseW s₀.mem t) (nSlotsLe s₀.mem) (homeW h (nSlotsLe s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, letFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, lefindLoop_step_spec p n, ld64] <;>
      finish [nSlotsLe, homeW, baseW]

end find

/-! ## `letE_push(t, ty, val, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `letE` table, `CTL[20 + t]`. -/
def lecnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (20 + t)

/-- `letE_push`'s room checks: the handle index, the record array, the load limit. `LEREC`'s
width (3) is not a power of two, so (unlike `app`'s `>> 2`) the record-room check is stated by
multiplication, `(c + 1) * 6 ≤ len`, matching `PushRoom`'s own shape directly (L has no division:
`PLAN.md`, "the language L"). -/
def lepushOK (m : Mem) (t : Word) : Bool :=
  decide (lecnt m t < (134217728 : Word)) && decide ((lecnt m t + 1) * 6 ≤ m.len64 LEREC)

/-- The memory after `letE_push(t, ty, val, body, j)` appended node `c`. -/
def lepushMem (m : Mem) (t ty val body j c : Word) : Mem :=
  ((((m.set64 LEREC (c * 6 + t * 3) ty).set64 LEREC (c * 6 + t * 3 + 1) val).set64 LEREC
    (c * 6 + t * 3 + 2) body).set64 LESLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (20 + (t &&& 1)) (c + 1)

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def letPush : FunDecl := lfn (t, ty, val, body, j) locals (c, k, gn, gk, gt, gi, gc, gh, gj, gb, gd) {
  c := CTL.u64[20 + t];
  if c >= 134217728 { abort };
  if len(LEREC.u64) < (c + 1) * 6 { abort };
  k := c * 6 + t * 3;
  LEREC.u64[k] := ty;
  LEREC.u64[k + 1] := val;
  LEREC.u64[k + 2] := body;
  gk := LESLOT.u64[len(LESLOT.u64) - 1];
  LESLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[20 + (t & 1)] := c + 1;
  if (⟪SN0⟫ << gk) < (c + 1) * 2 { ⟪growBlkG letGS 7⟫ };
  return c
}

/-- The hash of node `i` of tier `t`. -/
def lehash (m : Mem) (t i : Word) : Word :=
  letHashW (rdW (m.arr64 LEREC) (i * 6 + t * 3)) (rdW (m.arr64 LEREC) (i * 6 + t * 3 + 1))
    (rdW (m.arr64 LEREC) (i * 6 + t * 3 + 2))

section push
variable (p : Prog) (hp : p.lookup "letE_push" = some letPush)

/-- The growth's hash block computes `lehash`. -/
theorem lehash_ok : HashOK p letGS 7 lehash := by
  intro k s₀
  simp only [letGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [lehash, letHashW, LocEq, St.setLoc]

include hp in
theorem letPush_spec (n : Nat) (s₀ : St) (t ty val body j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "letE_push" [t, ty, val, body, j]
    ⦃fun r s' => LocEq s' s₀ ∧ lepushOK s₀.mem t = true ∧ r = [lecnt s₀.mem t] ∧
      growIf LESLOT 20 lehash s₀.mem (lepushMem s₀.mem t ty val body j (lecnt s₀.mem t))
        (lecnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, letPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64,
        growBlkG_spec p letGS LESLOT 20 rfl rfl 7 lehash (lehash_ok p) n]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals first
      | (rw [growIf_grow]; (focus simp only [lepushMem, lecnt, baseW, SCB]; grind [arena_grind, lang_grind]);
          grind [arena_grind, lang_grind, lecnt, gnW, gexpW])
      | (rw [growIf_keep]; (focus simp only [lepushMem, lecnt, baseW, SCB]; grind [arena_grind, lang_grind]);
          grind [arena_grind, lang_grind, lecnt, gnW, gexpW])
      | grind [arena_grind, lang_grind, lecnt, lepushOK, baseW, LocEq]

end push

/-! ## `intern_letE(ty, val, body)`: hash-cons the expression `letE ty val body`

con-ron's `EStore::intern` at `letE` and the arena's `internE (.letE ty val body)`: the
persistent probe unless the scratch tier is open and a child is a scratch handle, the scratch
probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The handle word of node `0` of the persistent / scratch `letE` tier (tag `7`). -/
def letP : Word := 0x70000000
def letS : Word := 0x78000000

/-- The scratch skip: the scratch tier is open and `ty`, `val` or `body` is a scratch handle. -/
def leskipW (m : Mem) (ty val body : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((ty ||| val ||| body) >>> 27) &&& 1 else 0

/-- The model of `intern_letE`: the handle and the memory after, or `none` where the L code
aborts. -/
def leinternW (m : Mem) (ty val body : Word) : Option (Word × Mem) :=
  let h := letHashW ty val body
  let rs₀ := leprobeW (m.arr64 LESLOT) (m.arr64 LEREC) 0 ty val body (baseW m 0) (nSlotsLe m) (homeW h (nSlotsLe m)) 0
  let rs₁ := leprobeW (m.arr64 LESLOT) (m.arr64 LEREC) 1 ty val body (baseW m 1) (nSlotsLe m) (homeW h (nSlotsLe m)) 0
  if leskipW m ty val body = 0 ∧ rs₀ = [] then none
  else if leskipW m ty val body = 0 ∧ rs₀.headD 0 ≠ 0 then some (letP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (letS + rs₁.tail.headD 0, m)
    else if lepushOK m 1 then
      match growIf LESLOT 20 lehash m (lepushMem m 1 ty val body (rs₁.tail.tail.headD 0) (lecnt m 1)) (lecnt m 1) with
      | some m' => some (letS + lecnt m 1, m')
      | none => none
    else none
  else if lepushOK m 0 then
    match growIf LESLOT 20 lehash m (lepushMem m 0 ty val body (rs₀.tail.tail.headD 0) (lecnt m 0)) (lecnt m 0) with
    | some m' => some (letP + lecnt m 0, m')
    | none => none
  else none

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internLet : FunDecl := lfn (ty, val, body) locals (h, sk, fd, i, j, d) {
  h := (((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ val) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫;
  sk := 0;
  if CTL.u64[1] != 0 { sk := ((ty | val | body) >> 27) & 1 };
  if sk == 0 {
    (fd, i, j, d) := call letE_find(0, ty, val, body, h);
    if fd != 0 { return ⟪letP⟫ + i }
  };
  if CTL.u64[1] != 0 {
    (fd, i, j, d) := call letE_find(1, ty, val, body, h);
    if fd != 0 { return ⟪letS⟫ + i };
    i := call letE_push(1, ty, val, body, j);
    return ⟪letS⟫ + i
  };
  i := call letE_push(0, ty, val, body, j);
  return ⟪letP⟫ + i
}

/-- The `letE` store functions, as one `#eval`-able program. -/
def letProg : Prog :=
  [("letE_find", letFind), ("letE_push", letPush), ("intern_letE", internLet)]

/-- A memory with 8 `letE` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥19 (the other tables') are unused here and left empty. -/
def letMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0),
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate 48 0, Array.replicate 32 0] }

/-- Intern each triple in turn; the handles. -/
def internLets (m : Mem) : List (Word × Word × Word) → Option (List Word)
  | [] => some []
  | (ty, val, body) :: xs => match run letProg 100 "intern_letE" [ty, val, body] m with
    | .ok (r, m') => (internLets m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2, 3)`, `(3, 2, 1)`, `(1, 2, 3)`: persistent handles 0, 1, 0. -/
#guard internLets (letMem 0) [(1, 2, 3), (3, 2, 1), (1, 2, 3)] ==
  some [0x70000000, 0x70000001, 0x70000000]

/- Scratch open: a scratch child (`0x78000000`) skips the persistent probe. -/
#guard internLets (letMem 1) [(1, 2, 3), (0x78000000, 2, 3), (1, 2, 3), (0x78000000, 2, 3)] ==
  some [0x78000000, 0x78000001, 0x78000000, 0x78000001]

section intern
variable (p : Prog) (hpf : p.lookup "letE_find" = some letFind)
  (hpp : p.lookup "letE_push" = some letPush) (hp : p.lookup "intern_letE" = some internLet)

include hpf hpp hp in
theorem internLet_spec (n : Nat) (s₀ : St) (ty val body : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_letE" [ty, val, body]
    ⦃fun r s' => LocEq s' s₀ ∧ leinternW s₀.mem ty val body = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internLet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        letFind_spec p hpf n, letPush_spec p hpp n] <;>
      finish [leinternW, leskipW, letHashW, baseW]

end intern

end L.Arena
