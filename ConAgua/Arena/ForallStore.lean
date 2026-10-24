module

public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
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

The functions `forall_find(t, ty, body, h)` (the probe, the match inline: two word comparisons),
`forall_push(t, ty, body, j)` and `intern_forall(ty, body)` are the cons-table library's templates
(`ConsLib.lean`) at the schema `forallCS`; their specs are the library's (`ConsLibSpec.lean`) from
this table's obligations (`forallOK`).
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
def forallGS : GrowSch :=
  ⟨FASLOT, FAREC, 2, 30, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ FAREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ FAREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of a `forallE` record (FNV-1a over its two words). -/
def forallHashW (ty body : Word) : Word := ((fnvBasis ^^^ ty) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, body)`. -/
def famatchW (r : Array Word) (t i ty body : Word) : Bool :=
  rdW r (i * 4 + t * 2) == ty && rdW r (i * 4 + t * 2 + 1) == body

/-- The hash of node `i` of tier `t`. -/
def fahash (m : Mem) (t i : Word) : Word :=
  forallHashW (rdW (m.arr64 FAREC) (i * 4 + t * 2)) (rdW (m.arr64 FAREC) (i * 4 + t * 2 + 1))

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `forallE` tier (tag `6`). -/
def forallP : Word := 0x60000000
def forallS : Word := 0x68000000

/-- The `forallE` table as a cons schema: two key words `ty body`, stored as the record; the match
is two word comparisons; the scratch skip is bit 27 of `ty | body`. -/
def forallCS : ConsSch where
  ra := FAREC
  sa := FASLOT
  w := 2
  st := 4
  ca := 30
  P := forallP
  S := forallS
  tag := 6
  fname := "forall_find"
  pname := "forall_push"
  nk := 2
  mc := condOf (lblk (t, ty, body, h, n, j, d, v, b) {
    if FAREC.u64[(v - 1) * 4 + t * 2] == ty && FAREC.u64[(v - 1) * 4 + t * 2 + 1] == body { skip } })
  np := 2
  room := condOf (lblk (t, ty, body, j, c) { if len(FAREC.u64) >> 2 <= c { skip } })
  recW := [.var 1, .var 2]
  ghash := forallGS.hash
  ihash := lblk (ty, body, h) { h := ((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (ty, body, h, sk) { sk := ((ty | body) >> 27) & 1 }))
  mtM m ks t i := famatchW (m.arr64 FAREC) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := forallHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := fahash
  vsM as := as
  roomM m _ c := decide (m.len64 FAREC >>> (2 : Word) ≤ c)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0) >>> 27) &&& 1

/-! ## `forall_find(t, ty, body, h)`: the probe -/

/-- The model of the probe, from slot `j` after `d` steps (the library's `cprobeW`). -/
def faprobeW (sl r : Array Word) (t ty body b n j d : Word) : List Word :=
  cprobeW sl (fun i => famatchW r t i ty body) t b n j d

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def forallFind : FunDecl := consFindG forallCS

/-- The slot count of a tier of the `forallE` table. -/
def nSlotsFa (m : Mem) : Word := rdW (m.arr64 FASLOT) (m.len64 FASLOT - 1) + SN0

/-! ## `forall_push(t, ty, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `forallE` table, `CTL[30 + t]`. -/
def facnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (30 + t)

/-- `forall_push`'s room checks: the handle index, the record array. -/
def fapushOK (m : Mem) (t : Word) : Bool :=
  decide (facnt m t < (134217728 : Word)) && decide (facnt m t < m.len64 FAREC >>> (2 : Word))

/-- The memory after `forall_push(t, ty, body, j)` appended node `c`. -/
def fapushMem (m : Mem) (t ty body j c : Word) : Mem :=
  ((((m.set64 FAREC (c * 4 + t * 2) ty).set64 FAREC (c * 4 + t * 2 + 1) body).set64 FASLOT
    (j * 2 + t) (baseW m t + c + 1)).set64 CTL (30 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def forallPush : FunDecl := consPushG forallCS

/-! ## `intern_forall(ty, body)`: hash-cons the `forallE` binder with binder type `ty` and body
`body`

con-ron's `EStore::internForallE` (through `internBind`) and the arena's `internForallEE`: the
persistent probe unless the scratch tier is open and a child is a scratch handle, the scratch
probe if the scratch tier is open, the append to the tier the store is in. Same L shape as
`app`'s/`lam`'s; `ForallRefine.lean` carries the different unfolding of `internForallEE` to
`protoRun`. -/

/-- The scratch skip: the scratch tier is open and `ty` or `body` is a scratch handle. -/
def faskipW (m : Mem) (ty body : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((ty ||| body) >>> 27) &&& 1 else 0

/-- The model of `intern_forall`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def fainternW (m : Mem) (ty body : Word) : Option (Word × Mem) := consInternM forallCS m [ty, body]

/-- The L FunDecl for `intern_forall`. Named `internForallL`, not `internForallE`: con-ron's
`ConRon.Arena.internForallEE`/`EStore.internForallE` are sibling names in a different namespace,
but the `L`-suffix keeps the two visually apart in this file, which `open`s `ConRon.Arena`. -/
-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
-- con-ron: ConRon/Arena/Monad.lean:199-216 ConRon.Arena.internForallEE
@[l_impl ConRon.Arena.internE ConRon.Arena.internForallEE]
def internForallL : FunDecl := consInternG forallCS

/-- The `forallE` store functions, as one `#eval`-able program. -/
def forallProg : Prog :=
  [("forall_find", forallFind), ("forall_push", forallPush), ("intern_forall", internForallL)]

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

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- The growth's hash block computes `fahash`. -/
theorem fahash_ok : HashOK p forallGS 6 fahash := by
  intro k s₀
  simp only [forallGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [fahash, forallHashW, LocEq, St.setLoc]

/-- **The `forallE` table's obligations.** -/
theorem forallOK : ConsOK p forallCS where
  match_ := by
    intro s
    simp [forallCS, condOf, Cond.pval, Expr.pval, famatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ghash := fahash_ok p
  ihash := by
    intro n s₀
    simp only [forallCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, forallHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [forallCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [forallCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [forallCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [forallCS, Option.some.injEq] at he
    subst he
    simp [forallCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [forallCS]
  push_np := by decide
  arrs := by decide

theorem forallFind_spec (hp : p.lookup "forall_find" = some forallFind) (n : Nat) (s₀ : St)
    (t ty body h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "forall_find" [t, ty, body, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = faprobeW (s₀.mem.arr64 FASLOT) (s₀.mem.arr64 FAREC) t ty body
        (baseW s₀.mem t) (nSlotsFa s₀.mem) (homeW h (nSlotsFa s₀.mem)) 0; ⊤⦄ :=
  consFindG_spec p forallCS ((forallOK p).match_) hp n s₀ t [ty, body] rfl h trivial

theorem fapushOK_eqC (m : Mem) (t : Word) : fapushOK m t = pushOKC forallCS m t := by
  simp only [fapushOK, pushOKC, forallCS, facnt, cntC, ← decide_not, UInt64.not_le]; rfl

theorem fapushMem_eqC (m : Mem) (t ty body j c : Word) :
    fapushMem m t ty body j c = pushMC forallCS m t [ty, body] j c := by
  simp [fapushMem, pushMC, tailM, wrRecK, forallCS, baseW,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ FAREC by decide)]

theorem forallPush_spec (hp : p.lookup "forall_push" = some forallPush) (n : Nat) (s₀ : St)
    (t ty body j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "forall_push" [t, ty, body, j]
    ⦃fun r s' => LocEq s' s₀ ∧ fapushOK s₀.mem t = true ∧ r = [facnt s₀.mem t] ∧
      growIf FASLOT 30 fahash s₀.mem (fapushMem s₀.mem t ty body j (facnt s₀.mem t))
        (facnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [fapushOK_eqC]
  simp only [fapushMem_eqC]
  exact consPushG_spec p forallCS (forallOK p) hp n s₀ t [ty, body] rfl j

theorem internForallL_spec (hpf : p.lookup "forall_find" = some forallFind)
    (hpp : p.lookup "forall_push" = some forallPush)
    (hp : p.lookup "intern_forall" = some internForallL)
    (n : Nat) (s₀ : St) (ty body : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_forall" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ fainternW s₀.mem ty body = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p forallCS (forallOK p) hpf hpp "intern_forall" hp n s₀ [ty, body] rfl
    trivial

end specs

end L.Arena
