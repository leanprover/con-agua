module

public import ConAgua.Arena.ConsLibSpec
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The `forallE` node store in L: a binder record, two handle fields per node

The arena's `forallE` constructor is a `Tbl BindNode EIdx UInt64` per tier
(`Arena/Store.lean:287`, `ETables.foralls`), `BindNode`'s other array, shared with `lam`
(`LamStore.lean`). Same record shape as `app`/`lam` (two handle fields), so the L representation
is theirs, written out again for this record:

* **Records.** Word array `FAREC`, one word per node (the handle words of `ty` and `body`, packed: `ty | body << 32`),
  tiers interleaved: node `i` of tier `t` at `FAREC⟨t⟩[i]`. The node count of tier `t` is
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

The functions `forall_find(t, ty, body, h)` (the probe, the match inline: two half-word comparisons),
`forall_push(t, ty, body, j)` and `intern_forall(ty, body)` are the cons-table library's templates
(`ConsLib.lean`) at the schema `forallCS`; their specs are the library's (`ConsLibSpec.lean`) from
this table's obligations (`forallOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `forallE` records, both tiers interleaved (one packed word per node). -/
abbrev FAREC : ArrId := 29
/-- The `forallE` cons-table slots, both tiers interleaved. -/
abbrev FASLOT : ArrId := 30

/-- The hash of a `forallE` record (FNV-1a over its two handle words). -/
def forallHashW (ty body : Word) : Word := ((fnvBasis ^^^ ty) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, body)`. -/
def famatchW (r : Array Word) (_t i ty body : Word) : Bool :=
  rdW r i &&& 4294967295 == ty && rdW r i >>> 32 == body

/-- The hash of node `i` of tier `t`. -/
def fahash (m : Mem) (t i : Word) : Word :=
  forallHashW (rdW (m.arr64 (tierA FAREC t)) i &&& 4294967295) (rdW (m.arr64 (tierA FAREC t)) i >>> 32)

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `forallE` tier (tag `6`). -/
def forallP : Word := 0x60000000
def forallS : Word := 0x68000000

/-- The `forallE` table as a cons schema: two key words `ty body`, stored as the record; the match
is two word comparisons; the scratch skip is bit 27 of `ty | body`. -/
def forallCS : ConsSch where
  ra := FAREC
  sa := FASLOT
  w := 1
  ca := 30
  P := forallP
  S := forallS
  tag := 6
  fname := "forall_find"
  pname := "forall_push"
  nk := 2
  exact := true
  kpk := true
  mc := condOf (lblk (t, ty, body, h, n, j, d, v, b) {
    if (FAREC⟨t⟩[v - 1] & 4294967295) == ty && (FAREC⟨t⟩[v - 1] >> 32) == body { skip } })
  np := 2
  room := condOf (lblk (t, ty, body, j, c) { if len(FAREC⟨t⟩) <= c { skip } })
  recW := [.bin .or (.var 1) (.bin .shl (.var 2) (.const 32))]
  ihash := lblk (ty, body, h) { h := ((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (ty, body, h, sk) { sk := ((ty | body) >> 27) & 1 }))
  mtM m ks t i := famatchW (m.arr64 (tierA FAREC t)) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := forallHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := fahash
  vsM as := [as.getD 0 0 ||| as.getD 1 0 <<< 32]
  roomM m t c := decide (m.len64 (tierA FAREC t) ≤ c)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0) >>> 27) &&& 1

/-! ## `forall_find(t, ty, body, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def forallFind : FunDecl := consFindG forallCS

/-! ## `forall_push(t, ty, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `forallE` table, `CTL[30 + t]`. -/
def facnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (30 + t)

/-- `forall_push`'s room checks: the handle index, the record array. -/
def fapushOK (m : Mem) (t : Word) : Bool :=
  decide (facnt m t < (134217728 : Word)) && decide (facnt m t < m.len64 (tierA FAREC t))

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

/-- A memory with 8 `forallE` nodes and `SN0` slots per tier, the scratch tier closed or open.
Arrays other than `CTL`/`FAREC`/`FASLOT` are unused here and left empty; `CTL` reaches
`30 + 2 = 32` words. -/
def forallMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[],
      (#[0, scratch] ++ Array.replicate 62 0),
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate consTestWords 0, Array.replicate consTestWords 0] }

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

/-- **The `forallE` table's obligations.** -/
theorem forallOK : ConsOK p forallCS where
  match_ := by
    intro s
    simp [forallCS, condOf, Cond.pval, Expr.pval, famatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [forallCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, forallHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, forallCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, forallHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [forallCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [forallCS, argsOf, Expr.pval, BinOp.eval, List.range_succ]⟩
  room := fun s => by
    simp only [forallCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by
    intro e he s
    simp only [forallCS, Option.some.injEq] at he
    subst he
    simp [forallCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [forallCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [forallCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [forallCS] at h
  mloc := fun h => by simp [forallCS] at h
  exnk := fun _ => by decide

theorem fapushOK_eqC (m : Mem) (t : Word) : fapushOK m t = pushOKC forallCS m t := by
  simp only [fapushOK, pushOKC, forallCS, facnt, cntC, ← decide_not, UInt64.not_le]; rfl

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
