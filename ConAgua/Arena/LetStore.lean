module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
public import ConAgua.Arena.ConsLibSpec
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# The expression `letE` node store in L: three handle fields per node

The arena's expression store keeps `letE ty val body` nodes in a `Tbl LetNode EIdx UInt64` per
tier (`Arena/Store.lean:294`, `ETables.lets`). Its L representation is `app`'s/`const`'s shape
(open addressing, scratch-skipping) at three fields instead of two:

* **Records.** Word array `LEREC`, two words per node (the handle words of `ty`, `val` and
  `body`: `ty | val << 32`, then `body`), one array per tier: node `i` of tier `t` at `LEREC⟨t⟩[2 i ..]`. The node count of
  tier `t` is `CTL[20 + t]`.
* **Cons table.** Word array `LESLOT`, the same open addressing as `SLOT`/`ASLOT`.
* **The scratch skip.** `internE (.letE ty val body)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `ty | val | body`.

The functions `letE_find(t, ty, val, body, h)` (the probe, the match inline: three word
comparisons), `letE_push(t, ty, val, body, j)` and `intern_letE(ty, val, body)` are the cons-table
library's templates (`ConsLib.lean`) at the schema `letCS`; their specs are the library's
(`ConsLibSpec.lean`) from this table's obligations (`letOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The hash of a `letE` record (FNV-1a over its three fields). -/
def letHashW (ty val body : Word) : Word :=
  (((fnvBasis ^^^ ty) * fnvPrime ^^^ val) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, val, body)`. -/
def lematchW (r : Array Word) (_t i ty val body : Word) : Bool :=
  rdW r (i * 2) &&& 4294967295 == ty && rdW r (i * 2) >>> 32 == val && rdW r (i * 2 + 1) == body

/-- The hash of node `i` of tier `t`. -/
def lehash (m : Mem) (t i : Word) : Word :=
  letHashW (rdW (m.arr64 (tierA LEREC t)) (i * 2) &&& 4294967295) (rdW (m.arr64 (tierA LEREC t)) (i * 2) >>> 32)
    (rdW (m.arr64 (tierA LEREC t)) (i * 2 + 1))

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `letE` tier (tag `7`). -/
def letP : Word := 0x70000000
def letS : Word := 0x78000000

/-- The `letE` table as a cons schema: three key words `ty val body`, packed into the record (lane
memlay); the match is three field comparisons; the scratch skip is bit 27 of `ty | val | body`. -/
def letCS : ConsSch where
  ra := LEREC
  sa := LESLOT
  w := 2
  ca := 20
  P := letP
  S := letS
  tag := 7
  fname := "letE_find"
  pname := "letE_push"
  nk := 3
  mc := condOf (lblk (t, ty, val, body, h, n, j, d, w, b) {
    if (LEREC⟨t⟩[(w - 1) * 2] & 4294967295) == ty && (LEREC⟨t⟩[(w - 1) * 2] >> 32) == val
        && LEREC⟨t⟩[(w - 1) * 2 + 1] == body { skip } })
  np := 3
  room := condOf (lblk (t, ty, val, body, j, c) { if len(LEREC⟨t⟩) < (c + 1) * 2 { skip } })
  recW := [.bin .or (.var 1) (.bin .shl (.var 2) (.const 32)), .var 3]
  ihash := lblk (ty, val, body, h) {
    h := (((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ val) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (ty, val, body, h, sk) { sk := ((ty | val | body) >> 27) & 1 }))
  mtM m ks t i := lematchW (m.arr64 (tierA LEREC t)) t i (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)
  qhM _ ks := letHashW (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)
  hsM := lehash
  vsM as := [as.getD 0 0 ||| as.getD 1 0 <<< 32, as.getD 2 0]
  roomM m t c := decide (m.len64 (tierA LEREC t) < (c + 1) * 2)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0 ||| ks.getD 2 0) >>> 27) &&& 1

/-! ## `letE_find(t, ty, val, body, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def letFind : FunDecl := consFindG letCS

/-! ## `letE_push(t, ty, val, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `letE` table, `CTL[20 + t]`. -/
def lecnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (20 + t)

/-- `letE_push`'s room checks: the handle index, the record array, the load limit. `LEREC`'s
width (3) is not a power of two, so (unlike `app`'s `>> 2`) the record-room check is stated by
multiplication, `(c + 1) * 6 ≤ len`, matching `PushRoom`'s own shape directly (L has no division:
`PLAN.md`, "the language L"). -/
def lepushOK (m : Mem) (t : Word) : Bool :=
  decide (lecnt m t < (134217728 : Word)) && decide ((lecnt m t + 1) * 2 ≤ m.len64 (tierA LEREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def letPush : FunDecl := consPushG letCS

/-! ## `intern_letE(ty, val, body)`: hash-cons the expression `letE ty val body`

con-ron's `EStore::intern` at `letE` and the arena's `internE (.letE ty val body)`: the
persistent probe unless the scratch tier is open and a child is a scratch handle, the scratch
probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The scratch skip: the scratch tier is open and `ty`, `val` or `body` is a scratch handle. -/
def leskipW (m : Mem) (ty val body : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((ty ||| val ||| body) >>> 27) &&& 1 else 0

/-- The model of `intern_letE`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def leinternW (m : Mem) (ty val body : Word) : Option (Word × Mem) := consInternM letCS m [ty, val, body]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internLet : FunDecl := consInternG letCS

/-- The `letE` store functions, as one `#eval`-able program. -/
def letProg : Prog :=
  [("letE_find", letFind), ("letE_push", letPush), ("intern_letE", internLet)]

/-- A memory with 8 `letE` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
0‥19 (the other tables') are unused here and left empty. -/
def letMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0),
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate 48 0, Array.replicate consTestWords 0] }

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

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `letE` table's obligations.** -/
theorem letOK : ConsOK p letCS where
  match_ := by
    intro s
    simp [letCS, condOf, Cond.pval, Expr.pval, lematchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ, Bool.and_assoc]
  ihash := by
    intro n s₀
    simp only [letCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, letHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, letCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, letHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [letCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [letCS, argsOf, Expr.pval, BinOp.eval, List.range_succ]⟩
  room := fun s => by
    simp only [letCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [letCS, Option.some.injEq] at he
    subst he
    simp [letCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [letCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [letCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun _ _ _ _ _ => rfl
  mloc := fun h => by simp [letCS] at h
  exnk := fun h => by simp [letCS] at h

theorem lepushOK_eqC (m : Mem) (t : Word) : lepushOK m t = pushOKC letCS m t := by
  simp only [lepushOK, pushOKC, letCS, lecnt, cntC, ← decide_not, UInt64.not_lt]; rfl

theorem internLet_spec (hpf : p.lookup "letE_find" = some letFind)
    (hpp : p.lookup "letE_push" = some letPush) (hp : p.lookup "intern_letE" = some internLet)
    (n : Nat) (s₀ : St) (ty val body : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_letE" [ty, val, body]
    ⦃fun r s' => LocEq s' s₀ ∧ leinternW s₀.mem ty val body = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p letCS (letOK p) hpf hpp "intern_letE" hp n s₀ [ty, val, body] rfl trivial

end specs

end L.Arena
