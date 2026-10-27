module

meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
public import ConAgua.Arena.LpCol
public import ConAgua.Arena.ConsLibSpec
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# The level `max` node store in L: a fourth store, two level-handle fields per node

The arena's level store keeps `max u v` nodes in a `Tbl BinLNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.maxs`). Its L representation is the `app` store's
(`AppStore.lean`) with two handle fields and no scratch skip (the level store's `LStore.find?`
probes the persistent tier unconditionally, as for `succ`):

* **Records.** Word array `MREC`, one word per node (the handle words of `u` and `v`, packed: `u | v << 32`), tiers
  interleaved: node `i` of tier `t` at `MREC⟨t⟩[i]`. The node count of tier `t` is
  `CTL[10 + t]`.
* **Cons table.** Word array `MSLOT`, the same open addressing as `SLOT`/`ASLOT`/`SSLOT`.

The functions: `max_find(t, u, v, h)`, `max_push(t, u, v, j)` and `intern_max(u, v)`. They are the cons-table library's templates
(`ConsLib.lean`) at the schema `maxCS`, the derived column written by the template's prelude;
their specs are the library's (`ConsLibSpec.lean`) from this table's obligations.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The hash of a `max` record (FNV-1a over its two handle words). -/
def maxHashW (u v : Word) : Word := ((fnvBasis ^^^ u) * fnvPrime ^^^ v) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(u, v)`. -/
def mmatchW (r : Array Word) (_t i u v : Word) : Bool :=
  rdW r i &&& 4294967295 == u && rdW r i >>> 32 == v

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `max` tier (tag `2`). -/
def maxP : Word := 0x20000000
def maxS : Word := 0x28000000

/-- The hash of node `i` of tier `t`. -/
def mhash (m : Mem) (t i : Word) : Word :=
  maxHashW (rdW (m.arr64 (tierA MREC t)) i &&& 4294967295) (rdW (m.arr64 (tierA MREC t)) i >>> 32)

/-- The column's prelude: `x := lvlHP(u) | lvlHP(v)`. -/
def mPre : Stmt :=
  .seq hpBlkM1 (.seq hpBlkM2 (lblk (t, u, v, j, c, k, x, g, ti, ix, y) { x := x | y }))

/-- The `max` table as a cons schema (`ConsLib.lean`); the derived column `MHP`
(either child's `hasParam` bit, `hpBlkM1`, `hpBlkM2`). -/
def maxCS : ConsSch where
  ra := MREC
  sa := MSLOT
  w := 1
  ca := 10
  P := maxP
  S := maxS
  tag := 2
  fname := "max_find"
  pname := "max_push"
  nk := 2
  exact := true
  kpk := true
  mc := condOf (lblk (t, u, v, h, n, j, d, w, b) {
    if (MREC⟨t⟩[w - 1] & 4294967295) == u && (MREC⟨t⟩[w - 1] >> 32) == v { skip } })
  np := 2
  room := condOf (lblk (t, u, v, j, c) {
    if len(MREC⟨t⟩) <= c || len(MHP⟨t⟩) <= c { skip } })
  recW := [.bin .or (.var 1) (.bin .shl (.var 2) (.const 32))]
  ihash := lblk (u, v, h) { h := ((⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ ^ v) * ⟪fnvPrime⟫ }
  skipW := none
  xloc := 5
  pre := some mPre
  col := some MHP
  colM m as := lvlHPW m (as.getD 0 0) ||| lvlHPW m (as.getD 1 0)
  mtM m ks t i := mmatchW (m.arr64 (tierA MREC t)) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := maxHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := mhash
  vsM as := [as.getD 0 0 ||| as.getD 1 0 <<< 32]
  roomM m t c := decide (m.len64 (tierA MREC t) ≤ c) || decide (m.len64 (tierA MHP t) ≤ c)

/-! ## `max_find(t, u, v, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def maxFind : FunDecl := consFindG maxCS

/-! ## `max_push(t, u, v, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `max` table, `CTL[10 + t]`. -/
def mcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (10 + t)

/-- `max_push`'s room checks: the handle index, the record array. -/
def mpushOK (m : Mem) (t : Word) : Bool :=
  decide (mcnt m t < (134217728 : Word)) && decide (mcnt m t < m.len64 (tierA MREC t)) &&
    decide (mcnt m t < m.len64 (tierA MHP t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def maxPush : FunDecl := consPushG maxCS

/-! ## `intern_max(u, v)`: hash-cons the level `max u v`

con-ron's `LStore::intern` at `max` and the arena's `internLNode (.max u v)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_max`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def minternW (m : Mem) (u v : Word) : Option (Word × Mem) := consInternM maxCS m [u, v]

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internMax : FunDecl := consInternG maxCS

/-- The `max` store functions, as one `#eval`-able program. -/
def maxProg : Prog :=
  [("max_find", maxFind), ("max_push", maxPush), ("intern_max", internMax)]

/-- A memory with 8 `max` nodes and `SN0` slots per tier, the scratch tier closed or open. -/
def maxMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], #[], #[],
      #[], #[], Array.replicate consTestWords 0, Array.replicate consTestWords 0] ++
      Array.replicate 62 (Array.replicate consTestWords 0) }

/-- Intern each pair in turn; the handles. -/
def internMaxs (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (u, v) :: xs => match run maxProg 100 "intern_max" [u, v] m with
    | .ok (r, m') => (internMaxs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internMaxs (maxMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x20000000, 0x20000001, 0x20000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internMaxs (maxMem 1) [(1, 2), (2, 1), (1, 2)] == some [0x28000000, 0x28000001, 0x28000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

theorem mPre_spec (k : Stmt → M Sig) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k mPre
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.loc 6 = lvlHPW s₀.mem (s₀.loc 1) ||| lvlHPW s₀.mem (s₀.loc 2); ⊤⦄ := by
  simp only [mPre, L.Notation.blk]
  vcgen [step, evalE_spec, setLoc, hpBlkM1_spec p k, hpBlkM2_spec p k]
  all_goals simp_all [Expr.pval, BinOp.eval, St.setLoc_loc, St.setLoc_mem]

/-- **The `max` table's obligations.** -/
theorem maxOK : ConsOK p maxCS where
  match_ := by
    intro s
    simp [maxCS, condOf, Cond.pval, Expr.pval, mmatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [maxCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, maxHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, maxCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, maxHashW, argsOf, BinOp.eval]
  pre := by
    intro n s₀
    vcgen [mPre_spec p (exec p n) s₀]
    all_goals obtain ⟨h0, h1, h2, h3, hx⟩ := ‹_ ∧ _›
    · assumption
    · intro x hx'
      simp only [maxCS] at hx'
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> assumption
    · simp [maxCS, argsOf, List.range_succ, hx]
  colA := by
    intro A h
    simp only [maxCS, Option.some.injEq] at h
    subst h; decide
  recs := ⟨by
      intro e he s s' h
      simp only [maxCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [maxCS, argsOf, Expr.pval, BinOp.eval, List.range_succ]⟩
  room := fun s => by
    simp only [maxCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by
    intro e he
    simp [maxCS] at he
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [maxCS, Option.some.injEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [maxCS] at h
  mloc := fun h => by simp [maxCS] at h
  exnk := fun _ => by decide

theorem mpushOK_eqC (m : Mem) (t : Word) : mpushOK m t = pushOKC maxCS m t := by
  simp only [mpushOK, pushOKC, maxCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem internMax_spec (hpf : p.lookup "max_find" = some maxFind)
    (hpp : p.lookup "max_push" = some maxPush) (hp : p.lookup "intern_max" = some internMax)
    (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_max" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ minternW s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p maxCS (maxOK p) hpf hpp "intern_max" hp n s₀ [u, v] rfl trivial

end specs

end L.Arena
