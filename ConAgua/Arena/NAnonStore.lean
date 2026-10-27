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
# The name store's `anonymous` node store in L: a table with no fields

The arena's name store keeps the single `anonymous` node in a `Tbl AnonNode NIdx UInt64` per tier
(`vendor/con-ron/ConRon/Arena/Store.lean:137`, `NTables.anons`). `AnonNode` has no fields
(`mk ::`), so there is at most one node per tier and the cons key never distinguishes two nodes:
the match function is the constant `true` (**any** node that is there is the `anonymous` node).
As the level store's `zero` table (`ZeroStore.lean`), this uses a one-word dummy record (`w = 0`
is excluded by `Schema.WF`'s shape).

* **Records.** Word array `NAREC`, one (unused) word per node, tiers interleaved: node `i` of
  tier `t` at `NAREC[2 i + t]`. The node count of tier `t` is `CTL[34 + t]`.
* **Cons table.** Word array `NASLOT`, the same open addressing as `SLOT`/`ZSLOT`.

The functions `nanon_find(t, h)`, `nanon_push(t, j)` and `intern_nanon()` are the
cons-table library's templates (`ConsLib.lean`) at the schema `nanonCS` (no scratch skip); their
specs are the library's (`ConsLibSpec.lean`) from this table's obligations (`nanonOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The (constant) hash of the `anonymous` record: there is only one key, so the home slot of
every probe is the same, fixed slot. -/
def nahashW : Word := fnvBasis

/-- The model of the match: **every** node of this table is the `anonymous` node. -/
def namatchW (_r : Array Word) (_t _i : Word) : Bool := true

/-- The (constant) hash of node `i` of tier `t`. -/
def nahash (_m : Mem) (_t _i : Word) : Word := nahashW

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `anonymous` tier (tag `0`). -/
def naP : Word := 0x00000000
def naS : Word := 0x08000000

/-- The `nanon` table as a cons schema: no key word, a dummy record word `0`; every node matches;
no scratch skip. -/
def nanonCS : ConsSch where
  ra := NAREC
  sa := NASLOT
  w := 1
  ca := 34
  P := naP
  S := naS
  tag := 0
  fname := "nanon_find"
  pname := "nanon_push"
  nk := 0
  exact := true
  mc := condOf (lblk (t, h, n, j, d, v, b) { if 0 == 0 { skip } })
  np := 0
  room := condOf (lblk (t, j, c) { if len(NAREC⟨t⟩) <= c { skip } })
  recW := [.const 0]
  ihash := lblk (h) { h := ⟪nahashW⟫ }
  skipW := none
  mtM m _ t i := namatchW (m.arr64 (tierA NAREC t)) t i
  qhM _ _ := nahashW
  hsM := nahash
  vsM _ := [0]
  roomM m t c := decide (m.len64 (tierA NAREC t) ≤ c)

/-! ## `nanon_find(t, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def nanonFind : FunDecl := consFindG nanonCS

/-! ## `nanon_push(t, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `anonymous` table, `CTL[34 + t]`. -/
def nacnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (34 + t)

/-- `nanon_push`'s room checks: the handle index, the record array. -/
def napushOK (m : Mem) (t : Word) : Bool :=
  decide (nacnt m t < (134217728 : Word)) && decide (nacnt m t < m.len64 (tierA NAREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def nanonPush : FunDecl := consPushG nanonCS

/-! ## `intern_nanon()`: hash-cons the name `anonymous`

con-ron's `NStore::intern` at `anonymous` and the arena's `internNNode .anonymous`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_nanon`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def nainternW (m : Mem) : Option (Word × Mem) := consInternM nanonCS m []

/-- con-ron: ConRon/Arena/Monad.lean:381-397 ConRon.Arena.internNNode -/
@[l_impl ConRon.Arena.internNNode]
def internNAnon : FunDecl := consInternG nanonCS

/-- The `anonymous` store functions, as one `#eval`-able program. -/
def nanonProg : Prog :=
  [("nanon_find", nanonFind), ("nanon_push", nanonPush), ("intern_nanon", internNAnon)]

/-- A memory with 8 `anonymous` slots per tier, the scratch tier closed or open. Arrays 0‥32 (the
other tables') are unused here and left empty. -/
def nanonMem (scratch : Word) : Mem :=
  { words := withTiers <| ((Array.replicate 33 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch)) ++
      #[Array.replicate 16 0, Array.replicate consTestWords 0] }

/-- Intern `anonymous` `k` times in a row: the handle, every time, is the first persistent
node. -/
def internNAnons (m : Mem) : Nat → Option (List Word)
  | 0 => some []
  | k + 1 => match run nanonProg 100 "intern_nanon" [] m with
    | .ok (r, m') => (internNAnons m' k).map (r.headD 0 :: ·)
    | .error _ => none

/- Interning `anonymous` three times in a row: the same persistent handle every time (sharing). -/
#guard internNAnons (nanonMem 0) 3 == some [0x00000000, 0x00000000, 0x00000000]

/- Scratch open: the one node goes to the scratch tier (the persistent tier is empty). -/
#guard internNAnons (nanonMem 1) 2 == some [0x08000000, 0x08000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `nanon` table's obligations.** -/
theorem nanonOK : ConsOK p nanonCS where
  match_ := by
    intro s
    simp [nanonCS, condOf, Cond.pval, Expr.pval, namatchW, Cmp.eval, L.Notation.blk]
  ihash := by
    intro n s₀
    simp only [nanonCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, nahashW]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, nanonCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, nahashW]
  recs := ⟨by
      intro e he s s' _
      simp only [nanonCS, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; simp [Expr.pval],
    fun s => by simp [nanonCS, Expr.pval]⟩
  room := fun s => by
    simp only [nanonCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by intro e he; simp [nanonCS] at he
  pre := rfl
  colA := by simp [nanonCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [nanonCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [nanonCS] at h
  mloc := fun h => by simp [nanonCS] at h
  exnk := fun _ => by decide

theorem napushOK_eqC (m : Mem) (t : Word) : napushOK m t = pushOKC nanonCS m t := by
  simp only [napushOK, pushOKC, nacnt, cntC, nanonCS, ← decide_not, UInt64.not_le]; rfl

theorem internNAnon_spec (hpf : p.lookup "nanon_find" = some nanonFind)
    (hpp : p.lookup "nanon_push" = some nanonPush) (hp : p.lookup "intern_nanon" = some internNAnon)
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nanon" []
    ⦃fun r s' => LocEq s' s₀ ∧ nainternW s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p nanonCS (nanonOK p) hpf hpp "intern_nanon" hp n s₀ [] rfl trivial

end specs

end L.Arena
