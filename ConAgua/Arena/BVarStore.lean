module

public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The expression `bvar` node store in L: one `Nat` field per node

The arena's expression store keeps `bvar i` nodes in a `Tbl BVarNode EIdx UInt64` per tier
(`Arena/Store.lean:252`, `ETables.bvars`). Its L representation is the `succ` store's
(`LevelStore.lean`, one word per node), the word being the de Bruijn index itself (below `2^64`)
rather than a handle. A `bvar` has no child, so the scratch skip never fires
(`eViewHasScratchChild (.bvar _) = false`): the persistent tier is always probed.

* **Records.** Word array `BREC`, one word per node (the index `i` as a word), tiers
  interleaved: node `i` of tier `t` at `BREC[2 i + t]`. The node count of tier `t` is
  `CTL[22 + t]`.
* **Cons table.** Word array `BSLOT`, the same open addressing as `SLOT`.

The functions `bvar_find(t, u, h)`, `bvar_push(t, u, j)` and `intern_bvar(u)` are the cons-table
library's templates (`ConsLib.lean`) at the schema `bvarCS` (no scratch skip); their specs are the
library's (`ConsLibSpec.lean`) from this table's obligations (`bvarOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `bvar` records, both tiers interleaved (one word per node). -/
abbrev BREC : ArrId := 22
/-- The `bvar` cons-table slots, both tiers interleaved. -/
abbrev BSLOT : ArrId := 23

/-- The hash of a `bvar` record (FNV-1a over its word). -/
def bvarHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `bvar u`. -/
def bmatchW (r : Array Word) (_t i u : Word) : Bool := rdW r i == u

/-- The hash of node `i` of tier `t`. -/
def bhash (m : Mem) (t i : Word) : Word := bvarHashW (rdW (m.arr64 (tierA BREC t)) i)

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `bvar` tier (tag `0`). -/
def bvarP : Word := 0x00000000
def bvarS : Word := 0x08000000

/-- The `bvar` table as a cons schema: one key word `u`, stored as the record; the match is one
word comparison; no scratch skip. -/
def bvarCS : ConsSch where
  ra := BREC
  sa := BSLOT
  w := 1
  ca := 22
  P := bvarP
  S := bvarS
  tag := 0
  fname := "bvar_find"
  pname := "bvar_push"
  nk := 1
  exact := true
  mc := condOf (lblk (t, u, h, n, j, d, v, b) { if BREC⟨t⟩[(v - 1)] == u { skip } })
  np := 1
  room := condOf (lblk (t, u, j, c) { if len(BREC⟨t⟩) <= c { skip } })
  recW := [.var 1]
  ihash := lblk (u, h) { h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ }
  skipW := none
  mtM m ks t i := bmatchW (m.arr64 (tierA BREC t)) t i (ks.getD 0 0)
  qhM _ ks := bvarHashW (ks.getD 0 0)
  hsM := bhash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA BREC t) ≤ c)

/-! ## `bvar_find(t, u, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def bvarFind : FunDecl := consFindG bvarCS

/-! ## `bvar_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `bvar` table, `CTL[22 + t]`. -/
def bcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (22 + t)

/-- `bvar_push`'s room checks: the handle index, the record array. -/
def bpushOK (m : Mem) (t : Word) : Bool :=
  decide (bcnt m t < (134217728 : Word)) && decide (bcnt m t < m.len64 (tierA BREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def bvarPush : FunDecl := consPushG bvarCS

/-! ## `intern_bvar(u)`: hash-cons the expression `bvar u`

con-ron's `EStore::intern` at `bvar` and the arena's `internE (.bvar u)`: the persistent probe,
the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_bvar`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def binternW (m : Mem) (u : Word) : Option (Word × Mem) := consInternM bvarCS m [u]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internBVar : FunDecl := consInternG bvarCS

/-- The `bvar` store functions, as one `#eval`-able program. -/
def bvarProg : Prog :=
  [("bvar_find", bvarFind), ("bvar_push", bvarPush), ("intern_bvar", internBVar)]

/-- A memory with 8 `bvar` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
0‥21 (the other tables') are unused here and left empty. -/
def bvarMem (scratch : Word) : Mem :=
  { words := withTiers <| (Array.replicate 22 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch) ++
      #[Array.replicate 16 0, Array.replicate consTestWords 0] }

/-- Intern each index in turn; the handles. -/
def internBVars (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run bvarProg 100 "intern_bvar" [u] m with
    | .ok (r, m') => (internBVars m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `bvar 0`, `bvar 1`, `bvar 0`, `bvar 7`: persistent handles 0, 1, 0, 2. -/
#guard internBVars (bvarMem 0) [0, 1, 0, 7] == some [0, 1, 0, 2]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internBVars (bvarMem 1) [0, 1, 0] == some [0x08000000, 0x08000001, 0x08000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `bvar` table's obligations.** -/
theorem bvarOK : ConsOK p bvarCS where
  match_ := by
    intro s
    simp [bvarCS, condOf, Cond.pval, Expr.pval, bmatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [bvarCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, bvarHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, bvarCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, bvarHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [bvarCS, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; simp [Expr.pval, h],
    fun s => by simp [bvarCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [bvarCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by intro e he; simp [bvarCS] at he
  pre := rfl
  colA := by simp [bvarCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [bvarCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [bvarCS] at h
  mloc := fun h => by simp [bvarCS] at h
  exnk := fun _ => by decide

theorem bpushOK_eqC (m : Mem) (t : Word) : bpushOK m t = pushOKC bvarCS m t := by
  simp only [bpushOK, pushOKC, bcnt, cntC, bvarCS, ← decide_not, UInt64.not_le]; rfl

theorem internBVar_spec (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hp : p.lookup "intern_bvar" = some internBVar)
    (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_bvar" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ binternW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p bvarCS (bvarOK p) hpf hpp "intern_bvar" hp n s₀ [u] rfl trivial

end specs

end L.Arena
