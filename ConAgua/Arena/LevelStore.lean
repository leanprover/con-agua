module

meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
public import ConAgua.Arena.LpCol
public import ConAgua.Arena.ConsLibSpec
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The level `succ` node store in L: a third store, one handle field per node

The arena's level store keeps `succ u` nodes in a `Tbl SuccNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.succs`). Its L representation is the `app` store's
(`AppStore.lean`) with one word per node and no scratch skip (`LStore.find?` probes the
persistent tier unconditionally):

* **Records.** Word array `SREC`, one word per node (the handle word of `u`), tiers
  interleaved: node `i` of tier `t` at `SREC[2 i + t]`. The node count of tier `t` is
  `CTL[6 + t]`.
* **Cons table.** Word array `SSLOT`, the same open addressing as `SLOT`.

The functions: `succ_find(t, u, h)`, `succ_push(t, u, j)` and `intern_succ(u)`. They are the cons-table library's templates
(`ConsLib.lean`) at the schema `succCS`, the derived column written by the template's prelude;
their specs are the library's (`ConsLibSpec.lean`) from this table's obligations.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The hash of a `succ` record (FNV-1a over its word). -/
def succHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `succ u`. -/
def smatchW (r : Array Word) (_t i u : Word) : Bool := rdW r i == u

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `succ` tier (tag `1`). -/
def succP : Word := 0x10000000
def succS : Word := 0x18000000

/-- The hash of node `i` of tier `t`. -/
def shash (m : Mem) (t i : Word) : Word := succHashW (rdW (m.arr64 (tierA SREC t)) i)

/-- The column's prelude in the template's layout (`hpBlkS` with the push's `k` inserted before
`x`): `x := lvlHP(u)`. -/
def sPre : Stmt := mapS (fun v => if v < 4 then v else v + 1) hpBlkS

/-- The `succ` table as a cons schema (`ConsLib.lean`); the derived column `SHP`
(the child's `hasParam` bit, `hpBlkS`). -/
def succCS : ConsSch where
  ra := SREC
  sa := SSLOT
  w := 1
  ca := 6
  P := succP
  S := succS
  tag := 1
  fname := "succ_find"
  pname := "succ_push"
  nk := 1
  exact := true
  mc := condOf (lblk (t, u, h, n, j, d, v, b) {
    if SREC⟨t⟩[(v - 1)] == u { skip } })
  np := 1
  room := condOf (lblk (t, u, j, c) {
    if len(SREC⟨t⟩) <= c || len(SHP⟨t⟩) <= c { skip } })
  recW := [.var 1]
  ihash := lblk (u, h) { h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ }
  skipW := none
  xloc := 4
  pre := some sPre
  col := some SHP
  colM m as := lvlHPW m (as.getD 0 0)
  mtM m ks t i := smatchW (m.arr64 (tierA SREC t)) t i (ks.getD 0 0)
  qhM _ ks := succHashW (ks.getD 0 0)
  hsM := shash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA SREC t) ≤ c) || decide (m.len64 (tierA SHP t) ≤ c)

/-! ## `succ_find(t, u, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def succFind : FunDecl := consFindG succCS

/-! ## `succ_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `succ` table, `CTL[6 + t]`. -/
def scnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (6 + t)

/-- `succ_push`'s room checks: the handle index, the record array. -/
def spushOK (m : Mem) (t : Word) : Bool :=
  decide (scnt m t < (134217728 : Word)) && decide (scnt m t < m.len64 (tierA SREC t)) &&
    decide (scnt m t < m.len64 (tierA SHP t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def succPush : FunDecl := consPushG succCS

/-! ## `intern_succ(u)`: hash-cons the level `succ u`

con-ron's `LStore::intern` at `succ` and the arena's `internLNode (.succ u)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_succ`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def sinternW (m : Mem) (u : Word) : Option (Word × Mem) := consInternM succCS m [u]

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internSucc : FunDecl := consInternG succCS

/-- The `succ` store functions, as one `#eval`-able program. -/
def succProg : Prog :=
  [("succ_find", succFind), ("succ_push", succPush), ("intern_succ", internSucc)]

/-- A memory with 8 `succ` nodes and `SN0` slots per tier, the scratch tier closed or open. -/
def succMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], Array.replicate 16 0,
      Array.replicate consTestWords 0] ++ Array.replicate 62 (Array.replicate consTestWords 0) }

/-- Intern each word in turn; the handles. -/
def internSuccs (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run succProg 100 "intern_succ" [u] m with
    | .ok (r, m') => (internSuccs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `succ 0`, `succ 1`, `succ 0`, `succ (succ 0)`: persistent handles 0, 1, 0, 2. -/
#guard internSuccs (succMem 0) [0, 1, 0, 0x10000000] ==
  some [0x10000000, 0x10000001, 0x10000000, 0x10000002]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internSuccs (succMem 1) [0, 1, 0] == some [0x18000000, 0x18000001, 0x18000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

theorem sPre_spec (k : Stmt → M Sig) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k sPre
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 5 = lvlHPW s₀.mem (s₀.loc 1); ⊤⦄ := by
  simp only [sPre, hpBlkS, mapS, mapE_tld, mapE_cntE, mapE_tierE, mapE_idxE, mapE, mapC, L.Notation.blk]
  simp only [Nat.reduceLT, Nat.reduceAdd, ↓reduceIte]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [lvlHPW, tierW, idxW]

/-- **The `succ` table's obligations.** -/
theorem succOK : ConsOK p succCS where
  match_ := by
    intro s
    simp [succCS, condOf, Cond.pval, Expr.pval, smatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [succCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, succHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, succCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, succHashW, argsOf, BinOp.eval]
  pre := by
    intro n s₀
    vcgen [sPre_spec p (exec p n) s₀]
    all_goals obtain ⟨h0, h1, h2, hx⟩ := ‹_ ∧ _›
    · assumption
    · intro x hx'
      simp only [succCS] at hx'
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2) with rfl | rfl | rfl <;> assumption
    · simp [succCS, argsOf, List.range_succ, hx]
  colA := by
    intro A h
    simp only [succCS, Option.some.injEq] at h
    subst h; decide
  recs := ⟨by
      intro e he s s' h
      simp only [succCS, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; simp [Expr.pval, h],
    fun s => by simp [succCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [succCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by
    intro e he
    simp [succCS] at he
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [succCS, Option.some.injEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [succCS] at h
  mloc := fun h => by simp [succCS] at h
  exnk := fun _ => by decide

theorem spushOK_eqC (m : Mem) (t : Word) : spushOK m t = pushOKC succCS m t := by
  simp only [spushOK, pushOKC, succCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem internSucc_spec (hpf : p.lookup "succ_find" = some succFind)
    (hpp : p.lookup "succ_push" = some succPush) (hp : p.lookup "intern_succ" = some internSucc)
    (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_succ" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ sinternW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p succCS (succOK p) hpf hpp "intern_succ" hp n s₀ [u] rfl trivial

end specs

end L.Arena
